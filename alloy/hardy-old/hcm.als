module hcm

/*
 * Specification & refinement of the Hardy Cross method of moment distribution
 *
 * Authors: John Baugh and Tristan Dyer
 * Date: February 4, 2018
 * Alloy Analyzer 4.2_2015-02-22 (build date: 2015-02-22 18:21 EST)
 *
 */

-- let joints have a state "balanced" (a Boolean for each vertex), and
-- include just one type of pending operation (a carryover, another
-- Boolean, on each edge) ... assume that release and distribute are
-- combined into an atomic operation.  Then, a carryover operation,
-- when processed, makes an adjacent joint unbalanced.

open util/graph [Vertex]
open util/ordering [State] as so

abstract sig Bool {}
one sig True, False extends Bool {}

abstract sig Counter {}
one sig Test, Send, Recv extends Counter {}

sig State {}

sig Vertex {
  fixed: Bool,                      -- joint is prevented from rotating
  balanced: Bool one -> State,      -- moments of adjoining ends are balanced
  moment: Vertex -> Bool -> State,  -- carry a moment over to an adjacent joint
  pc: Counter lone -> State,        -- program counter (only for the refinement)
}

-- graph edges are defined by vertex pairs that carry over moments
fun edges: Vertex->Vertex { { x, y: Vertex | some moment[x, y] } }

-- minimal topological requirements for representing a building structure
-- (since some cannot be realized in practice, this is an over-approximation)
fact { noSelfLoops[edges] and undirected[edges] and stronglyConnected[edges] }

-- moments can be carried over from one joint to another, one at a time
fact { all x, y: Vertex, s: State | x->y in edges => one moment[x, y].s }

------------------------------------------------------------------------------

-- Specification S

-- start with no moments to carry over
pred init_S [s: State] {
  all x, y: Vertex |
    x->y in edges => moment[x, y].s = False
}

-- release and balance a joint, carry over a moment, or stutter
pred step_S [s, s': State] {
  (some x: Vertex | x.fixed = False and release[x, s, s'])
  or (some x, y: Vertex | x->y in edges and carryover[x, y, s, s'])
  or stutter[s, s']
}

pred stutter [s, s': State] {
  all x: Vertex |
    x.balanced.s' = x.balanced.s
  all x, y: Vertex |
    x->y in edges => moment[x, y].s' = moment[x, y].s
}

-- enabled when u is unbalanced and has no moment to carry over
pred release [u: Vertex, s, s': State] {
  u.balanced.s = False and not pending[u, s]
  all x: Vertex |                                          -- distribution
    x.balanced.s' = (x = u => True else x.balanced.s)
  all x, y: Vertex | x->y in edges =>                      -- carry over
    moment[x, y].s' = (x = u => True else moment[x, y].s)
}

-- carry a moment from u over to v, making v unbalanced
pred carryover [u, v: Vertex, s, s': State] {
  moment[u, v].s = True
  all y: Vertex |
    y.balanced.s' = (y = v => False else y.balanced.s)
  all x, y: Vertex | x->y in edges =>
    moment[x, y].s' = (x = u and y = v => False else moment[x, y].s)
}

-- a moment from u is waiting to be carried over
pred pending [u: Vertex, s: State] {
  some v: Vertex | u->v in edges and moment[u, v].s = True
}

------------------------------------------------------------------------------

-- generate some instances

pred show_S {
  no pc -- not needed for specification S
  no x: Vertex | x = A or x = B or x = C -- disable Baugh/Liu example
  #Vertex > 1
  init_S[so/first]
  all s: State - so/last | step_S[s, s.so/next]
}

run show_S for 4 Vertex, 10 State

-- example from Baugh/Liu

lone sig A, B, C extends Vertex {}

pred example [a_fixed: Bool] {
  all x: Vertex | x = A or x = B or x = C -- or declare Vertex abstract
  all x: Vertex | x.balanced.so/first = False
  A.fixed = a_fixed and B.fixed = False and C.fixed = False
  A->B in edges
  B->C in edges
  A->C not in edges
}

pred show_S_ex {
  no pc -- not needed for specification S
  init_S[so/first]
  all s: State - so/last | step_S[s, s.so/next]
  example[True]
  possible_steps
--  broken_steps
}

run show_S_ex for 3 Vertex, 11 State -- 11 states needed for my_steps

-- a sample trace with simultaneous releases, followed by carryovers,
-- releases, and so on ...
pred possible_steps {
  let s0 = so/first, s1 = s0.so/next, s2 = s1.so/next, s3 = s2.so/next,
    s4 = s3.so/next, s5 = s4.so/next, s6 = s5.so/next, s7 = s6.so/next,
    s8 = s7.so/next, s9 = s8.so/next, s10 = s9.so/next {
      release[B, s0, s1]
      release[C, s1, s2]
      carryover[B, C, s2, s3]
      carryover[B, A, s3, s4]
      carryover[C, B, s4, s5]
      release[B, s5, s6]
      carryover[B, C, s6, s7]
      carryover[B, A, s7, s8]
      release[C, s8, s9]
      carryover[C, B, s9, s10]
  }
}

pred broken_steps {
  let s0 = so/first, s1 = s0.so/next, s2 = s1.so/next, s3 = s2.so/next,
    s4 = s3.so/next, s5 = s4.so/next, s6 = s5.so/next, s7 = s6.so/next,
    s8 = s7.so/next {
      release[B, s0, s1]
      release[C, s1, s2]
      carryover[B, C, s2, s3]
      carryover[B, A, s3, s4]
      carryover[C, B, s4, s5]
      release[B, s5, s6]
      carryover[B, C, s6, s7]
      -- carryover[B, A, s7, s8]
      release[B, s7, s8]      -- can't release B, has a pending carryover
  }
}

------------------------------------------------------------------------------

-- Refinement R: synchronous message passing between concurrent processes

pred init_R [s: State] {
  init_S[s]
  all x: Vertex | x.pc.s = Test
}

pred step_R [s, s': State] {
  some x: Vertex | process[x, s, s']
}

-- associate a concurrent process with each vertex
pred process [u: Vertex, s, s': State] {
  test[u, s, s'] or leave_send[u, s, s'] or leave_receive[u, s, s']
  or one v: Vertex | u->v in edges and synch[u, v, s, s']
}

pred test [u: Vertex, s, s': State] {
  u.pc.s = Test
  enter_send[u, s, s'] or enter_receive[u, s, s']
}

pred enter_send[u: Vertex, s, s': State] {
  u.fixed = False and u.balanced.s = False
  u.pc.s' = Send
  u.balanced.s' = True
  all x, y: Vertex | x->y in edges =>
    moment[x, y].s' = (x = u => True else moment[x, y].s)
  unchanged[Vertex - u, none->none, s, s']
}

pred leave_send [u: Vertex, s, s': State] {
  u.pc.s = Send and no { v: Vertex | moment[u, v].s = True }
  u.pc.s' = Test
  u.balanced.s' = u.balanced.s -- was made True in test, leave as is
  unchanged[Vertex - u, edges, s, s']
}

pred enter_receive[u: Vertex, s, s': State] {
  some x: Vertex | moment[x, u].s = True and x.pc.s = Send
  u.pc.s' = Recv
  u.balanced.s' = u.balanced.s
  unchanged[Vertex - u, edges, s, s']
}

pred leave_receive [v: Vertex, s, s': State] {
  v.pc.s = Recv and no { u: Vertex | moment[u, v].s = True }
  v.pc.s' = Test
  v.balanced.s' = v.balanced.s -- was made False on synch, leave as is
  unchanged[Vertex - v, edges, s, s']
}

pred synch [u, v: Vertex, s, s': State] {
  u.pc.s = Send and v.pc.s = Recv and moment[u, v].s = True
  v.pc.s' = v.pc.s          -- receiver remains in receive mode    
  v.balanced.s' = False     -- but becomes unbalanced
  moment[u, v].s' = False   -- and the edge token is consumed
  unchanged[Vertex - v, edges - u->v, s, s']
}

pred unchanged [vs: set Vertex, es: Vertex->Vertex, s, s': State] {
  all x: vs |
    x.pc.s' = x.pc.s and x.balanced.s' = x.balanced.s
  all x, y: Vertex |
    x->y in es => moment[x, y].s' = moment[x, y].s
}

------------------------------------------------------------------------------

-- generate some instances

pred show_R_ex {
  all x: Vertex, s: State | one x.pc.s -- needed for refinement R
  init_R[so/first]
  all s: State - so/last | step_R[s, s.so/next]
  example[False]
  step_R_and_S -- comment out to generate all traces
}

run show_R_ex for 3 Vertex, 9 State

run show_R_ex for 3 Vertex, 40 State

-- show (an instance of) the relationship between S and R
pred step_R_and_S {
  let s0 = so/first, s1 = s0.so/next, s2 = s1.so/next, s3 = s2.so/next,
    s4 = s3.so/next, s5 = s4.so/next, s6 = s5.so/next, s7 = s6.so/next,
    s8 = s7.so/next {
      test[B, s0, s1] and release[B, s0, s1]     -- balance B, send to A & C
      test[A, s1, s2] and stutter[s1, s2]        -- let A enter receive mode
      test[C, s2, s3] and stutter[s2, s3]        -- let C enter receive mode
      synch[B, C, s3, s4] and carryover[B, C, s3, s4] -- pass from B to C
      leave_receive[C, s4, s5] and stutter[s4, s5] -- C returns to test
      test[C, s5, s6] and release[C, s5, s6]     -- balance C, send to B
      synch[B, A, s6, s7] and carryover[B, A, s6, s7] -- pass from B to A
      leave_send[B, s7, s8] and stutter[s7, s8]  -- B returns to test
  }
}

------------------------------------------------------------------------------

-- fails because it includes states in R that are unreachable

assert refines {
  (all x: Vertex, s: State | one x.pc.s) and example[True] =>
    let s0 = so/first, s = s0.so/next, s' = s.so/next {
        init_R[s0] => init_S[s0]
        step_R[s, s'] => step_S[s, s']
      }
}

check refines for 3 Vertex, 3 State

-- a process cannot be in test and have moments to carry over
pred unreachable [s: State] {
  some u: Vertex | u.pc.s = Test and pending[u, s]
}

pred show_unreachable {
  init_R[so/first]
  all s: State - so/last | step_R[s, s.so/next]
  some s: State | unreachable[s]
}

run show_unreachable for 5 Vertex, 30 State

-- shows that R is a refinement of specification S

assert refines2 {
  let s0 = so/first, s = s0.so/next, s' = s.so/next {
      init_R[s0] => init_S[s0]
      (not unreachable[s] and step_R[s, s']) => step_S[s, s']
    }
}

check refines2 for 10 Vertex, 3 State
