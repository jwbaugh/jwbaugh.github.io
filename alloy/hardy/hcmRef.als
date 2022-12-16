module hcmRef

/*
 * A refinement with communicating processes: a process for each joint
 *   and communication between them using synchronous message passing
 *
 * For a detailed description, see:
 *
 *   Models of Scientific Software: A State-Based Approach, submitted
 *     John Baugh, Tristan Dyer, and Alper Altuntas
 *
 * Date: January 29, 2019
 * Alloy Analyzer 5.0.0
 *
 */

open hcmSpec

abstract sig Counter {}
one sig Test, Send, Recv extends Counter {}

sig State_R extends State {
   pc: Joint -> one Counter
}

pred init_R [s: State_R] {
   no s.pending
   all u: Joint | s.pc[u] = Test
}

pred step_R [s, s': State_R] {
   some u: Joint | process[u, s, s']
}

-- associate a concurrent process with each joint
pred process [u: Joint, s, s': State_R] {
   test[u, s, s'] or leave_send[u, s, s'] or leave_receive[u, s, s']
      or one v: Joint | synch[u, v, s, s']
}

pred test [u: Joint, s, s': State_R] {
   s.pc[u] = Test
   (u not in Fixed and enter_send[u, s, s']) or enter_receive[u, s, s']
}

pred enter_send [u: Joint, s, s': State_R] {
   u not in s.balanced
   s'.pc = s.pc ++ u->Send
   s'.balanced = s.balanced + u
   s'.pending = s.pending + u <: neighbors
}

pred leave_send [u: Joint, s, s': State_R] {
   s.pc[u] = Send and no v: Joint | u->v in s.pending
   s'.pc = s.pc ++ u->Test
   s'.balanced = s.balanced      -- u made balanced in enter_send, leave as is
   s'.pending = s.pending
}

pred enter_receive [u: Joint, s, s': State_R] {
   some x: Joint | x->u in s.pending and s.pc[x] = Send
   s'.pc = s.pc ++ u->Recv
   s'.balanced = s.balanced
   s'.pending = s.pending
}

pred leave_receive [u: Joint, s, s': State_R] {
   s.pc[u] = Recv and no x: Joint | x->u in s.pending
   s'.pc = s.pc ++ u->Test
   s'.balanced = s.balanced
   s'.pending = s.pending
}

pred synch [u, v: Joint, s, s': State_R] {
   s.pc[u] = Send and s.pc[v] = Recv and u->v in s.pending
   s'.pc = s.pc                      -- all modes remain unchanged
   s'.balanced = s.balanced - v      -- but receiver becomes unbalanced
   s'.pending = s.pending - u->v     -- and the edge token is consumed
}

-- a process associated with a joint cannot have moments to carry over unless
-- it is in send mode
pred inv_R [r: State_R] {
   no u: Joint | r.pc[u] != Send and some v: Joint | u->v in r.pending
}

-- show that inv_R is an inductive invariant
assert check_inv {
   all r, r': State_R {
      init_R[r] => inv_R[r]
      inv_R[r] and step_R[r, r'] => inv_R[r']
   }
}

check check_inv for 10

-- Refinement checking

-- see Table 18.2 Rules for functional refinement, p. 285
--   Uzing Z, Woodcock and Davies

-- The retrieve relation is a total, surjective function from
-- refinement R to specification S, i.e., every state in R maps to
-- exactly one state in S, i.e., an abstraction function

-- a definition of the abstraction function as a predicate
pred alpha [r: State_R, s: State - State_R] {
  s.pending = r.pending and s.balanced = r.balanced
}

assert refines {
   all r, r': State_R, s, s': State - State_R {
      alpha[r, s] and init_R[r] => init[s]
      inv_R[r] and alpha[r, s] and alpha[r', s']
         and step_R[r, r'] => step[s, s']
   }
}

check refines for 10
