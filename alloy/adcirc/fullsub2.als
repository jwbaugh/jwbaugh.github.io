module fullsub2

/*
 * Compare full and subdomain runs: alternative approach
 *
 * Authors: John Baugh and Alper Altuntas
 * Date: August 8, 2017
 * Alloy Analyzer 4.2_2015-02-22 (build date: 2015-02-22 18:21 EST)
 *
 * For a detailed description, see:
 *
 *   Formal methods and finite element analysis of hurricane storm surge:
 *   A case study in software verification, Science of Computer Programming
 *
 *     => Section 5.2. An alternative approach for full and subdomain runs
 */

open mesh
open util/relation                  -- dom
open util/ordering [F] as fo        -- full domain states
open util/ordering [S] as so        -- subdomain states

abstract sig Bool {}
one sig True, False extends Bool {}

-- separate states are needed for full domain and subdomain runs
sig F, S extends State {}

fact { all s: State | s in F + S }         -- or declare State abstract

sig Node extends Vertex {
  W, Wt: Bool one -> State,
  H: Height                    -- water column height
}

fact { all v: Vertex | v in Node }         -- or declare Vertex abstract

-- The declaration "W, Wt: Bool one -> State" is equivalent to saying:
-- fact { all n: Node | all s: State | one n.W.s and one n.Wt.s }

sig Element extends Triangle {
  wet: Bool one -> State,
  slowFlow: Bool,             -- Vss(e) <= Vmin
  lowNode: Node               -- node with the lowest water surface elevation
}

fact { all t: Triangle | t in Element }    -- or declare Triangle abstract

-- incident node with lowest water surface elevation must indeed be incident
fact { all e: Element | e.lowNode in dom[e.edges] }

sig State {}

abstract sig Height {}
one sig Low, Med, High extends Height {}

-- height values:
--   Low  :  H < H_0
--   Med  :  H_0 < H < 1.2 H_0
--   High :  H > 1.2 H_0


// BEGIN alternative approach

sig Interface extends Node {  -- subdomain interface node is incident to an
                              --   imaginary element e in Omega_E that:
  allowsWetting: Bool,        --     has exactly 2 wet nodes and Vss(e) > Vmin
  preventsDrying: Bool        --     is active
}

-- subdomain interface nodes can appear only on a domain border
fact { all m: Mesh, i: Interface | borderVertex[m, i] }

// END alternative approach


-- the set of all nodes in a mesh
fun nodes [m: Mesh]: set Node { dom[m.triangles.edges] }

-- the set of all elements in a mesh
fun elements [m: Mesh]: set Element { m.triangles }


-- Wetting and drying algorithm

-- Initialization (start with triangles wet and vertices either wet or dry)
pred init [m: Mesh, s: State] {
  all e: m.elements | e.wet.s = True
  all n: m.nodes | n.W.s = n.Wt.s
}

-- nodal drying (consider vertices with low water column height to be dry)
pred part1 [m: Mesh, s, s': State] {
  noElementChange[m, s, s']
  all n: m.nodes |
    n.W.s = True and n.H = Low
      implies n.W.s' = False and n.Wt.s' = False
      else n.W.s' = n.W.s and n.Wt.s' = n.Wt.s
}

// BEGIN alternative approach

-- nodal wetting (propagate wetness across triangle if flow is not slow)
pred part2_orig [m: Mesh, s, s': State] {
  noElementChange[m, s, s']
  all n: m.nodes {
    n.W.s' = n.W.s
    n.Wt.s' = (make_wet[m, n, s] implies True else n.Wt.s)
  }
}

-- nodal wetting (propagate wetness across triangle if flow is not slow)
-- (force subdomain boundaries with full domain state)
pred part2 [m: Mesh, s, s': State] {
  noElementChange[m, s, s']
  all n: m.nodes {
    n.W.s' = n.W.s
    n.Wt.s' = (s in S and n in Interface implies n.W.fo/last
                else (make_wet[m, n, s] implies True else n.Wt.s))
  }
}

-- define the conditions that cause a node to become wet
-- (include the possibility that an external element in the full domain
--   can CAUSE a node to become wet)
pred make_wet [m: Mesh, n: Node, s: State] {
  (some e: m.elements | e.slowFlow = False and loneDryNode[n, e, s])
  or (s in F and n in Interface and n.allowsWetting = True)
}

// END alternative approach

pred loneDryNode [n: Node, e: Element, s: State] {
  n in dom[e.edges] and n.W.s = False and wetNodes[e, s] = 2
}

fun wetNodes [e: Element, s: State]: Int {
  #(dom[e.edges] <: W).s.True
}

-- elemental drying (allow water to build up in a "barely wet" triangle)
pred part3 [m: Mesh, s, s': State] {
  noNodeChange[m, s, s']
  all e: m.elements |
    let ij = dom[e.edges] - e.lowNode |
      e.wet.s' = (some ij.H - High implies False else e.wet.s)
}

// BEGIN alternative approach

-- nodal drying (make landlocked nodes dry)
pred part4_orig [m: Mesh, s, s': State] {
  noElementChange[m, s, s']
  all n: m.nodes {
    n.W.s' = n.W.s
    n.Wt.s' = (make_dry[m, n, s] implies False else n.Wt.s)
  }
}

-- nodal drying (make landlocked nodes dry)
-- (force subdomain boundaries with full domain state)
pred part4 [m: Mesh, s, s': State] {
  noElementChange[m, s, s']
  all n: m.nodes {
    n.W.s' = n.W.s
    n.Wt.s' = (s in S and n in Interface implies n.W.fo/last
                else (make_dry[m, n, s] implies False else n.Wt.s))
  }
}

-- define the conditions that cause a node to become dry
-- (include the possibility that an external element in the full domain
--   can PREVENT a node from becoming dry)
pred make_dry [m: Mesh, n: Node, s: State] {
  n.Wt.s = True and landlocked[m, n, s]
  not (s in F and n in Interface and n.preventsDrying = True)
}

// END alternative approach

pred landlocked [m: Mesh, n: Node, s: State] {
  no { e: m.elements | n in dom[e.edges] and active[e, s] }
}

pred active [e: Element, s: State] {
  e.wet.s = True and all n: dom[e.edges] | n.Wt.s = True
}

-- assign the final wet-dry states for nodes
pred part5 [m: Mesh, s, s': State] {
  noElementChange[m, s, s']
  all n: m.nodes | n.W.s' = n.Wt.s and n.Wt.s' = n.Wt.s
}

-- frame conditions say which parts of the state do not change

pred noNodeChange [m: Mesh, s, s': State] {
  all n: m.nodes | n.W.s = n.W.s' and n.Wt.s = n.Wt.s'
}

pred noElementChange [m: Mesh, s, s': State] {
  all e: m.elements | e.wet.s = e.wet.s'
}

-----------------------------------------------------------------------------

pred solve [m: Mesh, s: Int -> State] {
    init[m, s[0]]
    part1[m, s[0], s[1]]
    part2[m, s[1], s[2]]
    part3[m, s[2], s[3]]
    part4[m, s[3], s[4]]
    part5[m, s[4], s[5]]
}

-----------------------------------------------------------------------------

-- make a sequence from an ordering of 6 states (clumsily?)
fun toSeq [s0: State, n: State -> State]: Int -> State {
  let s1 = s0.n, s2 = s1.n, s3 = s2.n, s4 = s3.n, s5 = s4.n |
    { i: Int, s: State |
       (i = 0 and s = s0) or
       (i = 1 and s = s1) or
       (i = 2 and s = s2) or
       (i = 3 and s = s3) or
       (i = 4 and s = s4) or
       (i = 5 and s = s5)
    }
}

-----------------------------------------------------------------------------

one sig M extends Mesh {}

assert SameFinalStates {
  let f = toSeq[fo/first, fo/next], s = toSeq[so/first, so/next] |
    { all n: M.nodes | n.W.(s[0]) = n.W.(f[0])
      solve[M, f]
      solve[M, s]
    }
    implies all n: M.nodes | n.W.(s[5]) = n.W.(f[5])
}

check SameFinalStates for 8 Triangle, 10 Vertex, exactly 1 Mesh, 12 State, 6 F, 6 S, 6 int

