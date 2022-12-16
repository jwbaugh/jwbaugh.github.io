module fullsub

/*
 * Compare full and subdomain runs of the wet-dry algorithm
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
 *     => Section 5. Full and subdomain runs
 */

open mesh
open wetdry
open util/relation             -- dom
open util/ordering [F] as fo   -- full domain states
open util/ordering [S] as so   -- subdomain states

-- separate states are needed for full domain and subdomain runs
sig F, S extends State {}

fact { all s: State | s in F + S }         -- or declare State abstract

-- define full domain and subdomain meshes
one sig Full, Sub extends Mesh {}

fact { all m: Mesh | m in Full + Sub }     -- or declare Mesh abstract

-- subdomain elements are a subset of full domain elements
fact { all e: Sub.elements | e in Full.elements }

-- identify nodes that appear on a subdomain interface: it's a node on a
--   subdomain border that's incident to an element in Omega_E
pred gamma [m: Mesh, n: Node] {
  m = Sub and borderVertex[m, n]
  some incidentElts[Full, n] - incidentElts[Sub, n]
}

fun incidentElts[m: Mesh, n: Node]: set Element {
  { e: m.elements | n in dom[e.edges] }
}

-----------------------------------------------------------------------------

-- correctness condition: WITHOUT forcing boundary conditions

assert SameFinalStates {
  let f = toSeq[fo/first, fo/next], s = toSeq[so/first, so/next] |
    { all n: Sub.nodes | n.W.(s[0]) = n.W.(f[0])
      solve[Full, f]
      solve[Sub, s]
    }
    implies all n: Sub.nodes | n.W.(s[5]) = n.W.(f[5])
}

check SameFinalStates for 2 Mesh, 3 Triangle, 5 Vertex, 12 State, 6 F, 6 S, 6 int

-----------------------------------------------------------------------------

-- correctness condition: WITHOUT forcing but with Sub.elements = Full.elements

assert SameFinalStates2 {
  let f = toSeq[fo/first, fo/next], s = toSeq[so/first, so/next] |
    { all n: Sub.nodes | n.W.(s[0]) = n.W.(f[0])
      solve[Full, f]
      solve[Sub, s]
      Sub.elements = Full.elements -- subdomain covers the entire full domain
    }
    implies all n: Sub.nodes | n.W.(s[5]) = n.W.(f[5])
}

check SameFinalStates2 for 2 Mesh, 5 Triangle, 7 Vertex, 12 State, 6 F, 6 S, 6 int

-----------------------------------------------------------------------------

-- correctness condition: WITHOUT forcing but check just the non-gamma part
--   of Sub

assert SameFinalStates3 {
  let f = toSeq[fo/first, fo/next], s = toSeq[so/first, so/next] |
    { all n: Sub.nodes | n.W.(s[0]) = n.W.(f[0])
      solve[Full, f]
      solve[Sub, s]
    }
    implies all n: Sub.nodes | not gamma[Sub, n] implies n.W.(s[5]) = n.W.(f[5])
}

-- need just 2 elements here to generate a counterexample
check SameFinalStates3 for 2 Mesh, 2 Triangle, 4 Vertex, 12 State, 6 F, 6 S, 6 int

-----------------------------------------------------------------------------

-- correctness condition: forcing initial states of gamma with final states
--   from the full domain

assert SameFinalStates4 {
  let f = toSeq[fo/first, fo/next], s = toSeq[so/first, so/next] |
    { all n: Sub.nodes |
        n.W.(s[0]) = (gamma[Sub, n] implies n.W.(f[5]) else n.W.(f[0]))
      solve[Full, f]
      solve[Sub, s]
    }
    implies all n: Sub.nodes | n.W.(s[5]) = n.W.(f[5])
}

check SameFinalStates4 for 2 Mesh, 2 Triangle, 4 Vertex, 12 State, 6 F, 6 S, 6 int

-----------------------------------------------------------------------------

-- nodal wetting (propagate wetness across triangle if flow is not slow)
--   [like part2, but applies boundary conditions]
pred part2_bcs [m: Mesh, s, s': State] {
  noElementChange[m, s, s']
  all n: m.nodes {
    n.W.s' = n.W.s
    n.Wt.s' = (gamma[m, n] implies n.W.fo/last
                else (make_wet[m, n, s] implies True else n.Wt.s))
  }
}

-- nodal drying (make landlocked nodes dry)
--   [like part4, but applies boundary conditions]
pred part4_bcs [m: Mesh, s, s': State] {
  noElementChange[m, s, s']
  all n: m.nodes {
    n.W.s' = n.W.s
    n.Wt.s' = (gamma[m, n] implies n.W.fo/last
                else (make_dry[m, n, s] implies False else n.Wt.s))
  }
}

pred solve_bcs [m: Mesh, s: Int -> State] {
    init[m, s[0]]
    part1[m, s[0], s[1]]
    part2_bcs[m, s[1], s[2]]
    part3[m, s[2], s[3]]
    part4_bcs[m, s[3], s[4]]
    part5[m, s[4], s[5]]
}

-- introducing this fact reduces the time required to check assertions
fact NoCutPointsFact {
  all m: Mesh, v: Vertex |
    borderVertex[m, v] or interiorVertex[m, v]
}

-----------------------------------------------------------------------------

-- correctness condition: FORCING boundary conditions

assert SameFinalStates5 {
  let f = toSeq[fo/first, fo/next], s = toSeq[so/first, so/next] |
    { all n: Sub.nodes | n.W.(s[0]) = n.W.(f[0])
      solve_bcs[Full, f]
      solve_bcs[Sub, s]
    }
    implies all n: Sub.nodes | n.W.(s[5]) = n.W.(f[5])
}

check SameFinalStates5 for 2 Mesh, 4 Triangle, 6 Vertex, 12 State, 6 F, 6 S, 6 int

check SameFinalStates5 for 2 Mesh, 5 Triangle, 7 Vertex, 12 State, 6 F, 6 S, 6 int
