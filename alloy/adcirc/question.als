module question

/*
 * Question: why would an element with three wet nodes be dry?
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
 *     => Section 6. Role in understanding empirical algorithms
 */

open mesh
open wetdry
open util/relation                    -- dom, totalOrder
open util/ordering [State] as so

open util/ordering [Element] as eord  -- for generating instance in paper
open util/ordering [Node] as nord     -- ditto

one sig M extends Mesh { lte: Node -> Node }

fact { totalOrder[M.lte, M.nodes] }

fact { all e: M.elements | e.lowNode = min[M.lte, dom[e.edges]] }

fun min [r: univ->univ, s: set univ]: univ {
  { y : s | (no x: s | x -> y in r - iden) }
}

pred dryElementWetNodes {
  let s = toSeq[so/first, so/next] | solve[M, s]
  some e: M.elements |
    e.wet.so/last = False and wetNodes[e, so/last] = 3
}

run dryElementWetNodes for 1 Mesh, 3 Triangle, 4 Vertex, 6 State, 6 int

-----------------------------------------------------------------------------

-- a predicate that produces the instance shown in the paper

pred dryElementWetNodes2 {
  let e0 = eord/first, e1 = e0.next, e2 = e1.next,
      n0 = nord/first, n1 = n0.next, n2 = n1.next, n3 = n2.next {
    n0 -> n2 in e0.edges and n2 -> n3 in e0.edges and n3 -> n0 in e0.edges
    n0 -> n1 in e1.edges and n1 -> n2 in e1.edges and n2 -> n0 in e1.edges
    n2 -> n1 in e2.edges and n1 -> n3 in e2.edges and n3 -> n2 in e2.edges
    e0.lowNode = n3
    e1.lowNode = n1
    e2.lowNode = n3 
    all e: M.elements | e.slowFlow = True and e.wet.so/first = True
    all n: M.nodes | n.Wt.so/first = True
    n0.H = High
    n1.H = Med
    n2.H = High
    n3.H = Med
    dryElementWetNodes      -- look for a dry element with wet nodes
  }
}

run dryElementWetNodes2 for 1 Mesh, 3 Triangle, 4 Vertex, 6 State, 6 int

