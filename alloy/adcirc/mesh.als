module mesh

/*
 * Model the topology of meshes that are made up of triangles and vertices
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
 *     => Section 3. Statics: Representing a mesh
 */

open util/relation             -- dom, ran, symmetric, irreflexive

sig Mesh {
  triangles: some Triangle,
  adj: Triangle -> Triangle  
}

sig Triangle {
  edges: Vertex -> Vertex
}

sig Vertex {}

-- every triangle appears in some mesh
fact { all t: Triangle | t in Mesh.triangles }

-- every vertex appears in some triangle
fact { all v: Vertex | v in dom[Mesh.triangles.edges] }

-- every triangle has 3 edges
fact { all t: Triangle | #t.edges = 3 }

-- the edge set of each triangle forms a ring
fact { all t: Triangle | ring[t.edges] }

-- the edge set e forms a ring
pred ring [e: Vertex->Vertex] {
  all v: dom[e] | one v.e and dom[e] in v.^e
}

-- The use of "one v.e" above ensures that each vertex has exactly one
-- successor, so all we need to add for a ring is the constraint that all
-- vertices are reachable from any vertex by following edges repeatedly.

-- no two triangles in the same mesh can share the same edge
fact { all m: Mesh | all disj t, t': m.triangles | no t.edges & t'.edges }

-- triangles in the m.adj relation must be in the set m.triangles
fact { all m: Mesh | dom[m.adj] + ran[m.adj] in m.triangles }

-- properties of the dual of a mesh, viewing triangles as dual nodes
fact {
  all m: Mesh |
    let r = m.adj, s = m.triangles |
      symmetric[r] and irreflexive[r] and stronglyConnected[r, s]
}

-- A strongly connected digraph is a directed graph in which it is
-- possible to reach any node starting from any other node by traversing
-- edges in the direction(s) in which they point.

pred stronglyConnected[r: univ -> univ, s: set univ] {
  all x, y: s | x in y.*r
}

-- Note in the above that stronglyConnected needs REFLEXIVE transitive
-- closure, otherwise a mesh with one triangle is disallowed

-- triangles that share a pair of incident vertices define the adj relation
fact { all m: Mesh, t, t': m.triangles |
          t in m.adj[t'] iff one ~(t.edges) & t'.edges }

-- the number of "undirected" edges (considering interior ones as half edges)
fun undirectedEdges [m: Mesh]: Int {
  minus[#m.triangles.edges, div[#m.adj, 2]]
}

-- Note in the above that the number of tuples in m.adj will equal the number
-- of interior edges, or: #m.adj = #(~e & e) where e = m.triangles.edges

-- Euler's formula: T - 1 = E - V
fact {
  all m: Mesh |
    let T = #m.triangles, E = undirectedEdges[m], V = #dom[m.triangles.edges] |
      minus[T, 1] = minus[E, V]
}

/*
 *  Euler's formula for a simple closed polygon
 *
 *  Given a polygon that does not cross itself, we can triangulate the
 *  inside of the polygon into non-overlapping triangles such that any two
 *  triangles meet (if at all) either along a common edge, or at a common
 *  vertex. Suppose that there are T triangles, E edges, and V vertices;
 *  then Euler's formula for a polygon is T - E + V = 1.
 */

-- a border vertex has exactly two border edges that are incident on it
--   (a border edge has no anti-parallel mate)
pred borderVertex [m: Mesh, v: Vertex] {
  let e = m.triangles.edges | #symDiff[e.v, v.e] = 2
}

-- an interior vertex is one whose incident edges all have an anti-parallel
--   mate
pred interiorVertex [m: Mesh, v: Vertex] {
  let e = m.triangles.edges | no symDiff[e.v, v.e]
}

-- symmetric difference of two sets
fun symDiff [a, b: univ]: univ { (a + b) - (a & b) }

-----------------------------------------------------------------------------

pred show {
     #Mesh = 1
     #Triangle = 3
--   # Triangle = 1 produces 1 topology, 1 instance
--              = 2 produces 1 topology, 3 instances
--              = 3 produces 2 topologies, 12 instances
--                    6 w/ 4 vertices, 6 w/ 5 vertices
--     #Vertex = 6
--     some t: Triangle | dom[t.edges] != ran[t.edges]
}

run show for 6 but 8 int

-- max integer for "n int" = 2^(n-1) - 1
--    n = 10, max = 511
--    n =  9, max = 255
--    n =  8, max = 127
--    n =  7, max =  63
--    n =  6, max =  31
--    n =  5, max =  15
--    n =  4, max =   7

-- In fun undirectedEdges we have #m.triangles.edges, so we need an int
-- big enough to allow us to count these.  Ensuring that max is at least
-- 3 * #Triangles is probably a good rule of thumb.

-----------------------------------------------------------------------------

-- at most two border edges for a vertex is already implied, but we
-- can check to make sure that "local cut points" are disallowed

assert NoCutPoints {
  all m: Mesh, v: Vertex | borderVertex[m, v] or interiorVertex[m, v]
}

check NoCutPoints for 1 Mesh, 6 Triangle, 9 Vertex, 6 int

/*
Executing "Check NoCutPoints for 6 int, 1 Mesh, 6 Triangle, 9 Vertex"
   Solver=lingeling(jni) Bitwidth=6 MaxSeq=4 SkolemDepth=1 Symmetry=20
   44179 vars. 554 primary vars. 105263 clauses. 205ms.
   No counterexample found. Assertion may be valid. 53390ms.
   (about 53 sec)

Executing "Check NoCutPoints for 6 int, 1 Mesh, 7 Triangle, 10 Vertex"
   Solver=lingeling(jni) Bitwidth=6 MaxSeq=4 SkolemDepth=1 Symmetry=20
   68213 vars. 785 primary vars. 162500 clauses. 203ms.
   No counterexample found. Assertion may be valid. 441009ms.
   (about 7 min 21 sec)
*/

-----------------------------------------------------------------------------

/*
   Comments on ring:

   -- the edge set e forms a ring
   pred ring [e: Vertex->Vertex] {
     all v: dom[e] | one v.e and dom[e] in v.^e
   }

   without "one v.e" we might have, for instance, a triangle t0
     with t0.edges = {v0->v0, v0->v1, v0->v2}
     and v0.(t0.edges) = {v0, v1, v2}
   without "dom[e] in v.^e" we might have, for instance, a triangle t0
     with t0.edges = {v0->v1, v1->v0, v2->v2}
     and v0.^(t0.edges) = {v0, v1}, v1.^(t0.edges) = {v0, v1},
     and v2.^(t0.edges) = {v2}

   As Jackson writes on p. 173 (tailored to our problem):

   The vertices are to form a ring.  The use of "one v.e" ensures that
   each vertex has exactly one successor, so all we need to add is the
   constraint that all vertices are reachable from any vertex by
   following edges repeatedly.
*/
