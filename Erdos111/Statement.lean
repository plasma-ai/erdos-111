module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Statement of Erdős Problem 111: bipartizing finite subgraphs of uncountably chromatic graphs

The definitions here repeat those of `Challenge.lean` for the proof
development; Comparator requires them to agree exactly.
-/

@[expose] public section

universe u

namespace Erdos111

/-- The least number of edges whose deletion leaves the subgraph `H` bipartite, for `H`
with finitely many vertices (the only case used below). -/
noncomputable def bipartizationNumber {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) : ℕ :=
  sInf {k : ℕ | ∃ D ⊆ H.edgeSet, D.ncard = k ∧ (H.deleteEdges D).coe.IsBipartite}

/-- `h G n` is the least bound such that every subgraph of `G` on `n` vertices can be
made bipartite by deleting at most `h G n` edges. -/
noncomputable def h {V : Type*} (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ H : G.Subgraph, H.verts.Finite ∧ H.verts.ncard = n ∧
    bipartizationNumber H = k}

/-- The chromatic number of `G` as a cardinal: the least cardinality of a set of colors
that properly colors `G`. -/
noncomputable def chromaticCardinal {V : Type u} (G : SimpleGraph V) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ α : Type u, Cardinal.mk α = κ ∧ Nonempty (G.Coloring α)}

end Erdos111
