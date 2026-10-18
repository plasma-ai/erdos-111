module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Erdős Problem 111: bipartizing finite subgraphs of uncountably chromatic graphs

For a graph `G`, let `h G n` be the least bound such that every subgraph of `G`
on `n` vertices can be made bipartite by deleting at most `h G n` edges. Erdős
asked for the behaviour of `h G n`, and whether `h G n / n → ∞` for every graph
`G` of chromatic number `ℵ₁`.

**Claim.** For every `C ≥ 0`, a graph in which every finite subgraph on `m`
vertices can be made bipartite by deleting at most `C m` edges has countable
chromatic number. Hence `h G n / n → ∞` for every graph `G` that is not
countably colorable, of any cardinality, and in particular for every graph of
chromatic number `ℵ₁`. This answers the second question of Erdős Problem 111
in the affirmative.

Thomas F. Bloom catalogs the question as
[Erdős Problem 111](https://www.erdosproblems.com/111).

The three theorems below have deliberate proof holes. `Solution.lean` supplies
their proofs, and Comparator checks them against these statements.
-/

@[expose] public section

open Filter
open scoped Cardinal

universe u

namespace Erdos111

/-- The least number of edges whose deletion leaves the subgraph `H` bipartite. -/
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

/-- A graph in which every finite subgraph on `m` vertices can be made bipartite by
deleting at most `C m` edges has countable chromatic number. -/
theorem countably_colorable_of_linear {V : Type u} (G : SimpleGraph V) (C : ℝ)
    (hC : ∀ H : G.Subgraph, H.verts.Finite →
      (bipartizationNumber H : ℝ) ≤ C * H.verts.ncard) :
    Nonempty (G.Coloring ℕ) := by
  sorry

/-- `h G n / n → ∞` for every graph `G` that is not countably colorable. -/
theorem tendsto_of_not_countably_colorable {V : Type u} (G : SimpleGraph V)
    (hG : IsEmpty (G.Coloring ℕ)) :
    Tendsto (fun n : ℕ => (h G n : ℝ) / n) atTop atTop := by
  sorry

/-- Erdős Problem 111: `h G n / n → ∞` for every graph `G` of chromatic number `ℵ₁`. -/
theorem erdos_111 {V : Type u} (G : SimpleGraph V) (hG : chromaticCardinal G = ℵ₁) :
    Tendsto (fun n : ℕ => (h G n : ℝ) / n) atTop atTop := by
  sorry

end Erdos111
