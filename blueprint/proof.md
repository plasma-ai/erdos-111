# Blueprint: countable colorings of linear graphs

This document proves, in prose, the three theorems that Comparator checks,
following the Lean development module by module. Each section names the module
and the Lean declarations it describes. The argument is Plasma AI's. This
document was written with Claude Code from Plasma AI's unpublished write-up of
the proof, which the rest of it calls the original argument; §7 lists how the
two differ.

**Conventions.** Graphs are simple. A *sign assignment* is `σ : V → Bool`; an
edge is *monochromatic* under `σ` when its two ends get the same sign. For a
finite edge set `E`, `edgeCost E` is the least number of monochromatic edges
of `E` over all sign assignments. This is the least number of edges of `E`
whose deletion leaves `E` bipartite. `G` is *`C`-linear* (`Linear G C`, with
`C ≥ 0`) if `edgeCost E ≤ C |s|` for every finite set `E` of edges of `G` with
ends in a finite vertex set `s`. Laws are probability measures on `V → Bool`
with the product σ-algebra, for an arbitrary vertex type `V`.

---

## 1. The challenge and the reduction

`Bridge.lean`.

- **Bridge.** For a finite subgraph `H` with edge set `E`,
  `bipartizationNumber H = edgeCost E` (`bipartizationNumber_eq_edgeCost`).
  - Deleting the monochromatic edges of a sign assignment leaves a 2-colorable
    graph.
  - Conversely, a 2-coloring of `H` minus `D`, extended arbitrarily to `V`,
    has all its monochromatic edges in `D`.
  - Consequences: the hypothesis of `countably_colorable_of_linear` is
    `C`-linearity (`linear_of_bipartizationNumber_le`). Every finite edge set
    of `G` with ends in an `n`-set bounds `h G n` from below
    (`edgeCost_le_h`).

`Reduction.lean`.

- **Countable deletion** (`nonempty_coloring_of_countable_compl`). If `S` is
  countable and `G - S` has a coloring by `ℕ`, so has `G`: color `S`
  injectively by odd numbers and `G - S` by even ones.
- **Packing** (`eventually_lt_h_of_uncountable`). Let uncountably many
  pairwise vertex-disjoint finite edge sets `E_i`, with ends in `s_i`, have
  `edgeCost E_i > 2K |s_i|`. The pairs `(|s_i|, edgeCost E_i)` are natural
  numbers, so infinitely many members share one size `v ≥ 1` and one cost
  `b > 2Kv`. For `n ≥ 2v`, take `q = ⌊n / v⌋` of them and pad to `n`
  vertices. Edge costs add over vertex-disjoint edge sets, so
  `h G n ≥ qb > 2K(n - v) ≥ Kn`.
- **The limit** (`tendsto_of_isEmpty_coloring`). Let `G` have no coloring
  by `ℕ`, and fix `K ≥ 0`.
  - By Zorn, take a maximal family of pairwise vertex-disjoint *witnesses*
    `(s, E)` with `edgeCost E > 2K |s|`.
  - If the family were countable, its vertex union `S` would be countable.
  - By maximality `G - S` would be `2K`-linear: a violating edge set of the
    induced graph maps injectively to a new disjoint witness.
  - So `G - S`, and by countable deletion `G`, would have a coloring by `ℕ`.
  - Hence the family is uncountable, and packing gives `h G n > K n` for all
    large `n`.
- **`ℵ₁`** (`isEmpty_coloring_of_chromaticCardinal`). A coloring by `ℕ`
  would give `chromaticCardinal G ≤ ℵ₀ < ℵ₁`.

`FinalAssembly.lean` combines these with the main theorem of §6.

---

## 2. Closure chains

`Closure.lean`, `Chain.lean`.

**Closure over a set.** `N` is *closed over* `M` (`ClosedOver G M N`) if
`M ⊆ N` and the following holds. Let `R, D ⊆ N` be finite. Let
`f : Fin m → V` be injective, with values outside `M ∪ D ∪ R`. Then some
injective `g : Fin m → V` with values in `N \ (M ∪ D ∪ R)` realizes the same
diagram over `R` (`SameDiagram`): the same adjacencies among the new vertices,
and between new vertices and roots.

This is the only property of elementary submodels that the argument uses: a
finite configuration hanging off roots in `N` and lying outside `M` has a
copy over the same roots inside `N \ M`. The finite set `D` lets copies be
chosen pairwise disjoint.

`exists_closedOver` gives, for all `M` and `X`, such an `N ⊇ M ∪ X` with
`#N ≤ max (#M + #X) ℵ₀`. Build `N` in `ω` rounds. A *request* is a tuple
`(R, D, m, A, B)` of finite root and avoidance sets in the current set, a
size `m`, and a diagram `A`, `B`. Each round adds one realization outside
`M ∪ D ∪ R` for every request that has one. There are at most
`max (#N) ℵ₀` requests, and each adds finitely many vertices.

**Chains.** For uncountable `V`, a `Chain G` consists of sets `N ξ`, for all
ordinals `ξ`, with these properties:

- `N 0 = ∅`, and `N` is monotone and continuous at limits.
- `N (ξ + 1)` is closed over `N ξ`.
- `#(N ξ) < #V` for `ξ < (#V).ord`.
- Every vertex lies in some `N (ξ + 1)` with `ξ < (#V).ord`.

`exists_chain` builds one by transfinite recursion. Enumerate `V` along the
ordinals below `(#V).ord`, and at `ξ + 1` close `N ξ` together with the
`ξ`-th vertex. This gives `#(N ξ) ≤ max ξ.card ℵ₀`. Using the initial
ordinal of `#V`, rather than a chain of length `cf #V`, avoids choosing a cover
of `V` by `cf #V` smaller sets.

**Layers and traces.**

- The *layer* of `v` is the least `ξ` with `v ∈ N (ξ + 1)`. We have
  `v ∈ N ξ ↔ layer v < ξ` (`mem_N_iff`).
- The *trace* of `v` is the set of its neighbours in `N (layer v)`. It
  contains every neighbour in an earlier layer (`mem_trace_of_layer_lt`).
- When `V` is infinite, every layer has fewer than `#V` vertices
  (`card_layer_lt`).

---

## 3. Patterns and the invariant `J`

`Basic.lean`.

**Patterns.** A pattern `P = (R, S, E)` *over* `N` (`Pattern.IsOver G N`) is
built as follows:

- `R` is a finite set of roots in `N`.
- `S` is a finite set of new vertices outside `N`.
- `E` is a finite set of edges of `G`, each meeting `S` and lying inside
  `R ∪ S`.

Its *extension cost* is `extCost S E τ`: the least number of monochromatic
edges of `E` when the signs on `S` are chosen freely and the others are those
of `τ`. It depends only on `τ` on `R` (`extCost_dependsOn`).

**The invariant `J`.** `Rooted G C N ν` states that every pattern over `N`
has `E_ν extCost ≤ C |S|`. It depends only on the finite-dimensional marginals
of `ν` on `N` (`SameOn`, `Rooted.of_sameOn`).

`rooted_empty`: for a `C`-linear graph, every law satisfies `J` over `∅`.
A pattern with no roots has all its edges inside `S`, so its extension cost
is at most `edgeCost E ≤ C |S|` whatever the signs. Starting the chain at `∅`
makes this the base case. The original argument needed a separate compactness
construction at the first model.

**Trace bounds.** `TraceBound C ν v T` states that
`∑_{u ∈ B} ν(σ_u = σ_v) ≤ C` for every finite `B ⊆ T`. It also depends only
on the marginals on `T ∪ {v}` (`TraceBound.of_sameOn`).

---

## 4. Probability tools

`Probability/`.

**Kolmogorov extension for Boolean coordinates**
(`exists_isProjectiveLimit_bool`). A projective family of probability laws
on the finite coordinate sets of `ι → Bool` has a projective limit, for any
index type `ι`.

- Every measurable cylinder is closed in the compact product topology.
- So a decreasing sequence of cylinders with empty intersection is
  eventually empty.
- Hence the family's content is σ-additive on the cylinder algebra.
- Carathéodory's construction then extends it, as Mathlib does for
  `Measure.infinitePi`.

**Limits along an ultrafilter** (`exists_limit`). Given laws `ν_a`, indexed
by `a`, and an ultrafilter `F`:

- For each finite `J`, the marginals on the finite type `J → Bool` converge
  along `F`.
- The limits form a projective family, so Kolmogorov extension gives a law
  `μ`.
- The integral of every finite-valued function of finitely many coordinates
  converges to its integral under `μ`.

Consequently every closed condition on finitely many coordinates that holds
eventually along `F` holds for `μ`. In particular `J` (`rooted_of_tendsto`),
agreement of marginals with a fixed law (`sameOn_of_tendsto`) and trace
bounds (`traceBound_of_tendsto`) pass to the limit. This replaces weak-star
compactness of Radon measures.

**Finite minimax** (`exists_mixed_le`). Take finitely many pure strategies
`x`, with payoffs `f i x` against finitely many constraints `c i`. Suppose
every nonnegative combination `∑ ρ_i f_i ≤ ∑ ρ_i c_i` is met by some pure
strategy. Then one mixed strategy meets every constraint.

*Proof.* Otherwise the image of the strategy simplex is a compact convex set
disjoint from the closed orthant below `c`. Hahn–Banach separation gives a
functional, whose coefficients are nonpositive because the orthant is
unbounded below. Its negation is a combination `ρ ≥ 0` that no pure strategy
meets.

---

## 5. The successor step

**Lemma D, derived signs** (`DerivedSign.lean`, `exists_derivedSign`). Let
`ν` satisfy `J` over `M`, and let `y ∉ M` have infinitely many neighbours in
`M`. Enumerate infinitely many of them injectively as `a 0, a 1, …`.

- **Derived sign.** Let `s(σ)` be the sign that occurs infinitely often
  along `σ(a n)`: `true` if `true` does, `false` otherwise. It is a
  measurable function of the coordinates `a n`.
- **Stars bound the minority.** A star from `y` to a finite set `B` of
  neighbours is a pattern over `M`. Its extension cost is the smaller of the
  two sign counts on `B`, so `J` bounds the expected minority on `B` by `C`.
- **Few exceptions.** The minority count along `a 0, …, a (L - 1)` increases
  with `L`. By monotone convergence its limit has expectation at most `C`,
  so it is almost surely finite. Hence almost surely only finitely many
  `σ(a n)` differ from `s(σ)`.
- **Sum bound.** For finite `B`, the star on `B ∪ {a 0, …, a (L - 1)}` costs
  at least `min(#{u ∈ B : σ_u ≠ s}, #{n < L : σ(a n) = s})`. As `L → ∞` the
  second count tends to infinity, so monotone convergence gives
  `∑_{u ∈ B} ν(σ_u ≠ s) ≤ C`.

**Forcing** (`Successor/Forcing.lean`). Let `X` be a set of vertices outside
`M` with infinite traces in `M`, each with the data of Lemma D
(`ForcingData`, `exists_forcingData`).

- The forcing map gives each `y ∈ X` the sign `¬ s_y(σ)` and keeps every
  other sign.
- The forced law `Λ = ν ∘ forced⁻¹` has the marginals of `ν` on `M`
  (`sameOn_map_forced`).
- Under `Λ`, `Λ(σ_u = σ_y) = ν(σ_u ≠ s_y)` for neighbours `u ∈ M`, so every
  `y ∈ X` has trace energy at most `C` (`traceBound_map_forced`).

**The key inequality** (`Successor/Key.lean`, `key_inequality`). Let `N` be
closed over `M`, let `ν` satisfy `J` over `M`, and let `X ⊆ N \ M` carry
forcing data. Fix the following:

- finitely many patterns `P_i = (R_i, S_i, E_i)` over `N`;
- weights `ρ_i ≥ 0`;
- a finite set `W ⊆ N \ M` containing every root that is in neither `M` nor
  `X`.

Then

    E_ν [ min_η ∑_i ρ_i · extCost(P_i)(W ← η, forced σ) ] ≤ ∑_i ρ_i C |S_i|.

*Proof.* Fix `k ≥ 1`, and put `m_i = ⌈k ρ_i⌉`.

1. **Copies.** Since `N` is closed over `M`, choose `m_i` copies of each
   `S_i` over `R_i` (`exists_copies`). They lie in `N \ M`, are pairwise
   disjoint, avoid every root, and carry the image of `E_i` as edges of `G`.
2. **The pattern `P*_L` over `M`.**
   - New vertices: the roots in `X ∪ W` and all the copies.
   - Roots: the roots in `M`, and `a_y 0, …, a_y (L - 1)` for each root
     `y ∈ X`.
   - Edges: the stars from each such `y` to its `L` trace vertices, and the
     copied edges (`starCopy`, `starCopy_isOver`).
   - By `J`, `E_ν extCost(P*_L) ≤ C (|R_X| + |W| + ∑_i m_i |S_i|)`.
3. **Pointwise lower bound** (`le_extCost_starCopy`). Almost surely, once `L`
   exceeds the number of disagreements along every `a_y` plus
   `∑_i m_i |E_i|`, `extCost(P*_L)` is at least `k` times the integrand. Take
   any choice of the new signs.
   - *Every `y` gets its forced sign.* Each copy of `P_i` costs at least
     `extCost(P_i)` at the signs `(W ← η, forced σ)`, so the total is at
     least `∑ m_i extCost(P_i) ≥ k ∑ ρ_i extCost(P_i)`.
   - *Some `y` gets `s_y`.* Then all but finitely many of its `L` star edges
     are monochromatic. That alone exceeds `∑ m_i |E_i| ≥ k ∑ ρ_i |E_i|`,
     which is at least `k` times the integrand.
4. **Limits.**
   - Fatou's lemma in `L` gives
     `k · E_ν[min_η …] ≤ C (|R_X| + |W|) + C ∑_i ⌈k ρ_i⌉ |S_i|`.
   - Divide by `k`, use `⌈k ρ_i⌉ ≤ k ρ_i + 1`, and let `k → ∞`.

Using `⌈k ρ_i⌉` copies handles real weights directly. Neither rational
approximation nor continuity in the weights is needed.

**Mixtures of couplings** (`Successor/Mixture.lean`, `exists_mixture`). Let
`A` be a set of coordinates and `W` a finite set outside it. Let `U` be a
finite set, and let finitely many costs `f_i` depend only on `U ∪ W`.

- A *coupling* chooses the signs on `W` as a function of the signs on `U`.
- Suppose every nonnegative combination of the costs has expected optimal
  value at most `∑ ρ_i c_i`. Take the pointwise optimal coupling: it meets
  that combination.
- Finite minimax then gives a mixture of couplings meeting every bound
  `E f_i ≤ c_i` at once.
- A mixture of couplings keeps the marginals on `A`.

**Lemma S** (`Successor.lean`, `exists_successor`). Let `N` be closed over
`M`, and let `ν` satisfy `J` over `M`. Then there is a law `ν'` such that:

- `ν'` has the marginals of `ν` on `M`;
- `ν'` satisfies `J` over `N`;
- every vertex of `N \ M` with infinitely many neighbours in `M` has trace
  energy at most `C` over them.

*Proof.* Let `X` be the set of such vertices, and force their signs, giving
`Λ`.

- For each finite family of patterns, take its patterns over `N`. Their
  roots in `M ∪ X` form `U`; the remaining roots form `W`.
- The key inequality, moved to `Λ`, is the hypothesis of the mixture lemma
  with `A = M ∪ X`. The mixture lemma gives a law that keeps the marginals of
  `Λ` on `M ∪ X` and satisfies `J` for those patterns.
- Take the limit along an ultrafilter finer than the filter of finite
  families. It keeps the marginals on `M ∪ X` and satisfies `J` for every
  pattern over `N`.
- Its trace bounds and its marginals on `M` come from `Λ`.

---

## 6. The limit law and the coloring

**Proposition L** (`LimitMeasure.lean`, `exists_traceBound_law`). For a
`C`-linear graph and a chain, some law gives every vertex with infinite trace
trace energy at most `C`.

*Proof.* By induction on `ξ`, show that some law satisfies `J` over every
`N ζ` with `ζ ≤ ξ`, together with the trace bound at every vertex of layer
below `ξ` with infinite trace.

- **Zero.** This is `rooted_empty`.
- **Successor `ξ + 1`.** Apply Lemma S to `N ξ ⊆ N (ξ + 1)`.
  - Its law has the old marginals on `N ξ`. These carry `J` over every
    earlier `N ζ`, and every earlier trace bound, since those vertices and
    traces lie in `N ξ`.
  - It adds `J` over `N (ξ + 1)` and the trace bounds of layer `ξ`.
- **Limit `ξ`.** Take a limit along an ultrafilter finer than `atTop` on the
  ordinals below `ξ`.
  - A pattern over `N ζ'` with `ζ' ≤ ξ` has finitely many roots. All lie in
    `N ζ₀` with `ζ₀ < ξ`, where `ζ₀` is the supremum of the successors of
    their layers. So it is a pattern over `N ζ₀`, satisfied from `ζ₀` on.
  - Every trace bound below `ξ` also holds from some stage on.

At `ξ = (#V).ord` every vertex has its layer below.

**Proposition C** (`HilbertClasses.lean`, `exists_unitVector_classes`). The
unit vectors of a real Hilbert space fall into countably many classes such
that `1 + ⟪x, y⟫ ≥ η > 0` within each class, for a constant `η` of the class.

*Proof.* Take a Hilbert basis `(b_i)`. A unit vector has a nonzero
coordinate, and by Bessel's inequality only finitely many coordinates exceed
any positive size. So there are rationals `0 < q₂ < q₁` with these
properties:

- some coordinate has magnitude at least `q₁`;
- every coordinate below `q₁` in magnitude is at most `q₂`.

Classify `x` by such a pair and by the sign of its coordinate at a canonical
index chosen from the set `S(x)` of coordinates of magnitude at least `q₁`
(by `Classical.epsilon`). Take two vectors of one class:

- If `S(x) ≠ S(y)`, some coordinate gives `‖x + y‖ ≥ q₁ - q₂`.
- If `S(x) = S(y)`, the canonical coordinate gives `‖x + y‖ ≥ 2 q₁`.

Either way `1 + ⟪x, y⟫ = ‖x + y‖² / 2 ≥ (q₁ - q₂)² / 2`.

**Sign classes** (`exists_sign_classes`). In `L²(ν)`, the signs `±1` are unit
vectors with `1 + ⟪x_u, x_v⟫ = 2 ν(σ_u = σ_v)`. So the vertices fall into
countably many classes, within which any two signs agree with probability at
least a positive constant of the class.

**Lemma T** (`Coloring.lean`, `nonempty_coloring_of_traceBound`). Suppose a
law gives every vertex with infinite trace trace energy at most `C`, and
every layer has a coloring by `ℕ`. Then `G` has a coloring by `ℕ`.

*Proof.* Within a sign class, the neighbours of `v` in earlier layers lie in
its trace.

- If the trace is finite, there are finitely many of them.
- If the trace is infinite, each such neighbour contributes at least `η` to
  a trace energy bounded by `C`, so again there are finitely many.

Greedy coloring along the well-founded order of layers (`Greedy.lean`)
colors, inside each class, the edges between different layers. Color `v` by
the triple (class, greedy color, color in its layer):

- edges between classes differ in the first coordinate;
- edges between layers within a class differ in the second;
- edges inside a layer differ in the third.

**The theorem** (`nonempty_coloring_of_linear`). Induct on `#V`.

- A countable graph is colored injectively.
- For uncountable `V`, take a chain. Each layer has fewer than `#V` vertices
  and induces a `C`-linear graph (`Linear.induce`), so it is colored by
  induction. Proposition L and Lemma T finish.

---

## 7. Relation to the original argument

The original argument used a chain of elementary submodels of `H(θ)` of
length `cf #V`, starting from a nonempty model. It needed a compactness
construction for `J` at the first model and Radon measures with weak-star
compactness. The labels Lemma D, Lemma S, Proposition L and Lemma T follow
the original. There, Proposition C is a coloring theorem whose proof contains
the partition that §6 calls Proposition C. The Lean route makes these changes:

- **Closure.** Closure over a set replaces elementary submodels, since
  replication is all the argument uses.
- **The chain.** The chain starts from `∅`, so `J` holds there for every
  law, and the original's construction of a law at the first model is not
  needed. It has length `(#V).ord` and enumerates `V`, so no cover of `V` by
  `cf #V` smaller sets has to be chosen.
- **Laws.** Laws live on the product σ-algebra. Compactness is replaced by
  ultrafilter limits of finite-dimensional marginals plus Kolmogorov
  extension for Boolean coordinates.
- **The induction.** The induction along the chain carries a proposition,
  not a coherent family of measures, because every condition passes to
  ultrafilter limits.
- **Lemma D.** Its proof works along any injective enumeration of infinitely
  many trace neighbours, instead of a countable set of trace neighbours on
  which the expected minority is maximal.
- **The key inequality.** It treats real weights with `⌈k ρ_i⌉` copies. Its
  pointwise lower bound splits on whether every forced root keeps its forced
  sign, instead of arguing about minimizers.
- **Lemma S.** It concludes that every new vertex with an infinite trace has
  trace energy at most `C`. The original concludes that the new vertex
  almost surely takes its forced sign, and derives the trace bound from that
  in Proposition L.
