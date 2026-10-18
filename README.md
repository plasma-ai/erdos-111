# Erdős Problem 111: bipartizing finite subgraphs of uncountably chromatic graphs

This Lean 4 project concerns [Erdős Problem 111](https://www.erdosproblems.com/111), as cataloged by Thomas F. Bloom. For a graph `G`, let `h_G(n)` be the least number such that every subgraph of `G` on `n` vertices can be made bipartite by deleting at most `h_G(n)` edges. Erdős asked for the behaviour of `h_G(n)`, and whether `h_G(n) / n → ∞` for every graph `G` of chromatic number `ℵ₁`. We prove:

**Theorem.** For every `C ≥ 0`, a graph in which every finite subgraph on `m` vertices can be made bipartite by deleting at most `C m` edges has countable chromatic number.

**Corollary.** `h_G(n) / n → ∞` for every graph `G` that is not countably colorable, of any cardinality. In particular this holds for every graph of chromatic number `ℵ₁`, which answers the second question of the problem in the affirmative.

The divergence is of the whole sequence, not along a subsequence. No rate comes with it.

The proof is Plasma AI's. The [blueprint](blueprint/proof.md) states it in prose, following the Lean development module by module.

## The argument

**Reduction.** Call `G` `C`-linear if every finite edge set of `G` whose ends lie in a vertex set `s` can be made bipartite by deleting at most `C |s|` of its edges. Suppose `G` is not countably colorable and fix `K`. Take a maximal family of pairwise disjoint finite subgraphs, each needing more than `2 K` deletions per vertex. If the family were countable, deleting its vertices would leave a `2 K`-linear graph. By the theorem that graph is countably colorable, so `G` would be too. Hence the family is uncountable, and infinitely many of its members share one size and one cost. Packing `⌊n / v⌋` of them into `n` vertices gives `h_G(n) > K n` for all large `n`.

**The theorem.** The theorem is proved by induction on the number of vertices. For an uncountable vertex set, take a continuous chain of vertex sets `N_ξ`, indexed by the ordinals below the initial ordinal of `#V`. The chain starts from `∅`, each set has fewer than `#V` vertices, and it covers `V`. Each successor set is closed over its predecessor in a finitary sense: every finite configuration hanging off finitely many roots in `N_{ξ+1}`, outside `N_ξ`, has a copy over the same roots inside `N_{ξ+1}`. A vertex enters the chain in one layer, and its trace is its set of neighbours in earlier sets.

Signs `σ : V → Bool` are drawn at random, and laws on `V → Bool` are built along the chain:

- **The invariant `J` at `N_ξ`.** For every rooted pattern with roots in `N_ξ` and new vertices outside it, the expected cost of extending the root signs optimally is at most `C` times the number of new vertices.
- **Successor step.** At each successor step, every new vertex with an infinite trace receives the opposite of its derived trace sign. That sign is the one that recurs along its trace, a measurable function of countably many old signs.
- **Keeping `J`.** The remaining new signs are coupled so that `J` survives at `N_{ξ+1}`. Copies of the patterns over `N_{ξ+1}`, together with long stars into the traces, form one pattern over `N_ξ`. Fatou's lemma, a finite minimax argument and compactness of laws finish the step.
- **Limits.** At limit stages, and at the end, the laws converge along an ultrafilter.

In the final law, every vertex `v` with infinite trace has `∑_{u ∈ trace v} P(σ_u = σ_v) ≤ C`. The signs are unit vectors in `L²`. A Hilbert-basis argument splits them into countably many classes, within each of which any two signs agree with probability bounded below. Within a class, each vertex therefore has finitely many neighbours in earlier layers, so greedy coloring across layers, combined with colorings of the layers from the induction hypothesis, colors `G` with countably many colors.

## Literature and scope

The question appears in [Er81] (P. Erdős, *On the combinatorial problems which I would most like to see solved*, Combinatorica 1 (1981), 25–42) and [EHS82] (P. Erdős, A. Hajnal and E. Szemerédi, *On almost bipartite large chromatic graphs*, Annals of Discrete Mathematics 12 (1982), 117–123). Every graph of chromatic number `ℵ₁` has `h_G(n) ≫ n`, because it contains arbitrarily many vertex-disjoint odd cycles of one length. Erdős, Hajnal and Szemerédi constructed graphs of arbitrarily large chromatic number with `h_G(n) ≤ 2 n^{3/2}` (Theorem 3 of [EHS82]). In [Er81] Erdős conjectured that for a graph of chromatic number `ℵ₁` the bound can be lowered to `n^{1+ε}` for every `ε > 0`. The finite-density reformulation in the reduction above is also stated in Section 2 of the [Erdős Problem a Day report](https://www.erdosproblemaday.com/report/111) (26 July 2026). The argument here does not rely on it.

To our knowledge, the theorem above and its consequence for Problem 111 have not been proved before. On October 17, 2026:

- Bloom's entry listed the problem as open.
- A search of arXiv and the web found no proof.
- [`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures) had no statement of the problem on its main branch, and two open pull requests ([#3785](https://github.com/google-deepmind/formal-conjectures/pull/3785) and [#6635](https://github.com/google-deepmind/formal-conjectures/pull/6635)) that state it without a proof.

The first question, the exact behaviour of `h_G(n)`, is open-ended and is not addressed beyond the divergence.

## Publication layout

`Challenge.lean` states the results using only Mathlib imports. Its three `sorry` proofs are deliberate: this file contains the statements to audit.

- `bipartizationNumber H` is the least number of edges of a subgraph `H` whose deletion leaves it bipartite (`IsBipartite`).
- `h G n` is the supremum of `bipartizationNumber H` over subgraphs `H` of `G` on `n` vertices.
- `chromaticCardinal G` is the least cardinality of a color set that properly colors `G`.

The three theorems are:

- `countably_colorable_of_linear`, the theorem;
- `tendsto_of_not_countably_colorable`, the corollary for every graph without a coloring by `ℕ`;
- `erdos_111`, the corollary for graphs of chromatic number `ℵ₁`.

`Solution.lean` imports the proof development and supplies the three theorems. `comparator.json` selects their names and the allowed axioms for [Comparator](https://github.com/leanprover/comparator).

The proof development lives under `Erdos111/` and depends on Mathlib only:

- `Statement.lean` repeats the definitions of `Challenge.lean`.
- `Basic.lean` defines edge costs, `C`-linearity, rooted patterns and their extension costs, the invariant `J` (`Rooted`), agreement of finite marginals (`SameOn`) and trace bounds (`TraceBound`).
- `Bridge.lean` identifies `bipartizationNumber` with the edge cost, so the hypothesis of the challenge is `C`-linearity. `Reduction.lean` proves countable deletion, packing and the reduction of the corollaries to the theorem.
- `Closure.lean` builds sets closed over a given set, and `Chain.lean` the chain of closed sets with its layers and traces.
- `Probability/` proves Kolmogorov extension for laws on `ι → Bool` (`Kolmogorov.lean`), limits of laws along an ultrafilter (`Limit.lean`) and a finite minimax lemma (`Minimax.lean`).
- `DerivedSign.lean` proves Lemma D, the derived sign of an infinite trace. `Successor/Forcing.lean` forces the new infinite-trace signs, `Successor/Key.lean` proves the key inequality of the successor step, `Successor/Mixture.lean` builds mixtures of couplings, and `Successor.lean` assembles the successor step (Lemma S).
- `LimitMeasure.lean` builds the final law along the chain (Proposition L).
- `HilbertClasses.lean` proves the countable partition of unit vectors (Proposition C). `Greedy.lean` proves greedy coloring along a well-founded order. `Coloring.lean` proves Lemma T and the theorem by induction on cardinality.
- `FinalAssembly.lean` assembles the three compared theorems.

Every Lean file uses the module system: it begins with `module`, imports with `public import`, and exposes its definitions with `@[expose] public section`.

`formalization.yaml` records the mathematical sources, authorship, AI use, source fidelity, and review status for a registry submission.

The Lean and Mathlib versions are fixed by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The full build includes `Challenge` and therefore reports its intentional `sorry` warnings. The proofs in `Solution` can also be built directly with `lake build Solution`.
