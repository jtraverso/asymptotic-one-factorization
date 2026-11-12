# Asymptotic 1-factorization (Perković–Reed / Häggkvist; Vaughan 2013, case r = 1)

Target (Vaughan, arXiv:1010.5192, Theorem 3 = Theorem 4 with r = 1):

> For every ε > 0 there is N such that for all n ≥ N every d-regular simple graph on 2n vertices
> with d ≥ (1 + ε) n is 1-factorizable (its line graph is d-colourable).

## Parameters (all linear in n, no fractional powers)

Vaughan uses n^{2/3} and n^{5/6}. For r = 1 any s, t with the inequalities below work; take
`s = ⌊α n⌋`, `t = ⌊β n⌋` with β = ε/20, α = ε²/400 (so 4ns/t ≈ εn/5).

* (P1) Chernoff: 4n · exp(−s²/(2n)) < 1 (balanced partition exists).
* (P2) D := d_min_part − n/2 margin with D > 3s + 2t + 4ns/t + 4 (Step 2 and Step 3 counts).

## Lemma 13 (balanced partition), r = 1, no probability

Pair the 2n vertices (p_i, q_i). For signs σ ∈ {±1}^n put p_i in A iff σ_i = 1. For a vertex v,
d_A(v) − d_B(v) = Σ σ_i c_i with c_i = [v ~ p_i] − [v ~ q_i] ∈ {−1, 0, 1}.
Counting bound: #{σ : |Σ σ_i c_i| ≥ s} ≤ 2 · 2^n · exp(−s²/(2n)), from
Σ_σ exp(λ Σ σ_i c_i) = Π (2 cosh(λ c_i)) ≤ 2^n exp(λ² n/2) (`Real.cosh_le_exp_half_sq`) and
Markov with λ = s/n. Union bound over 2n vertices.

## Lemma 14 (deterministic), r = 1

A, B with |A| = |B| = n, G d-regular, every v: d_A(v), d_B(v) > n/2 + D, and all of
Δ(G_A), δ(G_A), Δ(G_B), δ(G_B) in an interval of length < s.

1. k = max(Δ_A, Δ_B) + 1. Equitable k-colourings of G_A and G_B (Vizing v2,
   `exists_equitable_edge_colouring`), colours permuted so each colour has equally many edges in
   G_A and G_B. Each vertex misses ≤ s colours; each colour misses equally many vertices in A and
   B, at most 2s + 2.
2. For each colour c, pair the A- and B-vertices missing c; for a pair (a, b) exchange a 5-edge
   alternating path a b₁ b₂ a₂ a₁ b (ab₁, b₂a₂, a₁b uncoloured C-edges; b₁b₂, a₂a₁ good edges
   coloured c; good = both ends have R-degree < t). Invariants: |R_A| = |R_B| ≤ ns, Δ(R) ≤ t,
   coloured C-edges at each vertex ≤ s + t. Existence: |N_B|, |M_A| > n/2 by the margin D.
3. Equitable (t + 1)-colourings of R_A, R_B with matched class sizes; each class meets
   ≤ 2(ns/t + 1) vertices per side; complete each class by a perfect matching of the remaining
   bipartite C-graph (min degree ≥ half its side: Hall, Lemma 9).
4. The uncoloured rest is a regular bipartite graph ⊆ C: decompose into perfect matchings (Hall
   for regular bipartite graphs, repeated).

## Reuse

* vizing @ 33b2de8 (PALOMAR-2026-10-15-000004 v2): `PEC`, equitable edge colourings.
* Mathlib: Hall (`exists_isPerfectMatching_of_forall_ncard_le`), `Real.cosh_le_exp_half_sq`.
* Not usable together: konig-edge-colouring vendors `LeanPool.Vizing` (module clash with vizing);
  Step 4 is done with Hall instead.

## Status (2026-11-12): complete

All of the above is formalized (`AOF/`, ~3,100 lines, no `sorry`). The final parameters are linear
(`s = ⌊a/(200q)⌋`, `t = ⌊a/6⌋`, `a = ⌊n/q⌋`), see `AOF/Main.lean`.

**Gap repaired in Vaughan's Step 2 count.** A vertex `w ∈ B` whose edge of colour `c` crosses to
`A` is not incident with a *good* `c`-edge inside `B`, but the count "fewer than 8n^{5/6} vertices
in B incident with a non-good edge coloured c_i, plus fewer than 2n^{2/3}+3 missed" omits them.
Each exchange for colour `c` creates three crossing `c`-edges, so they are at most `3 (2s + 2)`;
the invariant `lcount + 3 · missed ≤ 6s + 6` (`AOF/Step2.lean`) bounds them, and the count in
`AOF/PathExists.lean` includes them.
