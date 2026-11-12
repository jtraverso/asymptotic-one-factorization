/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Real.Basic

/-!
# Asymptotic 1-factorization of dense regular graphs

Perković–Reed (1997) and Häggkvist: for every `ε > 0`, every `d`-regular simple graph on `2n`
vertices with `n` large and `d ≥ (1 + ε) n` is 1-factorizable, i.e. its line graph is
`d`-colourable. The proof follows E. R. Vaughan, *An asymptotic version of the multigraph
1-factorization conjecture* (arXiv:1010.5192), in the case of multiplicity `r = 1`.

* `one_factorization`: the statement with a real `ε > 0`.
* `one_factorization_of_ge`: the integer form `(q + 1) n ≤ q d`, for `q ≥ 1`.
-/

@[expose] public section

namespace PerkovicReed

universe u

/-- **Asymptotic 1-factorization**, integer form: `d ≥ (1 + 1/q) n`. -/
theorem one_factorization_of_ge {q : ℕ} (hq : 0 < q) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n d : ℕ), N ≤ n → Fintype.card V = 2 * n → G.IsRegularOfDegree d →
        (q + 1) * n ≤ q * d → G.lineGraph.Colorable d := by
  sorry

/-- **Asymptotic 1-factorization** (Perković–Reed 1997, Häggkvist). For every `ε > 0` there is
`N` such that every `d`-regular simple graph on `2n` vertices, `n ≥ N`, with `d ≥ (1 + ε) n` has a
proper edge colouring with `d` colours (a 1-factorization). -/
theorem one_factorization (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n d : ℕ), N ≤ n → Fintype.card V = 2 * n → G.IsRegularOfDegree d →
        (1 + ε) * n ≤ d → G.lineGraph.Colorable d := by
  sorry

end PerkovicReed
