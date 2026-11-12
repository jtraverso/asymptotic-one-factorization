/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Matchings as sets of edges

* `IsMatch M`: no two distinct edges of `M` share a vertex.
* `colorable_of_matchings`: if `d` matchings cover the edge set of `G`, the line graph of `G` is
  `d`-colourable.
* `exists_bij_of_halfDegree` (Vaughan, Lemma 9) and `exists_bij_of_regular` (Hall): perfect
  matchings between two vertex sets of equal size.
-/

@[expose] public section

namespace AOF

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- `M` is a matching: two distinct edges of `M` have no common vertex. -/
def IsMatch (M : Finset (Sym2 V)) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v ∈ e, v ∉ f

omit [DecidableEq V] in
theorem IsMatch.subset {M M' : Finset (Sym2 V)} (h : IsMatch M) (hM : M' ⊆ M) : IsMatch M' :=
  fun e he f hf hne v hv => h e (hM he) f (hM hf) hne v hv

theorem IsMatch.eq_of_mem {M : Finset (Sym2 V)} (h : IsMatch M) {e f : Sym2 V} (he : e ∈ M)
    (hf : f ∈ M) {v : V} (hve : v ∈ e) (hvf : v ∈ f) : e = f := by
  by_contra hne
  exact h e he f hf hne v hve hvf

/-- **Colouring from matchings.** If every edge of `G` lies in one of `d` matchings, the line
graph of `G` is `d`-colourable. -/
theorem colorable_of_matchings [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (F : Fin d → Finset (Sym2 V)) (hF : ∀ i, IsMatch (F i))
    (hcov : ∀ e ∈ G.edgeSet, ∃ i, e ∈ F i) : G.lineGraph.Colorable d := by
  classical
  refine ⟨Coloring.mk (fun e => Classical.choose (hcov e.1 e.2)) ?_⟩
  intro e f hadj hcol
  rw [lineGraph_adj_iff_exists] at hadj
  obtain ⟨hne, v, hve, hvf⟩ := hadj
  have he := Classical.choose_spec (hcov e.1 e.2)
  have hf := Classical.choose_spec (hcov f.1 f.2)
  rw [hcol] at he
  exact hne (Subtype.ext ((hF _).eq_of_mem he hf hve hvf))

section Hall

variable {X Y : Finset V}

/-- **Lemma 9 of Vaughan** (balanced bipartite graphs with half degrees have perfect matchings),
for an arbitrary relation `P` between `X` and `Y` with `|X| = |Y| = m`: if every `x ∈ X` has at
least `m/2` partners in `Y` and every `y ∈ Y` at least `m/2` partners in `X`, there is a bijection
`f : X → Y` with `P x (f x)`. -/
theorem exists_bij_of_halfDegree (P : V → V → Prop) [DecidableRel P] (hXY : #X = #Y)
    (hX : ∀ x ∈ X, #X ≤ 2 * #(Y.filter fun y => P x y))
    (hY : ∀ y ∈ Y, #X ≤ 2 * #(X.filter fun x => P x y)) :
    ∃ f : X → Y, Function.Bijective f ∧ ∀ x : X, P x (f x) := by
  classical
  let t : X → Finset Y := fun x => univ.filter fun y => P x y
  have hall : ∀ S : Finset X, #S ≤ #(S.biUnion t) := by
    intro S
    rcases S.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
    · simp
    by_cases hsmall : 2 * #S ≤ #X
    · -- `S` is small: the neighbourhood of one vertex is large enough
      have h1 : #(t x0) ≤ #(S.biUnion t) := card_le_card (subset_biUnion_of_mem t hx0)
      have h2 : #(t x0) = #(Y.filter fun y => P x0 y) := by
        rw [card_filter, card_filter, ← sum_coe_sort Y]
      have := hX x0 x0.2
      omega
    · -- `S` is large: every `y` has a partner in `S`
      have hfull : S.biUnion t = univ := by
        rw [eq_univ_iff_forall]
        intro y
        by_contra hy
        have hsub : (X.filter fun x => P x y) ⊆ X \ S.map (Function.Embedding.subtype _) := by
          intro x hx
          rw [mem_filter] at hx
          rw [mem_sdiff]
          refine ⟨hx.1, fun hxS => hy ?_⟩
          rw [mem_map] at hxS
          obtain ⟨x', hx'S, rfl⟩ := hxS
          exact mem_biUnion.2 ⟨x', hx'S, mem_filter.2 ⟨mem_univ _, hx.2⟩⟩
        have h3 := card_le_card hsub
        have h4 : #(X \ S.map (Function.Embedding.subtype _)) = #X - #S := by
          rw [card_sdiff_of_subset, card_map]
          intro x hx
          rw [mem_map] at hx
          obtain ⟨x', -, rfl⟩ := hx
          exact x'.2
        have := hY y y.2
        have hS : #S ≤ #X := (card_le_univ S).trans (by simp)
        omega
      rw [hfull, card_univ, Fintype.card_coe]
      have : #S ≤ #(univ : Finset X) := card_le_univ S
      rw [card_univ, Fintype.card_coe] at this
      omega
  obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  refine ⟨f, ?_, fun x => (mem_filter.1 (hf x)).2⟩
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨hinj, by simp [hXY]⟩

/-- **Regular bipartite graphs have perfect matchings** (Hall). If every `x ∈ X` has exactly `r`
partners in `Y` and every `y ∈ Y` exactly `r` partners in `X`, with `r ≥ 1`, there is a bijection
`f : X → Y` with `P x (f x)`. -/
theorem exists_bij_of_regular (P : V → V → Prop) [DecidableRel P] (r : ℕ) (hr : 0 < r)
    (hX : ∀ x ∈ X, #(Y.filter fun y => P x y) = r)
    (hY : ∀ y ∈ Y, #(X.filter fun x => P x y) = r) :
    ∃ f : X → Y, Function.Bijective f ∧ ∀ x : X, P x (f x) := by
  classical
  let t : X → Finset Y := fun x => univ.filter fun y => P x y
  have ht : ∀ x : X, #(t x) = r := by
    intro x
    rw [← hX x x.2, card_filter, card_filter, ← sum_coe_sort Y]
  have hall : ∀ S : Finset X, #S ≤ #(S.biUnion t) := by
    intro S
    let R : X → Y → Prop := fun x y => P x y
    have hdc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := S)
      (t := (univ : Finset Y)) (r := R)
    have hleft : ∑ x ∈ S, #((univ : Finset Y).bipartiteAbove R x) = r * #S := by
      change ∑ x ∈ S, #(t x) = r * #S
      rw [sum_congr rfl fun x _ => ht x]
      simp [mul_comm]
    have hright : ∑ y ∈ (univ : Finset Y), #(S.bipartiteBelow R y) =
        ∑ y ∈ S.biUnion t, #(S.bipartiteBelow R y) := by
      refine (sum_subset (subset_univ _) fun y _ hy => ?_).symm
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro x hx
      apply hy
      rw [bipartiteBelow, mem_filter] at hx
      exact mem_biUnion.2 ⟨x, hx.1, mem_filter.2 ⟨mem_univ _, hx.2⟩⟩
    have hbound : ∑ y ∈ S.biUnion t, #(S.bipartiteBelow R y) ≤ ∑ _y ∈ S.biUnion t, r := by
      refine sum_le_sum fun y _ => ?_
      calc #(S.bipartiteBelow R y) ≤ #(univ.filter fun x : X => P x y) :=
            card_le_card fun x hx => by
              rw [bipartiteBelow, mem_filter] at hx
              exact mem_filter.2 ⟨mem_univ _, hx.2⟩
        _ = r := by rw [← hY y y.2, card_filter, card_filter, ← sum_coe_sort X]
    rw [sum_const, smul_eq_mul] at hbound
    have : r * #S ≤ r * #(S.biUnion t) := by
      rw [← hleft, hdc, hright]
      exact hbound.trans (le_of_eq (mul_comm _ _))
    exact Nat.le_of_mul_le_mul_left this hr
  obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  refine ⟨f, ?_, fun x => (mem_filter.1 (hf x)).2⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨hinj, ?_⟩
  -- `|X| = |Y|` by double counting
  have h1 : r * #X = r * #Y := by
    have e1 : ∑ x ∈ X, #(Y.filter fun y => P x y) = ∑ y ∈ Y, #(X.filter fun x => P x y) := by
      simp_rw [card_filter]
      exact sum_comm
    rw [sum_congr rfl hX, sum_congr rfl hY] at e1
    simpa [mul_comm] using e1
  have := Nat.eq_of_mul_eq_mul_left hr h1
  simp [this]

end Hall

end AOF
