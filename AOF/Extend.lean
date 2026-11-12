/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.Initial

/-!
# Step 3 of Vaughan's proof: extending a pair of residual classes to a perfect matching

Given a perfect family `F`, matchings `QA` inside `A` and `QB` inside `Aᶜ` of uncoloured edges with
`|QA| = |QB|`, and degree margins, the vertices missed by `QA ∪ QB` can be matched by uncoloured
crossing edges (Hall, Vaughan's Lemma 9).
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace AOF

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The vertices of `S` covered by `Q`. -/
def coveredBy (Q : Finset (Sym2 V)) (S : Finset V) : Finset V :=
  S.filter fun v => ∃ w, s(v, w) ∈ Q

theorem card_cross_colored_le {p : ℕ} {A : Finset V} (F : Fin p → Finset (Sym2 V)) {x : V}
    {S : Finset V} (hS : (S = A ∧ x ∉ A) ∨ (S = Aᶜ ∧ x ∈ A)) :
    #(S.filter fun u => G.Adj x u ∧ colored F s(x, u)) ≤ ccol G A F x := by
  rw [ccol]
  refine card_le_card fun u hu => ?_
  rw [mem_filter] at hu ⊢
  refine ⟨mem_univ _, hu.2.1, fun hs => ?_, hu.2.2⟩
  have hs' : x ∈ A ↔ u ∈ A := hs
  rcases hS with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · exact hx (hs'.2 hu.1)
  · exact (mem_compl.1 hu.1) (hs'.1 hx)

/-- **Extension of a pair of classes.** -/
theorem exists_extension {p : ℕ} {F : Fin p → Finset (Sym2 V)} (hF : IsPerfectFamily G F)
    {A : Finset V} {n D β γ : ℕ} (hA : #A = n) (hB : #Aᶜ = n)
    (hdeg : ∀ v, n + 2 * D < 2 * degIn G A v ∧ n + 2 * D < 2 * degIn G Aᶜ v)
    (hcc : ∀ v, ccol G A F v ≤ γ) (hβγ : β + γ ≤ D)
    (QA QB : Finset (Sym2 V)) (hmA : IsMatch QA) (hmB : IsMatch QB)
    (hinA : ∀ e ∈ QA, e ∈ G.edgeFinset ∧ (∀ v ∈ e, v ∈ A) ∧ ¬ colored F e)
    (hinB : ∀ e ∈ QB, e ∈ G.edgeFinset ∧ (∀ v ∈ e, v ∈ Aᶜ) ∧ ¬ colored F e)
    (hcard : #QA = #QB) (hβ : 2 * #QA ≤ β) :
    ∃ N : Finset (Sym2 V), N ⊆ G.edgeFinset ∧ IsMatch N ∧ (∀ v, ∃ w, s(v, w) ∈ N) ∧
      (∀ e ∈ N, ¬ colored F e) ∧ QA ⊆ N ∧ QB ⊆ N ∧
      (∀ x y, s(x, y) ∈ N → s(x, y) ∉ QA → s(x, y) ∉ QB → (x ∈ A ↔ y ∉ A)) := by
  classical
  have hdiagA : ∀ e ∈ QA, ¬ e.IsDiag := fun e he hd =>
    G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.1 (hinA e he).1) hd
  have hdiagB : ∀ e ∈ QB, ¬ e.IsDiag := fun e he hd =>
    G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.1 (hinB e he).1) hd
  have hcA := card_covered_eq QA hmA A (fun e he => (hinA e he).2.1) hdiagA
  have hcB := card_covered_eq QB hmB Aᶜ (fun e he => (hinB e he).2.1) hdiagB
  set X := A.filter fun v => ¬ ∃ w, s(v, w) ∈ QA
  set Y := Aᶜ.filter fun v => ¬ ∃ w, s(v, w) ∈ QB
  have hX : #X + 2 * #QA = n := by
    rw [← hcA, ← hA, add_comm]
    exact card_filter_add_card_filter_not (s := A) (fun v => ∃ w, s(v, w) ∈ QA)
  have hY : #Y + 2 * #QB = n := by
    rw [← hcB, ← hB, add_comm]
    exact card_filter_add_card_filter_not (s := Aᶜ) (fun v => ∃ w, s(v, w) ∈ QB)
  let P : V → V → Prop := fun x y => G.Adj x y ∧ ¬ colored F s(x, y)
  -- degree bounds for Hall
  have hdegX : ∀ x ∈ X, #X ≤ 2 * #(Y.filter fun y => P x y) := by
    intro x hx
    rw [mem_filter] at hx
    have h1 := (hdeg x).2
    have h2 := card_cross_colored_le (G := G) (A := A) F (S := Aᶜ) (x := x) (Or.inr ⟨rfl, hx.1⟩)
    have h3 := hcc x
    have hsub : (Aᶜ.filter fun u => G.Adj x u) ⊆ (Y.filter fun y => P x y) ∪
        (Aᶜ.filter fun u => G.Adj x u ∧ colored F s(x, u)) ∪
        (Aᶜ.filter fun v => ∃ w, s(v, w) ∈ QB) := by
      intro u hu
      rw [mem_filter] at hu
      simp only [mem_union, mem_filter, P, Y]
      by_cases hc : colored F s(x, u)
      · exact Or.inl (Or.inr ⟨hu.1, hu.2, hc⟩)
      · by_cases hq : ∃ w, s(u, w) ∈ QB
        · exact Or.inr ⟨hu.1, hq⟩
        · exact Or.inl (Or.inl ⟨⟨hu.1, hq⟩, hu.2, hc⟩)
    have c1 := card_le_card hsub
    have c2 := card_union_le ((Y.filter fun y => P x y) ∪
      (Aᶜ.filter fun u => G.Adj x u ∧ colored F s(x, u))) (Aᶜ.filter fun v => ∃ w, s(v, w) ∈ QB)
    have c3 := card_union_le (Y.filter fun y => P x y)
      (Aᶜ.filter fun u => G.Adj x u ∧ colored F s(x, u))
    rw [hcB] at c2
    unfold degIn at h1
    omega
  have hdegY : ∀ y ∈ Y, #X ≤ 2 * #(X.filter fun x => P x y) := by
    intro y hy
    rw [mem_filter] at hy
    have h1 := (hdeg y).1
    have h2 := card_cross_colored_le (G := G) (A := A) F (S := A) (x := y)
      (Or.inl ⟨rfl, mem_compl.1 hy.1⟩)
    have h3 := hcc y
    have hsub : (A.filter fun u => G.Adj y u) ⊆ (X.filter fun x => P x y) ∪
        (A.filter fun u => G.Adj y u ∧ colored F s(y, u)) ∪
        (A.filter fun v => ∃ w, s(v, w) ∈ QA) := by
      intro u hu
      rw [mem_filter] at hu
      simp only [mem_union, mem_filter, P, X]
      by_cases hc : colored F s(y, u)
      · exact Or.inl (Or.inr ⟨hu.1, hu.2, hc⟩)
      · by_cases hq : ∃ w, s(u, w) ∈ QA
        · exact Or.inr ⟨hu.1, hq⟩
        · exact Or.inl (Or.inl ⟨⟨hu.1, hq⟩, hu.2.symm, by rwa [Sym2.eq_swap]⟩)
    have c1 := card_le_card hsub
    have c2 := card_union_le ((X.filter fun x => P x y) ∪
      (A.filter fun u => G.Adj y u ∧ colored F s(y, u))) (A.filter fun v => ∃ w, s(v, w) ∈ QA)
    have c3 := card_union_le (X.filter fun x => P x y)
      (A.filter fun u => G.Adj y u ∧ colored F s(y, u))
    rw [hcA] at c2
    unfold degIn at h1
    omega
  obtain ⟨f, hfb, hfP⟩ := exists_bij_of_halfDegree P (by omega) hdegX hdegY
  set E := univ.image fun x : X => s(x.1, (f x).1)
  have hEmem : ∀ e ∈ E, ∃ x : X, e = s(x.1, (f x).1) := by
    intro e he; obtain ⟨x, -, rfl⟩ := mem_image.1 he; exact ⟨x, rfl⟩
  have hXA : ∀ x : X, x.1 ∈ A ∧ ¬ ∃ w, s(x.1, w) ∈ QA := fun x => mem_filter.1 x.2
  have hYB : ∀ y : Y, y.1 ∉ A ∧ ¬ ∃ w, s(y.1, w) ∈ QB := fun y => by
    have := mem_filter.1 y.2; exact ⟨mem_compl.1 this.1, this.2⟩
  refine ⟨QA ∪ QB ∪ E, ?_, ?_, ?_, ?_, fun e he => mem_union_left _ (mem_union_left _ he),
    fun e he => mem_union_left _ (mem_union_right _ he), ?_⟩
  · intro e he
    rcases mem_union.1 he with he | he
    · rcases mem_union.1 he with he | he
      · exact (hinA e he).1
      · exact (hinB e he).1
    · obtain ⟨x, rfl⟩ := hEmem e he
      exact mem_edgeFinset.2 (hfP x).1
  · intro e he e' he' hne v hv hv'
    -- classify the two edges
    have hside : ∀ e ∈ QA ∪ QB ∪ E, (e ∈ QA ∧ ∀ v ∈ e, v ∈ A) ∨ (e ∈ QB ∧ ∀ v ∈ e, v ∉ A) ∨
        ∃ x : X, e = s(x.1, (f x).1) := by
      intro e he
      rcases mem_union.1 he with he | he
      · rcases mem_union.1 he with he | he
        · exact Or.inl ⟨he, (hinA e he).2.1⟩
        · exact Or.inr (Or.inl ⟨he, fun v hv => mem_compl.1 ((hinB e he).2.1 v hv)⟩)
      · exact Or.inr (Or.inr (hEmem e he))
    rcases hside e he with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨x, rfl⟩ <;>
      rcases hside e' he' with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨x', rfl⟩
    · exact hmA e h1 e' h2 hne v hv hv'
    · exact h2' v hv' (h1' v hv)
    · -- `e ∈ QA`, `e'` new: `v` is `x'` (not covered by `QA`) or `f x'` (not in `A`)
      rcases Sym2.mem_iff.1 hv' with rfl | rfl
      · obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv
        exact (hXA x').2 ⟨w, h1⟩
      · exact (hYB (f x')).1 (h1' _ hv)
    · exact h1' v hv (h2' v hv')
    · exact hmB e h1 e' h2 hne v hv hv'
    · rcases Sym2.mem_iff.1 hv' with rfl | rfl
      · exact h1' _ hv (hXA x').1
      · obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv
        exact (hYB (f x')).2 ⟨w, h1⟩
    · rcases Sym2.mem_iff.1 hv with rfl | rfl
      · obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv'
        exact (hXA x).2 ⟨w, h2⟩
      · exact (hYB (f x)).1 (h2' _ hv')
    · rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact h2' _ hv' (hXA x).1
      · obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv'
        exact (hYB (f x)).2 ⟨w, h2⟩
    · have hxx : x ≠ x' := fun h => hne (by rw [h])
      have hfx : f x ≠ f x' := fun h => hxx (hfb.1 h)
      rcases Sym2.mem_iff.1 hv with h | h <;> rcases Sym2.mem_iff.1 hv' with h' | h'
      · exact hxx (Subtype.ext (h.symm.trans h'))
      · exact (hYB (f x')).1 (h' ▸ h ▸ (hXA x).1)
      · exact (hYB (f x)).1 (h ▸ h' ▸ (hXA x').1)
      · exact hfx (Subtype.ext (h.symm.trans h'))
  · intro v
    by_cases hv : v ∈ A
    · by_cases hq : ∃ w, s(v, w) ∈ QA
      · obtain ⟨w, hw⟩ := hq
        exact ⟨w, mem_union_left _ (mem_union_left _ hw)⟩
      · have hvX : v ∈ X := mem_filter.2 ⟨hv, hq⟩
        exact ⟨f ⟨v, hvX⟩, mem_union_right _ (mem_image.2 ⟨⟨v, hvX⟩, mem_univ _, rfl⟩)⟩
    · by_cases hq : ∃ w, s(v, w) ∈ QB
      · obtain ⟨w, hw⟩ := hq
        exact ⟨w, mem_union_left _ (mem_union_right _ hw)⟩
      · have hvY : v ∈ Y := mem_filter.2 ⟨mem_compl.2 hv, hq⟩
        obtain ⟨x, hx⟩ := hfb.2 ⟨v, hvY⟩
        refine ⟨x.1, mem_union_right _ (mem_image.2 ⟨x, mem_univ _, ?_⟩)⟩
        rw [hx, Sym2.eq_swap]
  · intro e he
    rcases mem_union.1 he with he | he
    · rcases mem_union.1 he with he | he
      · exact (hinA e he).2.2
      · exact (hinB e he).2.2
    · obtain ⟨x, rfl⟩ := hEmem e he
      exact (hfP x).2
  · intro a b hab h1 h2
    rcases mem_union.1 hab with hab | hab
    · rcases mem_union.1 hab with hab | hab
      · exact absurd hab h1
      · exact absurd hab h2
    · obtain ⟨x, hx⟩ := hEmem _ hab
      have hxA := (hXA x).1
      have hfA := (hYB (f x)).1
      rcases Sym2.eq_iff.1 hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨fun _ => hfA, fun _ => hxA⟩
      · exact ⟨fun h => absurd h hfA, fun h => absurd hxA h⟩

end AOF
