/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.Step2

/-!
# Families of perfect matchings, and Step 4

A *perfect family* is a state `F : Fin p → Finset (Sym2 V)` whose classes are perfect matchings.

* `card_colored_nbrs`: in a perfect family every vertex has exactly `p` coloured edges.
* `snoc`: adding a perfect matching disjoint from the coloured edges keeps a perfect family.
* `step4` (Vaughan, Step 4): if `G` is `d`-regular, `|A| = |Aᶜ|`, and every uncoloured edge of a
  perfect family crosses the bipartition, then the line graph of `G` is `d`-colourable.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace AOF

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A family of pairwise disjoint perfect matchings of `G`. -/
structure IsPerfectFamily (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (F : Fin p → Finset (Sym2 V)) : Prop where
  state : IsState G F
  cover : ∀ c v, covered F c v

/-- The partner of `v` in colour `c`. -/
noncomputable def partner {p : ℕ} (F : Fin p → Finset (Sym2 V)) (hF : ∀ c v, covered F c v)
    (c : Fin p) (v : V) : V :=
  Classical.choose (hF c v)

theorem partner_mem {p : ℕ} {F : Fin p → Finset (Sym2 V)} (hF : ∀ c v, covered F c v)
    (c : Fin p) (v : V) : s(v, partner F hF c v) ∈ F c :=
  Classical.choose_spec (hF c v)

/-- In a perfect family every vertex has exactly `p` coloured edges. -/
theorem card_colored_nbrs {p : ℕ} {F : Fin p → Finset (Sym2 V)} (hF : IsPerfectFamily G F)
    (v : V) : #(univ.filter fun u => G.Adj v u ∧ colored F s(v, u)) = p := by
  classical
  have himage : (univ.filter fun u => G.Adj v u ∧ colored F s(v, u)) =
      univ.image (partner F hF.cover · v) := by
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨-, c, hc⟩
      exact ⟨c, hF.state.partner_unique (partner_mem hF.cover c v) hc⟩
    · rintro ⟨c, rfl⟩
      exact ⟨hF.state.adj_of_mem (partner_mem hF.cover c v), c, partner_mem hF.cover c v⟩
  rw [himage, card_image_of_injective, card_univ, Fintype.card_fin]
  intro c c' h
  by_contra hne
  have h1 := partner_mem hF.cover c v
  have h2 := partner_mem hF.cover c' v
  simp only at h
  rw [h] at h1
  exact Finset.disjoint_left.1 (hF.state.disj c c' hne) h1 h2

/-- Adding a perfect matching disjoint from the coloured edges. -/
theorem IsPerfectFamily.snoc {p : ℕ} {F : Fin p → Finset (Sym2 V)} (hF : IsPerfectFamily G F)
    {N : Finset (Sym2 V)} (hNsub : N ⊆ G.edgeFinset) (hNm : IsMatch N)
    (hNcov : ∀ v, ∃ w, s(v, w) ∈ N) (hNdisj : ∀ e ∈ N, ¬ colored F e) :
    IsPerfectFamily G (Fin.snoc F N : Fin (p + 1) → Finset (Sym2 V)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro c
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simpa using hNsub
    · simpa using hF.state.sub i
  · intro c
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simpa using hNm
    · simpa using hF.state.match_ i
  · intro c c' hne
    rw [Finset.disjoint_left]
    intro e he he'
    induction c using Fin.lastCases with
    | last =>
      induction c' using Fin.lastCases with
      | last => exact hne rfl
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at he he'
        exact hNdisj e he ⟨j, he'⟩
    | cast i =>
      induction c' using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at he he'
        exact hNdisj e he' ⟨i, he⟩
      | cast j =>
        simp only [Fin.snoc_castSucc] at he he'
        have hij : i ≠ j := fun h => hne (by rw [h])
        exact Finset.disjoint_left.1 (hF.state.disj i j hij) he he'
  · intro c v
    induction c using Fin.lastCases with
    | last =>
      obtain ⟨w, hw⟩ := hNcov v
      exact ⟨w, by simpa using hw⟩
    | cast i =>
      obtain ⟨w, hw⟩ := hF.cover i v
      exact ⟨w, by simpa using hw⟩

theorem colored_snoc {p : ℕ} {F : Fin p → Finset (Sym2 V)} {N : Finset (Sym2 V)} {e : Sym2 V} :
    colored (Fin.snoc F N : Fin (p + 1) → Finset (Sym2 V)) e ↔ colored F e ∨ e ∈ N := by
  constructor
  · rintro ⟨c, hc⟩
    induction c using Fin.lastCases with
    | last => exact Or.inr (by simpa using hc)
    | cast i => exact Or.inl ⟨i, by simpa using hc⟩
  · rintro (⟨i, hi⟩ | h)
    · exact ⟨Fin.castSucc i, by simpa using hi⟩
    · exact ⟨Fin.last p, by simpa using h⟩

/-- **Step 4.** If `G` is `d`-regular, `|A| = |Aᶜ|`, and every uncoloured edge of a perfect family
crosses the bipartition, the line graph of `G` is `d`-colourable. -/
theorem step4 {A : Finset V} {d : ℕ} (hreg : G.IsRegularOfDegree d) (hAB : #A = #Aᶜ) :
    ∀ (r p : ℕ) (F : Fin p → Finset (Sym2 V)), p + r = d → IsPerfectFamily G F →
      (∀ u v, G.Adj u v → ¬ colored F s(u, v) → (u ∈ A ↔ v ∉ A)) →
      G.lineGraph.Colorable d := by
  classical
  intro r
  induction r with
  | zero =>
    intro p F hpd hF _
    rw [add_zero] at hpd
    subst hpd
    refine colorable_of_matchings G F hF.state.match_ fun e he => ?_
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_edgeSet] at he
      by_contra hne
      push Not at hne
      have h1 := card_colored_nbrs hF u
      have h2 : #(univ.filter fun w => G.Adj u w ∧ colored F s(u, w)) <
          #(univ.filter fun w => G.Adj u w) := by
        refine card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨fun w hw => ?_, fun heq => ?_⟩)
        · simp only [mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.1⟩
        · have : v ∈ univ.filter fun w => G.Adj u w := by simp [he]
          rw [← heq] at this
          simp only [mem_filter] at this
          obtain ⟨c, hc⟩ := this.2.2
          exact hne c hc
      have h3 : #(univ.filter fun w => G.Adj u w) = p := by
        rw [← hreg u, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
      omega
  | succ r ih =>
    intro p F hpd hF hcross
    -- the uncoloured edges form an `(r+1)`-regular bipartite graph between `A` and `Aᶜ`
    let P : V → V → Prop := fun x y => G.Adj x y ∧ ¬ colored F s(x, y)
    have hdegP : ∀ x, #(univ.filter fun y => P x y) = r + 1 := by
      intro x
      have h1 := card_colored_nbrs hF x
      have h3 : #(univ.filter fun w => G.Adj x w) = d := by
        rw [← hreg x, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
      have hsplit : (univ.filter fun w => G.Adj x w) =
          (univ.filter fun w => G.Adj x w ∧ colored F s(x, w)) ∪ univ.filter fun y => P x y := by
        ext w; simp only [mem_filter, mem_univ, true_and, mem_union, P]; tauto
      have hdisj : Disjoint (univ.filter fun w => G.Adj x w ∧ colored F s(x, w))
          (univ.filter fun y => P x y) := by
        rw [Finset.disjoint_left]; intro w h1 h2
        simp only [mem_filter, mem_univ, true_and, P] at h1 h2; exact h2.2 h1.2
      rw [hsplit, card_union_of_disjoint hdisj] at h3
      omega
    have hside : ∀ x S, (S = A ∨ S = Aᶜ) → x ∉ S →
        #(S.filter fun y => P x y) = r + 1 := by
      intro x S hS hx
      rw [← hdegP x]
      congr 1
      ext y
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        have := (hcross x y h.1 h.2)
        rcases hS with rfl | rfl
        · tauto
        · rw [mem_compl] at hx ⊢; tauto
    obtain ⟨f, hfb, hfP⟩ := exists_bij_of_regular (X := A) (Y := Aᶜ) P (r + 1) (Nat.succ_pos r)
      (fun x hx => hside x Aᶜ (Or.inr rfl) (by simpa using hx))
      (fun y hy => by
        have := hside y A (Or.inl rfl) (by simpa using hy)
        rw [← this]
        congr 1
        ext x
        simp only [mem_filter, P]
        constructor
        · rintro ⟨hx, h1, h2⟩; exact ⟨hx, h1.symm, by rwa [Sym2.eq_swap]⟩
        · rintro ⟨hx, h1, h2⟩; exact ⟨hx, h1.symm, by rwa [Sym2.eq_swap]⟩)
    -- the new perfect matching
    let N : Finset (Sym2 V) := univ.image fun x : A => s(x.1, (f x).1)
    have hNmem : ∀ e ∈ N, ∃ x : A, e = s(x.1, (f x).1) := by
      intro e he; obtain ⟨x, -, rfl⟩ := mem_image.1 he; exact ⟨x, rfl⟩
    have hNsub : N ⊆ G.edgeFinset := by
      intro e he
      obtain ⟨x, rfl⟩ := hNmem e he
      exact mem_edgeFinset.2 (hfP x).1
    have hNm : IsMatch N := by
      intro e he e' he' hne v hv hv'
      obtain ⟨x, rfl⟩ := hNmem e he
      obtain ⟨x', rfl⟩ := hNmem e' he'
      have hxx : x ≠ x' := fun h => hne (by rw [h])
      have hfx : f x ≠ f x' := fun h => hxx (hfb.1 h)
      have hxA := x.2; have hx'A := x'.2
      have hfxA := mem_compl.1 (f x).2; have hfx'A := mem_compl.1 (f x').2
      simp only [Sym2.mem_iff] at hv hv'
      rcases hv with rfl | rfl <;> rcases hv' with h | h
      · exact hxx (Subtype.ext h)
      · exact hfx'A (h ▸ hxA)
      · exact hfxA (h ▸ hx'A)
      · exact hfx (Subtype.ext h)
    have hNcov : ∀ v, ∃ w, s(v, w) ∈ N := by
      intro v
      by_cases hv : v ∈ A
      · exact ⟨f ⟨v, hv⟩, mem_image.2 ⟨⟨v, hv⟩, mem_univ _, rfl⟩⟩
      · obtain ⟨x, hx⟩ := hfb.2 ⟨v, mem_compl.2 hv⟩
        refine ⟨x.1, mem_image.2 ⟨x, mem_univ _, ?_⟩⟩
        rw [hx, Sym2.eq_swap]
    have hNdisj : ∀ e ∈ N, ¬ colored F e := by
      intro e he
      obtain ⟨x, rfl⟩ := hNmem e he
      exact (hfP x).2
    have hF' := hF.snoc hNsub hNm hNcov hNdisj
    refine ih (p + 1) _ (by omega) hF' fun u v huv hc => ?_
    rw [colored_snoc, not_or] at hc
    exact hcross u v huv hc.1

end AOF
