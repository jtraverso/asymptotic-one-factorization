/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.Family
public import LeanPool.Vizing.Corollaries

/-!
# Equitable colour classes of the graphs inside the two sides

* `resid G S F`: the uncoloured edges of `G` with both ends in `S`.
* `exists_classes`: equitable colourings (Vizing entry, McDiarmid) give `j` matchings covering
  `resid G S F`, of sizes differing by at most one and at most `⌈|E|/j⌉`.
* `exists_perm_of_equitable`: two equitable size distributions with the same total agree up to a
  permutation of the colours.
* `card_covered_eq`: a matching with all ends in `S` covers exactly `2|M|` vertices of `S`.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace AOF

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The uncoloured edges of `G` with both ends in `S`. -/
def resid (G : SimpleGraph V) {p : ℕ} (S : Finset V) (F : Fin p → Finset (Sym2 V)) :
    SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S ∧ ¬ colored F s(u, v)
  symm := ⟨fun u v ⟨h, hu, hv, hc⟩ => ⟨h.symm, hv, hu, by rwa [Sym2.eq_swap]⟩⟩
  loopless := ⟨fun v ⟨h, _⟩ => G.loopless.irrefl v h⟩

instance {p : ℕ} (S : Finset V) (F : Fin p → Finset (Sym2 V)) :
    DecidableRel (resid G S F).Adj := fun u v =>
  inferInstanceAs (Decidable (G.Adj u v ∧ u ∈ S ∧ v ∈ S ∧ ¬ colored F s(u, v)))

theorem resid_degree {p : ℕ} (S : Finset V) (F : Fin p → Finset (Sym2 V)) (v : V) :
    (resid G S F).degree v =
      #(univ.filter fun u => G.Adj v u ∧ v ∈ S ∧ u ∈ S ∧ ¬ colored F s(v, u)) := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  rfl

theorem mem_resid_edgeFinset {p : ℕ} {S : Finset V} {F : Fin p → Finset (Sym2 V)} {u v : V} :
    s(u, v) ∈ (resid G S F).edgeFinset ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S ∧ ¬ colored F s(u, v) := by
  rw [mem_edgeFinset, mem_edgeSet]
  rfl

/-- **Equitable classes.** -/
theorem exists_classes {p : ℕ} (S : Finset V) (F : Fin p → Finset (Sym2 V)) (j : ℕ)
    (hj : (resid G S F).maxDegree + 1 ≤ j) :
    ∃ Q : Fin j → Finset (Sym2 V),
      (∀ i, IsMatch (Q i)) ∧ (∀ i, Q i ⊆ (resid G S F).edgeFinset) ∧
      (∀ i i', i ≠ i' → Disjoint (Q i) (Q i')) ∧
      (∀ e ∈ (resid G S F).edgeFinset, ∃ i, e ∈ Q i) ∧
      (∀ i i', #(Q i) ≤ #(Q i') + 1) ∧
      (∀ i, #(Q i) ≤ #(resid G S F).edgeFinset ⌈/⌉ j) := by
  classical
  obtain ⟨colour, hprop, heq, hceil⟩ :=
    LeanPool.Vizing.exists_equitable_edge_colouring (resid G S F) j hj
  refine ⟨fun i => (resid G S F).edgeFinset.filter fun e => colour e = i, fun i => ?_,
    fun i => filter_subset _ _, fun i i' hne => ?_, fun e he => ⟨colour e, mem_filter.2 ⟨he, rfl⟩⟩,
    fun i i' => heq i i', fun i => hceil i⟩
  · intro e he f hf hne v hve hvf
    rw [mem_filter] at he hf
    have := hprop e he.1 f hf.1 hne (he.2.trans hf.2.symm)
    exact Finset.disjoint_left.1 this (Sym2.mem_toFinset.2 hve) (Sym2.mem_toFinset.2 hvf)
  · rw [Finset.disjoint_left]
    intro e he he'
    rw [mem_filter] at he he'
    exact hne (he.2.symm.trans he'.2)

/-- In an equitable distribution, the values are `⌊S/k⌋` and `⌊S/k⌋ + 1`, the latter `S % k`
times. -/
theorem equitable_values {k : ℕ} (hk : 0 < k) (f : Fin k → ℕ) (hf : ∀ i i', f i ≤ f i' + 1) :
    (∀ i, f i = (∑ i, f i) / k ∨ f i = (∑ i, f i) / k + 1) ∧
      #(univ.filter fun i => f i = (∑ i, f i) / k + 1) = (∑ i, f i) % k := by
  classical
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨i0, -, hi0⟩ := exists_min_image univ f univ_nonempty
  set q := f i0
  have hval : ∀ i, f i = q ∨ f i = q + 1 := by
    intro i
    have h1 := hi0 i (mem_univ i)
    have h2 := hf i i0
    omega
  set T := univ.filter fun i => f i = q + 1
  have hsum : ∑ i, f i = k * q + #T := by
    calc ∑ i, f i = ∑ i, (q + if f i = q + 1 then 1 else 0) := by
          refine sum_congr rfl fun i _ => ?_
          rcases hval i with h | h <;> simp [h]
      _ = k * q + #T := by
          rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, sum_boole]
          simp [T]
  have hT : #T ≤ k := by
    have := card_le_univ T
    rwa [Fintype.card_fin] at this
  rcases Nat.lt_or_ge #T k with hlt | hge
  · have hdiv : (∑ i, f i) / k = q := by
      rw [hsum, Nat.div_eq_of_lt_le] <;> nlinarith
    have hmod : (∑ i, f i) % k = #T := by
      rw [hsum, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt]
    rw [hdiv, hmod]
    exact ⟨hval, rfl⟩
  · have hTk : #T = k := le_antisymm hT hge
    have hall : ∀ i, f i = q + 1 := by
      intro i
      by_contra h
      have hsub : T ⊆ univ.erase i := fun x hx => mem_erase.2
        ⟨fun hxi => h (hxi ▸ (mem_filter.1 hx).2), mem_univ x⟩
      have := card_le_card hsub
      rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin] at this
      omega
    have hdiv : (∑ i, f i) / k = q + 1 := by
      rw [hsum, hTk, show k * q + k = k * (q + 1) by ring, Nat.mul_div_cancel_left _ hk]
    have hmod : (∑ i, f i) % k = 0 := by
      rw [hsum, hTk, show k * q + k = k * (q + 1) by ring, Nat.mul_mod_right]
    rw [hdiv, hmod]
    refine ⟨fun i => Or.inl (hall i), ?_⟩
    rw [card_eq_zero, filter_eq_empty_iff]
    intro i _ h
    rw [hall i] at h
    omega

/-- **Matching the class sizes.** -/
theorem exists_perm_of_equitable {k : ℕ} (f g : Fin k → ℕ) (hf : ∀ i i', f i ≤ f i' + 1)
    (hg : ∀ i i', g i ≤ g i' + 1) (hsum : ∑ i, f i = ∑ i, g i) :
    ∃ π : Equiv.Perm (Fin k), ∀ i, g (π i) = f i := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨Equiv.refl _, fun i => i.elim0⟩
  obtain ⟨hfv, hfc⟩ := equitable_values hk f hf
  obtain ⟨hgv, hgc⟩ := equitable_values hk g hg
  rw [hsum] at hfv hfc
  set m := (∑ i, g i) / k
  -- level sets of the same sizes
  have h1 : Fintype.card {i // f i = m + 1} = Fintype.card {i // g i = m + 1} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, hfc, hgc]
  have h2 : Fintype.card {i // ¬ f i = m + 1} = Fintype.card {i // ¬ g i = m + 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  let e1 := Fintype.equivOfCardEq h1
  let e2 := Fintype.equivOfCardEq h2
  let π : Equiv.Perm (Fin k) :=
    ((Equiv.sumCompl fun i => f i = m + 1).symm.trans (Equiv.sumCongr e1 e2)).trans
      (Equiv.sumCompl fun i => g i = m + 1)
  refine ⟨π, fun i => ?_⟩
  by_cases hi : f i = m + 1
  · have : π i = (e1 ⟨i, hi⟩ : Fin k) := by
      simp only [π, Equiv.trans_apply, Equiv.sumCongr_apply]
      rw [Equiv.sumCompl_symm_apply_of_pos (p := fun i => f i = m + 1) hi]
      rfl
    rw [this, (e1 ⟨i, hi⟩).2, hi]
  · have : π i = (e2 ⟨i, hi⟩ : Fin k) := by
      simp only [π, Equiv.trans_apply, Equiv.sumCongr_apply]
      rw [Equiv.sumCompl_symm_apply_of_neg (p := fun i => f i = m + 1) hi]
      rfl
    rw [this]
    have hg2 := (e2 ⟨i, hi⟩).2
    rcases hgv (e2 ⟨i, hi⟩) with h | h
    · rcases hfv i with h' | h'
      · rw [h, h']
      · exact absurd h' hi
    · exact absurd h hg2

/-- A matching with all ends in `S` covers exactly `2|M|` vertices of `S`. -/
theorem card_covered_eq (M : Finset (Sym2 V)) (hM : IsMatch M) (S : Finset V)
    (hS : ∀ e ∈ M, ∀ v ∈ e, v ∈ S) (hdiag : ∀ e ∈ M, ¬ e.IsDiag) :
    #(S.filter fun v => ∃ w, s(v, w) ∈ M) = 2 * #M := by
  classical
  have hdc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := M) (t := S)
    (r := fun e v => v ∈ e)
  have hleft : ∀ e ∈ M, #(S.bipartiteAbove (fun e v => v ∈ e) e) = 2 := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : x ≠ y := fun h => hdiag _ he (by simp [h])
      have : S.bipartiteAbove (fun e v => v ∈ e) s(x, y) = {x, y} := by
        ext v
        simp only [bipartiteAbove, mem_filter, Sym2.mem_iff, mem_insert, mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl)
          · exact ⟨hS _ he _ (Sym2.mem_mk_left _ _), Or.inl rfl⟩
          · exact ⟨hS _ he _ (Sym2.mem_mk_right _ _), Or.inr rfl⟩
      rw [this, card_pair hxy]
  have hright : ∀ v ∈ S, #(M.bipartiteBelow (fun e v => v ∈ e) v) =
      if ∃ w, s(v, w) ∈ M then 1 else 0 := by
    intro v _
    split_ifs with hv
    · obtain ⟨w, hw⟩ := hv
      rw [card_eq_one]
      refine ⟨s(v, w), ?_⟩
      ext e
      simp only [bipartiteBelow, mem_filter, mem_singleton]
      constructor
      · rintro ⟨he, hve⟩; exact hM.eq_of_mem he hw hve (Sym2.mem_mk_left _ _)
      · rintro rfl; exact ⟨hw, Sym2.mem_mk_left _ _⟩
    · rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro e he
      simp only [bipartiteBelow, mem_filter] at he
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 he.2
      exact hv ⟨w, he.1⟩
  rw [sum_congr rfl hleft, sum_congr rfl hright, sum_const, smul_eq_mul, sum_boole] at hdc
  simp only [Nat.cast_id] at hdc
  omega

end AOF
