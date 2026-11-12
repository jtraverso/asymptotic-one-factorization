/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.State

/-!
# Existence of the alternating path (Vaughan, Step 2)

For a colour `c` and vertices `a ∈ A`, `b ∈ Aᶜ` missed by `c`, there is a path
`a b₁ b₂ a₂ a₁ b` with `ab₁`, `b₂a₂`, `a₁b` uncoloured crossing edges and `b₁b₂`, `a₂a₁` edges of
colour `c` inside `Aᶜ` and `A` whose ends have `rdeg < t`.

The counting is Vaughan's, with one addition: a vertex whose `c`-edge crosses the bipartition is
excluded from `N_B` (Vaughan's count omits these; they are at most `3 · (2s + 2)`).
-/

@[expose] public section

namespace AOF

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {k : ℕ} {M : Fin k → Finset (Sym2 V)}

/-- The pairs `(w, w')` in `S` with `zw` an uncoloured edge and `ww'` a `c`-edge whose ends have
`rdeg < t`. -/
def goodPairs (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (M : Fin k → Finset (Sym2 V))
    (c : Fin k) (t : ℕ) (S : Finset V) (z : V) : Finset (V × V) :=
  (S ×ˢ S).filter fun p => G.Adj z p.1 ∧ ¬ colored M s(z, p.1) ∧ s(p.1, p.2) ∈ M c ∧
    rdeg G A M p.1 < t ∧ rdeg G A M p.2 < t

theorem mem_goodPairs {c : Fin k} {t : ℕ} {S : Finset V} {z : V} {p : V × V} :
    p ∈ goodPairs G A M c t S z ↔ (p.1 ∈ S ∧ p.2 ∈ S) ∧ G.Adj z p.1 ∧ ¬ colored M s(z, p.1) ∧
      s(p.1, p.2) ∈ M c ∧ rdeg G A M p.1 < t ∧ rdeg G A M p.2 < t := by
  simp [goodPairs, mem_product]

/-- **Many good pairs.** -/
theorem many_goodPairs (hM : IsState G M) (c : Fin k) {n s t D : ℕ} (ht : 0 < t)
    (S : Finset V) (z : V)
    (hz : n + 2 * D < 2 * #(S.filter fun u => G.Adj z u))
    (hcz : #(S.filter fun u => G.Adj z u ∧ colored M s(z, u)) ≤ s + t)
    (hUL : #(S.filter fun w => ¬ covered M c w) +
      #(S.filter fun w => ∃ u ∉ S, s(w, u) ∈ M c) ≤ 6 * s + 6)
    (hH : t * #(S.filter fun w => t ≤ rdeg G A M w) ≤ 2 * n * s)
    (hnum : 4 * n * s + t * (7 * s + t + 6) ≤ t * D) :
    n < 2 * #(goodPairs G A M c t S z) := by
  set N := S.filter fun u => G.Adj z u
  set C1 := S.filter fun u => G.Adj z u ∧ colored M s(z, u)
  set U := S.filter fun w => ¬ covered M c w
  set L := S.filter fun w => ∃ u ∉ S, s(w, u) ∈ M c
  set H := S.filter fun w => t ≤ rdeg G A M w
  set H' := S.filter fun w => ∃ w' ∈ H, s(w, w') ∈ M c
  -- partners of `H` are at most `|H|`
  have hH' : #H' ≤ #H := by
    have hcov : ∀ w ∈ H', ∃ w' ∈ H, s(w, w') ∈ M c := fun w hw => (mem_filter.1 hw).2
    choose! f hfH hfM using hcov
    refine card_le_card_of_injOn f (fun w hw => hfH w hw) fun w1 hw1 w2 hw2 h => ?_
    have h1 := hfM w1 hw1
    have h2 := hfM w2 hw2
    rw [Sym2.eq_swap] at h1 h2
    rw [h] at h1
    exact hM.partner_unique h1 h2
  -- the first coordinates of good pairs contain `N` minus the bad vertices
  have hsub : N \ (C1 ∪ U ∪ L ∪ H ∪ H') ⊆ (goodPairs G A M c t S z).image Prod.fst := by
    intro w hw
    simp only [mem_sdiff, mem_union, not_or] at hw
    obtain ⟨hwN, ⟨⟨⟨⟨hC1, hU⟩, hL⟩, hHw⟩, hH'w⟩⟩ := hw
    rw [mem_filter] at hwN
    have hcolw : ¬ colored M s(z, w) := fun h => hC1 (mem_filter.2 ⟨hwN.1, hwN.2, h⟩)
    have hcov : covered M c w := by
      by_contra h
      exact hU (mem_filter.2 ⟨hwN.1, h⟩)
    obtain ⟨w', hw'⟩ := hcov
    have hw'S : w' ∈ S := by
      by_contra h
      exact hL (mem_filter.2 ⟨hwN.1, w', h, hw'⟩)
    have hrw : rdeg G A M w < t := by
      by_contra h
      exact hHw (mem_filter.2 ⟨hwN.1, not_lt.1 h⟩)
    have hrw' : rdeg G A M w' < t := by
      by_contra h
      exact hH'w (mem_filter.2 ⟨hwN.1, w', mem_filter.2 ⟨hw'S, not_lt.1 h⟩, hw'⟩)
    exact mem_image.2 ⟨(w, w'), mem_goodPairs.2 ⟨⟨hwN.1, hw'S⟩, hwN.2, hcolw, hw', hrw, hrw'⟩, rfl⟩
  have h1 : #N - (#C1 + #U + #L + #H + #H') ≤ #(goodPairs G A M c t S z) := by
    calc #N - (#C1 + #U + #L + #H + #H') ≤ #(N \ (C1 ∪ U ∪ L ∪ H ∪ H')) := by
          have := le_card_sdiff (C1 ∪ U ∪ L ∪ H ∪ H') N
          have h2 : #(C1 ∪ U ∪ L ∪ H ∪ H') ≤ #C1 + #U + #L + #H + #H' := by
            calc #(C1 ∪ U ∪ L ∪ H ∪ H') ≤ #(C1 ∪ U ∪ L ∪ H) + #H' := card_union_le _ _
              _ ≤ #(C1 ∪ U ∪ L) + #H + #H' := by gcongr; exact card_union_le _ _
              _ ≤ #(C1 ∪ U) + #L + #H + #H' := by gcongr; exact card_union_le _ _
              _ ≤ #C1 + #U + #L + #H + #H' := by gcongr; exact card_union_le _ _
          omega
      _ ≤ #((goodPairs G A M c t S z).image Prod.fst) := card_le_card hsub
      _ ≤ #(goodPairs G A M c t S z) := card_image_le
  -- `2 |H| ≤ D − 7s − t − 6`
  have hH2 : t * (2 * #H) ≤ t * (D - (7 * s + t + 6)) := by
    have : t * (2 * #H) ≤ 4 * n * s := by nlinarith
    calc t * (2 * #H) ≤ 4 * n * s := this
      _ ≤ t * (D - (7 * s + t + 6)) := by
          rw [Nat.mul_sub]
          omega
  have hH2' := Nat.le_of_mul_le_mul_left hH2 ht
  have hD : 7 * s + t + 6 ≤ D :=
    Nat.le_of_mul_le_mul_left (show t * (7 * s + t + 6) ≤ t * D by omega) ht
  omega

/-- **Existence of the alternating path.** -/
theorem exists_alt_path (hM : IsState G M) (c : Fin k) {n s t D : ℕ} (ht : 0 < t)
    (hA : #A = n) (hB : #Aᶜ = n) {a b : V} (ha : a ∈ A) (hb : b ∈ Aᶜ)
    (hdeg : ∀ v, n + 2 * D < 2 * #(A.filter fun u => G.Adj v u) ∧
      n + 2 * D < 2 * #(Aᶜ.filter fun u => G.Adj v u))
    (hcc : ∀ v, ccol G A M v ≤ s + t)
    (hUL : ∀ S : Finset V, (S = A ∨ S = Aᶜ) → #(S.filter fun w => ¬ covered M c w) +
      #(S.filter fun w => ∃ u ∉ S, s(w, u) ∈ M c) ≤ 6 * s + 6)
    (hH : ∀ S : Finset V, (S = A ∨ S = Aᶜ) →
      t * #(S.filter fun w => t ≤ rdeg G A M w) ≤ 2 * n * s)
    (hnum : 4 * n * s + t * (7 * s + t + 6) ≤ t * D) :
    ∃ b₁ b₂ a₂ a₁ : V, b₁ ∈ Aᶜ ∧ b₂ ∈ Aᶜ ∧ a₂ ∈ A ∧ a₁ ∈ A ∧
      G.Adj a b₁ ∧ ¬ colored M s(a, b₁) ∧ s(b₁, b₂) ∈ M c ∧ rdeg G A M b₁ < t ∧
      rdeg G A M b₂ < t ∧ G.Adj b₂ a₂ ∧ ¬ colored M s(b₂, a₂) ∧ s(a₁, a₂) ∈ M c ∧
      rdeg G A M a₁ < t ∧ rdeg G A M a₂ < t ∧ G.Adj b a₁ ∧ ¬ colored M s(b, a₁) := by
  have hccA : ∀ v ∈ A, #(Aᶜ.filter fun u => G.Adj v u ∧ colored M s(v, u)) ≤ s + t := by
    intro v hv
    have h0 := hcc v
    unfold ccol at h0
    refine le_trans (card_le_card fun u hu => ?_) h0
    simp only [mem_filter, mem_compl] at hu
    rw [mem_filter]
    exact ⟨mem_univ _, hu.2.1, fun hs => hu.1 ((hs : v ∈ A ↔ u ∈ A).1 hv), hu.2.2⟩
  have hccB : ∀ v ∉ A, #(A.filter fun u => G.Adj v u ∧ colored M s(v, u)) ≤ s + t := by
    intro v hv
    have h0 := hcc v
    unfold ccol at h0
    refine le_trans (card_le_card fun u hu => ?_) h0
    simp only [mem_filter] at hu
    rw [mem_filter]
    exact ⟨mem_univ _, hu.2.1, fun hs => hv ((hs : v ∈ A ↔ u ∈ A).2 hu.1), hu.2.2⟩
  have hPB := many_goodPairs hM c ht Aᶜ a (hdeg a).2 (hccA a ha)
    (hUL Aᶜ (Or.inr rfl)) (hH Aᶜ (Or.inr rfl)) hnum
  have hPA := many_goodPairs hM c ht A b (hdeg b).1 (hccB b (mem_compl.1 hb))
    (hUL A (Or.inl rfl)) (hH A (Or.inl rfl)) hnum
  -- a good pair `(b₁, b₂)`
  obtain ⟨⟨b₁, b₂⟩, hp⟩ : (goodPairs G A M c t Aᶜ a).Nonempty := by
    rw [← card_pos]; omega
  rw [mem_goodPairs] at hp
  obtain ⟨⟨hb₁, hb₂⟩, hab₁, hcab₁, hb₁b₂, hr₁, hr₂⟩ := hp
  -- the uncoloured `A`-neighbours of `b₂`
  set X := A.filter fun u => G.Adj b₂ u ∧ ¬ colored M s(b₂, u)
  have hX : n < 2 * #X := by
    have h1 := (hdeg b₂).1
    have h2 := hccB b₂ (mem_compl.1 hb₂)
    have hsplit : #(A.filter fun u => G.Adj b₂ u) ≤
        #X + #(A.filter fun u => G.Adj b₂ u ∧ colored M s(b₂, u)) := by
      calc #(A.filter fun u => G.Adj b₂ u) ≤
          #(X ∪ A.filter fun u => G.Adj b₂ u ∧ colored M s(b₂, u)) := by
            refine card_le_card fun u hu => ?_
            rw [mem_filter] at hu
            by_cases hc : colored M s(b₂, u)
            · exact mem_union_right _ (mem_filter.2 ⟨hu.1, hu.2, hc⟩)
            · exact mem_union_left _ (mem_filter.2 ⟨hu.1, hu.2, hc⟩)
        _ ≤ _ := card_union_le _ _
    have : s + t ≤ D := by
      have : t * (s + t) ≤ t * D := by nlinarith
      exact Nat.le_of_mul_le_mul_left this ht
    omega
  -- the second coordinates of the good pairs of `b`
  set MA := (goodPairs G A M c t A b).image Prod.snd
  have hMA : #MA = #(goodPairs G A M c t A b) := by
    refine card_image_of_injOn fun p hp q hq h => ?_
    rw [mem_coe, mem_goodPairs] at hp hq
    have h1 := hp.2.2.2.1
    have h2 := hq.2.2.2.1
    rw [Sym2.eq_swap] at h1 h2
    rw [h] at h1
    have := hM.partner_unique h1 h2
    exact Prod.ext this h
  have hXsub : X ⊆ A := filter_subset _ _
  have hMAsub : MA ⊆ A := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hu
    exact ((mem_goodPairs.1 hp).1).2
  obtain ⟨a₂, ha₂X, ha₂M⟩ : ∃ a₂, a₂ ∈ X ∧ a₂ ∈ MA := by
    by_contra h
    push Not at h
    have hdisj : Disjoint X MA := disjoint_left.2 fun u hu hu' => h u hu hu'
    have := card_le_card (union_subset hXsub hMAsub)
    rw [card_union_of_disjoint hdisj] at this
    omega
  obtain ⟨⟨a₁, a₂'⟩, hq, rfl⟩ := mem_image.1 ha₂M
  rw [mem_goodPairs] at hq
  obtain ⟨⟨ha₁, ha₂⟩, hba₁, hcba₁, ha₁a₂, hr₃, hr₄⟩ := hq
  rw [mem_filter] at ha₂X
  exact ⟨b₁, b₂, a₂', a₁, hb₁, hb₂, ha₂, ha₁, hab₁, hcab₁, hb₁b₂, hr₁, hr₂, ha₂X.2.1, ha₂X.2.2,
    ha₁a₂, hr₃, hr₄, hba₁, hcba₁⟩

end AOF
