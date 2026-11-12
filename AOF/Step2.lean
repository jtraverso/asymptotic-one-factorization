/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.ExchangeCounts

/-!
# Step 2 of Vaughan's proof: completing the first `k` colour classes

The invariant `Inv2` is preserved by an exchange; repeating exchanges (induction on the number of
missing colour–vertex incidences in `A`) every colour class becomes a perfect matching, while
`rdeg ≤ t`, `ccol ≤ s + t` and `Σ_A rdeg = Σ_{Aᶜ} rdeg` hold throughout.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace AOF

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {k : ℕ} {M : Fin k → Finset (Sym2 V)}

/-- The vertices of `S` on an edge of colour `c` leaving `S`. -/
def lcount (M : Fin k → Finset (Sym2 V)) (c : Fin k) (S : Finset V) : ℕ :=
  #(S.filter fun w => ∃ u ∉ S, s(w, u) ∈ M c)

/-- The invariant of Step 2. -/
structure Inv2 (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (M : Fin k → Finset (Sym2 V)) (s t : ℕ) (m0 : V → ℕ) : Prop where
  state : IsState G M
  rdeg_le : ∀ v, rdeg G A M v ≤ t
  acc : ∀ v, ccol G A M v + missing M v ≤ m0 v + rdeg G A M v
  sumA : ∑ v ∈ A, rdeg G A M v + 2 * ∑ v ∈ A, missing M v ≤ 2 * ∑ v ∈ A, m0 v
  sumB : ∑ v ∈ Aᶜ, rdeg G A M v + 2 * ∑ v ∈ Aᶜ, missing M v ≤ 2 * ∑ v ∈ Aᶜ, m0 v
  rsum : ∑ v ∈ A, rdeg G A M v = ∑ v ∈ Aᶜ, rdeg G A M v
  bal : ∀ c, missed M c A = missed M c Aᶜ
  lA : ∀ c, lcount M c A + 3 * missed M c A ≤ 6 * s + 6
  lB : ∀ c, lcount M c Aᶜ + 3 * missed M c Aᶜ ≤ 6 * s + 6

namespace AltPath

variable {c : Fin k} {a b₁ b₂ a₂ a₁ b : V}
variable (hM : IsState G M) (h : AltPath G A M c a b₁ b₂ a₂ a₁ b)
include hM h

theorem lcount_exchange_A :
    lcount (exchange M c a b₁ b₂ a₂ a₁ b) c A ≤ lcount M c A + 3 := by
  classical
  have hsub : (A.filter fun w => ∃ u ∉ A, s(w, u) ∈ exchange M c a b₁ b₂ a₂ a₁ b c) ⊆
      (A.filter fun w => ∃ u ∉ A, s(w, u) ∈ M c) ∪ {a, a₂, a₁} := by
    intro w hw
    rw [mem_filter] at hw
    obtain ⟨hwA, u, hu, hwu⟩ := hw
    rw [exchange_self, mem_newClass] at hwu
    rcases hwu with ⟨hwu, -, -⟩ | hwu | hwu | hwu
    · exact mem_union_left _ (mem_filter.2 ⟨hwA, u, hu, hwu⟩)
    all_goals
      rcases Sym2.eq_iff.1 hwu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | (apply mem_union_right; simp; done)
        | exact absurd hwA h.hb₁
        | exact absurd hwA h.hb₂
        | exact absurd hwA h.hb
        | exact absurd h.ha hu
        | exact absurd h.ha₂ hu
        | exact absurd h.ha₁ hu
  calc _ ≤ #((A.filter fun w => ∃ u ∉ A, s(w, u) ∈ M c) ∪ {a, a₂, a₁}) := card_le_card hsub
    _ ≤ #(A.filter fun w => ∃ u ∉ A, s(w, u) ∈ M c) + #({a, a₂, a₁} : Finset V) :=
        card_union_le _ _
    _ ≤ lcount M c A + 3 := by
        have : #({a, a₂, a₁} : Finset V) ≤ 3 := card_le_three
        rw [lcount]; omega

theorem lcount_exchange_B :
    lcount (exchange M c a b₁ b₂ a₂ a₁ b) c Aᶜ ≤ lcount M c Aᶜ + 3 := by
  classical
  have hsub : (Aᶜ.filter fun w => ∃ u ∉ Aᶜ, s(w, u) ∈ exchange M c a b₁ b₂ a₂ a₁ b c) ⊆
      (Aᶜ.filter fun w => ∃ u ∉ Aᶜ, s(w, u) ∈ M c) ∪ {b₁, b₂, b} := by
    intro w hw
    rw [mem_filter] at hw
    obtain ⟨hwA, u, hu, hwu⟩ := hw
    rw [mem_compl] at hwA
    rw [mem_compl, not_not] at hu
    rw [exchange_self, mem_newClass] at hwu
    rcases hwu with ⟨hwu, -, -⟩ | hwu | hwu | hwu
    · exact mem_union_left _ (mem_filter.2 ⟨mem_compl.2 hwA, u, by simpa using hu, hwu⟩)
    all_goals
      rcases Sym2.eq_iff.1 hwu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | (apply mem_union_right; simp; done)
        | exact absurd h.ha hwA
        | exact absurd h.ha₂ hwA
        | exact absurd h.ha₁ hwA
        | exact absurd hu h.hb₁
        | exact absurd hu h.hb₂
        | exact absurd hu h.hb
  calc _ ≤ #((Aᶜ.filter fun w => ∃ u ∉ Aᶜ, s(w, u) ∈ M c) ∪ {b₁, b₂, b}) := card_le_card hsub
    _ ≤ #(Aᶜ.filter fun w => ∃ u ∉ Aᶜ, s(w, u) ∈ M c) + #({b₁, b₂, b} : Finset V) :=
        card_union_le _ _
    _ ≤ lcount M c Aᶜ + 3 := by
        have : #({b₁, b₂, b} : Finset V) ≤ 3 := card_le_three
        rw [lcount]; omega

theorem lcount_exchange_ne {c' : Fin k} (hc : c' ≠ c) (S : Finset V) :
    lcount (exchange M c a b₁ b₂ a₂ a₁ b) c' S = lcount M c' S := by
  simp only [lcount, exchange_ne hc]

theorem sum_inner_A :
    ∑ v ∈ A, (if v = b₁ ∨ v = b₂ ∨ v = a₂ ∨ v = a₁ then 1 else 0) = 2 := by
  classical
  rw [sum_boole]
  have : (A.filter fun v => v = b₁ ∨ v = b₂ ∨ v = a₂ ∨ v = a₁) = {a₂, a₁} := by
    ext v
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hv, rfl | rfl | rfl | rfl⟩
      · exact absurd hv h.hb₁
      · exact absurd hv h.hb₂
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨h.ha₂, by tauto⟩
      · exact ⟨h.ha₁, by tauto⟩
  rw [this, card_pair (h.a₁_ne_a₂ hM).symm]
  rfl

theorem sum_inner_B :
    ∑ v ∈ Aᶜ, (if v = b₁ ∨ v = b₂ ∨ v = a₂ ∨ v = a₁ then 1 else 0) = 2 := by
  classical
  rw [sum_boole]
  have : (Aᶜ.filter fun v => v = b₁ ∨ v = b₂ ∨ v = a₂ ∨ v = a₁) = {b₁, b₂} := by
    ext v
    simp only [mem_filter, mem_compl, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hv, rfl | rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd h.ha₂ hv
      · exact absurd h.ha₁ hv
    · rintro (rfl | rfl)
      · exact ⟨h.hb₁, by tauto⟩
      · exact ⟨h.hb₂, by tauto⟩
  rw [this, card_pair (h.b₁_ne_b₂ hM)]
  rfl

theorem sum_ab_A : ∑ v ∈ A, (if v = a ∨ v = b then 1 else 0) = 1 := by
  classical
  rw [sum_boole]
  have : (A.filter fun v => v = a ∨ v = b) = {a} := by
    ext v
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hv, rfl | rfl⟩
      · rfl
      · exact absurd hv h.hb
    · rintro rfl; exact ⟨h.ha, Or.inl rfl⟩
  rw [this, card_singleton]
  rfl

theorem sum_ab_B : ∑ v ∈ Aᶜ, (if v = a ∨ v = b then 1 else 0) = 1 := by
  classical
  rw [sum_boole]
  have : (Aᶜ.filter fun v => v = a ∨ v = b) = {b} := by
    ext v
    simp only [mem_filter, mem_compl, mem_singleton]
    constructor
    · rintro ⟨hv, rfl | rfl⟩
      · exact absurd h.ha hv
      · rfl
    · rintro rfl; exact ⟨h.hb, Or.inr rfl⟩
  rw [this, card_singleton]
  rfl

/-- **The exchange preserves `Inv2`.** -/
theorem inv2_exchange {s t : ℕ} {m0 : V → ℕ} (hI : Inv2 G A M s t m0)
    (hr₁ : rdeg G A M b₁ < t) (hr₂ : rdeg G A M b₂ < t) (hr₃ : rdeg G A M a₂ < t)
    (hr₄ : rdeg G A M a₁ < t) :
    Inv2 G A (exchange M c a b₁ b₂ a₂ a₁ b) s t m0 := by
  have hR := rdeg_exchange (G := G) hM h
  have hC := ccol_exchange_le (G := G) hM h
  have hC' := ccol_exchange_of_ne (G := G) hM h
  have hMi := missing_exchange_le (G := G) hM h
  refine ⟨isState_exchange hM h, fun v => ?_, fun v => ?_, ?_, ?_, ?_, fun c' => ?_,
    fun c' => ?_, fun c' => ?_⟩
  · rw [hR]
    split_ifs with hv
    · rcases hv with rfl | rfl | rfl | rfl <;> omega
    · simpa using hI.rdeg_le v
  · have h1 := hI.acc v
    have h2 := hMi v
    have h3 := hR v
    have h4 := hC v
    by_cases hab : v = a ∨ v = b
    · rw [if_pos hab] at h2
      have : ¬ (v = b₁ ∨ v = b₂ ∨ v = a₂ ∨ v = a₁) := by
        rcases hab with rfl | rfl
        · have := h.hb₁; have := h.hb₂
          rintro (h' | h' | h' | h')
          · exact h.hb₁ (h' ▸ h.ha)
          · exact h.hb₂ (h' ▸ h.ha)
          · exact h.a_ne_a₂ h'
          · exact h.a_ne_a₁ h'
        · rintro (h' | h' | h' | h')
          · exact h.b_ne_b₁ h'
          · exact h.b_ne_b₂ h'
          · exact h.hb (h' ▸ h.ha₂)
          · exact h.hb (h' ▸ h.ha₁)
      rw [if_neg this] at h3
      omega
    · rw [if_neg hab] at h2
      by_cases hin : v = b₁ ∨ v = b₂ ∨ v = a₂ ∨ v = a₁
      · rw [if_pos hin] at h3
        omega
      · rw [if_neg hin] at h3
        have h5 := hC' v (by tauto)
        omega
  · have e1 : ∑ v ∈ A, rdeg G A (exchange M c a b₁ b₂ a₂ a₁ b) v =
        ∑ v ∈ A, rdeg G A M v + 2 := by
      rw [sum_congr rfl fun v _ => hR v, sum_add_distrib, sum_inner_A hM h]
    have e2 : ∑ v ∈ A, missing (exchange M c a b₁ b₂ a₂ a₁ b) v + 1 ≤ ∑ v ∈ A, missing M v := by
      have := sum_le_sum fun v (_ : v ∈ A) => hMi v
      rw [sum_add_distrib, sum_ab_A hM h] at this
      exact this
    have := hI.sumA
    omega
  · have e1 : ∑ v ∈ Aᶜ, rdeg G A (exchange M c a b₁ b₂ a₂ a₁ b) v =
        ∑ v ∈ Aᶜ, rdeg G A M v + 2 := by
      rw [sum_congr rfl fun v _ => hR v, sum_add_distrib, sum_inner_B hM h]
    have e2 : ∑ v ∈ Aᶜ, missing (exchange M c a b₁ b₂ a₂ a₁ b) v + 1 ≤
        ∑ v ∈ Aᶜ, missing M v := by
      have := sum_le_sum fun v (_ : v ∈ Aᶜ) => hMi v
      rw [sum_add_distrib, sum_ab_B hM h] at this
      exact this
    have := hI.sumB
    omega
  · rw [sum_congr rfl fun v _ => hR v, sum_add_distrib, sum_inner_A hM h,
      sum_congr rfl fun v _ => hR v, sum_add_distrib, sum_inner_B hM h, hI.rsum]
  · by_cases hc : c' = c
    · subst hc
      have h1 := missed_exchange_A (G := G) hM h
      have h2 := missed_exchange_B (G := G) hM h
      have := hI.bal c'
      omega
    · rw [missed_exchange_ne hM h hc, missed_exchange_ne hM h hc]
      exact hI.bal c'
  · by_cases hc : c' = c
    · subst hc
      have h1 := missed_exchange_A (G := G) hM h
      have h2 := lcount_exchange_A (G := G) hM h
      have := hI.lA c'
      omega
    · rw [missed_exchange_ne hM h hc, lcount_exchange_ne hM h hc]
      exact hI.lA c'
  · by_cases hc : c' = c
    · subst hc
      have h1 := missed_exchange_B (G := G) hM h
      have h2 := lcount_exchange_B (G := G) hM h
      have := hI.lB c'
      omega
    · rw [missed_exchange_ne hM h hc, lcount_exchange_ne hM h hc]
      exact hI.lB c'

end AltPath

/-- **Step 2.** From a state satisfying `Inv2`, exchanges make every colour class a perfect
matching. -/
theorem step2 {n s t D : ℕ} (ht : 0 < t) (hA : #A = n) (hB : #Aᶜ = n) {m0 : V → ℕ}
    (hm0 : ∀ v, m0 v ≤ s)
    (hdeg : ∀ v, n + 2 * D < 2 * #(A.filter fun u => G.Adj v u) ∧
      n + 2 * D < 2 * #(Aᶜ.filter fun u => G.Adj v u))
    (hnum : 4 * n * s + t * (7 * s + t + 6) ≤ t * D) :
    ∀ (μ : ℕ) (M : Fin k → Finset (Sym2 V)), ∑ c, missed M c A = μ → Inv2 G A M s t m0 →
      ∃ M' : Fin k → Finset (Sym2 V), Inv2 G A M' s t m0 ∧ ∀ c v, covered M' c v := by
  intro μ
  induction μ using Nat.strong_induction_on with
  | _ μ ih =>
  intro M hμ hI
  by_cases hall : ∀ c, missed M c A = 0
  · refine ⟨M, hI, fun c v => ?_⟩
    by_contra hv
    by_cases hvA : v ∈ A
    · have := hall c
      rw [missed, card_eq_zero, filter_eq_empty_iff] at this
      exact this hvA hv
    · have := hall c
      rw [hI.bal c, missed, card_eq_zero, filter_eq_empty_iff] at this
      exact this (mem_compl.2 hvA) hv
  push Not at hall
  obtain ⟨c, hc⟩ := hall
  obtain ⟨a, ha⟩ : (A.filter fun v => ¬ covered M c v).Nonempty := by
    rw [← card_pos]; unfold missed at hc; omega
  have hcB : 0 < missed M c Aᶜ := by rw [← hI.bal c]; omega
  obtain ⟨b, hb⟩ : (Aᶜ.filter fun v => ¬ covered M c v).Nonempty := by
    rw [← card_pos]; unfold missed at hcB; omega
  rw [mem_filter] at ha hb
  -- the hypotheses of `exists_alt_path`
  have hcc : ∀ v, ccol G A M v ≤ s + t := by
    intro v
    have := hI.acc v
    have := hm0 v
    have := hI.rdeg_le v
    omega
  have hUL : ∀ S : Finset V, (S = A ∨ S = Aᶜ) → #(S.filter fun w => ¬ covered M c w) +
      #(S.filter fun w => ∃ u ∉ S, s(w, u) ∈ M c) ≤ 6 * s + 6 := by
    rintro S (rfl | rfl)
    · have := hI.lA c; unfold missed lcount at this; omega
    · have := hI.lB c; unfold missed lcount at this; omega
  have hH : ∀ S : Finset V, (S = A ∨ S = Aᶜ) →
      t * #(S.filter fun w => t ≤ rdeg G A M w) ≤ 2 * n * s := by
    intro S hS
    have hsumS : ∑ v ∈ S, rdeg G A M v ≤ 2 * (n * s) := by
      have hm : ∑ v ∈ S, m0 v ≤ n * s := by
        calc ∑ v ∈ S, m0 v ≤ ∑ _v ∈ S, s := sum_le_sum fun v _ => hm0 v
          _ = n * s := by
              rw [sum_const, smul_eq_mul]
              rcases hS with rfl | rfl
              · rw [hA]
              · rw [hB]
      rcases hS with rfl | rfl
      · have := hI.sumA; omega
      · have := hI.sumB; omega
    calc t * #(S.filter fun w => t ≤ rdeg G A M w)
        = ∑ _v ∈ S.filter fun w => t ≤ rdeg G A M w, t := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ S.filter fun w => t ≤ rdeg G A M w, rdeg G A M v :=
          sum_le_sum fun v hv => (mem_filter.1 hv).2
      _ ≤ ∑ v ∈ S, rdeg G A M v :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.zero_le _
      _ ≤ 2 * n * s := by rw [mul_assoc]; exact hsumS
  obtain ⟨b₁, b₂, a₂, a₁, hb₁, hb₂, ha₂, ha₁, hab₁, hcab₁, hb₁b₂, hr₁, hr₂, hb₂a₂, hcb₂a₂,
    ha₁a₂, hr₃, hr₄, hba₁, hcba₁⟩ :=
    exists_alt_path hI.state c ht hA hB ha.1 (mem_compl.2 (mem_compl.1 hb.1)) hdeg hcc hUL hH hnum
  have hP : AltPath G A M c a b₁ b₂ a₂ a₁ b :=
    { ha := ha.1, hb := mem_compl.1 hb.1, hb₁ := mem_compl.1 hb₁, hb₂ := mem_compl.1 hb₂,
      ha₂ := ha₂, ha₁ := ha₁, hfa := ha.2, hfb := hb.2, ab₁ := hab₁, cab₁ := hcab₁,
      b₁b₂ := hb₁b₂, b₂a₂ := hb₂a₂, cb₂a₂ := hcb₂a₂, a₁a₂ := ha₁a₂,
      a₁b := (G.adj_comm _ _).1 hba₁,
      ca₁b := by rw [Sym2.eq_swap]; exact hcba₁ }
  have hI' := hP.inv2_exchange hI.state hI hr₁ hr₂ hr₄ hr₃
  have hμ' : ∑ c', missed (exchange M c a b₁ b₂ a₂ a₁ b) c' A + 1 = μ := by
    rw [← hμ, ← add_sum_erase _ _ (mem_univ c), ← add_sum_erase _ _ (mem_univ c),
      sum_congr rfl fun c' hc' => hP.missed_exchange_ne hI.state (ne_of_mem_erase hc') A]
    have := hP.missed_exchange_A hI.state
    omega
  exact ih _ (by omega) _ rfl hI'

end AOF
