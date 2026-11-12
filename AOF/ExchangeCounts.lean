/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.ExchangeInv

/-!
# How the counts change under the exchange

* `rdeg` grows by exactly one at `b₁, b₂, a₂, a₁` and is unchanged elsewhere;
* `ccol` grows by at most one, and only at the six path vertices;
* `missing` drops by one at `a` and `b` and does not grow;
* `missed c` drops by one on each side; the other colours are unchanged.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace AOF

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {k : ℕ} {M : Fin k → Finset (Sym2 V)} {c : Fin k} {a b₁ b₂ a₂ a₁ b : V}

namespace AltPath

variable (hM : IsState G M) (h : AltPath G A M c a b₁ b₂ a₂ a₁ b)
include hM h

theorem not_sameSide_of_new {v u : V}
    (he : s(v, u) = s(a, b₁) ∨ s(v, u) = s(b₂, a₂) ∨ s(v, u) = s(a₁, b)) :
    ¬ sameSide A v u := by
  have s1 := h.ha; have s2 := h.hb; have s3 := h.hb₁; have s4 := h.hb₂
  have s5 := h.ha₂; have s6 := h.ha₁
  unfold sameSide
  rcases he with he | he | he <;> rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp_all

theorem sameSide_of_removed {v u : V} (he : s(v, u) = s(b₁, b₂) ∨ s(v, u) = s(a₁, a₂)) :
    sameSide A v u := by
  have s3 := h.hb₁; have s4 := h.hb₂; have s5 := h.ha₂; have s6 := h.ha₁
  unfold sameSide
  rcases he with he | he <;> rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp_all

/-- On same-side pairs, colouredness after the exchange. -/
theorem colored_exchange_same {v u : V} (hs : sameSide A v u) :
    colored (exchange M c a b₁ b₂ a₂ a₁ b) s(v, u) ↔
      colored M s(v, u) ∧ s(v, u) ≠ s(b₁, b₂) ∧ s(v, u) ≠ s(a₁, a₂) := by
  rw [colored_exchange hM h]
  constructor
  · rintro (h1 | h1)
    · exact h1
    · exact absurd hs (not_sameSide_of_new hM h h1)
  · exact Or.inl

/-- On crossing pairs, colouredness after the exchange. -/
theorem colored_exchange_cross {v u : V} (hs : ¬ sameSide A v u) :
    colored (exchange M c a b₁ b₂ a₂ a₁ b) s(v, u) ↔
      colored M s(v, u) ∨ s(v, u) = s(a, b₁) ∨ s(v, u) = s(b₂, a₂) ∨ s(v, u) = s(a₁, b) := by
  rw [colored_exchange hM h]
  constructor
  · rintro (⟨h1, -, -⟩ | h1)
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (h1 | h1)
    · refine Or.inl ⟨h1, fun he => hs ?_, fun he => hs ?_⟩
      · exact sameSide_of_removed hM h (Or.inl he)
      · exact sameSide_of_removed hM h (Or.inr he)
    · exact Or.inr h1

/-- `rdeg` after the exchange. -/
theorem rdeg_exchange (v : V) :
    rdeg G A (exchange M c a b₁ b₂ a₂ a₁ b) v =
      rdeg G A M v + if v = b₁ ∨ v = b₂ ∨ v = a₂ ∨ v = a₁ then 1 else 0 := by
  classical
  set T := univ.filter fun u => s(v, u) = s(b₁, b₂) ∨ s(v, u) = s(a₁, a₂)
  have hsplit : (univ.filter fun u => G.Adj v u ∧ sameSide A v u ∧
      ¬ colored (exchange M c a b₁ b₂ a₂ a₁ b) s(v, u)) =
      (univ.filter fun u => G.Adj v u ∧ sameSide A v u ∧ ¬ colored M s(v, u)) ∪ T := by
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_union, T]
    constructor
    · rintro ⟨hadj, hs, hc⟩
      rw [colored_exchange_same hM h hs] at hc
      by_cases h1 : s(v, u) = s(b₁, b₂)
      · exact Or.inr (Or.inl h1)
      by_cases h2 : s(v, u) = s(a₁, a₂)
      · exact Or.inr (Or.inr h2)
      exact Or.inl ⟨hadj, hs, fun h3 => hc ⟨h3, h1, h2⟩⟩
    · rintro (⟨hadj, hs, hc⟩ | hT)
      · exact ⟨hadj, hs, fun h3 => hc ((colored_exchange_same hM h hs).1 h3).1⟩
      · have hs := sameSide_of_removed hM h hT
        refine ⟨?_, hs, fun h3 => ?_⟩
        · rcases hT with hT | hT
          · exact hM.adj_of_mem (by rw [hT]; exact h.b₁b₂)
          · exact hM.adj_of_mem (by rw [hT]; exact h.a₁a₂)
        · have := ((colored_exchange_same hM h hs).1 h3).2
          tauto
  have hdisj : Disjoint (univ.filter fun u => G.Adj v u ∧ sameSide A v u ∧
      ¬ colored M s(v, u)) T := by
    rw [Finset.disjoint_left]
    intro u hu hT
    simp only [mem_filter, mem_univ, true_and, T] at hu hT
    rcases hT with hT | hT
    · exact hu.2.2 ⟨c, hT ▸ h.b₁b₂⟩
    · exact hu.2.2 ⟨c, hT ▸ h.a₁a₂⟩
  have hT : #T = if v = b₁ ∨ v = b₂ ∨ v = a₂ ∨ v = a₁ then 1 else 0 := by
    have s3 := h.hb₁; have s4 := h.hb₂; have s5 := h.ha₂; have s6 := h.ha₁
    have hle : #T ≤ 1 := by
      rw [card_le_one]
      intro u hu u' hu'
      simp only [T, mem_filter, mem_univ, true_and] at hu hu'
      by_cases heq : s(v, u) = s(v, u')
      · exact Sym2.congr_right.1 heq
      · exfalso
        have hv1 : v = b₁ ∨ v = b₂ ∨ v = a₁ ∨ v = a₂ := by
          rcases hu with hu | hu <;> rcases Sym2.eq_iff.1 hu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> tauto
        have hv2 : v = b₁ ∨ v = b₂ ∨ v = a₁ ∨ v = a₂ := hv1
        rcases hu with hu | hu <;> rcases hu' with hu' | hu'
        · exact heq (hu.trans hu'.symm)
        · rcases Sym2.eq_iff.1 hu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
            rcases Sym2.eq_iff.1 hu' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp_all
        · rcases Sym2.eq_iff.1 hu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
            rcases Sym2.eq_iff.1 hu' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp_all
        · exact heq (hu.trans hu'.symm)
    split_ifs with hv
    · have hne : T.Nonempty := by
        rcases hv with rfl | rfl | rfl | rfl
        · exact ⟨b₂, by simp [T]⟩
        · exact ⟨b₁, by simp [T, Sym2.eq_swap]⟩
        · exact ⟨a₁, by simp [T, Sym2.eq_swap]⟩
        · exact ⟨a₂, by simp [T]⟩
      have := card_pos.2 hne
      omega
    · rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro u hu
      simp only [T, mem_filter, mem_univ, true_and] at hu
      apply hv
      rcases hu with hu | hu <;> rcases Sym2.eq_iff.1 hu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> tauto
  rw [rdeg, hsplit, card_union_of_disjoint hdisj, hT, rdeg]

/-- `ccol` grows by at most one. -/
theorem ccol_exchange_le (v : V) :
    ccol G A (exchange M c a b₁ b₂ a₂ a₁ b) v ≤ ccol G A M v + 1 := by
  classical
  set T := univ.filter fun u => s(v, u) = s(a, b₁) ∨ s(v, u) = s(b₂, a₂) ∨ s(v, u) = s(a₁, b)
  have hsub : (univ.filter fun u => G.Adj v u ∧ ¬ sameSide A v u ∧
      colored (exchange M c a b₁ b₂ a₂ a₁ b) s(v, u)) ⊆
      (univ.filter fun u => G.Adj v u ∧ ¬ sameSide A v u ∧ colored M s(v, u)) ∪ T := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and, mem_union, T] at hu ⊢
    obtain ⟨hadj, hs, hc⟩ := hu
    rcases (colored_exchange_cross hM h hs).1 hc with h1 | h1
    · exact Or.inl ⟨hadj, hs, h1⟩
    · exact Or.inr h1
  have hT : #T ≤ 1 := by
    rw [card_le_one]
    intro u hu u' hu'
    simp only [T, mem_filter, mem_univ, true_and] at hu hu'
    by_cases heq : s(v, u) = s(v, u')
    · exact Sym2.congr_right.1 heq
    · exact (new_disjoint hM h hu hu' heq (Sym2.mem_mk_left v u) (Sym2.mem_mk_left v u')).elim
  calc _ ≤ #((univ.filter fun u => G.Adj v u ∧ ¬ sameSide A v u ∧ colored M s(v, u)) ∪ T) :=
        card_le_card hsub
    _ ≤ _ := (card_union_le _ _).trans (by rw [ccol]; omega)

/-- `ccol` does not change away from the six path vertices. -/
theorem ccol_exchange_of_ne (v : V)
    (hv : ¬ (v = a ∨ v = b₁ ∨ v = b₂ ∨ v = a₂ ∨ v = a₁ ∨ v = b)) :
    ccol G A (exchange M c a b₁ b₂ a₂ a₁ b) v ≤ ccol G A M v := by
  classical
  refine card_le_card fun u hu => ?_
  simp only [mem_filter, mem_univ, true_and] at hu ⊢
  obtain ⟨hadj, hs, hc⟩ := hu
  rcases (colored_exchange_cross hM h hs).1 hc with h1 | h1
  · exact ⟨hadj, hs, h1⟩
  · exfalso
    apply hv
    rcases h1 with h1 | h1 | h1 <;> rcases Sym2.eq_iff.1 h1 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> tauto

/-- `missing` does not grow, and drops at `a` and `b`. -/
theorem missing_exchange_le (v : V) :
    missing (exchange M c a b₁ b₂ a₂ a₁ b) v + (if v = a ∨ v = b then 1 else 0) ≤
      missing M v := by
  classical
  have hsub : (univ.filter fun c' : Fin k => ¬ covered (exchange M c a b₁ b₂ a₂ a₁ b) c' v) ⊆
      (univ.filter fun c' : Fin k => ¬ covered M c' v) := by
    intro c' hc'
    simp only [mem_filter, mem_univ, true_and] at hc' ⊢
    intro hcov
    apply hc'
    by_cases hcc : c' = c
    · subst hcc; exact (covered_exchange_self hM h v).2 (Or.inl hcov)
    · exact (covered_exchange_ne hM h hcc v).2 hcov
  split_ifs with hv
  · have hc : c ∈ univ.filter fun c' : Fin k => ¬ covered M c' v := by
      simp only [mem_filter, mem_univ, true_and]
      rcases hv with rfl | rfl
      · exact h.hfa
      · exact h.hfb
    have hc' : c ∉ univ.filter fun c' : Fin k => ¬ covered (exchange M c a b₁ b₂ a₂ a₁ b) c' v := by
      simp only [mem_filter, mem_univ, true_and, not_not]
      exact (covered_exchange_self hM h v).2 (Or.inr hv)
    have := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun he => hc' (he ▸ hc)⟩)
    unfold missing
    omega
  · rw [add_zero]
    exact card_le_card hsub

theorem missed_exchange_aux (S : Finset V) (z : V) (hz : z ∈ S) (hzc : ¬ covered M c z)
    (hzab : z = a ∨ z = b) (hother : ∀ v ∈ S, (v = a ∨ v = b) → v = z) :
    missed (exchange M c a b₁ b₂ a₂ a₁ b) c S + 1 = missed M c S := by
  classical
  have heq : (S.filter fun v => ¬ covered (exchange M c a b₁ b₂ a₂ a₁ b) c v) =
      (S.filter fun v => ¬ covered M c v).erase z := by
    ext v
    simp only [mem_filter, mem_erase, covered_exchange_self hM h v, not_or]
    constructor
    · rintro ⟨hv, hc, ha, hb⟩
      refine ⟨fun hvz => ?_, hv, hc⟩
      rcases hzab with h1 | h1
      · exact ha (hvz.trans h1)
      · exact hb (hvz.trans h1)
    · rintro ⟨hvz, hv, hc⟩
      exact ⟨hv, hc, fun ha => hvz (hother v hv (Or.inl ha)),
        fun hb => hvz (hother v hv (Or.inr hb))⟩
  unfold missed
  rw [heq, card_erase_of_mem (mem_filter.2 ⟨hz, hzc⟩)]
  have : 0 < #(S.filter fun v => ¬ covered M c v) := card_pos.2 ⟨z, mem_filter.2 ⟨hz, hzc⟩⟩
  omega

theorem missed_exchange_A :
    missed (exchange M c a b₁ b₂ a₂ a₁ b) c A + 1 = missed M c A :=
  missed_exchange_aux hM h A a h.ha h.hfa (Or.inl rfl) fun v hv hab => by
    rcases hab with rfl | rfl
    · rfl
    · exact absurd hv h.hb

theorem missed_exchange_B :
    missed (exchange M c a b₁ b₂ a₂ a₁ b) c Aᶜ + 1 = missed M c Aᶜ :=
  missed_exchange_aux hM h Aᶜ b (mem_compl.2 h.hb) h.hfb (Or.inr rfl) fun v hv hab => by
    rcases hab with rfl | rfl
    · exact absurd h.ha (mem_compl.1 hv)
    · rfl

theorem missed_exchange_ne {c' : Fin k} (hc : c' ≠ c) (S : Finset V) :
    missed (exchange M c a b₁ b₂ a₂ a₁ b) c' S = missed M c' S := by
  unfold missed
  simp only [covered_exchange_ne hM h hc]

end AltPath

end AOF
