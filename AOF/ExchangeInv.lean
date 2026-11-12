/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.Exchange

/-!
# Invariants of the exchange

The exchanged family is again a state; colour `c` now covers `a` and `b`; `rdeg` grows by one
exactly at `b₁, b₂, a₂, a₁`; `ccol` grows by at most one, and only at the six path vertices.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace AOF

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {k : ℕ} {M : Fin k → Finset (Sym2 V)} {c : Fin k} {a b₁ b₂ a₂ a₁ b : V}

theorem covered_of_mem {c : Fin k} {v : V} {e : Sym2 V} (he : e ∈ M c) (hv : v ∈ e) :
    covered M c v := by
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv
  exact ⟨w, he⟩

namespace AltPath

variable (hM : IsState G M) (h : AltPath G A M c a b₁ b₂ a₂ a₁ b)
include hM h

/-- The six path vertices are not on the remaining old edges of colour `c`. -/
theorem notMem_old {e : Sym2 V} (he : e ∈ M c) (h1 : e ≠ s(b₁, b₂)) (h2 : e ≠ s(a₁, a₂))
    {v : V} (hv : v = a ∨ v = b₁ ∨ v = b₂ ∨ v = a₂ ∨ v = a₁ ∨ v = b) : v ∉ e := by
  intro hve
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.hfa (covered_of_mem he hve)
  · exact h1 ((hM.match_ c).eq_of_mem he h.b₁b₂ hve (Sym2.mem_mk_left _ _))
  · exact h1 ((hM.match_ c).eq_of_mem he h.b₁b₂ hve (Sym2.mem_mk_right _ _))
  · exact h2 ((hM.match_ c).eq_of_mem he h.a₁a₂ hve (Sym2.mem_mk_right _ _))
  · exact h2 ((hM.match_ c).eq_of_mem he h.a₁a₂ hve (Sym2.mem_mk_left _ _))
  · exact h.hfb (covered_of_mem he hve)

theorem new_uncolored {e : Sym2 V} (he : e = s(a, b₁) ∨ e = s(b₂, a₂) ∨ e = s(a₁, b)) :
    ¬ colored M e := by
  rcases he with rfl | rfl | rfl
  · exact h.cab₁
  · exact h.cb₂a₂
  · exact h.ca₁b

/-- The new edges have no common vertex. -/
theorem new_disjoint {e f : Sym2 V} (he : e = s(a, b₁) ∨ e = s(b₂, a₂) ∨ e = s(a₁, b))
    (hf : f = s(a, b₁) ∨ f = s(b₂, a₂) ∨ f = s(a₁, b)) (hne : e ≠ f) {v : V} (hve : v ∈ e)
    (hvf : v ∈ f) : False := by
  have n1 := h.b₁_ne_b₂ hM
  have n2 := h.a₁_ne_a₂ hM
  have n3 := h.a_ne_a₁
  have n4 := h.a_ne_a₂
  have n5 := h.b_ne_b₁
  have n6 := h.b_ne_b₂
  have s1 := h.ha; have s2 := h.hb; have s3 := h.hb₁; have s4 := h.hb₂
  have s5 := h.ha₂; have s6 := h.ha₁
  rcases he with rfl | rfl | rfl <;> rcases hf with rfl | rfl | rfl <;>
    first
    | exact hne rfl
    | (simp only [Sym2.mem_iff] at hve hvf
       rcases hve with rfl | rfl <;> rcases hvf with h' | h' <;> subst h' <;> simp_all)

/-- The exchanged family is a state. -/
theorem isState_exchange : IsState G (exchange M c a b₁ b₂ a₂ a₁ b) := by
  refine ⟨fun c' => ?_, fun c' => ?_, fun c' c'' hne => ?_⟩
  · by_cases hc : c' = c
    · subst hc
      rw [exchange_self]
      intro e he
      rw [mem_newClass] at he
      rcases he with ⟨he, -, -⟩ | rfl | rfl | rfl
      · exact hM.sub c' he
      · exact mem_edgeFinset.2 h.ab₁
      · exact mem_edgeFinset.2 h.b₂a₂
      · exact mem_edgeFinset.2 h.a₁b
    · rw [exchange_ne hc]; exact hM.sub c'
  · by_cases hc : c' = c
    · subst hc
      rw [exchange_self]
      intro e he f hf hne v hve hvf
      rw [mem_newClass] at he hf
      rcases he with ⟨he, he1, he2⟩ | he <;> rcases hf with ⟨hf, hf1, hf2⟩ | hf
      · exact hM.match_ c' e he f hf hne v hve hvf
      · -- `v` lies on a new edge, so it is one of the six vertices
        have hv : v = a ∨ v = b₁ ∨ v = b₂ ∨ v = a₂ ∨ v = a₁ ∨ v = b := by
          rcases hf with rfl | rfl | rfl <;> simp only [Sym2.mem_iff] at hvf <;> tauto
        exact notMem_old hM h he he1 he2 hv hve
      · have hv : v = a ∨ v = b₁ ∨ v = b₂ ∨ v = a₂ ∨ v = a₁ ∨ v = b := by
          rcases he with rfl | rfl | rfl <;> simp only [Sym2.mem_iff] at hve <;> tauto
        exact notMem_old hM h hf hf1 hf2 hv hvf
      · exact new_disjoint hM h he hf hne hve hvf
    · rw [exchange_ne hc]; exact hM.match_ c'
  · rw [Finset.disjoint_left]
    intro e he he'
    by_cases hc : c' = c
    · subst hc
      rw [exchange_self, mem_newClass] at he
      rw [exchange_ne (Ne.symm hne)] at he'
      rcases he with ⟨he, -, -⟩ | he
      · exact Finset.disjoint_left.1 (hM.disj c' c'' hne) he he'
      · exact new_uncolored hM h he ⟨c'', he'⟩
    · by_cases hc' : c'' = c
      · subst hc'
        rw [exchange_ne hc] at he
        rw [exchange_self, mem_newClass] at he'
        rcases he' with ⟨he', -, -⟩ | he'
        · exact Finset.disjoint_left.1 (hM.disj c' c'' hne) he he'
        · exact new_uncolored hM h he' ⟨c', he⟩
      · rw [exchange_ne hc] at he
        rw [exchange_ne hc'] at he'
        exact Finset.disjoint_left.1 (hM.disj c' c'' hne) he he'

/-- Coverage by colour `c` after the exchange. -/
theorem covered_exchange_self (v : V) :
    covered (exchange M c a b₁ b₂ a₂ a₁ b) c v ↔ covered M c v ∨ v = a ∨ v = b := by
  constructor
  · rintro ⟨w, hw⟩
    rw [exchange_self, mem_newClass] at hw
    rcases hw with ⟨hw, -, -⟩ | hw | hw | hw
    · exact Or.inl ⟨w, hw⟩
    · rcases Sym2.eq_iff.1 hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl ⟨b₂, h.b₁b₂⟩
    · rcases Sym2.eq_iff.1 hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨b₁, by rw [Sym2.eq_swap]; exact h.b₁b₂⟩
      · exact Or.inl ⟨a₁, by rw [Sym2.eq_swap]; exact h.a₁a₂⟩
    · rcases Sym2.eq_iff.1 hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨a₂, h.a₁a₂⟩
      · exact Or.inr (Or.inr rfl)
  · rintro (⟨w, hw⟩ | rfl | rfl)
    · by_cases h1 : s(v, w) = s(b₁, b₂)
      · rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨a, by rw [exchange_self, mem_newClass, Sym2.eq_swap]; tauto⟩
        · exact ⟨a₂, by rw [exchange_self, mem_newClass]; tauto⟩
      by_cases h2 : s(v, w) = s(a₁, a₂)
      · rcases Sym2.eq_iff.1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨b, by rw [exchange_self, mem_newClass]; tauto⟩
        · exact ⟨b₂, by rw [exchange_self, mem_newClass, Sym2.eq_swap]; tauto⟩
      exact ⟨w, by rw [exchange_self, mem_newClass]; exact Or.inl ⟨hw, h1, h2⟩⟩
    · exact ⟨b₁, by rw [exchange_self, mem_newClass]; tauto⟩
    · exact ⟨a₁, by rw [exchange_self, mem_newClass, Sym2.eq_swap]; tauto⟩

theorem covered_exchange_ne {c' : Fin k} (hc : c' ≠ c) (v : V) :
    covered (exchange M c a b₁ b₂ a₂ a₁ b) c' v ↔ covered M c' v := by
  simp only [covered, exchange_ne hc]

end AltPath

end AOF
