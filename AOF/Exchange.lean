/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.PathExists

/-!
# Exchanging an alternating path

`exchange M c a b₁ b₂ a₂ a₁ b` recolours the path `a b₁ b₂ a₂ a₁ b`: the edges `ab₁`, `b₂a₂`,
`a₁b` get colour `c` and `b₁b₂`, `a₂a₁` lose it. We compute how `colored`, `covered`, `rdeg`,
`ccol` and `missing` change.
-/

@[expose] public section

namespace AOF

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {k : ℕ} {M : Fin k → Finset (Sym2 V)}

/-- The new colour class `c`. -/
def newClass (M : Fin k → Finset (Sym2 V)) (c : Fin k) (a b₁ b₂ a₂ a₁ b : V) :
    Finset (Sym2 V) :=
  (((M c).erase s(b₁, b₂)).erase s(a₁, a₂)) ∪ {s(a, b₁), s(b₂, a₂), s(a₁, b)}

/-- The exchanged state. -/
def exchange (M : Fin k → Finset (Sym2 V)) (c : Fin k) (a b₁ b₂ a₂ a₁ b : V) :
    Fin k → Finset (Sym2 V) :=
  Function.update M c (newClass M c a b₁ b₂ a₂ a₁ b)

/-- The data of an alternating path for colour `c` (as produced by `exists_alt_path`). -/
structure AltPath (G : SimpleGraph V) (A : Finset V) (M : Fin k → Finset (Sym2 V)) (c : Fin k)
    (a b₁ b₂ a₂ a₁ b : V) : Prop where
  ha : a ∈ A
  hb : b ∉ A
  hb₁ : b₁ ∉ A
  hb₂ : b₂ ∉ A
  ha₂ : a₂ ∈ A
  ha₁ : a₁ ∈ A
  hfa : ¬ covered M c a
  hfb : ¬ covered M c b
  ab₁ : G.Adj a b₁
  cab₁ : ¬ colored M s(a, b₁)
  b₁b₂ : s(b₁, b₂) ∈ M c
  b₂a₂ : G.Adj b₂ a₂
  cb₂a₂ : ¬ colored M s(b₂, a₂)
  a₁a₂ : s(a₁, a₂) ∈ M c
  a₁b : G.Adj a₁ b
  ca₁b : ¬ colored M s(a₁, b)

namespace AltPath

variable {c : Fin k} {a b₁ b₂ a₂ a₁ b : V}

theorem b₁_ne_b₂ (hM : IsState G M) (h : AltPath G A M c a b₁ b₂ a₂ a₁ b) : b₁ ≠ b₂ :=
  (hM.adj_of_mem h.b₁b₂).ne

theorem a₁_ne_a₂ (hM : IsState G M) (h : AltPath G A M c a b₁ b₂ a₂ a₁ b) : a₁ ≠ a₂ :=
  (hM.adj_of_mem h.a₁a₂).ne

theorem a_ne_a₁ (h : AltPath G A M c a b₁ b₂ a₂ a₁ b) : a ≠ a₁ := by
  rintro rfl; exact h.hfa ⟨a₂, h.a₁a₂⟩

theorem a_ne_a₂ (h : AltPath G A M c a b₁ b₂ a₂ a₁ b) : a ≠ a₂ := by
  rintro rfl; exact h.hfa ⟨a₁, by rw [Sym2.eq_swap]; exact h.a₁a₂⟩

theorem b_ne_b₁ (h : AltPath G A M c a b₁ b₂ a₂ a₁ b) : b ≠ b₁ := by
  rintro rfl; exact h.hfb ⟨b₂, h.b₁b₂⟩

theorem b_ne_b₂ (h : AltPath G A M c a b₁ b₂ a₂ a₁ b) : b ≠ b₂ := by
  rintro rfl; exact h.hfb ⟨b₁, by rw [Sym2.eq_swap]; exact h.b₁b₂⟩

/-- The two removed edges are coloured only by `c`. -/
theorem mem_iff_b₁b₂ (hM : IsState G M) (h : AltPath G A M c a b₁ b₂ a₂ a₁ b) (c' : Fin k) :
    s(b₁, b₂) ∈ M c' ↔ c' = c := by
  constructor
  · intro h'
    by_contra hne
    exact disjoint_left.1 (hM.disj c' c hne) h' h.b₁b₂
  · rintro rfl; exact h.b₁b₂

theorem mem_iff_a₁a₂ (hM : IsState G M) (h : AltPath G A M c a b₁ b₂ a₂ a₁ b) (c' : Fin k) :
    s(a₁, a₂) ∈ M c' ↔ c' = c := by
  constructor
  · intro h'
    by_contra hne
    exact disjoint_left.1 (hM.disj c' c hne) h' h.a₁a₂
  · rintro rfl; exact h.a₁a₂

end AltPath

section Basic

variable {c : Fin k} {a b₁ b₂ a₂ a₁ b : V}

theorem exchange_self : exchange M c a b₁ b₂ a₂ a₁ b c = newClass M c a b₁ b₂ a₂ a₁ b := by
  simp [exchange]

theorem exchange_ne {c' : Fin k} (h : c' ≠ c) : exchange M c a b₁ b₂ a₂ a₁ b c' = M c' := by
  simp [exchange, h]

theorem mem_newClass {e : Sym2 V} : e ∈ newClass M c a b₁ b₂ a₂ a₁ b ↔
    (e ∈ M c ∧ e ≠ s(b₁, b₂) ∧ e ≠ s(a₁, a₂)) ∨
      e = s(a, b₁) ∨ e = s(b₂, a₂) ∨ e = s(a₁, b) := by
  simp only [newClass, mem_union, mem_erase, mem_insert, mem_singleton]
  tauto

/-- How `colored` changes. -/
theorem colored_exchange (hM : IsState G M) (h : AltPath G A M c a b₁ b₂ a₂ a₁ b) (e : Sym2 V) :
    colored (exchange M c a b₁ b₂ a₂ a₁ b) e ↔
      (colored M e ∧ e ≠ s(b₁, b₂) ∧ e ≠ s(a₁, a₂)) ∨
        e = s(a, b₁) ∨ e = s(b₂, a₂) ∨ e = s(a₁, b) := by
  constructor
  · rintro ⟨c', hc'⟩
    by_cases hcc : c' = c
    · subst hcc
      rw [exchange_self, mem_newClass] at hc'
      rcases hc' with ⟨h1, h2, h3⟩ | h4
      · exact Or.inl ⟨⟨c', h1⟩, h2, h3⟩
      · exact Or.inr h4
    · rw [exchange_ne hcc] at hc'
      refine Or.inl ⟨⟨c', hc'⟩, ?_, ?_⟩
      · rintro rfl; exact hcc ((h.mem_iff_b₁b₂ hM c').1 hc')
      · rintro rfl; exact hcc ((h.mem_iff_a₁a₂ hM c').1 hc')
  · rintro (⟨⟨c', hc'⟩, h2, h3⟩ | h4)
    · by_cases hcc : c' = c
      · subst hcc
        exact ⟨c', by rw [exchange_self, mem_newClass]; exact Or.inl ⟨hc', h2, h3⟩⟩
      · exact ⟨c', by rw [exchange_ne hcc]; exact hc'⟩
    · exact ⟨c, by rw [exchange_self, mem_newClass]; exact Or.inr h4⟩

end Basic

end AOF
