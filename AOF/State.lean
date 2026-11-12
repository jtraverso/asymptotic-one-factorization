/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.Matchings
public import AOF.Partition

/-!
# Partial colourings by matchings, for the alternating-path step

A state is a family `M : Fin k → Finset (Sym2 V)` of pairwise disjoint matchings of `G`. With a
bipartition `A`, `Aᶜ` of the vertices:

* `colored M e`: the edge `e` has some colour;
* `rdeg M v`: the number of uncoloured edges at `v` inside the side of `v` (the degree of `v` in
  `R_A` or `R_B`);
* `ccol M v`: the number of coloured edges at `v` across the bipartition;
* `missing M v`: the number of colours missing at `v`;
* `xcount M c`: the number of vertices of `Aᶜ` on a crossing edge of colour `c`.
-/

@[expose] public section

namespace AOF

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (A : Finset V) {k : ℕ} (M : Fin k → Finset (Sym2 V))

/-- `u` and `v` lie on the same side of the bipartition `A`, `Aᶜ`. -/
def sameSide (u v : V) : Prop := (u ∈ A ↔ v ∈ A)

instance : DecidableRel (sameSide A) := fun u v => inferInstanceAs (Decidable (u ∈ A ↔ v ∈ A))

/-- The edge `e` is coloured. -/
def colored (e : Sym2 V) : Prop := ∃ c, e ∈ M c

instance (e : Sym2 V) : Decidable (colored M e) := inferInstanceAs (Decidable (∃ c, e ∈ M c))

/-- `v` is covered by the colour class `c`. -/
def covered (c : Fin k) (v : V) : Prop := ∃ w, s(v, w) ∈ M c

instance (c : Fin k) (v : V) : Decidable (covered M c v) := by
  unfold covered
  exact decidable_of_iff (∃ w ∈ (univ : Finset V), s(v, w) ∈ M c) (by simp)

/-- The degree of `v` in the graph of uncoloured edges inside its side. -/
def rdeg (v : V) : ℕ :=
  #(univ.filter fun u => G.Adj v u ∧ sameSide A v u ∧ ¬ colored M s(v, u))

/-- The number of coloured crossing edges at `v`. -/
def ccol (v : V) : ℕ :=
  #(univ.filter fun u => G.Adj v u ∧ ¬ sameSide A v u ∧ colored M s(v, u))

/-- The number of colours missing at `v`. -/
def missing (v : V) : ℕ := #(univ.filter fun c : Fin k => ¬ covered M c v)

/-- The number of vertices of `Aᶜ` on a crossing edge of colour `c`. -/
def xcount (c : Fin k) : ℕ :=
  #(Aᶜ.filter fun w => ∃ u ∈ A, s(w, u) ∈ M c)

/-- The number of vertices of `S` missed by colour `c`. -/
def missed (c : Fin k) (S : Finset V) : ℕ := #(S.filter fun v => ¬ covered M c v)

/-- Basic invariants of a state: pairwise disjoint matchings of `G`. -/
structure IsState : Prop where
  sub : ∀ c, M c ⊆ G.edgeFinset
  match_ : ∀ c, IsMatch (M c)
  disj : ∀ c c', c ≠ c' → Disjoint (M c) (M c')

variable {G A M}

theorem IsState.adj_of_mem (hM : IsState G M) {c : Fin k} {u v : V} (h : s(u, v) ∈ M c) :
    G.Adj u v := by
  have := hM.sub c h
  rwa [mem_edgeFinset, mem_edgeSet] at this

theorem IsState.partner_unique (hM : IsState G M) {c : Fin k} {u v w : V}
    (h1 : s(u, v) ∈ M c) (h2 : s(u, w) ∈ M c) : v = w := by
  have := (hM.match_ c).eq_of_mem h1 h2 (Sym2.mem_mk_left u v) (Sym2.mem_mk_left u w)
  rcases Sym2.eq_iff.1 this with ⟨-, h⟩ | ⟨rfl, rfl⟩
  · exact h
  · rfl

theorem covered_iff_not_free {c : Fin k} {v : V} :
    covered M c v ↔ ∃ w, s(v, w) ∈ M c := Iff.rfl

end AOF
