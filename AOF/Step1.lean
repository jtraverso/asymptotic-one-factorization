/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.Classes

/-!
# Step 1 of Vaughan's proof: the initial colouring

Equitable colourings of the graphs inside `A` and inside `Aᶜ` with `k = Δ_in + 1` colours, with the
colours of `Aᶜ` permuted so that each colour has equally many edges on both sides. The resulting
state satisfies `Inv2` with `m0 = missing`, every vertex misses at most `s` colours, and only edges
inside the two sides are coloured.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace AOF

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The empty family. -/
def noColours : Fin 0 → Finset (Sym2 V) := Fin.elim0

theorem not_colored_noColours (e : Sym2 V) : ¬ colored (noColours (V := V)) e :=
  fun ⟨c, _⟩ => c.elim0

theorem degIn_add_degIn (hreg : ∀ v, G.degree v = d) (A : Finset V) (v : V) :
    degIn G A v + degIn G Aᶜ v = d := by
  rw [← hreg v, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter, degIn, degIn,
    ← card_union_of_disjoint (disjoint_filter_filter disjoint_compl_right)]
  congr 1
  ext u
  simp only [mem_union, mem_filter, mem_compl, mem_univ, true_and]
  tauto

/-- The number of edges of `G` inside `S`, doubled, is the sum of the inner degrees. -/
theorem two_mul_card_resid (S : Finset V) :
    2 * #(resid G S noColours).edgeFinset = ∑ v ∈ S, degIn G S v := by
  classical
  rw [← sum_degrees_eq_twice_card_edges]
  rw [← sum_subset (subset_univ S) fun v _ hv => ?_]
  · refine sum_congr rfl fun v hv => ?_
    rw [resid_degree, degIn]
    congr 1
    ext u
    simp [hv, not_colored_noColours, and_comm]
  · rw [resid_degree, card_eq_zero, filter_eq_empty_iff]
    intro u _ h
    exact hv h.2.1

theorem sum_degIn_compl_comm (A : Finset V) :
    ∑ v ∈ A, degIn G Aᶜ v = ∑ v ∈ Aᶜ, degIn G A v := by
  classical
  simp only [degIn, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => sum_congr rfl fun u _ => ?_
  simp only [G.adj_comm]

theorem card_resid_eq (hreg : ∀ v, G.degree v = d) (A : Finset V) (hAB : #A = #Aᶜ) :
    #(resid G A noColours).edgeFinset = #(resid G Aᶜ noColours).edgeFinset := by
  have h1 := two_mul_card_resid (G := G) A
  have h2 := two_mul_card_resid (G := G) Aᶜ
  have e1 : ∑ v ∈ A, degIn G A v + ∑ v ∈ A, degIn G Aᶜ v = #A * d := by
    rw [← sum_add_distrib, sum_congr rfl fun v _ => degIn_add_degIn hreg A v, sum_const,
      smul_eq_mul]
  have e2 : ∑ v ∈ Aᶜ, degIn G Aᶜ v + ∑ v ∈ Aᶜ, degIn G A v = #Aᶜ * d := by
    rw [← sum_add_distrib, sum_congr rfl fun v _ => (add_comm _ _).trans (degIn_add_degIn hreg A v),
      sum_const, smul_eq_mul]
  have e3 := sum_degIn_compl_comm (G := G) A
  rw [hAB] at e1
  omega

/-- The colour classes of a family of matchings partition the edges they cover. -/
theorem sum_card_classes {j : ℕ} (Q : Fin j → Finset (Sym2 V)) (E : Finset (Sym2 V))
    (hsub : ∀ i, Q i ⊆ E) (hdisj : ∀ i i', i ≠ i' → Disjoint (Q i) (Q i'))
    (hcov : ∀ e ∈ E, ∃ i, e ∈ Q i) : ∑ i, #(Q i) = #E := by
  classical
  rw [← card_biUnion fun i _ i' _ h => hdisj i i' h]
  congr 1
  ext e
  simp only [mem_biUnion, mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ => hsub i hi, hcov e⟩

end AOF
