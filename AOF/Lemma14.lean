/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.Extend

/-!
# Vaughan's Lemma 14 (simple graphs)

Steps 1–4 assembled: under the degree margins and the numerical conditions, a `d`-regular graph
with a balanced bipartition is `d`-edge-colourable.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace AOF

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem ccol_snoc_le {A : Finset V} {p : ℕ} (F : Fin p → Finset (Sym2 V)) {N : Finset (Sym2 V)}
    (hN : IsMatch N) (v : V) :
    ccol G A (Fin.snoc F N : Fin (p + 1) → Finset (Sym2 V)) v ≤ ccol G A F v + 1 := by
  classical
  have hsub : (univ.filter fun u => G.Adj v u ∧ ¬ sameSide A v u ∧
      colored (Fin.snoc F N : Fin (p + 1) → Finset (Sym2 V)) s(v, u)) ⊆
      (univ.filter fun u => G.Adj v u ∧ ¬ sameSide A v u ∧ colored F s(v, u)) ∪
        univ.filter fun u => s(v, u) ∈ N := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and, mem_union, colored_snoc] at hu ⊢
    rcases hu.2.2 with h | h
    · exact Or.inl ⟨hu.1, hu.2.1, h⟩
    · exact Or.inr h
  have hle : #(univ.filter fun u => s(v, u) ∈ N) ≤ 1 := by
    rw [card_le_one]
    intro u hu u' hu'
    simp only [mem_filter, mem_univ, true_and] at hu hu'
    exact Sym2.congr_right.1 (hN.eq_of_mem hu hu' (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _))
  rw [ccol, ccol]
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (by omega))

theorem two_mul_card_resid_eq_sum_rdeg {A : Finset V} {p : ℕ} (F : Fin p → Finset (Sym2 V))
    (S : Finset V) (hS : S = A ∨ S = Aᶜ) :
    2 * #(resid G S F).edgeFinset = ∑ v ∈ S, rdeg G A F v := by
  classical
  rw [← sum_degrees_eq_twice_card_edges, ← sum_subset (subset_univ S) fun v _ hv => ?_]
  · refine sum_congr rfl fun v hv => ?_
    rw [resid_degree, rdeg]
    congr 1
    ext u
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, -, h2, h3⟩
      refine ⟨h1, ?_, h3⟩
      rcases hS with rfl | rfl
      · exact Iff.intro (fun _ => h2) (fun _ => hv)
      · exact Iff.intro (fun h => absurd h (mem_compl.1 hv)) (fun h => absurd h (mem_compl.1 h2))
    · rintro ⟨h1, h2, h3⟩
      have h2' : v ∈ A ↔ u ∈ A := h2
      refine ⟨h1, hv, ?_, h3⟩
      rcases hS with rfl | rfl
      · exact h2'.1 hv
      · exact mem_compl.2 fun h => mem_compl.1 hv (h2'.2 h)
  · rw [resid_degree, card_eq_zero, filter_eq_empty_iff]
    intro u _ h
    exact hv h.2.1

theorem not_colored_of_mem_resid {p : ℕ} {S : Finset V} {F : Fin p → Finset (Sym2 V)}
    {e : Sym2 V} (he : e ∈ (resid G S F).edgeFinset) : ¬ colored F e := by
  induction e using Sym2.ind with
  | _ x y => exact (mem_resid_edgeFinset.1 he).2.2.2

/-- **Steps 3 and 4.** -/
theorem step34 {A : Finset V} {n d s t D : ℕ} (hreg : G.IsRegularOfDegree d) (hA : #A = n)
    (hB : #Aᶜ = n) (hdeg : ∀ v, n + 2 * D < 2 * degIn G A v ∧ n + 2 * D < 2 * degIn G Aᶜ v)
    {k : ℕ} {F0 : Fin k → Finset (Sym2 V)} (hF0 : IsPerfectFamily G F0)
    (hrdeg : ∀ v, rdeg G A F0 v ≤ t) (hcc : ∀ v, ccol G A F0 v ≤ s + t)
    (hrsum : ∑ v ∈ A, rdeg G A F0 v = ∑ v ∈ Aᶜ, rdeg G A F0 v)
    (hRsize : ∑ v ∈ A, rdeg G A F0 v ≤ 2 * (n * s))
    (hnum3 : 2 * ((n * s) ⌈/⌉ (t + 1)) + s + 2 * t + 1 ≤ D) :
    G.lineGraph.Colorable d := by
  classical
  have hmaxdeg : ∀ S : Finset V, (S = A ∨ S = Aᶜ) → (resid G S F0).maxDegree + 1 ≤ (t + 1) := by
    intro S hS
    have : (resid G S F0).maxDegree ≤ t := maxDegree_le_of_forall_degree_le _ _ fun v => by
      rw [resid_degree]
      have h0 := hrdeg v
      unfold rdeg at h0
      refine le_trans (card_le_card fun u hu => ?_) h0
      simp only [mem_filter, mem_univ, true_and] at hu ⊢
      refine ⟨hu.1, ?_, hu.2.2.2⟩
      rcases hS with rfl | rfl
      · exact Iff.intro (fun _ => hu.2.2.1) (fun _ => hu.2.1)
      · exact Iff.intro (fun h => absurd h (mem_compl.1 hu.2.1))
          (fun h => absurd h (mem_compl.1 hu.2.2.1))
    omega
  obtain ⟨QA, hmA, hsA, hdA, hcA, heA, hceA⟩ := exists_classes (G := G) A F0 (t + 1) (hmaxdeg A (Or.inl rfl))
  obtain ⟨QB, hmB, hsB, hdB, hcB, heB, -⟩ := exists_classes (G := G) Aᶜ F0 (t + 1) (hmaxdeg Aᶜ (Or.inr rfl))
  have hEeq : #(resid G A F0).edgeFinset = #(resid G Aᶜ F0).edgeFinset := by
    have h1 := two_mul_card_resid_eq_sum_rdeg (G := G) (A := A) F0 A (Or.inl rfl)
    have h2 := two_mul_card_resid_eq_sum_rdeg (G := G) (A := A) F0 Aᶜ (Or.inr rfl)
    omega
  have hEle : #(resid G A F0).edgeFinset ≤ n * s := by
    have h1 := two_mul_card_resid_eq_sum_rdeg (G := G) (A := A) F0 A (Or.inl rfl)
    omega
  obtain ⟨π, hπ⟩ := exists_perm_of_equitable (fun c => #(QA c)) (fun c => #(QB c)) heA heB
    (by rw [sum_card_classes QA _ hsA hdA hcA, sum_card_classes QB _ hsB hdB hcB, hEeq])
  have hβ : ∀ i, 2 * #(QA i) ≤ 2 * ((n * s) ⌈/⌉ (t + 1)) := by
    intro i
    have := hceA i
    have hmono : #(resid G A F0).edgeFinset ⌈/⌉ (t + 1) ≤ (n * s) ⌈/⌉ (t + 1) := by
      simp only [Nat.ceilDiv_eq_add_pred_div]
      exact Nat.div_le_div_right (by omega)
    omega
  -- the loop over the remaining classes
  suffices key : ∀ (m : ℕ) (R : Finset (Fin (t + 1))) (p : ℕ) (F : Fin p → Finset (Sym2 V)), #R = m →
      IsPerfectFamily G F → (∀ v, ccol G A F v + #R ≤ s + t + (t + 1)) →
      (∀ i ∈ R, ∀ e ∈ QA i ∪ QB (π i), ¬ colored F e) →
      (∀ u v, G.Adj u v → (u ∈ A ↔ v ∈ A) →
        colored F s(u, v) ∨ ∃ i ∈ R, s(u, v) ∈ QA i ∪ QB (π i)) →
      G.lineGraph.Colorable d by
    refine key _ univ k F0 rfl hF0 (fun v => ?_) (fun i _ e he => ?_) (fun u v huv hs => ?_)
    · have := hcc v; simp only [card_univ, Fintype.card_fin]; omega
    · rcases mem_union.1 he with he | he
      · exact not_colored_of_mem_resid (hsA i he)
      · exact not_colored_of_mem_resid (hsB _ he)
    · by_cases hc : colored F0 s(u, v)
      · exact Or.inl hc
      · right
        by_cases hu : u ∈ A
        · obtain ⟨i, hi⟩ := hcA s(u, v) (mem_resid_edgeFinset.2 ⟨huv, hu, hs.1 hu, hc⟩)
          exact ⟨i, mem_univ _, mem_union_left _ hi⟩
        · have hv : v ∉ A := fun h => hu (hs.2 h)
          obtain ⟨i, hi⟩ := hcB s(u, v)
            (mem_resid_edgeFinset.2 ⟨huv, mem_compl.2 hu, mem_compl.2 hv, hc⟩)
          exact ⟨π.symm i, mem_univ _, mem_union_right _ (by simpa using hi)⟩
  intro m
  induction m with
  | zero =>
    intro R p F hR hF _ _ hcov
    rw [card_eq_zero] at hR
    subst hR
    rcases isEmpty_or_nonempty V with hV | ⟨⟨u0⟩⟩
    · have : IsEmpty G.edgeSet := ⟨fun ⟨e, _⟩ => by
        induction e using Sym2.ind with | _ x y => exact hV.elim x⟩
      exact Colorable.of_isEmpty _
    have hpd : p ≤ d := by
      have h1 := card_colored_nbrs hF u0
      have h2 : #(univ.filter fun w => G.Adj u0 w ∧ colored F s(u0, w)) ≤
          #(univ.filter fun w => G.Adj u0 w) := card_le_card fun w hw => by
            simp only [mem_filter, mem_univ, true_and] at hw ⊢; exact hw.1
      rw [← neighborFinset_eq_filter, card_neighborFinset_eq_degree, hreg u0] at h2
      omega
    refine step4 (A := A) hreg (hA.trans hB.symm) (d - p) p F (by omega) hF fun u v huv hc => ?_
    · by_contra h
      have hs : u ∈ A ↔ v ∈ A := by tauto
      rcases hcov u v huv hs with h1 | ⟨i, hi, -⟩
      · exact hc h1
      · exact Finset.notMem_empty i hi
  | succ m ih =>
    intro R p F hR hF hcc' hunc hcov
    obtain ⟨i, hi⟩ : R.Nonempty := by rw [← card_pos]; omega
    have hγ : ∀ v, ccol G A F v ≤ s + t + (t + 1) := fun v => by have := hcc' v; omega
    obtain ⟨N, hNs, hNm, hNc, hNu, hQA, hQB, hNx⟩ := exists_extension hF hA hB hdeg hγ
      (β := 2 * ((n * s) ⌈/⌉ (t + 1))) (by omega) (QA i) (QB (π i)) (hmA i)
      (hmB _)
      (fun e he => ⟨(mem_of_mem_resid_edge (hsA i he)).1, (mem_of_mem_resid_edge (hsA i he)).2,
        hunc i hi e (mem_union_left _ he)⟩)
      (fun e he => ⟨(mem_of_mem_resid_edge (hsB _ he)).1, (mem_of_mem_resid_edge (hsB _ he)).2,
        hunc i hi e (mem_union_right _ he)⟩)
      (hπ i).symm (hβ i)
    refine ih (R.erase i) (p + 1) (Fin.snoc F N) (by rw [card_erase_of_mem hi]; omega)
      (hF.snoc hNs hNm hNc hNu) (fun v => ?_) (fun i' hi' e he => ?_) (fun u v huv hs => ?_)
    · have h1 := ccol_snoc_le (G := G) (A := A) F hNm v
      have h2 := hcc' v
      rw [card_erase_of_mem hi]
      have : 0 < #R := card_pos.2 ⟨i, hi⟩
      omega
    · rw [colored_snoc, not_or]
      have hi'R := mem_of_mem_erase hi'
      have hne : i' ≠ i := ne_of_mem_erase hi'
      refine ⟨hunc i' hi'R e he, fun heN => ?_⟩
      -- `e` lies inside one side, so it is in `QA i` or `QB (π i)`, a different class
      induction e using Sym2.ind with
      | _ x y =>
        have hin : (x ∈ A ↔ y ∈ A) := by
          rcases mem_union.1 he with he | he
          · have := (mem_of_mem_resid_edge (hsA i' he)).2
            exact ⟨fun _ => this y (Sym2.mem_mk_right _ _), fun _ => this x (Sym2.mem_mk_left _ _)⟩
          · have := (mem_of_mem_resid_edge (hsB _ he)).2
            have hx := mem_compl.1 (this x (Sym2.mem_mk_left _ _))
            have hy := mem_compl.1 (this y (Sym2.mem_mk_right _ _))
            tauto
        by_cases h1 : s(x, y) ∈ QA i
        · rcases mem_union.1 he with he | he
          · exact Finset.disjoint_left.1 (hdA i' i hne) he h1
          · have := (mem_of_mem_resid_edge (hsB _ he)).2 x (Sym2.mem_mk_left _ _)
            exact mem_compl.1 this ((mem_of_mem_resid_edge (hsA i h1)).2 x (Sym2.mem_mk_left _ _))
        by_cases h2 : s(x, y) ∈ QB (π i)
        · rcases mem_union.1 he with he | he
          · have := (mem_of_mem_resid_edge (hsA i' he)).2 x (Sym2.mem_mk_left _ _)
            exact mem_compl.1 ((mem_of_mem_resid_edge (hsB _ h2)).2 x (Sym2.mem_mk_left _ _)) this
          · exact Finset.disjoint_left.1 (hdB _ _ fun h => hne (π.injective h)) he h2
        have := hNx x y heN h1 h2
        tauto
    · rcases hcov u v huv hs with h1 | ⟨i', hi', h2⟩
      · exact Or.inl (colored_snoc.2 (Or.inl h1))
      · by_cases hii : i' = i
        · subst hii
          refine Or.inl (colored_snoc.2 (Or.inr ?_))
          rcases mem_union.1 h2 with h2 | h2
          · exact hQA h2
          · exact hQB h2
        · exact Or.inr ⟨i', mem_erase.2 ⟨hii, hi'⟩, h2⟩

/-- **Vaughan's Lemma 14** (simple graphs). -/
theorem lemma14 {A : Finset V} {n d s t D : ℕ} (hn : 0 < n) (ht : 0 < t)
    (hreg : G.IsRegularOfDegree d) (hA : #A = n) (hB : #Aᶜ = n)
    (hwin : ∀ v, degIn G A v < degIn G Aᶜ v + s ∧ degIn G Aᶜ v < degIn G A v + s)
    (hdeg : ∀ v, n + 2 * D < 2 * degIn G A v ∧ n + 2 * D < 2 * degIn G Aᶜ v)
    (hnum2 : 4 * n * s + t * (7 * s + t + 6) ≤ t * D)
    (hnum3 : 2 * ((n * s) ⌈/⌉ (t + 1)) + s + 2 * t + 1 ≤ D) :
    G.lineGraph.Colorable d := by
  obtain ⟨k, M0, hI0, hm0⟩ := step1 hn hA hB hreg hwin
    (fun v => ⟨by have := (hdeg v).1; omega, by have := (hdeg v).2; omega⟩) t
  obtain ⟨M, hI, hcov⟩ := step2 ht hA hB hm0 hdeg hnum2 _ M0 rfl hI0
  refine step34 hreg hA hB hdeg ⟨hI.state, hcov⟩ hI.rdeg_le (fun v => ?_) hI.rsum ?_ hnum3
  · have := hI.acc v; have := hm0 v; have := hI.rdeg_le v; omega
  · have h1 := hI.sumA
    have h2 : ∑ v ∈ A, missing M0 v ≤ n * s := by
      calc ∑ v ∈ A, missing M0 v ≤ ∑ _v ∈ A, s := sum_le_sum fun v _ => hm0 v
        _ = n * s := by rw [sum_const, smul_eq_mul, hA]
    omega

end AOF
