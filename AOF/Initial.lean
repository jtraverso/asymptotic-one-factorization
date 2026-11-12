/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.Step1

/-!
# The initial state of Step 2

From equitable colourings of the two sides (Step 1) we build the state `M c = Q_A c ∪ Q_B (π c)`
and check `Inv2` with `m0 = missing M`.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace AOF

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem mem_of_mem_resid_edge {p : ℕ} {S : Finset V} {F : Fin p → Finset (Sym2 V)} {e : Sym2 V}
    (he : e ∈ (resid G S F).edgeFinset) : e ∈ G.edgeFinset ∧ ∀ v ∈ e, v ∈ S := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_resid_edgeFinset] at he
    refine ⟨mem_edgeFinset.2 he.1, fun v hv => ?_⟩
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact he.2.1
    · exact he.2.2.1

/-- The colours at `v ∈ S` of a class decomposition of `resid G S noColours`. -/
theorem card_covering_colours {j : ℕ} (S : Finset V) (Q : Fin j → Finset (Sym2 V))
    (hsub : ∀ i, Q i ⊆ (resid G S noColours).edgeFinset)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (Q i) (Q i'))
    (hcov : ∀ e ∈ (resid G S noColours).edgeFinset, ∃ i, e ∈ Q i)
    (hm : ∀ i, IsMatch (Q i)) {v : V} (hv : v ∈ S) :
    #(univ.filter fun i => ∃ u, s(v, u) ∈ Q i) = degIn G S v := by
  classical
  have hcol : ∀ u ∈ S.filter fun u => G.Adj v u, ∃ i, s(v, u) ∈ Q i := by
    intro u hu
    rw [mem_filter] at hu
    exact hcov _ (mem_resid_edgeFinset.2 ⟨hu.2, hv, hu.1, not_colored_noColours _⟩)
  rcases (S.filter fun u => G.Adj v u).eq_empty_or_nonempty with hemp | ⟨u0, hu0⟩
  · rw [degIn, hemp, card_empty, card_eq_zero, filter_eq_empty_iff]
    rintro i - ⟨u, hu⟩
    have hres := hsub i hu
    rw [mem_resid_edgeFinset] at hres
    have : u ∈ S.filter fun u => G.Adj v u := mem_filter.2 ⟨hres.2.2.1, hres.1⟩
    rw [hemp] at this
    exact Finset.notMem_empty u this
  haveI : Nonempty (Fin j) := ⟨(hcol u0 hu0).choose⟩
  choose! col hcol using hcol
  have huniq : ∀ u ∈ S.filter (fun u => G.Adj v u), ∀ i, s(v, u) ∈ Q i → col u = i := by
    intro u hu i hi
    by_contra hne
    exact Finset.disjoint_left.1 (hdisj _ _ hne) (hcol u hu) hi
  have himage : (univ.filter fun i => ∃ u, s(v, u) ∈ Q i) =
      (S.filter fun u => G.Adj v u).image col := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨u, hu⟩
      have hres := hsub i hu
      rw [mem_resid_edgeFinset] at hres
      have hu' : u ∈ S.filter fun u => G.Adj v u := mem_filter.2 ⟨hres.2.2.1, hres.1⟩
      exact ⟨u, mem_filter.1 hu', huniq u hu' i hu⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hcol u (mem_filter.2 hu)⟩
  rw [himage, card_image_of_injOn, degIn]
  intro u hu u' hu' h
  have h1 := hcol u hu
  have h2 := hcol u' hu'
  rw [h] at h1
  exact (hm _).eq_of_mem h1 h2 (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _) |>
    fun he => Sym2.congr_right.1 he

/-- Two-sided window: inner degrees of any two vertices differ by less than `s`. -/
theorem din_lt {A : Finset V} {d s : ℕ} (hreg : ∀ v, G.degree v = d)
    (hwin : ∀ v, degIn G A v < degIn G Aᶜ v + s ∧ degIn G Aᶜ v < degIn G A v + s)
    (S T : Finset V) (hS : S = A ∨ S = Aᶜ) (hT : T = A ∨ T = Aᶜ) (x y : V) :
    degIn G S x < degIn G T y + s := by
  have hx := degIn_add_degIn hreg A x
  have hy := degIn_add_degIn hreg A y
  have wx := hwin x
  have wy := hwin y
  rcases hS with rfl | rfl <;> rcases hT with rfl | rfl <;> omega

theorem degIn_le_resid_degree (S : Finset V) {v : V} (hv : v ∈ S) :
    degIn G S v ≤ (resid G S noColours).degree v := by
  rw [resid_degree, degIn]
  refine card_le_card fun u hu => ?_
  simp only [mem_filter, mem_univ, true_and] at hu ⊢
  exact ⟨hu.2, hv, hu.1, not_colored_noColours _⟩

theorem resid_degree_le_degIn (S : Finset V) (w : V) :
    (resid G S noColours).degree w ≤ degIn G S w := by
  rw [resid_degree, degIn]
  refine card_le_card fun u hu => ?_
  simp only [mem_filter, mem_univ, true_and] at hu ⊢
  exact ⟨hu.2.2.1, hu.1⟩

/-- **Step 1.** An initial state satisfying `Inv2`, with at most `s` missing colours per vertex. -/
theorem step1 {A : Finset V} {n d s : ℕ} (hn : 0 < n) (hA : #A = n) (hB : #Aᶜ = n)
    (hreg : ∀ v, G.degree v = d)
    (hwin : ∀ v, degIn G A v < degIn G Aᶜ v + s ∧ degIn G Aᶜ v < degIn G A v + s)
    (hhalf : ∀ v, n < 2 * degIn G A v ∧ n < 2 * degIn G Aᶜ v) (t : ℕ) :
    ∃ (k : ℕ) (M : Fin k → Finset (Sym2 V)), Inv2 G A M s t (missing M) ∧
      ∀ v, missing M v ≤ s := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, k = max (resid G A (noColours (V := V))).maxDegree
      (resid G Aᶜ (noColours (V := V))).maxDegree + 1 := ⟨_, rfl⟩
  have hkA := le_max_left (resid G A (noColours (V := V))).maxDegree
    (resid G Aᶜ (noColours (V := V))).maxDegree
  have hkB := le_max_right (resid G A (noColours (V := V))).maxDegree
    (resid G Aᶜ (noColours (V := V))).maxDegree
  obtain ⟨QA, hmA, hsA, hdA, hcA, heA, -⟩ :=
    exists_classes (G := G) A noColours k (by omega)
  obtain ⟨QB, hmB, hsB, hdB, hcB, heB, -⟩ :=
    exists_classes (G := G) Aᶜ noColours k (by omega)
  have hsum : ∑ c, #(QA c) = ∑ c, #(QB c) := by
    rw [sum_card_classes QA _ hsA hdA hcA, sum_card_classes QB _ hsB hdB hcB,
      card_resid_eq hreg A (hA.trans hB.symm)]
  obtain ⟨π, hπ⟩ := exists_perm_of_equitable (fun c => #(QA c)) (fun c => #(QB c)) heA heB hsum
  have hinA : ∀ c e, e ∈ QA c → e ∈ G.edgeFinset ∧ ∀ v ∈ e, v ∈ A :=
    fun c e he => mem_of_mem_resid_edge (hsA c he)
  have hinB : ∀ c e, e ∈ QB c → e ∈ G.edgeFinset ∧ ∀ v ∈ e, v ∈ Aᶜ :=
    fun c e he => mem_of_mem_resid_edge (hsB c he)
  set M : Fin k → Finset (Sym2 V) := fun c => QA c ∪ QB (π c) with hMdef
  have hstate : IsState G M := by
    refine ⟨fun c e he => ?_, fun c => ?_, fun c c' hne => ?_⟩
    · rcases mem_union.1 he with he | he
      · exact (hinA c e he).1
      · exact (hinB _ e he).1
    · intro e he f hf hef v hve hvf
      rcases mem_union.1 he with he | he <;> rcases mem_union.1 hf with hf | hf
      · exact hmA c e he f hf hef v hve hvf
      · exact mem_compl.1 ((hinB _ f hf).2 v hvf) ((hinA c e he).2 v hve)
      · exact mem_compl.1 ((hinB _ e he).2 v hve) ((hinA c f hf).2 v hvf)
      · exact hmB _ e he f hf hef v hve hvf
    · rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨x, hx⟩ : ∃ x, x ∈ e := by
        induction e using Sym2.ind with | _ x y => exact ⟨x, Sym2.mem_mk_left _ _⟩
      rcases mem_union.1 he with he | he <;> rcases mem_union.1 he' with he' | he'
      · exact Finset.disjoint_left.1 (hdA c c' hne) he he'
      · exact mem_compl.1 ((hinB _ e he').2 x hx) ((hinA c e he).2 x hx)
      · exact mem_compl.1 ((hinB _ e he).2 x hx) ((hinA c' e he').2 x hx)
      · exact Finset.disjoint_left.1 (hdB _ _ fun h => hne (π.injective h)) he he'
  have hcovA : ∀ c, ∀ v ∈ A, covered M c v ↔ ∃ u, s(v, u) ∈ QA c := by
    intro c v hv
    constructor
    · rintro ⟨u, hu⟩
      rcases mem_union.1 hu with hu | hu
      · exact ⟨u, hu⟩
      · exact absurd hv (mem_compl.1 ((hinB _ _ hu).2 v (Sym2.mem_mk_left _ _)))
    · rintro ⟨u, hu⟩; exact ⟨u, mem_union_left _ hu⟩
  have hcovB : ∀ c, ∀ v ∉ A, covered M c v ↔ ∃ u, s(v, u) ∈ QB (π c) := by
    intro c v hv
    constructor
    · rintro ⟨u, hu⟩
      rcases mem_union.1 hu with hu | hu
      · exact absurd ((hinA _ _ hu).2 v (Sym2.mem_mk_left _ _)) hv
      · exact ⟨u, hu⟩
    · rintro ⟨u, hu⟩; exact ⟨u, mem_union_right _ hu⟩
  have hcovcount : ∀ v, #(univ.filter fun c => covered M c v) =
      if v ∈ A then degIn G A v else degIn G Aᶜ v := by
    intro v
    split_ifs with hv
    · rw [← card_covering_colours A QA hsA hdA hcA hmA hv]
      congr 1; ext c; simp [hcovA c v hv]
    · rw [← card_covering_colours Aᶜ QB hsB hdB hcB hmB (mem_compl.2 hv)]
      rw [← card_map π.toEmbedding]
      congr 1; ext c
      simp only [mem_map_equiv, mem_filter, mem_univ, true_and, hcovB _ v hv]
      simp
  have hmiss : ∀ v, missing M v + (if v ∈ A then degIn G A v else degIn G Aᶜ v) = k := by
    intro v
    rw [← hcovcount v, missing, add_comm, card_filter_add_card_filter_not, card_univ,
      Fintype.card_fin]
  have hkle : ∀ v, k ≤ (if v ∈ A then degIn G A v else degIn G Aᶜ v) + s := by
    intro v
    have hmax : ∀ (S : Finset V), (S = A ∨ S = Aᶜ) →
        (resid G S noColours).maxDegree < (if v ∈ A then degIn G A v else degIn G Aᶜ v) + s := by
      intro S hS
      have hpos : 0 < (if v ∈ A then degIn G A v else degIn G Aᶜ v) + s := by
        have := hhalf v
        split_ifs <;> omega
      have hle : ∀ w, (resid G S noColours).degree w ≤
          (if v ∈ A then degIn G A v else degIn G Aᶜ v) + s - 1 := by
        intro w
        have hw := din_lt hreg hwin S (if v ∈ A then A else Aᶜ) hS
          (by split_ifs <;> simp) w v
        have := resid_degree_le_degIn (G := G) S w
        split_ifs at hw ⊢ <;> omega
      have := maxDegree_le_of_forall_degree_le _ _ hle
      omega
    have h1 := hmax A (Or.inl rfl)
    have h2 := hmax Aᶜ (Or.inr rfl)
    have := max_lt h1 h2
    omega
  have hmissle : ∀ v, missing M v ≤ s := by
    intro v; have := hmiss v; have := hkle v; omega
  have hcolin : ∀ u v, G.Adj u v → (u ∈ A ↔ v ∈ A) → colored M s(u, v) := by
    intro u v huv hs
    by_cases hu : u ∈ A
    · obtain ⟨c, hc⟩ := hcA s(u, v)
        (mem_resid_edgeFinset.2 ⟨huv, hu, hs.1 hu, not_colored_noColours _⟩)
      exact ⟨c, mem_union_left _ hc⟩
    · have hv : v ∉ A := fun h => hu (hs.2 h)
      obtain ⟨c, hc⟩ := hcB s(u, v)
        (mem_resid_edgeFinset.2 ⟨huv, mem_compl.2 hu, mem_compl.2 hv, not_colored_noColours _⟩)
      exact ⟨π.symm c, mem_union_right _ (by simpa using hc)⟩
  have hcolout : ∀ u v, colored M s(u, v) → (u ∈ A ↔ v ∈ A) := by
    rintro u v ⟨c, hc⟩
    rcases mem_union.1 hc with hc | hc
    · have := (hinA c _ hc).2
      exact ⟨fun _ => this v (Sym2.mem_mk_right _ _), fun _ => this u (Sym2.mem_mk_left _ _)⟩
    · have := (hinB _ _ hc).2
      have hu := mem_compl.1 (this u (Sym2.mem_mk_left _ _))
      have hv := mem_compl.1 (this v (Sym2.mem_mk_right _ _))
      tauto
  have hrdeg : ∀ v, rdeg G A M v = 0 := by
    intro v
    rw [rdeg, card_eq_zero, filter_eq_empty_iff]
    rintro u - ⟨huv, hs, hc⟩
    exact hc (hcolin v u huv hs)
  have hccol : ∀ v, ccol G A M v = 0 := by
    intro v
    rw [ccol, card_eq_zero, filter_eq_empty_iff]
    rintro u - ⟨-, hs, hc⟩
    exact hs (hcolout v u hc)
  have hmissedA : ∀ c, missed M c A + 2 * #(QA c) = n := by
    intro c
    have hcard := card_covered_eq (QA c) (hmA c) A (fun e he => (hinA c e he).2)
      (fun e he hd => G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.1 (hinA c e he).1) hd)
    have hset : (A.filter fun v => ∃ u, s(v, u) ∈ QA c) = A.filter fun v => covered M c v := by
      ext v
      simp only [mem_filter]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (hcovA c v h1).2 h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (hcovA c v h1).1 h2⟩⟩
    rw [hset] at hcard
    have := card_filter_add_card_filter_not (s := A) (fun v => covered M c v)
    rw [missed, ← hcard, ← hA]
    omega
  have hmissedB : ∀ c, missed M c Aᶜ + 2 * #(QA c) = n := by
    intro c
    have hcard := card_covered_eq (QB (π c)) (hmB _) Aᶜ (fun e he => (hinB _ e he).2)
      (fun e he hd => G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.1 (hinB _ e he).1) hd)
    have hset : (Aᶜ.filter fun v => ∃ u, s(v, u) ∈ QB (π c)) =
        Aᶜ.filter fun v => covered M c v := by
      ext v
      simp only [mem_filter]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (hcovB c v (mem_compl.1 h1)).2 h2⟩,
        fun ⟨h1, h2⟩ => ⟨h1, (hcovB c v (mem_compl.1 h1)).1 h2⟩⟩
    rw [hset, hπ c] at hcard
    have := card_filter_add_card_filter_not (s := Aᶜ) (fun v => covered M c v)
    rw [missed, ← hcard, ← hB]
    omega
  have hlc : ∀ c, ∀ S : Finset V, (S = A ∨ S = Aᶜ) → lcount M c S = 0 := by
    intro c S hS
    rw [lcount, card_eq_zero, filter_eq_empty_iff]
    rintro w hw ⟨u, hu, hwu⟩
    have := hcolout w u ⟨c, hwu⟩
    rcases hS with rfl | rfl
    · exact hu (this.1 hw)
    · exact hu (mem_compl.2 fun h => mem_compl.1 hw (this.2 h))
  have hdc : ∑ c, missed M c A = ∑ v ∈ A, missing M v := by
    simp only [missed, missing, card_filter]
    exact sum_comm
  have hsumMissed : ∑ c, missed M c A ≤ n * s := by
    rw [hdc]
    calc ∑ v ∈ A, missing M v ≤ ∑ _v ∈ A, s := sum_le_sum fun v _ => hmissle v
      _ = n * s := by rw [sum_const, smul_eq_mul, hA]
  have hgap : ∀ c c', missed M c A ≤ missed M c' A + 2 := by
    intro c c'
    have h1 := hmissedA c
    have h2 := hmissedA c'
    have := heA c' c
    omega
  have hkn : n < 2 * k := by
    obtain ⟨v, hv⟩ : A.Nonempty := card_pos.1 (hA ▸ hn)
    have h1 := (hhalf v).1
    have h2 := degIn_le_resid_degree (G := G) A hv
    have h3 := (resid G A (noColours (V := V))).degree_le_maxDegree v
    omega
  have hmissed2 : ∀ c, missed M c A ≤ 2 * s + 2 := by
    intro c
    have hk0 : 0 < k := by omega
    have h1 : k * (missed M c A - 2) ≤ n * s := by
      calc k * (missed M c A - 2) = ∑ _c' : Fin k, (missed M c A - 2) := by simp
        _ ≤ ∑ c', missed M c' A := sum_le_sum fun c' _ => by have := hgap c c'; omega
        _ ≤ n * s := hsumMissed
    have h2 : k * (missed M c A - 2) ≤ k * (2 * s) := by
      calc k * (missed M c A - 2) ≤ n * s := h1
        _ ≤ (2 * k) * s := Nat.mul_le_mul_right _ hkn.le
        _ = k * (2 * s) := by ring
    have := Nat.le_of_mul_le_mul_left h2 hk0
    omega
  refine ⟨k, M, ⟨hstate, fun v => by rw [hrdeg v]; exact Nat.zero_le _,
    fun v => by rw [hrdeg v, hccol v]; omega, ?_, ?_, ?_, fun c => ?_, fun c => ?_,
    fun c => ?_⟩, hmissle⟩
  · simp [hrdeg]
  · simp [hrdeg]
  · simp [hrdeg]
  · have := hmissedA c; have := hmissedB c; omega
  · rw [hlc c A (Or.inl rfl)]; have := hmissed2 c; omega
  · rw [hlc c Aᶜ (Or.inr rfl)]
    have := hmissed2 c; have := hmissedA c; have := hmissedB c; omega

end AOF
