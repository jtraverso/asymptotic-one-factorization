/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# A Chernoff bound for signed sums, by counting

For weights `c : Fin n → ℝ` with `|cᵢ| ≤ 1`, the number of sign vectors `σ : Fin n → Bool` with
`Σ ±cᵢ ≥ s` is at most `2ⁿ exp(−s²/(2n))`. Proof: the exponential moment
`Σ_σ exp(λ Σ ±cᵢ) = Π (exp(λcᵢ) + exp(−λcᵢ)) = Π 2 cosh(λcᵢ) ≤ 2ⁿ exp(λ²n/2)`, then Markov with
`λ = s/n`.
-/

@[expose] public section

namespace AOF

open Finset Real

/-- The signed sum `Σ ±cᵢ` for the sign vector `σ`. -/
noncomputable def signedSum {n : ℕ} (c : Fin n → ℝ) (σ : Fin n → Bool) : ℝ :=
  ∑ i, if σ i then c i else -c i

theorem sum_exp_signedSum {n : ℕ} (c : Fin n → ℝ) (l : ℝ) :
    ∑ σ : Fin n → Bool, exp (l * signedSum c σ) =
      ∏ i, (exp (l * c i) + exp (-(l * c i))) := by
  have h : ∀ σ : Fin n → Bool, exp (l * signedSum c σ) =
      ∏ i, (fun i b => if b then exp (l * c i) else exp (-(l * c i))) i (σ i) := by
    intro σ
    rw [signedSum, mul_sum, exp_sum]
    refine prod_congr rfl fun i _ => ?_
    cases σ i <;> simp
  simp_rw [h]
  have key := Fintype.prod_sum (R := ℝ)
    (fun (i : Fin n) (b : Bool) => if b then exp (l * c i) else exp (-(l * c i)))
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false] at key
  rw [key]

theorem sum_exp_signedSum_le {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, |c i| ≤ 1) (l : ℝ) :
    ∑ σ : Fin n → Bool, exp (l * signedSum c σ) ≤ 2 ^ n * exp (l ^ 2 * n / 2) := by
  rw [sum_exp_signedSum]
  have hterm : ∀ i, exp (l * c i) + exp (-(l * c i)) ≤ 2 * exp (l ^ 2 / 2) := by
    intro i
    have h1 : exp (l * c i) + exp (-(l * c i)) = 2 * cosh (l * c i) := by
      rw [cosh_eq]; ring
    rw [h1]
    have h2 := cosh_le_exp_half_sq (l * c i)
    have h3 : (l * c i) ^ 2 / 2 ≤ l ^ 2 / 2 := by
      have : (c i) ^ 2 ≤ 1 := by
        have := sq_abs (c i)
        nlinarith [hc i, abs_nonneg (c i)]
      have hl : 0 ≤ l ^ 2 := sq_nonneg l
      nlinarith
    have h4 := exp_le_exp.2 h3
    linarith
  calc ∏ i, (exp (l * c i) + exp (-(l * c i)))
      ≤ ∏ _i : Fin n, 2 * exp (l ^ 2 / 2) :=
        prod_le_prod₀ (fun i _ => by positivity) fun i _ => hterm i
    _ = 2 ^ n * exp (l ^ 2 * n / 2) := by
        rw [prod_const, card_univ, Fintype.card_fin, mul_pow, ← exp_nat_mul]
        congr 2
        ring

/-- **One-sided Chernoff bound by counting.** -/
theorem card_signedSum_ge_le {n : ℕ} (hn : 0 < n) (c : Fin n → ℝ) (hc : ∀ i, |c i| ≤ 1)
    (s : ℝ) (hs : 0 ≤ s) :
    ((univ.filter fun σ : Fin n → Bool => s ≤ signedSum c σ).card : ℝ) ≤
      2 ^ n * exp (-(s ^ 2 / (2 * n))) := by
  set l : ℝ := s / n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 ≤ l := div_nonneg hs hn'.le
  have hmark : ((univ.filter fun σ : Fin n → Bool => s ≤ signedSum c σ).card : ℝ) * exp (l * s) ≤
      ∑ σ : Fin n → Bool, exp (l * signedSum c σ) := by
    calc ((univ.filter fun σ : Fin n → Bool => s ≤ signedSum c σ).card : ℝ) * exp (l * s)
        = ∑ σ ∈ univ.filter fun σ : Fin n → Bool => s ≤ signedSum c σ, exp (l * s) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ σ ∈ univ.filter fun σ : Fin n → Bool => s ≤ signedSum c σ,
            exp (l * signedSum c σ) := by
          refine sum_le_sum fun σ hσ => ?_
          rw [mem_filter] at hσ
          exact exp_le_exp.2 (mul_le_mul_of_nonneg_left hσ.2 hl)
      _ ≤ ∑ σ : Fin n → Bool, exp (l * signedSum c σ) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => (exp_pos _).le
  have hb := (hmark.trans (sum_exp_signedSum_le c hc l))
  have hpos := exp_pos (l * s)
  have key : 2 ^ n * exp (l ^ 2 * n / 2) / exp (l * s) = 2 ^ n * exp (-(s ^ 2 / (2 * n))) := by
    rw [mul_div_assoc, ← exp_sub]
    congr 2
    simp only [l]
    field_simp
    ring
  rw [← key, le_div_iff₀ hpos]
  exact hb

/-- **Two-sided Chernoff bound by counting.** -/
theorem card_abs_signedSum_ge_le {n : ℕ} (hn : 0 < n) (c : Fin n → ℝ) (hc : ∀ i, |c i| ≤ 1)
    (s : ℝ) (hs : 0 ≤ s) :
    ((univ.filter fun σ : Fin n → Bool => s ≤ |signedSum c σ|).card : ℝ) ≤
      2 * 2 ^ n * exp (-(s ^ 2 / (2 * n))) := by
  have hneg : ∀ σ, signedSum (fun i => -c i) σ = -signedSum c σ := by
    intro σ
    rw [signedSum, signedSum, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    cases σ i <;> simp
  have h1 := card_signedSum_ge_le hn c hc s hs
  have h2 := card_signedSum_ge_le hn (fun i => -c i) (fun i => by simpa using hc i) s hs
  simp_rw [hneg] at h2
  have hsub : (univ.filter fun σ : Fin n → Bool => s ≤ |signedSum c σ|) ⊆
      (univ.filter fun σ : Fin n → Bool => s ≤ signedSum c σ) ∪
        (univ.filter fun σ : Fin n → Bool => s ≤ -signedSum c σ) := by
    intro σ hσ
    simp only [mem_filter, mem_univ, true_and, mem_union] at hσ ⊢
    rcases le_abs'.1 hσ with h | h
    · right; linarith
    · left; exact h
  calc ((univ.filter fun σ : Fin n → Bool => s ≤ |signedSum c σ|).card : ℝ)
      ≤ ((univ.filter fun σ : Fin n → Bool => s ≤ signedSum c σ) ∪
          (univ.filter fun σ : Fin n → Bool => s ≤ -signedSum c σ)).card := by
        exact_mod_cast card_le_card hsub
    _ ≤ (univ.filter fun σ : Fin n → Bool => s ≤ signedSum c σ).card +
          ((univ.filter fun σ : Fin n → Bool => s ≤ -signedSum c σ).card : ℝ) := by
        exact_mod_cast card_union_le _ _
    _ ≤ 2 * 2 ^ n * exp (-(s ^ 2 / (2 * n))) := by linarith

end AOF
