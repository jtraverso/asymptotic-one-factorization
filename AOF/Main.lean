/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.Lemma14

/-!
# The asymptotic 1-factorization theorem (Perković–Reed, Häggkvist; Vaughan's proof, `r = 1`)

For every `ε > 0` there is `N` such that every `d`-regular simple graph on `2n ≥ 2N` vertices with
`d ≥ (1 + ε) n` is `d`-edge-colourable (1-factorizable).

Parameters, for `(q + 1) n ≤ q d`: `a = ⌊n/q⌋`, `s = ⌊a/(200q)⌋`, `t = ⌊a/6⌋`,
`D = ⌊(a − s)/2⌋ − 1`; Vaughan's `n^{2/3}` and `n^{5/6}` are replaced by these linear sizes.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace AOF

open Finset SimpleGraph Real

/-- The Chernoff condition from `32 n³ < s⁴`. -/
theorem chernoff_cond {n s : ℕ} (hn : 0 < n) (h : 32 * n ^ 3 < s ^ 4) :
    4 * (n : ℝ) * exp (-((s : ℝ) ^ 2 / (2 * n))) < 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set x : ℝ := (s : ℝ) ^ 2 / (2 * n)
  have hx : 0 ≤ x := by positivity
  have hexp := Real.pow_div_factorial_le_exp x hx 2
  have hx2 : x ^ 2 = (s : ℝ) ^ 4 / (4 * (n : ℝ) ^ 2) := by
    simp only [x]; field_simp; ring
  have hcast : (32 : ℝ) * (n : ℝ) ^ 3 < (s : ℝ) ^ 4 := by exact_mod_cast h
  have hbig : 4 * (n : ℝ) < exp x := by
    have : 4 * (n : ℝ) < x ^ 2 / 2 := by
      rw [hx2, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2), lt_div_iff₀ (by positivity)]
      nlinarith
    calc 4 * (n : ℝ) < x ^ 2 / 2 := this
      _ = x ^ 2 / (Nat.factorial 2 : ℝ) := by norm_num
      _ ≤ exp x := hexp
  rw [exp_neg, ← div_eq_mul_inv, div_lt_one (exp_pos x)]
  exact hbig

/-- The numerical conditions for large `n`. -/
theorem params_ok {q n : ℕ} (hq : 0 < q)
    (hn : (200 * q * q) * (512 * (200 * q * q) ^ 3 + 4) ≤ n) :
    0 < n / q / 6 ∧ n / q / (200 * q) + 4 ≤ n / q ∧
    4 * n * (n / q / (200 * q)) + n / q / 6 * (7 * (n / q / (200 * q)) + n / q / 6 + 6) ≤
      n / q / 6 * ((n / q - n / q / (200 * q)) / 2 - 1) ∧
    2 * ((n * (n / q / (200 * q))) ⌈/⌉ (n / q / 6 + 1)) + n / q / (200 * q) + 2 * (n / q / 6) + 1 ≤
      (n / q - n / q / (200 * q)) / 2 - 1 ∧
    32 * n ^ 3 < (n / q / (200 * q)) ^ 4 := by
  set L := 200 * q * q with hL
  set a := n / q with ha
  set s := a / (200 * q) with hs
  set t := a / 6 with ht
  have hL1 : 200 ≤ L := by rw [hL]; nlinarith
  -- basic bounds
  have ha1 : q * a ≤ n := Nat.mul_div_le n q
  have ha2 : n < q * (a + 1) := by
    have := Nat.lt_mul_div_succ n hq; rw [ha]; linarith
  have hs1 : 200 * q * s ≤ a := Nat.mul_div_le a (200 * q)
  have hs2 : a < 200 * q * (s + 1) := Nat.lt_mul_div_succ a (by positivity)
  have ht1 : 6 * t ≤ a := Nat.mul_div_le a 6
  have ht2 : a < 6 * (t + 1) := Nat.lt_mul_div_succ a (by norm_num)
  have hsL : s = n / L := by rw [hs, ha, Nat.div_div_eq_div_mul, hL]; ring_nf
  have hsbig : 512 * L ^ 3 + 4 ≤ s := by
    rw [hsL]; exact (Nat.le_div_iff_mul_le (by omega)).2 (by linarith)
  have hnL : n < L * (s + 1) := by rw [hsL]; exact Nat.lt_mul_div_succ n (by omega)
  have hs200 : 200 * s ≤ a := by nlinarith
  have hL3 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hsge : 516 ≤ s := by nlinarith
  have hage : 200 * 516 ≤ a := by omega
  have htge : 9 ≤ t := by omega
  -- `200 n s ≤ (a + 1) a`
  have hns : 200 * (n * s) ≤ (a + 1) * a := by
    have h1 : n ≤ q * (a + 1) := ha2.le
    calc 200 * (n * s) ≤ 200 * (q * (a + 1) * s) := by gcongr
      _ = (a + 1) * (200 * q * s) := by ring
      _ ≤ (a + 1) * a := by gcongr
  set D := (a - s) / 2 - 1 with hD
  have hD1 : a - s ≤ 2 * D + 3 := by omega
  have hD2 : 2 * D + 2 ≤ a - s := by omega
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · -- `4ns + t(7s + t + 6) ≤ tD`
    have hsa : 200 * s ≤ 6 * t + 5 := by omega
    have hat : a ≤ 6 * t + 5 := by omega
    have h50 : 50 * (4 * n * s + t * (7 * s + t + 6)) ≤ 50 * (t * D) := by
      have e1 : 200 * (n * s) ≤ (6 * t + 6) * (6 * t + 5) := by
        calc 200 * (n * s) ≤ (a + 1) * a := hns
          _ ≤ (6 * t + 6) * (6 * t + 5) := Nat.mul_le_mul (by omega) (by omega)
      have e2 : 2 * D + s + 3 ≥ 6 * t := by omega
      nlinarith
    omega
  · -- the ceiling bound
    have hc : (n * s) ⌈/⌉ (t + 1) ≤ t / 5 + 1 := by
      rw [ceilDiv_le_iff_le_mul (by omega)]
      have e1 : 200 * (n * s) ≤ (t + 1) * (36 * t + 30) := by
        calc 200 * (n * s) ≤ (a + 1) * a := hns
          _ ≤ (6 * t + 6) * (6 * t + 5) := Nat.mul_le_mul (by omega) (by omega)
          _ = (t + 1) * (36 * t + 30) := by ring
      have e2 : 36 * t + 30 ≤ 200 * (t / 5 + 1) := by omega
      nlinarith
    have hsa : 200 * s ≤ 6 * t + 5 := by omega
    omega
  · -- `32 n³ < s⁴`
    have h1 : n ≤ L * (2 * s) := by nlinarith
    have h2 : 32 * n ^ 3 ≤ 32 * (L * (2 * s)) ^ 3 := by gcongr
    have h3 : 32 * (L * (2 * s)) ^ 3 = 256 * L ^ 3 * s ^ 3 := by ring
    have h4 : 256 * L ^ 3 * s ^ 3 < s ^ 4 := by
      have : 256 * L ^ 3 < s := by omega
      have hs3 : 0 < s ^ 3 := by positivity
      calc 256 * L ^ 3 * s ^ 3 < s * s ^ 3 := by gcongr
        _ = s ^ 4 := by ring
    omega

universe u

/-- **Asymptotic 1-factorization**, integer form: if `(q + 1) n ≤ q d`. -/
theorem one_factorization_of_ge {q : ℕ} (hq : 0 < q) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n d : ℕ), N ≤ n → Fintype.card V = 2 * n → G.IsRegularOfDegree d →
        (q + 1) * n ≤ q * d → G.lineGraph.Colorable d := by
  refine ⟨(200 * q * q) * (512 * (200 * q * q) ^ 3 + 4), fun V _ _ G _ n d hN hV hreg hd => ?_⟩
  classical
  obtain ⟨ht0, has, hnum2, hnum3, hch⟩ := params_ok hq hN
  set a := n / q
  set s := a / (200 * q)
  set t := a / 6
  set D := (a - s) / 2 - 1
  have hn : 0 < n := by
    have : 0 < (200 * q * q) * (512 * (200 * q * q) ^ 3 + 4) := by positivity
    omega
  obtain ⟨A, hA, hwin⟩ := exists_balanced_half G hn hV (Nat.cast_nonneg s) (chernoff_cond hn hch)
  have hB : #Aᶜ = n := by rw [card_compl, hV, hA]; omega
  have hwin' : ∀ v, degIn G A v < degIn G Aᶜ v + s ∧ degIn G Aᶜ v < degIn G A v + s := by
    intro v
    have := abs_lt.1 (hwin v)
    constructor
    · have h := this.2; exact_mod_cast (by linarith : (degIn G A v : ℝ) < degIn G Aᶜ v + s)
    · have h := this.1; exact_mod_cast (by linarith : (degIn G Aᶜ v : ℝ) < degIn G A v + s)
  have hda : n + a ≤ d := by
    have h1 : q * a ≤ n := Nat.mul_div_le n q
    have : q * (n + a) ≤ q * d := by nlinarith
    exact Nat.le_of_mul_le_mul_left this hq
  have hdeg : ∀ v, n + 2 * D < 2 * degIn G A v ∧ n + 2 * D < 2 * degIn G Aᶜ v := by
    intro v
    have h1 := degIn_add_degIn hreg A v
    have h2 := hwin' v
    omega
  exact lemma14 hn ht0 hreg hA hB hwin' hdeg hnum2 hnum3

/-- **Asymptotic 1-factorization** (Perković–Reed, Häggkvist). -/
theorem one_factorization (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (n d : ℕ), N ≤ n → Fintype.card V = 2 * n → G.IsRegularOfDegree d →
        (1 + ε) * n ≤ d → G.lineGraph.Colorable d := by
  obtain ⟨q, hq⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := one_factorization_of_ge.{u} (Nat.succ_pos q)
  refine ⟨N, fun V _ _ G _ n d hn hV hreg hd => hN V G n d hn hV hreg ?_⟩
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have h1 : (1 + 1 / ((q : ℝ) + 1)) * n ≤ d := by
    refine le_trans ?_ hd
    gcongr
  have h2 : (((q + 1 + 1 : ℕ) : ℝ)) * n ≤ ((q + 1 : ℕ) : ℝ) * d := by
    push_cast
    have := mul_le_mul_of_nonneg_left h1 hq1.le
    have e : ((q : ℝ) + 1) * ((1 + 1 / ((q : ℝ) + 1)) * n) = ((q : ℝ) + 1 + 1) * n := by
      field_simp
    linarith
  exact_mod_cast h2

end AOF
