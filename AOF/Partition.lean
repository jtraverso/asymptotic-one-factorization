/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import AOF.Chernoff
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Balanced bipartitions (Vaughan, Lemma 13, simple graphs)

If `|V| = 2n` and `4n · exp(−s²/(2n)) < 1`, the vertex set splits into two halves `A`, `Aᶜ` of
size `n` with `|d_A(v) − d_{Aᶜ}(v)| < s` for every vertex `v`. Proof: pair up the vertices and put
one vertex of each pair in `A` according to a sign vector; by `card_abs_signedSum_ge_le` fewer
than `2ⁿ` sign vectors are bad, so some sign vector is good for every vertex.
-/

@[expose] public section

namespace AOF

open Finset Real SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of neighbours of `v` in `S`. -/
def degIn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : ℕ :=
  #(S.filter fun u => G.Adj v u)

/-- The half selected by a sign vector through a pairing `e`. -/
def half {n : ℕ} (e : Fin n × Bool ≃ V) (σ : Fin n → Bool) : Finset V :=
  univ.image fun i => e (i, σ i)

omit [Fintype V] in
theorem card_half {n : ℕ} (e : Fin n × Bool ≃ V) (σ : Fin n → Bool) : #(half e σ) = n := by
  rw [half, card_image_of_injective _ fun i j h => by
    have := e.injective h
    simpa using congrArg Prod.fst this]
  simp

omit [Fintype V] in
theorem mem_half {n : ℕ} (e : Fin n × Bool ≃ V) (σ : Fin n → Bool) (i : Fin n) (b : Bool) :
    e (i, b) ∈ half e σ ↔ b = σ i := by
  simp only [half, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    have := e.injective hj
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    rfl
  · rintro rfl
    exact ⟨i, rfl⟩

/-- `d_A(v) − d_{Aᶜ}(v)` as a signed sum over the pairs. -/
theorem degIn_sub_eq_signedSum (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ}
    (e : Fin n × Bool ≃ V) (σ : Fin n → Bool) (v : V) :
    (degIn G (half e σ) v : ℝ) - degIn G (half e σ)ᶜ v =
      signedSum (fun i => (if G.Adj v (e (i, true)) then (1 : ℝ) else 0) -
        (if G.Adj v (e (i, false)) then 1 else 0)) σ := by
  have hcount : ∀ S : Finset V, (degIn G S v : ℝ) =
      ∑ i : Fin n, ∑ b : Bool, if e (i, b) ∈ S ∧ G.Adj v (e (i, b)) then (1 : ℝ) else 0 := by
    intro S
    have h1 : degIn G S v = #(univ.filter fun u => u ∈ S ∧ G.Adj v u) := by
      rw [degIn]
      congr 1
      ext u
      simp
    rw [h1, card_filter, Nat.cast_sum, ← e.sum_comp, Fintype.sum_prod_type]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hcount, hcount, ← sum_sub_distrib, signedSum]
  refine sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool, Fintype.sum_bool]
  simp only [mem_compl, mem_half]
  cases σ i <;> simp

/-- **Balanced bipartition** (Vaughan, Lemma 13 for simple graphs). -/
theorem exists_balanced_half (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (hn : 0 < n)
    (hV : Fintype.card V = 2 * n) {s : ℝ} (hs : 0 ≤ s)
    (hch : 4 * n * exp (-(s ^ 2 / (2 * n))) < 1) :
    ∃ A : Finset V, #A = n ∧
      ∀ v, |(degIn G A v : ℝ) - degIn G Aᶜ v| < s := by
  classical
  have hcard : Fintype.card (Fin n × Bool) = Fintype.card V := by simp [hV, mul_comm]
  obtain e := (Fintype.equivOfCardEq hcard)
  let c : V → Fin n → ℝ := fun v i => (if G.Adj v (e (i, true)) then (1 : ℝ) else 0) -
    (if G.Adj v (e (i, false)) then 1 else 0)
  have hc : ∀ v i, |c v i| ≤ 1 := by
    intro v i
    simp only [c]
    split_ifs <;> norm_num
  let bad : Finset (Fin n → Bool) :=
    univ.biUnion fun v => univ.filter fun σ => s ≤ |signedSum (c v) σ|
  have hbad : (#bad : ℝ) < 2 ^ n := by
    calc (#bad : ℝ) ≤ ∑ v : V, ((univ.filter fun σ => s ≤ |signedSum (c v) σ|).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ _v : V, 2 * 2 ^ n * exp (-(s ^ 2 / (2 * n))) :=
          sum_le_sum fun v _ => card_abs_signedSum_ge_le hn (c v) (hc v) s hs
      _ = (2 * n : ℕ) * (2 * 2 ^ n * exp (-(s ^ 2 / (2 * n)))) := by
          rw [sum_const, card_univ, hV, nsmul_eq_mul]
      _ = 2 ^ n * (4 * n * exp (-(s ^ 2 / (2 * n)))) := by push_cast; ring
      _ < 2 ^ n * 1 := by
          exact mul_lt_mul_of_pos_left hch (by positivity)
      _ = 2 ^ n := mul_one _
  have hlt : #bad < #(univ : Finset (Fin n → Bool)) := by
    have : (#(univ : Finset (Fin n → Bool)) : ℝ) = 2 ^ n := by simp
    exact_mod_cast hbad.trans_eq this.symm
  obtain ⟨σ, -, hσ⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨half e σ, card_half e σ, fun v => ?_⟩
  rw [degIn_sub_eq_signedSum G e σ v]
  by_contra h
  apply hσ
  exact mem_biUnion.2 ⟨v, mem_univ v, mem_filter.2 ⟨mem_univ σ, not_lt.1 h⟩⟩

end AOF
