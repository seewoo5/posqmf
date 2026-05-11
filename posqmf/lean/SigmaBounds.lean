import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Trivial bounds on the divisor function `σₖ`

For `n ≥ 1` and `k : ℕ`, we prove the elementary bounds

* `pow_le_sigma`: `nᵏ ≤ σₖ(n)` (since `n` itself is a divisor),
* `sigma_le_two_mul_pow`: for `k ≥ 2`, `σₖ(n) ≤ 2 nᵏ`,

which follow from `σₖ(n) = nᵏ · ∑_{d ∣ n} 1/dᵏ` and `∑_{d=1}^∞ 1/dᵏ ≤ 2`.
-/

open ArithmeticFunction Finset
open scoped sigma

/-- **Lower bound for `σₖ(n)`**: `nᵏ ≤ σₖ(n)` for `n ≥ 1` (since `n` itself is a divisor). -/
lemma pow_le_sigma (k n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ k ≤ (σ k n : ℝ) := by
  rw [sigma_apply]
  exact_mod_cast single_le_sum (f := (· ^ k)) (fun _ _ => Nat.zero_le _)
    (n.mem_divisors.mpr ⟨dvd_refl n, by omega⟩)

private lemma sum_telescope_one_div (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Icc 2 N, ((1 : ℝ) / ((d - 1 : ℕ) : ℝ) - 1 / (d : ℝ)) = 1 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => rw [show Icc 2 1 = ∅ from Icc_eq_empty_of_lt (by omega)]; simp
  | succ m hm ih =>
    by_cases hm2 : 2 ≤ m
    · rw [show Icc 2 (m + 1) = insert (m + 1) (Icc 2 m) by
            ext x; simp [mem_Icc, mem_insert]; omega,
          sum_insert (by rw [mem_Icc]; omega), ih,
          show ((m + 1 - 1 : ℕ) : ℝ) = (m : ℝ) by rw [Nat.add_sub_cancel]]
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hm
      field_simp
      ring
    · interval_cases m
      rw [show Icc 2 (1 + 1) = {2} by ext x; rw [mem_Icc, mem_singleton]; omega]
      simp

private lemma sum_one_div_sq_le_one (N : ℕ) :
    ∑ d ∈ Icc 2 N, ((1 : ℝ) / (d : ℝ) ^ 2) ≤ 1 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · rw [Icc_eq_empty_of_lt hN]; simp
  have hbound : ∀ d ∈ Icc 2 N,
      ((1 : ℝ) / (d : ℝ) ^ 2) ≤ ((1 : ℝ) / ((d - 1 : ℕ) : ℝ) - 1 / (d : ℝ)) := by
    intro d hd
    rw [mem_Icc] at hd
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.1
    rw [show ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 by
          rw [Nat.cast_sub (by omega : 1 ≤ d)]; push_cast; ring,
        div_sub_div _ _ (by linarith) (by linarith), sq,
        div_le_div_iff₀ (by positivity) (by nlinarith)]
    nlinarith
  calc ∑ d ∈ Icc 2 N, ((1 : ℝ) / (d : ℝ) ^ 2)
      ≤ ∑ d ∈ Icc 2 N, ((1 : ℝ) / ((d - 1 : ℕ) : ℝ) - 1 / (d : ℝ)) := sum_le_sum hbound
    _ = 1 - 1 / (N : ℝ) := sum_telescope_one_div N (by omega)
    _ ≤ 1 := by linarith [show (0 : ℝ) ≤ 1 / (N : ℝ) by positivity]

private lemma one_div_pow_le_one_div_sq {d : ℕ} (hd : 1 ≤ d) {k : ℕ} (hk : 2 ≤ k) :
    ((1 : ℝ) / (d : ℝ) ^ k) ≤ (1 : ℝ) / (d : ℝ) ^ 2 :=
  one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by exact_mod_cast hd) hk)

private lemma sum_one_div_pow_Icc_le_two {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Icc 1 n, ((1 : ℝ) / (d : ℝ) ^ k) ≤ 2 := by
  rw [show Icc 1 n = insert 1 (Icc 2 n) by ext x; simp [mem_Icc, mem_insert]; omega,
      sum_insert (by rw [mem_Icc]; omega), Nat.cast_one, one_pow, div_one]
  have h_bound : ∀ d ∈ Icc 2 n, ((1 : ℝ) / (d : ℝ) ^ k) ≤ (1 : ℝ) / (d : ℝ) ^ 2 :=
    fun d hd => one_div_pow_le_one_div_sq (by rw [mem_Icc] at hd; omega) hk
  linarith [sum_le_sum h_bound, sum_one_div_sq_le_one n]

private lemma sigma_eq_pow_mul_sum_inv (k : ℕ) (n : ℕ) (hn : 1 ≤ n) :
    (σ k n : ℝ) = (n : ℝ) ^ k * ∑ d ∈ n.divisors, ((1 : ℝ) / (d : ℝ) ^ k) := by
  rw [show (σ k n : ℝ) = ((∑ d ∈ n.divisors, (n / d) ^ k : ℕ) : ℝ) by
        exact_mod_cast ArithmeticFunction.sigma_eq_sum_div k n]
  push_cast
  rw [Finset.mul_sum]
  refine sum_congr rfl fun d hd => ?_
  obtain ⟨hd_dvd, _⟩ := Nat.mem_divisors.mp hd
  rw [Nat.cast_div hd_dvd (Nat.cast_ne_zero.mpr (Nat.pos_of_dvd_of_pos hd_dvd (by omega)).ne'),
    div_pow]
  field_simp

/-- **Upper bound for `σₖ(n)`**: for `k ≥ 2` and `n ≥ 1`, `σₖ(n) ≤ 2 nᵏ`. -/
lemma sigma_le_two_mul_pow {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    (σ k n : ℝ) ≤ 2 * (n : ℝ) ^ k := by
  rw [sigma_eq_pow_mul_sum_inv k n hn]
  have h_sum_le : ∑ d ∈ n.divisors, ((1 : ℝ) / (d : ℝ) ^ k) ≤ 2 :=
    le_trans (sum_le_sum_of_subset_of_nonneg (fun d hd => by
      rw [Nat.mem_divisors] at hd; rw [mem_Icc]
      exact ⟨Nat.pos_of_dvd_of_pos hd.1 (by omega), Nat.le_of_dvd (by omega) hd.1⟩)
      (fun _ _ _ => by positivity)) (sum_one_div_pow_Icc_le_two hk n hn)
  nlinarith [mul_le_mul_of_nonneg_left h_sum_le (by positivity : (0:ℝ) ≤ (n:ℝ)^k)]
