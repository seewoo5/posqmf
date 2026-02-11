import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.ArithmeticFunction.Misc

abbrev divisorCount (n : ℕ) : ℕ := (ArithmeticFunction.sigma 0) n

private lemma sigma0_mul_rpow_le_pow7 (m : ℕ) (hm : 1 ≤ m) :
    (divisorCount m : ℝ) * (m : ℝ) ^ (11/2 : ℝ) ≤ (m : ℝ) ^ 7 :=
  calc ((divisorCount m : ℝ) * (m : ℝ) ^ (11/2 : ℝ))
      ≤ (m : ℝ) ^ (13/2 : ℝ) := by
        rw [show (13/2 : ℝ) = 1 + 11/2 from by norm_num,
            Real.rpow_add_of_nonneg (Nat.cast_nonneg m) (by norm_num)
            (by norm_num), Real.rpow_one]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by simp only [
            ArithmeticFunction.sigma_zero_apply, Nat.card_divisors_le_self]))
            (by positivity)
    _ ≤ (m : ℝ) ^ 7 := le_of_le_of_eq (Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hm) (show (13:ℝ)/2 ≤ 7 from by norm_num))
        (by norm_cast)

/- Inequality (60) -/
theorem main_theorem (m : ℕ) (hm_ge : 3 ≤ m) :
    (2520 : ℝ) / 3 * m ^ 9 -
    18224 / 21 * (divisorCount m : ℝ) * m ^ (11 / 2 : ℝ) +
    12 / 7 * m ^ 10 > 0 := by
  have hm' : (m : ℝ) ≥ 3 := by exact_mod_cast hm_ge
  have hpoly : (840 : ℝ) * m ^ 9 - 18224 / 21 * m ^ 7 + 12 / 7 * m ^ 10 > 0
      := by
    rw [show (840 : ℝ) * m ^ 9 - 18224 / 21 * m ^ 7 + 12 / 7 * m ^ 10 =
        (m ^ 7 / 21) * (36 * m ^ 3 + 17640 * m ^ 2 - 18224) by ring]
    have : (36 : ℝ) * m ^ 3 + 17640 * m ^ 2 - 18224 > 0 := by nlinarith
    positivity
  have h := sigma0_mul_rpow_le_pow7 m (by omega)
  have h_scaled : (18224 : ℝ) / 21 * (divisorCount m : ℝ) * m ^ (11 / 2 : ℝ) ≤
      18224 / 21 * m ^ 7 := by nlinarith
  linarith
