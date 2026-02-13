import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.StarOrdered

private lemma two_rpow_pos (x : ℝ) : (0 : ℝ) < (2 : ℝ) ^ x :=
  Real.rpow_pos_of_pos (by norm_num) x

lemma factor_two_pow_2k (k : ℕ) :
    (2560 : ℝ) / 3 * (2 : ℝ) ^ (9 * k) - 40 / 3 * (2 : ℝ) ^ (2 * k) -
    17 / 21 * ((k + 2 : ℝ) * (2 : ℝ) ^ ((11 : ℝ) / 2 * (k + 1)) +
              1048 * (k + 1 : ℝ) * (2 : ℝ) ^ ((11 : ℝ) / 2 * k)) =
    (2 : ℝ) ^ (2 * k) * ((2560 : ℝ) / 3 * (2 : ℝ) ^ (7 * k) -
      40 / 3 -
      17 / 21 * ((k + 2 : ℝ) * (2 : ℝ) ^ (((7 : ℝ) * k + 11) / 2) +
                1048 * (k + 1 : ℝ) * (2 : ℝ) ^ ((7 : ℝ) * k / 2))) := by
  have hf : ∀ a,
      (2 : ℝ) ^ (a + 2 * (↑k : ℝ)) = (2 : ℝ) ^ a * (2 : ℝ) ^ (2 * k : ℕ) := by
    intro a
    rw [Real.rpow_add (by norm_num : (2 : ℝ) > 0)]
    norm_cast
  rw [show (9 * k : ℕ) = 7 * k + 2 * k from by omega, pow_add]
  have he1 : (11 : ℝ) / 2 * ((↑k : ℝ) + 1) =
    ((7 : ℝ) * ↑k + 11) / 2 + 2 * ↑k := by ring
  have he2 : (11 : ℝ) / 2 * (↑k : ℝ) = (7 : ℝ) * ↑k / 2 + 2 * ↑k := by ring
  simp only [he1, he2, hf]
  ring

private lemma split_exp_7k_11 (k : ℕ) :
    (2 : ℝ) ^ (((7 : ℝ) * k + 11) / 2) =
    (2 : ℝ) ^ ((11 : ℝ) / 2) * (2 : ℝ) ^ ((7 : ℝ) * k / 2) := by
  rw [show ((7 : ℝ) * k + 11 : ℝ) / 2 = (11 : ℝ) / 2 + (7 : ℝ) * k / 2 by ring,
      Real.rpow_add (by norm_num : (2 : ℝ) > 0)]

private lemma rpow_sq (e : ℝ) : ((2 : ℝ) ^ e) ^ 2 = (2 : ℝ) ^ (2 * e) := by
  simp only [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring_nf

private lemma seven_k_as_square (k : ℕ) :
    (2 : ℝ) ^ (7 * k) = ((2 : ℝ) ^ ((7 : ℝ) * k / 2)) ^ 2 := by
  rw [rpow_sq, show 2 * ((7 : ℝ) * ↑k / 2) = (7 : ℝ) * ↑k from by ring]
  norm_cast

theorem coeff_multiplied_bound (k : ℕ) (hk : 1 ≤ k) :
    17 / 21 * ((k + 2 : ℝ) * (2 : ℝ) ^ ((11 : ℝ) / 2) + 1048 * (k + 1 : ℝ)) <
    1812 * k := by
  have hx_lt : (2 : ℝ) ^ ((11 : ℝ) / 2) < 46 := by
    nlinarith [show ((2 : ℝ) ^ ((11 : ℝ) / 2)) ^ 2 = 2048 from by rw [rpow_sq]; norm_num,
               two_rpow_pos ((11 : ℝ) / 2)]
  have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
  nlinarith [mul_pos (show (0 : ℝ) < ↑k + 2 from by positivity)
    (show (0 : ℝ) < 46 - (2 : ℝ) ^ ((11 : ℝ) / 2) from by linarith)]

private lemma rpow_7_div_2_sq : ((2 : ℝ) ^ ((7 : ℝ) / 2)) ^ 2 = 128 := by
  rw [rpow_sq]
  norm_num

private lemma quadratic_base_case :
    (2560 : ℝ) / 3 * ((2 : ℝ) ^ ((7 : ℝ) / 2)) ^ 2 -
    1812 * (2 : ℝ) ^ ((7 : ℝ) / 2) - 40 / 3 > 0 := by
  have h1 : (2 : ℝ) ^ ((7 : ℝ) / 2) = 8 * Real.sqrt 2 := by
    rw [show (7 : ℝ) / 2 = 3 + (1 : ℝ) / 2 by ring,
        Real.rpow_add (by norm_num : (2 : ℝ) > 0)]
    simp only [Real.sqrt_eq_rpow]
    norm_num
  nlinarith [h1, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2 - 1)]

private lemma coeff_positive (k : ℕ) (hk : 1 ≤ k) :
    k * (128 - (2 : ℝ) ^ ((7 : ℝ) / 2)) - (2 : ℝ) ^ ((7 : ℝ) / 2) > 0 := by
  have hk1 : (k : ℝ) ≥ 1 := Nat.one_le_cast.mpr hk
  nlinarith [Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (7 : ℝ) / 2 < 6)]

private lemma exp_split (k : ℕ) :
    (2 : ℝ) ^ ((7 : ℝ) * (k + 1) / 2) =
    (2 : ℝ) ^ ((7 : ℝ) * k / 2) * (2 : ℝ) ^ ((7 : ℝ) / 2) := by
  rw [show ((7 : ℝ) * (k + 1) / 2 : ℝ) = ((7 : ℝ) * k / 2 : ℝ) +
      ((7 : ℝ) / 2 : ℝ) by ring_nf,
      Real.rpow_add (by norm_num : (2 : ℝ) > 0)]

private lemma difference_algebraic (k : ℕ) :
    (2560 : ℝ) / 3 * ((2 : ℝ) ^ ((7 : ℝ) * (k + 1) / 2)) ^ 2 -
    1812 * (k + 1) * (2 : ℝ) ^ ((7 : ℝ) * (k + 1) / 2) - 40 / 3 -
    (128 * ((2560 : ℝ) / 3 * ((2 : ℝ) ^ ((7 : ℝ) * k / 2)) ^ 2 -
          1812 * k * (2 : ℝ) ^ ((7 : ℝ) * k / 2) - 40 / 3)) =
    1812 * (2 : ℝ) ^ ((7 : ℝ) * k / 2) *
      (k * (128 - (2 : ℝ) ^ ((7 : ℝ) / 2)) - (2 : ℝ) ^ ((7 : ℝ) / 2)) + 5080 / 3
    := by
  rw [exp_split]; set t := (2 : ℝ) ^ ((7 : ℝ) * k / 2)
  set a := (2 : ℝ) ^ ((7 : ℝ) / 2)
  rw [show (t * a) ^ 2 = t ^ 2 * 128 by rw [mul_pow, rpow_7_div_2_sq, mul_comm]]
  ring

private lemma difference_positive (k : ℕ) (hk : 1 ≤ k) :
    (2560 : ℝ) / 3 * ((2 : ℝ) ^ ((7 : ℝ) * (k + 1) / 2)) ^ 2 -
    1812 * (k + 1) * (2 : ℝ) ^ ((7 : ℝ) * (k + 1) / 2) - 40 / 3 >
    128 * ((2560 : ℝ) / 3 * ((2 : ℝ) ^ ((7 : ℝ) * k / 2)) ^ 2 -
          1812 * k * (2 : ℝ) ^ ((7 : ℝ) * k / 2) - 40 / 3) := by
  linarith [difference_algebraic k,
            mul_pos (mul_pos (by norm_num : (0 : ℝ) < 1812)
              (two_rpow_pos ((7 : ℝ) * k / 2))) (coeff_positive k hk)]

private lemma quadratic_lower_bound_pos (k : ℕ) (hk : 1 ≤ k) :
    (2560 : ℝ) / 3 * ((2 : ℝ) ^ ((7 : ℝ) * k / 2)) ^ 2 -
    1812 * k * (2 : ℝ) ^ ((7 : ℝ) * k / 2) - 40 / 3 > 0 := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases eq_or_lt_of_le' hk with hn | hn
    · simp only [Nat.succ_injective hn, Nat.zero_add, Nat.cast_one, mul_one]
      exact quadratic_base_case
    · simp only [Nat.cast_add, Nat.cast_one]
      have hn' := Nat.lt_succ_iff.mp hn
      linarith [difference_positive n hn', mul_pos (by norm_num : (128 : ℝ) > 0)
                (ih hn')]

private lemma factor_middle_term (k : ℕ) :
    17 / 21 * ((k + 2 : ℝ) * (2 : ℝ) ^ (((7 : ℝ) * k + 11) / 2) +
              1048 * (k + 1 : ℝ) * (2 : ℝ) ^ ((7 : ℝ) * k / 2)) =
    17 / 21 * ((k + 2 : ℝ) * (2 : ℝ) ^ ((11 : ℝ) / 2) + 1048 * (k + 1 : ℝ)) *
    (2 : ℝ) ^ ((7 : ℝ) * k / 2) := by
  rw [split_exp_7k_11]; ring

private lemma inner_expression_lower_bound (k : ℕ) (hk : 1 ≤ k) :
    (2560 : ℝ) / 3 * (2 : ℝ) ^ (7 * k) -
    40 / 3 -
    17 / 21 * ((k + 2 : ℝ) * (2 : ℝ) ^ (((7 : ℝ) * k + 11) / 2) +
              1048 * (k + 1 : ℝ) * (2 : ℝ) ^ ((7 : ℝ) * k / 2)) >
    (2560 : ℝ) / 3 * ((2 : ℝ) ^ ((7 : ℝ) * k / 2)) ^ 2 -
    1812 * k * (2 : ℝ) ^ ((7 : ℝ) * k / 2) - 40 / 3 := by
  rw [seven_k_as_square k, factor_middle_term k]
  nlinarith [two_rpow_pos ((7 : ℝ) * k / 2), coeff_multiplied_bound k hk]

/- Inequality (61) -/
theorem main_inequality (k : ℕ) (hk : 1 ≤ k) :
    (2560 : ℝ) / 3 * (2 : ℝ) ^ (9 * k) - 40 / 3 * (2 : ℝ) ^ (2 * k) -
    17 / 21 * ((k + 2 : ℝ) * (2 : ℝ) ^ ((11 : ℝ) / 2 * (k + 1)) +
              1048 * (k + 1 : ℝ) * (2 : ℝ) ^ ((11 : ℝ) / 2 * k)) > 0 := by
  rw [factor_two_pow_2k]
  exact mul_pos (by positivity) (lt_of_lt_of_le (quadratic_lower_bound_pos k hk)
    (le_of_lt (inner_expression_lower_bound k hk)))
