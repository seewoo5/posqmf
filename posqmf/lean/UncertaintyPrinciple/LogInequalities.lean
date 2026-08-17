import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Elementary logarithm inequalities behind the base cases of the positivity of `Y_w`

The positivity proof of `Y_w` in *Positive quasimodular forms and the sign uncertainty principle*
runs by induction from the base cases `Y_8` and `Y_10`, after first disposing of `Y_2` and `Y_4`.
Under the substitution `x = H₂(it)/H₄(it) > 0`, which turns `-𝓛_S(it)` into `log(1+x)`, the three
nontrivial base cases become the elementary inequalities proved here.  This is the one place where
the argument leaves modular forms for real-variable calculus.

## Main results

* `UncertaintyPrinciple.logIneq_basic`: `log(1+x) > 2x/(x+2)` for `x > 0`.
* `UncertaintyPrinciple.logIneq_Y₄`: `log(1+x) > x(x+2)/(2(x²+x+1))` for `x > 0`, the `Y_4` case.
* `UncertaintyPrinciple.logIneq_Y₈`:
  `(x²+x+1)² log(1+x) > (11x⁴+28x³+18x²+12x)/12` for `x > 0`.
* `UncertaintyPrinciple.logIneq_Y₁₀`:
  `-(x²+x+1)(2x+1)(x+2)(1-x) log(1+x) > (2x⁵+11x⁴-x³-24x²-12x)/6` for `x ≥ 1`.

`logIneq_Y₄` and `logIneq_Y₁₀` are corollaries of `logIneq_basic`.  `logIneq_Y₈` is not: the two
sides agree to second order at `0`, and in fact `2x/(x+2)` already falls below
`(11x⁴+28x³+18x²+12x)/(12(x²+x+1)²)` at `x = 1/10`.  It therefore gets its own monotonicity
argument, with the derivative identity displayed in the paper.

The restriction to `x ≥ 1` in `logIneq_Y₁₀` is the paper's: `x ≥ 1` corresponds to `0 < t ≤ 1`,
and the range `t > 1` is covered by the hypergeometric expression for `Y_w` instead.
-/

open Real Set

namespace UncertaintyPrinciple

/-- If `f` vanishes at `0` and has positive derivative on `(0, ∞)`, then `f` is positive on
`(0, ∞)`.  Both `logIneq_basic` and `logIneq_Y₈` are instances of this. -/
private lemma pos_of_hasDerivAt_pos {f g : ℝ → ℝ} (h0 : f 0 = 0)
    (hd : ∀ y : ℝ, 0 ≤ y → HasDerivAt f (g y) y) (hg : ∀ y : ℝ, 0 < y → 0 < g y)
    {x : ℝ} (hx : 0 < x) : 0 < f x := by
  have hmono : StrictMonoOn f (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0)
      (fun y hy ↦ (hd y hy).continuousAt.continuousWithinAt) fun y hy ↦ ?_
    rw [interior_Ici] at hy
    exact (hd y hy.le).deriv ▸ hg y hy
  simpa [h0] using hmono self_mem_Ici (mem_Ici.2 hx.le) hx

-- logIneq

private lemma quadratic_pos (x : ℝ) : 0 < x ^ 2 + x + 1 := by
  nlinarith [sq_nonneg (2 * x + 1)]

private lemma hasDerivAt_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun t : ℝ ↦ log (1 + t)) (1 / (1 + x)) x := by
  simpa using ((hasDerivAt_id x).const_add (1 : ℝ)).log (by linarith : 0 < 1 + x).ne'

/-! ### The basic inequality -/

private lemma hasDerivAt_logIneq_basic (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun t : ℝ ↦ log (1 + t) - 2 * t / (t + 2))
      (x ^ 2 / ((x + 1) * (x + 2) ^ 2)) x := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h2 : (0 : ℝ) < x + 2 := by linarith
  have hdiv : HasDerivAt (fun t : ℝ ↦ 2 * t / (t + 2)) (4 / (x + 2) ^ 2) x :=
    (((hasDerivAt_id x).const_mul (2 : ℝ)).div ((hasDerivAt_id x).add_const (2 : ℝ))
      h2.ne').congr_deriv (by norm_num; ring)
  refine ((hasDerivAt_log_one_add hx).sub hdiv).congr_deriv ?_
  field_simp
  ring

/-- **The basic inequality**: `log(1+x) > 2x/(x+2)` for every `x > 0`. -/
theorem logIneq_basic {x : ℝ} (hx : 0 < x) : 2 * x / (x + 2) < log (1 + x) := by
  linarith [pos_of_hasDerivAt_pos (f := fun t : ℝ ↦ log (1 + t) - 2 * t / (t + 2))
    (g := fun t : ℝ ↦ t ^ 2 / ((t + 1) * (t + 2) ^ 2)) (by simp) hasDerivAt_logIneq_basic
    (fun y hy ↦ div_pos (pow_pos hy 2) (mul_pos (by linarith) (pow_pos (by linarith) 2))) hx]

/-- **The `Y_4` base case**: `log(1+x) > x(x+2)/(2(x²+x+1))` for every `x > 0`.
The gap against `logIneq_basic` is exactly `3x³/(2(x+2)(x²+x+1))`. -/
theorem logIneq_Y₄ {x : ℝ} (hx : 0 < x) :
    x * (x + 2) / (2 * (x ^ 2 + x + 1)) < log (1 + x) :=
  calc x * (x + 2) / (2 * (x ^ 2 + x + 1))
      = 2 * x / (x + 2) - 3 * x ^ 3 / (2 * (x + 2) * (x ^ 2 + x + 1)) := by
        field_simp [(by linarith : 0 < x + 2).ne', (quadratic_pos x).ne']
        ring
    _ < 2 * x / (x + 2) := sub_lt_self _ (by positivity)
    _ < log (1 + x) := logIneq_basic hx

-- Y₁₀

private lemma hasDerivAt_logIneqY8 (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun t : ℝ ↦ log (1 + t)
        - (11 * t ^ 4 + 28 * t ^ 3 + 18 * t ^ 2 + 12 * t) / (12 * (t ^ 2 + t + 1) ^ 2))
      (x ^ 4 * (2 * x ^ 2 + 7 * x + 7) / (2 * (x + 1) * (x ^ 2 + x + 1) ^ 3)) x := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have hnum : HasDerivAt (fun t : ℝ ↦ 11 * t ^ 4 + 28 * t ^ 3 + 18 * t ^ 2 + 12 * t)
      (44 * x ^ 3 + 84 * x ^ 2 + 36 * x + 12) x :=
    ((((hasDerivAt_pow 4 x).const_mul (11 : ℝ)).add ((hasDerivAt_pow 3 x).const_mul (28 : ℝ))).add
      ((hasDerivAt_pow 2 x).const_mul (18 : ℝ))).add
        ((hasDerivAt_id x).const_mul (12 : ℝ)) |>.congr_deriv (by norm_num; ring)
  have hd : HasDerivAt (fun t : ℝ ↦ 12 * (t ^ 2 + t + 1) ^ 2)
      (24 * (x ^ 2 + x + 1) * (2 * x + 1)) x :=
    ((((hasDerivAt_pow 2 x).add (hasDerivAt_id x)).add_const (1 : ℝ)).pow 2).const_mul
      (12 : ℝ) |>.congr_deriv (by norm_num; ring)
  refine ((hasDerivAt_log_one_add hx).sub
    (hnum.div hd (by positivity : (12 : ℝ) * (x ^ 2 + x + 1) ^ 2 ≠ 0))).congr_deriv ?_
  field_simp
  ring

/-- **The `Y_8` base case**:
`(x²+x+1)² log(1+x) > (11x⁴+28x³+18x²+12x)/12` for every `x > 0`. -/
theorem logIneq_Y₈ {x : ℝ} (hx : 0 < x) :
    (11 * x ^ 4 + 28 * x ^ 3 + 18 * x ^ 2 + 12 * x) / 12
      < (x ^ 2 + x + 1) ^ 2 * log (1 + x) := by
  have key : (11 * x ^ 4 + 28 * x ^ 3 + 18 * x ^ 2 + 12 * x) / (12 * (x ^ 2 + x + 1) ^ 2)
      < log (1 + x) := sub_pos.mp <| pos_of_hasDerivAt_pos
    (f := fun t : ℝ ↦ log (1 + t)
      - (11 * t ^ 4 + 28 * t ^ 3 + 18 * t ^ 2 + 12 * t) / (12 * (t ^ 2 + t + 1) ^ 2))
    (g := fun t : ℝ ↦ t ^ 4 * (2 * t ^ 2 + 7 * t + 7) / (2 * (t + 1) * (t ^ 2 + t + 1) ^ 3))
    (by norm_num) hasDerivAt_logIneqY8
    (fun y hy ↦ div_pos (mul_pos (pow_pos hy 4) (by nlinarith))
      (mul_pos (mul_pos (by norm_num) (by linarith)) (pow_pos (quadratic_pos y) 3))) hx
  calc (11 * x ^ 4 + 28 * x ^ 3 + 18 * x ^ 2 + 12 * x) / 12
      = (x ^ 2 + x + 1) ^ 2
          * ((11 * x ^ 4 + 28 * x ^ 3 + 18 * x ^ 2 + 12 * x) / (12 * (x ^ 2 + x + 1) ^ 2)) := by
        field_simp [(quadratic_pos x).ne']
    _ < (x ^ 2 + x + 1) ^ 2 * log (1 + x) :=
        mul_lt_mul_of_pos_left key (pow_pos (quadratic_pos x) 2)

/-- **The `Y_10` base case**:
`-(x²+x+1)(2x+1)(x+2)(1-x) log(1+x) > (2x⁵+11x⁴-x³-24x²-12x)/6` for every `x ≥ 1`.
For `x ≥ 1` the coefficient of `log(1+x)` is nonnegative, so `logIneq_basic` may be substituted;
the factor `x+2` then cancels exactly and leaves `x³(22x²+x+1)/6 > 0`. -/
theorem logIneq_Y₁₀ {x : ℝ} (hx : 1 ≤ x) :
    (2 * x ^ 5 + 11 * x ^ 4 - x ^ 3 - 24 * x ^ 2 - 12 * x) / 6
      < -((x ^ 2 + x + 1) * (2 * x + 1) * (x + 2) * (1 - x)) * log (1 + x) := by
  have hx0 : 0 < x := by linarith
  have hc : 0 ≤ -((x ^ 2 + x + 1) * (2 * x + 1) * (x + 2) * (1 - x)) := by
    rw [show -((x ^ 2 + x + 1) * (2 * x + 1) * (x + 2) * (1 - x))
      = (x ^ 2 + x + 1) * (2 * x + 1) * (x + 2) * (x - 1) by ring]
    exact mul_nonneg (mul_nonneg (mul_nonneg (quadratic_pos x).le (by linarith)) (by linarith))
      (by linarith)
  calc (2 * x ^ 5 + 11 * x ^ 4 - x ^ 3 - 24 * x ^ 2 - 12 * x) / 6
      = -((x ^ 2 + x + 1) * (2 * x + 1) * (x + 2) * (1 - x)) * (2 * x / (x + 2))
          - x ^ 3 * (22 * x ^ 2 + x + 1) / 6 := by
        field_simp [(by linarith : 0 < x + 2).ne']
        ring
    _ < -((x ^ 2 + x + 1) * (2 * x + 1) * (x + 2) * (1 - x)) * (2 * x / (x + 2)) :=
        sub_lt_self _ (by positivity)
    _ ≤ -((x ^ 2 + x + 1) * (2 * x + 1) * (x + 2) * (1 - x)) * log (1 + x) :=
        mul_le_mul_of_nonneg_left (logIneq_basic hx0).le hc

end UncertaintyPrinciple
