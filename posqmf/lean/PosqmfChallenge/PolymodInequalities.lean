import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Comparator challenge: inequalities of *Inequalities involving polynomials and quasimodular forms*

Statements of the three inequalities of *Inequalities involving polynomials and quasimodular forms*
(arXiv:2602.10536) that `PolymodInequalities/` formalizes:

* inequality (41), from the proof of Lemma 3.5 (the monotonicity of `t ↦ t⁸X_{10,1}(it)`):
  `f(t) = ∑_{k=0}^{8} (a_k t + b_k) e^{kt} > 0` for `t > 0` (`f_pos`);
* inequality (60), from the proof of Proposition A.1 (the complete positivity of
  `Y_{12,2}(z) = X_{12,2}(z) - 2¹⁰X_{12,2}(2z)`):
  `2520/3 m⁹ - 18224/21 d(m) m^{11/2} + 12/7 m¹⁰ > 0` for `m ≥ 3` (`main_theorem`);
* inequality (61), from the same proof:
  `2560/3 · 2^{9k} - 40/3 · 2^{2k} - 17/21 ((k + 2) 2^{11(k+1)/2} + 1048 (k + 1) 2^{11k/2}) > 0`
  for `k ≥ 1` (`main_inequality`).

Only Mathlib is imported. The definitions are copied verbatim from `PolymodInequalities/`, and
Comparator checks that the solution uses identical ones.
-/

section Monotone

/-- The coefficients `a_k` of `P(x) = ∑ a_k x^k`. -/
def aCoeffs : Fin 9 → ℤ
  | 0 => 1
  | 1 => 502
  | 2 => 14608
  | 3 => 88234
  | 4 => 156190
  | 5 => 88234
  | 6 => 14608
  | 7 => 502
  | 8 => 1

/-- The coefficients `b_k = -[x^k]Q(x)`. -/
def bCoeffs : Fin 9 → ℤ
  | 0 => 8
  | 1 => 1968
  | 2 => 32368
  | 3 => 90608
  | 4 => 0
  | 5 => -90608
  | 6 => -32368
  | 7 => -1968
  | 8 => -8

/-- `f(t) = tP(e^t) - Q(e^t) = ∑_{k=0}^{8} (a_k t + b_k) e^{kt}`. -/
noncomputable def f (t : ℝ) : ℝ :=
  ∑ k : Fin 9, (aCoeffs k : ℝ) * t * Real.exp (k * t) +
  ∑ k : Fin 9, (bCoeffs k : ℝ) * Real.exp (k * t)

/-- **Inequality (41)**: `f(t) > 0` for every `t > 0`. -/
theorem f_pos (t : ℝ) (ht : 0 < t) : 0 < f t := sorry

end Monotone

section Ineq1

/-- The number of divisors `d(n) = σ₀(n)`. -/
abbrev divisorCount (n : ℕ) : ℕ := (ArithmeticFunction.sigma 0) n

/-- **Inequality (60)**: `2520/3 m⁹ - 18224/21 d(m) m^{11/2} + 12/7 m¹⁰ > 0` for `m ≥ 3`. -/
theorem main_theorem (m : ℕ) (hm_ge : 3 ≤ m) :
    (2520 : ℝ) / 3 * m ^ 9 -
    18224 / 21 * (divisorCount m : ℝ) * m ^ (11 / 2 : ℝ) +
    12 / 7 * m ^ 10 > 0 := sorry

end Ineq1

section Ineq2

/-- **Inequality (61)**:
`2560/3 · 2^{9k} - 40/3 · 2^{2k} - 17/21 ((k + 2) 2^{11(k+1)/2} + 1048 (k + 1) 2^{11k/2}) > 0`
for `k ≥ 1`. -/
theorem main_inequality (k : ℕ) (hk : 1 ≤ k) :
    (2560 : ℝ) / 3 * (2 : ℝ) ^ (9 * k) - 40 / 3 * (2 : ℝ) ^ (2 * k) -
    17 / 21 * ((k + 2 : ℝ) * (2 : ℝ) ^ ((11 : ℝ) / 2 * (k + 1)) +
              1048 * (k + 1 : ℝ) * (2 : ℝ) ^ ((11 : ℝ) / 2 * k)) > 0 := sorry

end Ineq2
