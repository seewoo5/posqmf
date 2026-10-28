import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Comparator challenge: the coefficients of `X_{16,5}`

The extremal quasimodular form of weight `16` and depth `5`, normalized to start with `q⁷`, is
`X_{16,5} = ∑_{n ≥ 7} a_n qⁿ` with `a_n = x_n + 240 c₆ y_n + c₇ z_n + c₆ τ(n)` and the sequences
defined below. That `a_n < 0` for every `n ≥ 8`, so that every coefficient of `X_{16,5}` but the
leading one is negative, is a claim of the author's PhD thesis; `X_16_5.lean` proves it for
`n ≥ 250` (`aSeq_neg_of_large`), and `notebooks/miscellaneous.ipynb` checks `8 ≤ n < 250`.

Only Mathlib is imported. The definitions are copied verbatim from `X_16_5.lean`, and Comparator
checks that the solution uses identical ones. Ramanujan's `τ` enters only through Deligne's bound,
which the development takes as an axiom about an opaque function `τ`; both are restated below, and
`comparator/X_16_5.json` permits the axiom, after checking that the solution's axiom of this name
states exactly what is written here.
-/

noncomputable section

open ArithmeticFunction Finset
open scoped sigma

/-- The constant `c₆` from the linear combination expressing `X_{16,5}`. -/
def c₆ : ℝ := 86619413 / 139015844352000

/-- The constant `c₇` from the linear combination expressing `X_{16,5}`. -/
def c₇ : ℝ := -118801 / 10746432000

/--
Ramanujan's `τ` function. We treat it abstractly: only Deligne's bound
(stated below as an axiom) is used in this file. -/
opaque τ : ℕ → ℤ

/--
**Deligne's bound** for the Ramanujan tau function:
`|τ(n)| ≤ σ₀(n) n^(11/2)` for `n ≥ 1`.

This is taken as an axiom; a proof would require the full force of the
Weil conjectures (Deligne, 1974). -/
axiom abs_tau_lt (n : ℕ) (hn : 1 ≤ n) :
    |(τ n : ℝ)| ≤ (σ 0 n : ℝ) * (n : ℝ) ^ ((11 : ℝ) / 2)

/-- The polynomial-in-`σ` part of `a_n`. -/
def xSeq (n : ℕ) : ℝ :=
  - (n : ℝ) * (σ 13 n : ℝ) / 201801600
  + 4531 * (n : ℝ) ^ 2 * (σ 11 n : ℝ) / 47809681920
  - 149 * (n : ℝ) ^ 3 * (σ 9 n : ℝ) / 228096000
  + 49 * (n : ℝ) ^ 4 * (σ 7 n : ℝ) / 25660800
  - 49 * (n : ℝ) ^ 5 * (σ 5 n : ℝ) / 24883200

/-- `y_n = ∑_{k=1}^{n-1} τ(k) σ₃(n - k)`. -/
def ySeq (n : ℕ) : ℝ :=
  ∑ k ∈ Ico 1 n, (τ k : ℝ) * (σ 3 (n - k) : ℝ)

/-- `z_n = ∑_{k=1}^{n-1} τ(k) (n - k) σ₁(n - k)`. -/
def zSeq (n : ℕ) : ℝ :=
  ∑ k ∈ Ico 1 n, (τ k : ℝ) * ((n : ℝ) - k) * (σ 1 (n - k) : ℝ)

/-- The full sequence `a_n = x_n + 240 c₆ y_n + c₇ z_n + c₆ τ(n)`. -/
def aSeq (n : ℕ) : ℝ :=
  xSeq n + 240 * c₆ * ySeq n + c₇ * zSeq n + c₆ * (τ n : ℝ)

/-- `a_n < 0` for every `n ≥ 250`. -/
theorem aSeq_neg_of_large (n : ℕ) (hn : 250 ≤ n) : aSeq n < 0 := sorry

end
