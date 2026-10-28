import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Comparator challenge: the coefficients of `𝒟_{6,3}`

The extremal quasimodular form of weight `6`, depth `3` and level `Γ₀(2)` is
`𝒟_{6,3} = ∑_{n ≥ 5} a_n qⁿ` with `a_n = (A_n + B_{n/2})/2688`, where `A` and `B` are defined below
and `B_{n/2} = 0` for odd `n` (*On extremal quasimodular forms of low levels*, Proposition on
`𝒟_{6,3}`). `D_6_3.lean` proves `a_n > 0` for every `n ≥ 5` (`D63.aSeq_pos`), so `𝒟_{6,3}` is
completely positive.

Only Mathlib is imported. The definitions are copied verbatim from `D_6_3.lean`, and Comparator
checks that the solution uses identical ones.
-/

noncomputable section

open ArithmeticFunction Finset
open scoped sigma

namespace D63

/-- `A_n = 10 n² σ₁(n) - 13 n σ₃(n) + 3 σ₅(n)`. -/
def A (n : ℕ) : ℝ :=
  10 * (n : ℝ) ^ 2 * (σ 1 n : ℝ) - 13 * (n : ℝ) * (σ 3 n : ℝ) + 3 * (σ 5 n : ℝ)

/-- `B_n = 120 n² σ₁(n) - 102 n σ₃(n) - 3 σ₅(n)`. -/
def B (n : ℕ) : ℝ :=
  120 * (n : ℝ) ^ 2 * (σ 1 n : ℝ) - 102 * (n : ℝ) * (σ 3 n : ℝ) - 3 * (σ 5 n : ℝ)

/-- `a_n = (A_n + B_{n/2}) / 2688`, with `B_{n/2} = 0` if `n` is odd. -/
def aSeq (n : ℕ) : ℝ :=
  (A n + (if Even n then B (n / 2) else 0)) / 2688

/-- Positivity of `a_n = (A_n + B_{n/2}) / 2688` for `n ≥ 5`. -/
theorem aSeq_pos (n : ℕ) (hn : 5 ≤ n) : 0 < aSeq n := sorry

end D63

end
