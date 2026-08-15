import Mathlib.Tactic.Module
import posqmf.lean.DifferentialOperators.Eisenstein

/-!
# Ramanujan's identities

The three identities

`E₂' = (E₂² - E₄)/12`,  `E₄' = (E₂E₄ - E₆)/3`,  `E₆' = (E₂E₆ - E₄²)/2`

are classical.  Proving them from the `q`-expansions of `E₂`, `E₄`, `E₆` amounts to a nontrivial
convolution identity for divisor sums, which is orthogonal to the operator bookkeeping this
development is about, so **they are taken as axioms here**.  They are true statements about the
concrete series defined in `Eisenstein.lean`, so no inconsistency is introduced; replacing the
three `axiom`s by theorems is the only thing needed to make everything downstream unconditional.

Every result that depends on them can be recognised by `#print axioms`, which will list
`KanekoZagier.ramanujan_E₂`, `KanekoZagier.ramanujan_E₄` or `KanekoZagier.ramanujan_E₆`.
Notably the coefficient formulas of `Coefficients.lean` do *not* depend on them.

## Main results

* `KanekoZagier.E₂_mul_E₂`, `E₂_mul_E₄`, `E₂_mul_D_E₂`: the reduction rules in which Ramanujan's
  identities are actually used, namely rewriting the products of `E₂` with `E₂`, `E₄` and `E₂'`
  that appear when an iterated Serre derivative is expanded in terms of `D`.  The `E₂E₆` reduction
  is not needed: `E₆` only ever enters through `∂₆E₆`, handled in Serre form by `serreD_E₆`.
-/

open PowerSeries

namespace KanekoZagier

/-- **Ramanujan's identity** `E₂' = (E₂² - E₄)/12`, taken as an axiom. -/
axiom ramanujan_E₂ : D E₂ = (1 / 12 : ℝ) • (E₂ * E₂ - E₄)

/-- **Ramanujan's identity** `E₄' = (E₂E₄ - E₆)/3`, taken as an axiom. -/
axiom ramanujan_E₄ : D E₄ = (1 / 3 : ℝ) • (E₂ * E₄ - E₆)

/-- **Ramanujan's identity** `E₆' = (E₂E₆ - E₄²)/2`, taken as an axiom. -/
axiom ramanujan_E₆ : D E₆ = (1 / 2 : ℝ) • (E₂ * E₆ - E₄ * E₄)

/-- `E₂² = 12E₂' + E₄`, the form of Ramanujan's identity used to eliminate `E₂²`. -/
lemma E₂_mul_E₂ : E₂ * E₂ = (12 : ℝ) • D E₂ + E₄ := by
  rw [ramanujan_E₂, smul_smul]
  norm_num

/-- `E₂E₄ = 3E₄' + E₆`, the form of Ramanujan's identity used to eliminate `E₂E₄`. -/
lemma E₂_mul_E₄ : E₂ * E₄ = (3 : ℝ) • D E₄ + E₆ := by
  rw [ramanujan_E₄, smul_smul]
  norm_num

/-- `E₂E₂' = 6E₂'' + E₄'/2`, obtained by differentiating `E₂_mul_E₂`.  This is what removes the
`E₂E₂'` term produced by expanding a threefold Serre derivative. -/
lemma E₂_mul_D_E₂ : E₂ * D E₂ = (6 : ℝ) • D (D E₂) + (1 / 2 : ℝ) • D E₄ := by
  have h := congrArg D E₂_mul_E₂
  rw [D_mul, D_add, D_smul, mul_comm (D E₂) E₂] at h
  refine smul_right_injective _ (two_ne_zero (α := ℝ)) ?_
  simp only [two_smul, h]
  module

end KanekoZagier
