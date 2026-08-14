import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# `q`-expansions and the operator `D = q d/dq`

Mathlib carries a normalised derivative and a Serre derivative for modular forms, but as genuine
differential operators acting on functions on the complex upper half plane.  None of that analytic
content is needed for the algebraic side of the Kaneko--Zagier theory: every identity there is an
identity of formal `q`-expansions.  This file sets up that formal picture, with `ℝ⟦X⟧` playing the
role of the ring of `q`-expansions (so the formal variable `X` is `q`).

## Main definitions

* `KanekoZagier.D`: the operator `q d/dq`, that is `∑ₙ aₙ qⁿ ↦ ∑ₙ n aₙ qⁿ`.

## Main results

* `KanekoZagier.D_mul`: `D` satisfies the Leibniz rule.
* `KanekoZagier.coeff_mk_mul`: for a series `f` with vanishing constant term,
  `[qⁿ](f * G) = ∑_{j < n} ([qⁿ⁻ʲ]f) · ([qʲ]G)`.  This is the shape in which every coefficient
  computation in this directory is carried out.
-/

open Finset PowerSeries

namespace KanekoZagier

noncomputable section

/-- The operator `D = q d/dq` on formal `q`-expansions: `D (∑ₙ aₙ qⁿ) = ∑ₙ n aₙ qⁿ`.

For a quasimodular form `F` this is the normalised derivative `F' = (2πi)⁻¹ dF/dz`. -/
def D (f : ℝ⟦X⟧) : ℝ⟦X⟧ := mk fun n ↦ (n : ℝ) * coeff n f

@[simp]
lemma coeff_D (n : ℕ) (f : ℝ⟦X⟧) : coeff n (D f) = (n : ℝ) * coeff n f := coeff_mk _ _

lemma D_mk (c : ℕ → ℝ) : D (mk c) = mk fun n ↦ (n : ℝ) * c n := by ext n; simp

@[simp]
lemma D_one : D 1 = 0 := by ext n; simp

lemma D_add (f g : ℝ⟦X⟧) : D (f + g) = D f + D g := by ext n; simp [mul_add]

lemma D_sub (f g : ℝ⟦X⟧) : D (f - g) = D f - D g := by ext n; simp [mul_sub]

lemma D_smul (c : ℝ) (f : ℝ⟦X⟧) : D (c • f) = c • D f := by ext n; simp [mul_left_comm]

/-- The Leibniz rule for `D = q d/dq`. -/
lemma D_mul (f g : ℝ⟦X⟧) : D (f * g) = D f * g + f * D g := by
  ext n
  simp only [coeff_D, PowerSeries.coeff_mul, map_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.mem_antidiagonal] at hp
  push_cast [← hp]
  ring

/-- Coefficients of a product with a series of the shape `∑_{n ≥ 1} c n qⁿ`.  Since the constant
term of `mk c` vanishes, the `j = n` term of the convolution drops out and the sum runs over
`j < n` only, which is exactly the shape of the two coefficient formulas in `Coefficients.lean`. -/
lemma coeff_mk_mul (c : ℕ → ℝ) (h0 : c 0 = 0) (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (mk c * G) = ∑ j ∈ range n, c (n - j) * coeff j G := by
  rw [PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one, Finset.sum_range_succ]
  simp [h0]

end

end KanekoZagier
