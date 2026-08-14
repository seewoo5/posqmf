import Mathlib.NumberTheory.ArithmeticFunction.Misc
import posqmf.lean.KanekoZagier.Basic

/-!
# The Eisenstein series `E₂`, `E₄`, `E₆` as formal `q`-expansions

Following `eqn:e2fourier`--`eqn:e6fourier` of the paper we set

* `E₂ = 1 - 24 ∑_{n ≥ 1} σ₁(n) qⁿ`,
* `E₄ = 1 + 240 ∑_{n ≥ 1} σ₃(n) qⁿ`,
* `E₆ = 1 - 504 ∑_{n ≥ 1} σ₅(n) qⁿ`,

as elements of `ℝ⟦X⟧`.  Since Mathlib's `ArithmeticFunction.sigma` sends `0` to `0`, the tail
`qSigma k = ∑_{n ≥ 1} σ_k(n) qⁿ` is simply `mk fun n ↦ σ_k(n)`, and it has vanishing constant term.

## Main results

The `coeff_*_mul` lemmas record `[qⁿ](E * G)` for `E` each of `E₂`, `E₄`, `E₆`, `DE₂`, `D²E₂`,
`DE₄` in the shape used by `lem:KZ2_coeff` and `lem:KZ3_coeff`: a diagonal contribution plus a
strictly lower triangular convolution against `σ₁`, `σ₃` or `σ₅`.
-/

open ArithmeticFunction Finset PowerSeries
open scoped sigma

namespace KanekoZagier

noncomputable section

/-- The cuspidal series `∑_{n ≥ 1} σ_k(n) qⁿ`. -/
def qSigma (k : ℕ) : ℝ⟦X⟧ := mk fun n ↦ (σ k n : ℝ)

/-- The quasimodular Eisenstein series `E₂ = 1 - 24 ∑_{n ≥ 1} σ₁(n) qⁿ` (`eqn:e2fourier`). -/
def E2 : ℝ⟦X⟧ := 1 - (24 : ℝ) • qSigma 1

/-- The Eisenstein series `E₄ = 1 + 240 ∑_{n ≥ 1} σ₃(n) qⁿ` (`eqn:e4fourier`). -/
def E4 : ℝ⟦X⟧ := 1 + (240 : ℝ) • qSigma 3

/-- The Eisenstein series `E₆ = 1 - 504 ∑_{n ≥ 1} σ₅(n) qⁿ` (`eqn:e6fourier`). -/
def E6 : ℝ⟦X⟧ := 1 - (504 : ℝ) • qSigma 5

@[simp]
lemma coeff_qSigma (k n : ℕ) : coeff n (qSigma k) = (σ k n : ℝ) := coeff_mk _ _

/-! ### Sanity checks on the `q`-expansions -/

example : coeff 1 E2 = -24 := by norm_num [E2, show σ 1 1 = 1 by decide]
example : coeff 2 E2 = -72 := by norm_num [E2, show σ 1 2 = 3 by decide]
example : coeff 1 E4 = 240 := by norm_num [E4, show σ 3 1 = 1 by decide]
example : coeff 2 E4 = 2160 := by norm_num [E4, show σ 3 2 = 9 by decide]
example : coeff 1 E6 = -504 := by norm_num [E6, show σ 5 1 = 1 by decide]
example : coeff 2 E6 = -16632 := by norm_num [E6, show σ 5 2 = 33 by decide]

/-! ### `D` applied to the Eisenstein series

Only the finitely many derivatives occurring in `eqn:KZ2_def` and `eqn:KZ3_def` are needed,
namely `E₂'`, `E₂''` and `E₄'`. -/

lemma D_E2 : D E2 = (-24 : ℝ) • mk fun m ↦ (m : ℝ) * (σ 1 m : ℝ) := by
  rw [E2, D_sub, D_one, D_smul, zero_sub, ← neg_smul, qSigma, D_mk]

lemma D_D_E2 : D (D E2) = (-24 : ℝ) • mk fun m ↦ (m : ℝ) ^ 2 * (σ 1 m : ℝ) := by
  rw [D_E2, D_smul, D_mk]
  ext m
  simp only [PowerSeries.coeff_smul, coeff_mk, smul_eq_mul]
  ring

lemma D_E4 : D E4 = (240 : ℝ) • mk fun m ↦ (m : ℝ) * (σ 3 m : ℝ) := by
  rw [E4, D_add, D_one, D_smul, zero_add, qSigma, D_mk]

/-! ### Coefficients of products with the Eisenstein series -/

/-- The basic convolution identity, specialised to the tails `qSigma k`. -/
lemma coeff_qSigma_mul (k : ℕ) (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (qSigma k * G) = ∑ j ∈ range n, (σ k (n - j) : ℝ) * coeff j G :=
  coeff_mk_mul _ (by simp) G n

lemma coeff_E2_mul (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (E2 * G) = coeff n G - 24 * ∑ j ∈ range n, (σ 1 (n - j) : ℝ) * coeff j G := by
  rw [E2, sub_mul, one_mul, smul_mul_assoc, map_sub, PowerSeries.coeff_smul, smul_eq_mul,
    coeff_qSigma_mul]

lemma coeff_E4_mul (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (E4 * G) = coeff n G + 240 * ∑ j ∈ range n, (σ 3 (n - j) : ℝ) * coeff j G := by
  rw [E4, add_mul, one_mul, smul_mul_assoc, map_add, PowerSeries.coeff_smul, smul_eq_mul,
    coeff_qSigma_mul]

lemma coeff_E6_mul (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (E6 * G) = coeff n G - 504 * ∑ j ∈ range n, (σ 5 (n - j) : ℝ) * coeff j G := by
  rw [E6, sub_mul, one_mul, smul_mul_assoc, map_sub, PowerSeries.coeff_smul, smul_eq_mul,
    coeff_qSigma_mul]

lemma coeff_D_E2_mul (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (D E2 * G) = -24 * ∑ j ∈ range n,
      ((n - j : ℕ) : ℝ) * (σ 1 (n - j) : ℝ) * coeff j G := by
  rw [D_E2, smul_mul_assoc, PowerSeries.coeff_smul, smul_eq_mul, coeff_mk_mul _ (by simp) G n]

lemma coeff_D_D_E2_mul (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (D (D E2) * G) = -24 * ∑ j ∈ range n,
      ((n - j : ℕ) : ℝ) ^ 2 * (σ 1 (n - j) : ℝ) * coeff j G := by
  rw [D_D_E2, smul_mul_assoc, PowerSeries.coeff_smul, smul_eq_mul, coeff_mk_mul _ (by simp) G n]

lemma coeff_D_E4_mul (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (D E4 * G) = 240 * ∑ j ∈ range n,
      ((n - j : ℕ) : ℝ) * (σ 3 (n - j) : ℝ) * coeff j G := by
  rw [D_E4, smul_mul_assoc, PowerSeries.coeff_smul, smul_eq_mul, coeff_mk_mul _ (by simp) G n]

end

end KanekoZagier
