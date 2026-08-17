import posqmf.lean.QuasiModularForms.KanekoZagier

/-!
# Fourier coefficients of the Kaneko--Zagier operators

This file proves the Fourier coefficient formulas for the two Kaneko--Zagier operators (items 1.2
and 1.3 of the verification plan): for `G = ∑_{n ≥ 0} aₙ qⁿ`,

`[qⁿ](L_{2,k}^α G) = κ_{2,k}^α(n) aₙ + ∑_{j<n} K_{2,k}^α(n,j) a_j`,
`[qⁿ](L_{3,k}^{(α,β)} G) = κ_{3,k}^{(α,β)}(n) aₙ + ∑_{j<n} K_{3,k}^{(α,β)}(n,j) a_j`,

with the `κ`'s and `K`'s defined below.  These are the formulas that drive every coefficient
induction of §§3--4 of the paper.

Both proofs use only the `D`-forms `L₂` and `L₃` and the `q`-expansions of `E₂`, `E₄`, `E₆`; in
particular they are independent of the Ramanujan axioms of `Ramanujan.lean`.
-/

open ArithmeticFunction Finset PowerSeries QExpansion
open scoped sigma

namespace KanekoZagier

noncomputable section

/-- `κ_{2,k}^α(n) = n² - ((k+1)/6)n + α`, the diagonal coefficient of
`L_{2,k}^α`. -/
def κ₂ (k α : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ 2 - (k + 1) / 6 * n + α

/-- `K_{2,k}^α(n,j) = 2(k+1)(2j - k(n-j))σ₁(n-j) + 240ασ₃(n-j)`, the strictly lower
triangular part of `L_{2,k}^α`. -/
def K₂ (k α : ℝ) (n j : ℕ) : ℝ :=
  2 * (k + 1) * (2 * (j : ℝ) - k * ((n : ℝ) - (j : ℝ))) * (σ 1 (n - j) : ℝ)
    + 240 * α * (σ 3 (n - j) : ℝ)

/-- `κ_{3,k}^{(α,β)}(n) = n³ - ((k+2)/4)n² + αn + β`. -/
def κ₃ (k α β : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ 3 - (k + 2) / 4 * (n : ℝ) ^ 2 + α * n + β

/-- The strictly lower triangular part `K_{3,k}^{(α,β)}(n,j)` of `L_{3,k}^{(α,β)}`. -/
def K₃ (k α β : ℝ) (n j : ℕ) : ℝ :=
  (k + 2) * (6 * (j : ℝ) ^ 2 - 6 * (k + 1) * ((n : ℝ) - (j : ℝ)) * (j : ℝ)
      + k * (k + 1) * ((n : ℝ) - (j : ℝ)) ^ 2) * (σ 1 (n - j) : ℝ)
    + 60 * α * (4 * (j : ℝ) - k * ((n : ℝ) - (j : ℝ))) * (σ 3 (n - j) : ℝ)
    - 504 * β * (σ 5 (n - j) : ℝ)

/-- **Coefficients of the second-order operator** (item 1.2 of the verification plan).
`[qⁿ](L_{2,k}^α G) = κ_{2,k}^α(n) aₙ + ∑_{j<n} K_{2,k}^α(n,j) a_j`. -/
theorem coeff_L₂ (k α : ℝ) (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (L₂ k α G) = κ₂ k α n * coeff n G + ∑ j ∈ range n, K₂ k α n j * coeff j G := by
  have hsum : ∑ j ∈ range n, K₂ k α n j * coeff j G
      = -((k + 1) / 6) * (-24 * ∑ j ∈ range n, (σ 1 (n - j) : ℝ) * ((j : ℝ) * coeff j G))
        + k * (k + 1) / 12
            * (-24 * ∑ j ∈ range n, ((n - j : ℕ) : ℝ) * (σ 1 (n - j) : ℝ) * coeff j G)
        + α * (240 * ∑ j ∈ range n, (σ 3 (n - j) : ℝ) * coeff j G) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    rw [K₂, Nat.cast_sub hj.le]
    ring
  rw [L₂, κ₂, hsum]
  simp only [map_add, map_sub, PowerSeries.coeff_smul, smul_eq_mul, coeff_D, coeff_E₂_mul,
    coeff_D_E₂_mul, coeff_E₄_mul]
  ring

/-- **Coefficients of the third-order operator** (item 1.3 of the verification plan).
`[qⁿ](L_{3,k}^{(α,β)} G) = κ_{3,k}^{(α,β)}(n) aₙ + ∑_{j<n} K_{3,k}^{(α,β)}(n,j) a_j`. -/
theorem coeff_L₃ (k α β : ℝ) (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (L₃ k α β G)
      = κ₃ k α β n * coeff n G + ∑ j ∈ range n, K₃ k α β n j * coeff j G := by
  have hsum : ∑ j ∈ range n, K₃ k α β n j * coeff j G
      = -((k + 2) / 4) * (-24 * ∑ j ∈ range n,
            (σ 1 (n - j) : ℝ) * ((j : ℝ) * ((j : ℝ) * coeff j G)))
        + (k + 1) * (k + 2) / 4
            * (-24 * ∑ j ∈ range n,
                ((n - j : ℕ) : ℝ) * (σ 1 (n - j) : ℝ) * ((j : ℝ) * coeff j G))
        + α * (240 * ∑ j ∈ range n, (σ 3 (n - j) : ℝ) * ((j : ℝ) * coeff j G))
        - k * (k + 1) * (k + 2) / 24
            * (-24 * ∑ j ∈ range n, ((n - j : ℕ) : ℝ) ^ 2 * (σ 1 (n - j) : ℝ) * coeff j G)
        - k * α / 4
            * (240 * ∑ j ∈ range n, ((n - j : ℕ) : ℝ) * (σ 3 (n - j) : ℝ) * coeff j G)
        + β * (-504 * ∑ j ∈ range n, (σ 5 (n - j) : ℝ) * coeff j G) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    rw [K₃, Nat.cast_sub hj.le]
    ring
  rw [L₃, κ₃, hsum]
  simp only [add_mul, sub_mul, smul_mul_assoc, map_add, map_sub, PowerSeries.coeff_smul,
    smul_eq_mul, coeff_D, coeff_E₂_mul, coeff_E₄_mul, coeff_E₆_mul, coeff_D_E₂_mul,
    coeff_D_D_E₂_mul, coeff_D_E₄_mul]
  ring

end

end KanekoZagier
