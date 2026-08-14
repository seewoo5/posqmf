import posqmf.lean.KanekoZagier.Operators

/-!
# Fourier coefficients of the Kaneko--Zagier operators

This file proves `lem:KZ2_coeff` and `lem:KZ3_coeff` (items 1.2 and 1.3 of the verification plan):
for `G = ∑_{n ≥ 0} aₙ qⁿ`,

`[qⁿ](L_{2,k}^α G) = κ_{2,k}^α(n) aₙ + ∑_{j<n} K_{2,k}^α(n,j) a_j`,
`[qⁿ](L_{3,k}^{(α,β)} G) = κ_{3,k}^{(α,β)}(n) aₙ + ∑_{j<n} K_{3,k}^{(α,β)}(n,j) a_j`,

with the `κ`'s and `K`'s of `eqn:kappa2`, `eqn:K2`, `eqn:KZ3_kappa`, `eqn:KZ3_K`.  These are the
formulas that drive every coefficient induction of §§3--4 of the paper.

Both proofs use only the `D`-forms `eqn:KZ2_def`, `eqn:KZ3_def` and the `q`-expansions of `E₂`,
`E₄`, `E₆`; in particular they are independent of the Ramanujan axioms of `Ramanujan.lean`.
-/

open ArithmeticFunction Finset PowerSeries
open scoped sigma

namespace KanekoZagier

noncomputable section

/-- `κ_{2,k}^α(n) = n² - ((k+1)/6)n + α` (`eqn:kappa2`), the diagonal coefficient of
`L_{2,k}^α`. -/
def kappa2 (k α : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ 2 - (k + 1) / 6 * n + α

/-- `K_{2,k}^α(n,j) = 2(k+1)(2j - k(n-j))σ₁(n-j) + 240ασ₃(n-j)` (`eqn:K2`), the strictly lower
triangular part of `L_{2,k}^α`. -/
def K2 (k α : ℝ) (n j : ℕ) : ℝ :=
  2 * (k + 1) * (2 * (j : ℝ) - k * ((n : ℝ) - (j : ℝ))) * (σ 1 (n - j) : ℝ)
    + 240 * α * (σ 3 (n - j) : ℝ)

/-- `κ_{3,k}^{(α,β)}(n) = n³ - ((k+2)/4)n² + αn + β` (`eqn:KZ3_kappa`). -/
def kappa3 (k α β : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ 3 - (k + 2) / 4 * (n : ℝ) ^ 2 + α * n + β

/-- `K_{3,k}^{(α,β)}(n,j)` of `eqn:KZ3_K`. -/
def K3 (k α β : ℝ) (n j : ℕ) : ℝ :=
  (k + 2) * (6 * (j : ℝ) ^ 2 - 6 * (k + 1) * ((n : ℝ) - (j : ℝ)) * (j : ℝ)
      + k * (k + 1) * ((n : ℝ) - (j : ℝ)) ^ 2) * (σ 1 (n - j) : ℝ)
    + 60 * α * (4 * (j : ℝ) - k * ((n : ℝ) - (j : ℝ))) * (σ 3 (n - j) : ℝ)
    - 504 * β * (σ 5 (n - j) : ℝ)

/-- **`lem:KZ2_coeff`** (item 1.2 of the verification plan).
`[qⁿ](L_{2,k}^α G) = κ_{2,k}^α(n) aₙ + ∑_{j<n} K_{2,k}^α(n,j) a_j`. -/
theorem coeff_L2 (k α : ℝ) (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (L2 k α G) = kappa2 k α n * coeff n G + ∑ j ∈ range n, K2 k α n j * coeff j G := by
  have hsum : ∑ j ∈ range n, K2 k α n j * coeff j G
      = -((k + 1) / 6) * (-24 * ∑ j ∈ range n, (σ 1 (n - j) : ℝ) * ((j : ℝ) * coeff j G))
        + k * (k + 1) / 12
            * (-24 * ∑ j ∈ range n, ((n - j : ℕ) : ℝ) * (σ 1 (n - j) : ℝ) * coeff j G)
        + α * (240 * ∑ j ∈ range n, (σ 3 (n - j) : ℝ) * coeff j G) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    rw [K2, Nat.cast_sub hj.le]
    ring
  rw [L2, kappa2, hsum]
  simp only [map_add, map_sub, PowerSeries.coeff_smul, smul_eq_mul, coeff_D, coeff_E2_mul,
    coeff_D_E2_mul, coeff_E4_mul]
  ring

/-- **`lem:KZ3_coeff`** (item 1.3 of the verification plan).
`[qⁿ](L_{3,k}^{(α,β)} G) = κ_{3,k}^{(α,β)}(n) aₙ + ∑_{j<n} K_{3,k}^{(α,β)}(n,j) a_j`. -/
theorem coeff_L3 (k α β : ℝ) (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (L3 k α β G)
      = kappa3 k α β n * coeff n G + ∑ j ∈ range n, K3 k α β n j * coeff j G := by
  have hsum : ∑ j ∈ range n, K3 k α β n j * coeff j G
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
    rw [K3, Nat.cast_sub hj.le]
    ring
  rw [L3, kappa3, hsum]
  simp only [add_mul, sub_mul, smul_mul_assoc, map_add, map_sub, PowerSeries.coeff_smul,
    smul_eq_mul, coeff_D, coeff_E2_mul, coeff_E4_mul, coeff_E6_mul, coeff_D_E2_mul,
    coeff_D_D_E2_mul, coeff_D_E4_mul]
  ring

end

end KanekoZagier
