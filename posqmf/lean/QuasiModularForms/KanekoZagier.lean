import posqmf.lean.QuasiModularForms.Serre

/-!
# The Kaneko--Zagier operators `L_{2,k}^α` and `L_{3,k}^{(α,β)}`

The second-order Kaneko--Zagier operator and its third-order analogue of
Kaneko--Nagatomo--Sakai are defined here by their `D`-forms, acting on formal
`q`-expansions.  Both are modular linear differential operators, of weight `4` and type
`(k, k+4)` resp. weight `6` and type `(k, k+6)` on `SL₂(ℤ)`; that modularity plays no role in the
identities proved here, which are identities of formal power series.

## Main results

* `KanekoZagier.L2_eq_serre`: `L_{2,k}^α = ∂_k² - (k(k+2)/144 - α)E₄`.
* `KanekoZagier.L3_eq_serre`: the `D`-form and the Serre-derivative form of the third-order
  operator agree, `L_{3,k}^{(α,β)} = ∂_k³ + (α - (3k²+12k+8)/144)E₄∂_k`
  `+ (β + kα/12 - k²(k+3)/864)E₆`.  This is item 1.1 of the verification plan.
-/

open PowerSeries

namespace KanekoZagier

open QExpansion

noncomputable section

/-- The second-order Kaneko--Zagier operator in `D`-form:
`L_{2,k}^α = D² - ((k+1)/6)E₂D + (k(k+1)/12)E₂' + αE₄`.
Taking `α = 0` recovers the classical operator `L_{2,k}` of Kaneko--Zagier. -/
def L2 (k α : ℝ) (f : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  D (D f) - ((k + 1) / 6) • (E₂ * D f) + (k * (k + 1) / 12) • (D E₂ * f) + α • (E₄ * f)

/-- The third-order Kaneko--Zagier operator in `D`-form:
`L_{3,k}^{(α,β)} = D³ - ((k+2)/4)E₂D² + ((((k+1)(k+2))/4)E₂' + αE₄)D`
`- ((k(k+1)(k+2)/24)E₂'' + (kα/4)E₄' - βE₆)`.
Taking `α = β = 0` recovers `L_{3,k}` of Kaneko--Nagatomo--Sakai. -/
def L3 (k α β : ℝ) (f : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  D (D (D f)) - ((k + 2) / 4) • (E₂ * D (D f))
    + (((k + 1) * (k + 2) / 4) • D E₂ + α • E₄) * D f
    - ((k * (k + 1) * (k + 2) / 24) • D (D E₂) + (k * α / 4) • D E₄ - β • E₆) * f

@[simp] lemma L2_zero (k α : ℝ) : L2 k α 0 = 0 := by simp [L2]

@[simp] lemma L3_zero (k α β : ℝ) : L3 k α β 0 = 0 := by simp [L3]

lemma L3_smul (k α β c : ℝ) (f : ℝ⟦X⟧) : L3 k α β (c • f) = c • L3 k α β f := by
  simp only [L3, D_smul, mul_smul_comm, smul_sub, smul_add, smul_smul]
  module

/-- **Serre form of the second-order operator**: `L_{2,k}^α = ∂_k² - (k(k+2)/144 - α)E₄`. -/
theorem L2_eq_serre (k α : ℝ) (f : ℝ⟦X⟧) :
    L2 k α f = serreDIter k 2 f - (k * (k + 2) / 144 - α) • (E₄ * f) := by
  rw [L2, serreD_two_eq]; module

/-- **Serre form of the third-order operator** (item 1.1 of the verification plan):
`L_{3,k}^{(α,β)} = ∂_k³ + (α - (3k²+12k+8)/144)E₄∂_k + (β + kα/12 - k²(k+3)/864)E₆`. -/
theorem L3_eq_serre (k α β : ℝ) (f : ℝ⟦X⟧) :
    L3 k α β f = serreDIter k 3 f + (α - (3 * k ^ 2 + 12 * k + 8) / 144) • (E₄ * serreD k f)
      + (β + k * α / 12 - k ^ 2 * (k + 3) / 864) • (E₆ * f) := by
  rw [L3, serreD_three_eq, serreD]
  simp only [smul_sub, smul_smul, smul_mul_assoc, mul_smul_comm, mul_sub, mul_add,
    add_mul, sub_mul]
  rw [show E₄ * (E₂ * f) = E₂ * E₄ * f by ring, E₂_mul_E₄]
  simp only [smul_add, add_mul, smul_mul_assoc, smul_smul]
  ring_nf
  module

end

end KanekoZagier
