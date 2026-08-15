import posqmf.lean.QuasiModularForms.KanekoZagier

/-!
# The intertwining criterion for the Kaneko--Zagier operators

This file proves the computational content of the intertwining criterion (item 1.4 and the
sufficiency half of 1.5 of the verification plan).  Following the paper we work throughout with
the Serre-derivative normal forms

`L_{2,k}^γ = ∂_k² + C E₄`,  `L_{3,k}^{(α,β)} = ∂_k³ + A E₄∂_k + B E₆`,

where `A`, `B`, `C` are the shifted parameters defined below; the `D`-forms `L2` and `L3` of
`KanekoZagier.lean` are recovered by `L2_eq_L2S` and `L3_eq_L3S`.

## Main results

* `KanekoZagier.L3S_comp_L2S`: the `∂_k`-normal form of `L_{3,k+4}^{(α,β)} L_{2,k}^γ`.
* `KanekoZagier.L2S_comp_L3S`: the `∂_k`-normal form of `L_{2,k+6}^{γ'} L_{3,k}^{(α',β')}`.
* `KanekoZagier.L3S_comp_L2S_eq_L2S_comp_L3S`: the four constraints on the shifted parameters
  imply the intertwining relation.
* `KanekoZagier.L3_comp_L2_eq_L2_comp_L3`: the same statement for the `D`-forms `L2`, `L3`, with
  the shifted parameters spelled out.

The converse implication is not proved here: it needs the uniqueness of the Serre-derivative normal
form, i.e. that `∂_k⁵`, `E₄∂_k³`, `E₆∂_k²`, `E₄²∂_k` and `E₄E₆` are linearly independent as
operators.  That direction remains a Sage check.
-/

open PowerSeries

namespace KanekoZagier

open QExpansion

noncomputable section

/-- `L_{2,k}^γ` in Serre form, `∂_k² + C E₄`, with `C = γ - k(k+2)/144`. -/
def L2S (k C : ℝ) (f : ℝ⟦X⟧) : ℝ⟦X⟧ := serreDIter k 2 f + C • (E₄ * f)

/-- `L_{3,k}^{(α,β)}` in Serre form, `∂_k³ + A E₄∂_k + B E₆`. -/
def L3S (k A B : ℝ) (f : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  serreDIter k 3 f + A • (E₄ * serreD k f) + B • (E₆ * f)

lemma L2_eq_L2S (k γ : ℝ) (f : ℝ⟦X⟧) : L2 k γ f = L2S k (γ - k * (k + 2) / 144) f := by
  rw [L2_eq_serre, L2S]; module

lemma L3_eq_L3S (k α β : ℝ) (f : ℝ⟦X⟧) :
    L3 k α β f
      = L3S k (α - (3 * k ^ 2 + 12 * k + 8) / 144) (β + k * α / 12 - k ^ 2 * (k + 3) / 864) f :=
  L3_eq_serre k α β f

/-! ### The two normal forms -/

/-- **The `∂_k`-normal form of `L_{3,k+4}^{(α,β)} L_{2,k}^{γ}`:**
`∂_k⁵ + (A+C)E₄∂_k³ + (B−C)E₆∂_k² + C(A+1/2)E₄²∂_k + C(B − A/3 − 1/9)E₄E₆`. -/
theorem L3S_comp_L2S (k A B C : ℝ) (f : ℝ⟦X⟧) :
    L3S (k + 4) A B (L2S k C f)
      = serreDIter k 5 f + (A + C) • (E₄ * serreDIter k 3 f)
        + (B - C) • (E₆ * serreDIter k 2 f)
        + (C * (A + 1 / 2)) • (E₄ * E₄ * serreD k f)
        + (C * (B - A / 3 - 1 / 9)) • (E₄ * E₆ * f) := by
  have g1 : serreD (k + 4) (L2S k C f)
      = serreDIter k 3 f + C • ((-1 / 3 : ℝ) • (E₆ * f) + E₄ * serreD k f) := by
    rw [L2S, serreD_add, serreD_smul, ← serreDIter_three, serreD_E₄_mul (k + 4) k (by ring)]
  have g2 : serreD (k + 4 + 2) (serreD (k + 4) (L2S k C f))
      = serreDIter k 4 f + C • ((1 / 6 : ℝ) • (E₄ * E₄ * f)
          + (-2 / 3 : ℝ) • (E₆ * serreD k f) + E₄ * serreDIter k 2 f) := by
    rw [g1, serreD_add, serreD_smul, serreD_serreDIter k 3 (k + 4 + 2) (by push_cast; ring) f,
      serreD_add, serreD_smul, serreD_E₆_mul (k + 4 + 2) k (by ring),
      serreD_E₄_mul (k + 4 + 2) (k + 2) (by ring), ← serreDIter_two]
    module
  have g3 : serreD (k + 4 + 4) (serreD (k + 4 + 2) (serreD (k + 4) (L2S k C f)))
      = serreDIter k 5 f + C • ((-1 / 9 : ℝ) • (E₄ * E₆ * f)
          + (1 / 2 : ℝ) • (E₄ * E₄ * serreD k f) + (-1 : ℝ) • (E₆ * serreDIter k 2 f)
          + E₄ * serreDIter k 3 f) := by
    rw [g2, serreD_add, serreD_smul, serreD_serreDIter k 4 (k + 4 + 4) (by push_cast; ring) f,
      serreD_add, serreD_add, serreD_smul, serreD_smul,
      serreD_E₄_sq_mul (k + 4 + 4) k (by ring),
      serreD_E₆_mul (k + 4 + 4) (k + 2) (by ring),
      serreD_E₄_mul (k + 4 + 4) (k + 4) (by ring), ← serreDIter_two, ← serreDIter_three]
    module
  rw [L3S, serreDIter_three (k + 4) (L2S k C f), serreDIter_two (k + 4) (L2S k C f), g3, g1, L2S]
  simp only [mul_add, mul_smul_comm, smul_add, smul_smul]
  ring_nf
  module

/-- **The `∂_k`-normal form of `L_{2,k+6}^{γ'} L_{3,k}^{(α',β')}`:**
`∂_k⁵ + (A'+C')E₄∂_k³ + (B' − 2A'/3)E₆∂_k² + (A'(C'+1/6) − B')E₄²∂_k + B'(C'+1/3)E₄E₆`. -/
theorem L2S_comp_L3S (k A' B' C' : ℝ) (f : ℝ⟦X⟧) :
    L2S (k + 6) C' (L3S k A' B' f)
      = serreDIter k 5 f + (A' + C') • (E₄ * serreDIter k 3 f)
        + (B' - 2 * A' / 3) • (E₆ * serreDIter k 2 f)
        + (A' * (C' + 1 / 6) - B') • (E₄ * E₄ * serreD k f)
        + (B' * (C' + 1 / 3)) • (E₄ * E₆ * f) := by
  have h1 : serreD (k + 6) (L3S k A' B' f)
      = serreDIter k 4 f + A' • ((-1 / 3 : ℝ) • (E₆ * serreD k f) + E₄ * serreDIter k 2 f)
        + B' • ((-1 / 2 : ℝ) • (E₄ * E₄ * f) + E₆ * serreD k f) := by
    rw [L3S, serreD_add, serreD_add, serreD_smul, serreD_smul,
      serreD_serreDIter k 3 (k + 6) (by push_cast; ring) f,
      serreD_E₄_mul (k + 6) (k + 2) (by ring), serreD_E₆_mul (k + 6) k (by ring),
      ← serreDIter_two]
  have h2 : serreD (k + 6 + 2) (serreD (k + 6) (L3S k A' B' f))
      = serreDIter k 5 f
        + A' • ((1 / 6 : ℝ) • (E₄ * E₄ * serreD k f)
            + (-2 / 3 : ℝ) • (E₆ * serreDIter k 2 f) + E₄ * serreDIter k 3 f)
        + B' • ((1 / 3 : ℝ) • (E₄ * E₆ * f) + (-1 : ℝ) • (E₄ * E₄ * serreD k f)
            + E₆ * serreDIter k 2 f) := by
    rw [h1, serreD_add, serreD_add, serreD_smul, serreD_smul,
      serreD_serreDIter k 4 (k + 6 + 2) (by push_cast; ring) f, serreD_add, serreD_add,
      serreD_smul, serreD_smul,
      serreD_E₆_mul (k + 6 + 2) (k + 2) (by ring),
      serreD_E₄_mul (k + 6 + 2) (k + 4) (by ring),
      serreD_E₄_sq_mul (k + 6 + 2) k (by ring), ← serreDIter_two, ← serreDIter_three]
    module
  rw [L2S, serreDIter_two (k + 6) (L3S k A' B' f), h2, L3S]
  simp only [mul_add, mul_smul_comm, smul_add, smul_smul]
  ring_nf
  module

/-! ### The intertwining relation -/

/-- **The intertwining criterion, sufficiency.**  The four constraints on the shifted parameters
imply `L_{3,k+4}^{(α,β)} L_{2,k}^γ = L_{2,k+6}^{γ'} L_{3,k}^{(α',β')}`. -/
theorem L3S_comp_L2S_eq_L2S_comp_L3S (k A B C A' B' C' : ℝ)
    (h₁ : A + C = A' + C')
    (h₂ : B - C = B' - 2 * A' / 3)
    (h₃ : C * (A + 1 / 2) = A' * (C' + 1 / 6) - B')
    (h₄ : C * (B - A / 3 - 1 / 9) = B' * (C' + 1 / 3))
    (f : ℝ⟦X⟧) :
    L3S (k + 4) A B (L2S k C f) = L2S (k + 6) C' (L3S k A' B' f) := by
  rw [L3S_comp_L2S, L2S_comp_L3S, h₁, h₂, h₃, h₄]

/-! ### The shifted parameters -/

/-- `A := α - (3k²+36k+104)/144`, the `E₄∂` coefficient of `L_{3,k+4}^{(α,β)}`. -/
def shiftA (k α : ℝ) : ℝ := α - (3 * k ^ 2 + 36 * k + 104) / 144

/-- `B := β + ((k+4)/12)α - (k+4)²(k+7)/864`, the `E₆` coefficient of `L_{3,k+4}^{(α,β)}`. -/
def shiftB (k α β : ℝ) : ℝ := β + (k + 4) / 12 * α - (k + 4) ^ 2 * (k + 7) / 864

/-- `C := γ - k(k+2)/144`, the `E₄` coefficient of `L_{2,k}^{γ}`. -/
def shiftC (k γ : ℝ) : ℝ := γ - k * (k + 2) / 144

/-- `A' := α' - (3k²+12k+8)/144`, the `E₄∂` coefficient of `L_{3,k}^{(α',β')}`. -/
def shiftA' (k α' : ℝ) : ℝ := α' - (3 * k ^ 2 + 12 * k + 8) / 144

/-- `B' := β' + (k/12)α' - k²(k+3)/864`, the `E₆` coefficient of `L_{3,k}^{(α',β')}`. -/
def shiftB' (k α' β' : ℝ) : ℝ := β' + k / 12 * α' - k ^ 2 * (k + 3) / 864

/-- `C' := γ' - (k+6)(k+8)/144`, the `E₄` coefficient of `L_{2,k+6}^{γ'}`. -/
def shiftC' (k γ' : ℝ) : ℝ := γ' - (k + 6) * (k + 8) / 144

/-- **The intertwining criterion** for the `D`-forms of `KanekoZagier.lean`: the four constraints on
the shifted parameters imply
`L_{3,k+4}^{(α,β)} L_{2,k}^{γ} = L_{2,k+6}^{γ'} L_{3,k}^{(α',β')}`. -/
theorem L3_comp_L2_eq_L2_comp_L3 (k α β γ α' β' γ' : ℝ)
    (h₁ : shiftA k α + shiftC k γ = shiftA' k α' + shiftC' k γ')
    (h₂ : shiftB k α β - shiftC k γ = shiftB' k α' β' - 2 * shiftA' k α' / 3)
    (h₃ : shiftC k γ * (shiftA k α + 1 / 2)
      = shiftA' k α' * (shiftC' k γ' + 1 / 6) - shiftB' k α' β')
    (h₄ : shiftC k γ * (shiftB k α β - shiftA k α / 3 - 1 / 9)
      = shiftB' k α' β' * (shiftC' k γ' + 1 / 3))
    (f : ℝ⟦X⟧) :
    L3 (k + 4) α β (L2 k γ f) = L2 (k + 6) γ' (L3 k α' β' f) := by
  rw [L2_eq_L2S, L3_eq_L3S, L2_eq_L2S, L3_eq_L3S,
    show (α - (3 * (k + 4) ^ 2 + 12 * (k + 4) + 8) / 144)
      = α - (3 * k ^ 2 + 36 * k + 104) / 144 by ring,
    show (β + (k + 4) * α / 12 - (k + 4) ^ 2 * ((k + 4) + 3) / 864)
      = β + (k + 4) / 12 * α - (k + 4) ^ 2 * (k + 7) / 864 by ring,
    show (γ' - (k + 6) * ((k + 6) + 2) / 144) = γ' - (k + 6) * (k + 8) / 144 by ring,
    show (β' + k * α' / 12 - k ^ 2 * (k + 3) / 864)
      = β' + k / 12 * α' - k ^ 2 * (k + 3) / 864 by ring]
  exact L3S_comp_L2S_eq_L2S_comp_L3S k _ _ _ _ _ _ h₁ h₂ h₃ h₄ f

end

end KanekoZagier
