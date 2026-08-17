import posqmf.lean.QuasiModularForms.Ramanujan

/-!
# The Serre derivative on formal `q`-expansions

The Serre derivative of the paper is `∂_k F = F' - (k/12) E₂ F`, and `∂_k^r` denotes the `r`-fold
composite `∂_{k+2(r-1)} ∘ ⋯ ∘ ∂_{k+2} ∘ ∂_k`.  The weight `k` is allowed to be an arbitrary real
number: all the identities below are polynomial in `k`.

## Main results

* `QExpansion.serreD_mul`: the product rule `∂_{w₁+w₂}(FG) = (∂_{w₁}F)G + F(∂_{w₂}G)`.
* `QExpansion.serreD_E₂`, `serreD_E₄`, `serreD_E₆`: Ramanujan's identities in Serre form.
* `QExpansion.serreD_two_eq`, `serreD_three_eq`: the expansions of `∂_k²` and `∂_k³` in terms of
  `D`, `E₂`, `E₄`, `E₆`.  These are the computations behind the two Kaneko--Zagier operators.
-/

open ArithmeticFunction Finset PowerSeries
open scoped sigma

namespace QExpansion

noncomputable section

/-- The Serre derivative `∂_k F = F' - (k/12) E₂ F`. -/
def serreD (k : ℝ) (f : ℝ⟦X⟧) : ℝ⟦X⟧ := D f - (k / 12) • (E₂ * f)

/-- The `r`-fold Serre derivative `∂_k^r F = ∂_{k+2(r-1)} ∂_{k+2(r-2)} ⋯ ∂_k F`. -/
def serreDIter (k : ℝ) : ℕ → ℝ⟦X⟧ → ℝ⟦X⟧
  | 0, f => f
  | r + 1, f => serreD (k + 2 * r) (serreDIter k r f)

@[simp]
lemma serreDIter_zero (k : ℝ) (f : ℝ⟦X⟧) : serreDIter k 0 f = f := rfl

lemma serreDIter_succ (k : ℝ) (r : ℕ) (f : ℝ⟦X⟧) :
    serreDIter k (r + 1) f = serreD (k + 2 * r) (serreDIter k r f) := rfl

lemma serreDIter_one (k : ℝ) (f : ℝ⟦X⟧) : serreDIter k 1 f = serreD k f := by
  rw [serreDIter_succ]; norm_num

lemma serreDIter_two (k : ℝ) (f : ℝ⟦X⟧) : serreDIter k 2 f = serreD (k + 2) (serreD k f) := by
  rw [serreDIter_succ, serreDIter_one]; norm_num

lemma serreDIter_three (k : ℝ) (f : ℝ⟦X⟧) :
    serreDIter k 3 f = serreD (k + 4) (serreDIter k 2 f) := by
  rw [serreDIter_succ]; norm_num

lemma serreD_add (k : ℝ) (f g : ℝ⟦X⟧) : serreD k (f + g) = serreD k f + serreD k g := by
  simp only [serreD, D_add, mul_add, smul_add]; abel

lemma serreD_smul (k c : ℝ) (f : ℝ⟦X⟧) : serreD k (c • f) = c • serreD k f := by
  simp only [serreD, D_smul, mul_smul_comm, smul_sub, smul_smul]; ring_nf

/-- The Fourier coefficients of the Serre derivative, with the `E₂`-convolution written out. -/
lemma coeff_serreD (k : ℝ) (f : ℝ⟦X⟧) (n : ℕ) :
    coeff n (serreD k f)
      = (n : ℝ) * coeff n f
        - k / 12 * (coeff n f - 24 * ∑ j ∈ range n, (σ 1 (n - j) : ℝ) * coeff j f) := by
  rw [serreD, map_sub, PowerSeries.coeff_smul, smul_eq_mul, coeff_D, coeff_E₂_mul]

/-- One more Serre derivative on top of an iterate: `∂_{k+2r}(∂_k^r F) = ∂_k^{r+1}F`.  The weight is
supplied as a hypothesis so that the lemma applies whatever form `k + 2r` happens to take. -/
lemma serreD_serreDIter (k : ℝ) (r : ℕ) (v : ℝ) (hv : v = k + 2 * (r : ℝ)) (f : ℝ⟦X⟧) :
    serreD v (serreDIter k r f) = serreDIter k (r + 1) f := by
  subst hv; rfl

/-- The Serre derivative is a derivation with respect to the grading by weight:
`∂_{w₁+w₂}(FG) = (∂_{w₁}F)G + F(∂_{w₂}G)`. -/
lemma serreD_mul (w₁ w₂ : ℝ) (f g : ℝ⟦X⟧) :
    serreD (w₁ + w₂) (f * g) = serreD w₁ f * g + f * serreD w₂ g := by
  simp only [serreD, D_mul, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, add_smul, add_div]
  ring_nf

/-! ### Ramanujan's identities in Serre form -/

lemma serreD_E₂ : serreD 1 E₂ = (-1 / 12 : ℝ) • E₄ := by
  rw [serreD, ramanujan_E₂]; module

lemma serreD_E₄ : serreD 4 E₄ = (-1 / 3 : ℝ) • E₆ := by
  rw [serreD, ramanujan_E₄]; module

lemma serreD_E₆ : serreD 6 E₆ = (-1 / 2 : ℝ) • (E₄ * E₄) := by
  rw [serreD, ramanujan_E₆]; module

lemma serreD_E₄_mul_E₄ : serreD 8 (E₄ * E₄) = (-2 / 3 : ℝ) • (E₄ * E₆) := by
  rw [show (8 : ℝ) = 4 + 4 by norm_num, serreD_mul, serreD_E₄]
  simp only [smul_mul_assoc, mul_smul_comm, mul_comm E₆ E₄]
  module

/-! ### Pushing the Serre derivative past a modular factor

If `F` has weight `w` then `E₄F`, `E₆F` and `E₄²F` have weights `w+4`, `w+6` and `w+8`.  The
weight of the product is passed as a hypothesis, so that these fire on whatever syntactic form
that weight has taken. -/

lemma serreD_E₄_mul (v w : ℝ) (hv : v = w + 4) (f : ℝ⟦X⟧) :
    serreD v (E₄ * f) = (-1 / 3 : ℝ) • (E₆ * f) + E₄ * serreD w f := by
  subst hv
  rw [show w + 4 = 4 + w by ring, serreD_mul, serreD_E₄, smul_mul_assoc]

lemma serreD_E₆_mul (v w : ℝ) (hv : v = w + 6) (f : ℝ⟦X⟧) :
    serreD v (E₆ * f) = (-1 / 2 : ℝ) • (E₄ * E₄ * f) + E₆ * serreD w f := by
  subst hv
  rw [show w + 6 = 6 + w by ring, serreD_mul, serreD_E₆, smul_mul_assoc]

lemma serreD_E₄_sq_mul (v w : ℝ) (hv : v = w + 8) (f : ℝ⟦X⟧) :
    serreD v (E₄ * E₄ * f) = (-2 / 3 : ℝ) • (E₄ * E₆ * f) + E₄ * E₄ * serreD w f := by
  subst hv
  rw [show w + 8 = 8 + w by ring, serreD_mul, serreD_E₄_mul_E₄, smul_mul_assoc]

/-! ### Expansion of the iterated Serre derivative in terms of `D` -/

/-- The twofold Serre derivative written out in terms of `D`:
`∂_k²F = F'' - ((k+1)/6)E₂F' + (k(k+1)/12)E₂'F + (k(k+2)/144)E₄F`.
Comparing with `L₂` this is exactly `L_{2,k} = ∂_k² - (k(k+2)/144)E₄`. -/
theorem serreD_two_eq (k : ℝ) (f : ℝ⟦X⟧) :
    serreDIter k 2 f = D (D f) - ((k + 1) / 6) • (E₂ * D f) + (k * (k + 1) / 12) • (D E₂ * f)
      + (k * (k + 2) / 144) • (E₄ * f) := by
  rw [serreDIter_two, serreD, serreD, D_sub, D_smul, D_mul]
  simp only [smul_sub, smul_add, smul_smul, mul_smul_comm, mul_sub, mul_add]
  rw [show E₂ * (E₂ * f) = E₂ * E₂ * f by ring, E₂_mul_E₂]
  simp only [smul_add, add_mul, smul_mul_assoc, smul_smul]
  ring_nf
  module

/-- The threefold Serre derivative written out in terms of `D`:
`∂_k³F = F''' - ((k+2)/4)E₂F'' + (((k+1)(k+2))/4)E₂'F' + ((3k²+12k+8)/144)E₄F'`
`- (k(k+1)(k+2)/24)E₂''F - (k(3k²+12k+8)/576)E₄'F - (k(k+2)(k+4)/1728)E₆F`. -/
theorem serreD_three_eq (k : ℝ) (f : ℝ⟦X⟧) :
    serreDIter k 3 f = D (D (D f)) - ((k + 2) / 4) • (E₂ * D (D f))
      + ((k + 1) * (k + 2) / 4) • (D E₂ * D f)
      + ((3 * k ^ 2 + 12 * k + 8) / 144) • (E₄ * D f)
      - (k * (k + 1) * (k + 2) / 24) • (D (D E₂) * f)
      - (k * (3 * k ^ 2 + 12 * k + 8) / 576) • (D E₄ * f)
      - (k * (k + 2) * (k + 4) / 1728) • (E₆ * f) := by
  rw [serreDIter_three, serreD_two_eq k f, serreD]
  simp only [D_add, D_sub, D_smul, D_mul, smul_sub, smul_add, smul_smul, mul_smul_comm, mul_sub,
    mul_add, add_mul]
  rw [show E₂ * (E₂ * D f) = E₂ * E₂ * D f by ring, E₂_mul_E₂,
    show E₂ * (D E₂ * f) = E₂ * D E₂ * f by ring, E₂_mul_D_E₂,
    show E₂ * (E₄ * f) = E₂ * E₄ * f by ring, E₂_mul_E₄]
  simp only [smul_add, add_mul, smul_mul_assoc, smul_smul]
  ring_nf
  module

end

end QExpansion
