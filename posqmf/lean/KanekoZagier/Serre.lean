import posqmf.lean.KanekoZagier.Ramanujan

/-!
# The Serre derivative on formal `q`-expansions

The Serre derivative of the paper is `∂_k F = F' - (k/12) E₂ F`, and `∂_k^r` denotes the `r`-fold
composite `∂_{k+2(r-1)} ∘ ⋯ ∘ ∂_{k+2} ∘ ∂_k`.  The weight `k` is allowed to be an arbitrary real
number: all the identities below are polynomial in `k`.

## Main results

* `KanekoZagier.serreD_mul`: the product rule `∂_{w₁+w₂}(FG) = (∂_{w₁}F)G + F(∂_{w₂}G)`.
* `KanekoZagier.serreD_E2`, `serreD_E4`, `serreD_E6`: Ramanujan's identities in Serre form.
* `KanekoZagier.serreD_two_eq`, `serreD_three_eq`: the expansions of `∂_k²` and `∂_k³` in terms of
  `D`, `E₂`, `E₄`, `E₆`.  These are the computations behind the two Kaneko--Zagier operators.
-/

open PowerSeries

namespace KanekoZagier

noncomputable section

/-- The Serre derivative `∂_k F = F' - (k/12) E₂ F`. -/
def serreD (k : ℝ) (f : ℝ⟦X⟧) : ℝ⟦X⟧ := D f - (k / 12) • (E2 * f)

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

lemma serreD_E2 : serreD 1 E2 = (-1 / 12 : ℝ) • E4 := by
  rw [serreD, ramanujan_E2]; module

lemma serreD_E4 : serreD 4 E4 = (-1 / 3 : ℝ) • E6 := by
  rw [serreD, ramanujan_E4]; module

lemma serreD_E6 : serreD 6 E6 = (-1 / 2 : ℝ) • (E4 * E4) := by
  rw [serreD, ramanujan_E6]; module

lemma serreD_E4_mul_E4 : serreD 8 (E4 * E4) = (-2 / 3 : ℝ) • (E4 * E6) := by
  rw [show (8 : ℝ) = 4 + 4 by norm_num, serreD_mul, serreD_E4]
  simp only [smul_mul_assoc, mul_smul_comm, mul_comm E6 E4]
  module

/-! ### Pushing the Serre derivative past a modular factor

If `F` has weight `w` then `E₄F`, `E₆F` and `E₄²F` have weights `w+4`, `w+6` and `w+8`.  The
weight of the product is passed as a hypothesis, so that these fire on whatever syntactic form
that weight has taken. -/

lemma serreD_E4_mul (v w : ℝ) (hv : v = w + 4) (f : ℝ⟦X⟧) :
    serreD v (E4 * f) = (-1 / 3 : ℝ) • (E6 * f) + E4 * serreD w f := by
  subst hv
  rw [show w + 4 = 4 + w by ring, serreD_mul, serreD_E4, smul_mul_assoc]

lemma serreD_E6_mul (v w : ℝ) (hv : v = w + 6) (f : ℝ⟦X⟧) :
    serreD v (E6 * f) = (-1 / 2 : ℝ) • (E4 * E4 * f) + E6 * serreD w f := by
  subst hv
  rw [show w + 6 = 6 + w by ring, serreD_mul, serreD_E6, smul_mul_assoc]

lemma serreD_E4_sq_mul (v w : ℝ) (hv : v = w + 8) (f : ℝ⟦X⟧) :
    serreD v (E4 * E4 * f) = (-2 / 3 : ℝ) • (E4 * E6 * f) + E4 * E4 * serreD w f := by
  subst hv
  rw [show w + 8 = 8 + w by ring, serreD_mul, serreD_E4_mul_E4, smul_mul_assoc]

/-! ### Expansion of the iterated Serre derivative in terms of `D` -/

/-- The twofold Serre derivative written out in terms of `D`:
`∂_k²F = F'' - ((k+1)/6)E₂F' + (k(k+1)/12)E₂'F + (k(k+2)/144)E₄F`.
Comparing with `L2` this is exactly `L_{2,k} = ∂_k² - (k(k+2)/144)E₄`. -/
theorem serreD_two_eq (k : ℝ) (f : ℝ⟦X⟧) :
    serreDIter k 2 f = D (D f) - ((k + 1) / 6) • (E2 * D f) + (k * (k + 1) / 12) • (D E2 * f)
      + (k * (k + 2) / 144) • (E4 * f) := by
  rw [serreDIter_two, serreD, serreD, D_sub, D_smul, D_mul]
  simp only [smul_sub, smul_add, smul_smul, mul_smul_comm, mul_sub, mul_add]
  rw [show E2 * (E2 * f) = E2 * E2 * f by ring, E2_mul_E2]
  simp only [smul_add, add_mul, smul_mul_assoc, smul_smul]
  ring_nf
  module

/-- The threefold Serre derivative written out in terms of `D`:
`∂_k³F = F''' - ((k+2)/4)E₂F'' + (((k+1)(k+2))/4)E₂'F' + ((3k²+12k+8)/144)E₄F'`
`- (k(k+1)(k+2)/24)E₂''F - (k(3k²+12k+8)/576)E₄'F - (k(k+2)(k+4)/1728)E₆F`. -/
theorem serreD_three_eq (k : ℝ) (f : ℝ⟦X⟧) :
    serreDIter k 3 f = D (D (D f)) - ((k + 2) / 4) • (E2 * D (D f))
      + ((k + 1) * (k + 2) / 4) • (D E2 * D f)
      + ((3 * k ^ 2 + 12 * k + 8) / 144) • (E4 * D f)
      - (k * (k + 1) * (k + 2) / 24) • (D (D E2) * f)
      - (k * (3 * k ^ 2 + 12 * k + 8) / 576) • (D E4 * f)
      - (k * (k + 2) * (k + 4) / 1728) • (E6 * f) := by
  rw [serreDIter_three, serreD_two_eq k f, serreD]
  simp only [D_add, D_sub, D_smul, D_mul, smul_sub, smul_add, smul_smul, mul_smul_comm, mul_sub,
    mul_add, add_mul]
  rw [show E2 * (E2 * D f) = E2 * E2 * D f by ring, E2_mul_E2,
    show E2 * (D E2 * f) = E2 * D E2 * f by ring, E2_mul_D_E2,
    show E2 * (E4 * f) = E2 * E4 * f by ring, E2_mul_E4]
  simp only [smul_add, add_mul, smul_mul_assoc, smul_smul]
  ring_nf
  module

end

end KanekoZagier
