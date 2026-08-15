import posqmf.lean.DifferentialOperators.Coefficients
import posqmf.lean.DifferentialOperators.Intertwine
import posqmf.lean.DifferentialOperators.QuasiModular
import posqmf.lean.SigmaBounds

/-!
# The family `F_w` and the positivity of `F̃_{w-2}`

In *Positive quasimodular forms and the sign uncertainty principle*, the value of `M_{d,+}` at the
origin is `-6 b_{0,+}/π`, and `b_{0,+}` is a positive combination of the Fourier coefficients `ã_j`
of `F̃_{w-2}` for `1 ≤ j ≤ n_{d,+}`.  Nonpositivity of `M_{d,+}(0)` therefore reduces to

`ã_j > 0` for `1 ≤ j ≤ w/4 - 3`,  and  `ã_{w/4-2} ≥ 1/360`,

for every `w ≡ 0 (mod 4)` with `w ≥ 12`, which is what this file proves, with nothing assumed.

## The two layers

The argument lives on two levels, and the file is sectioned accordingly, each section opening the
namespace of the layer it works in: `KanekoZagier` and `QuasiModular` both name `D`, `E₂`, `E₄`,
`E₆` and `∂_k`, so the two `open`s cannot be in scope at the same time.

* `QExpansion` works in `ℝ⟦X⟧`.  It runs the induction on `w` in steps of `4` driven by the
  recurrence `F̃_{w+2} = c_w(𝒮_w F̃_{w-2} - (1/3)∂_{w-1}F_w)`, where `𝒮_w = -L_{2,w-2}^{α_w}` and
  `α_w = -(w-10)(w-4)/48`: the specialised coefficient formulas, all the sign analysis, the
  boundary estimate, the base case `F̃₁₀ = (1/360)E₄X_{6,1}`, and the induction itself.  Its
  conclusions `ftildePos` and `ftildeBoundary` take the recurrence and the vanishing order and
  normalisation of `F_w` as explicit hypotheses.
* `PolynomialModel` works in `ℝ[E₂,E₄,E₆]`, and discharges all of those hypotheses.  It has to:
  their derivation needs `δ = ∂/∂E₂`, which is not an operator on `q`-expansions and so cannot even
  be stated on the first layer.  The `F_w` family is *defined* here by its recurrence, making
  `F̃_{w-2} := δF_w` an honest definition rather than a hypothesis; `delta_fStep` applies `δ` to
  that definition, which is where the paper's collapse
  `(1/6)∂_wF_w + (1/6)∂_{w-2}F_w = (1/3)∂_{w-1}F_w` happens; and `qexp` transports the resulting
  polynomial identity to `ℝ⟦X⟧`, landing exactly on `ftildeStep`.

In `QExpansion` weights are indexed by `N : ℕ` with `w = 4N + 12`, so that `w/4 - 3 = N`,
`w/4 - 2 = N + 1` and `w/4 - 1 = N + 2`; this keeps every index a genuine natural number.
`PolynomialModel` instead indexes by the weight itself: `fFam N` is the paper's `F_{4N}`, so that
`fFam 2` is `F₈`, `fFam 3` is `F₁₂`, and the statements here can be read directly against the
paper.  `F₀` and `F₄` do not exist and are set to zero.

## Main results

* `UncertaintyPrinciple.ftildeStep_pos` and `ftildeStep_boundary`: one induction step.
* `UncertaintyPrinciple.ftildePos` and `ftildeBoundary`: the induction, with the properties of
  `F_w` as hypotheses.
* `UncertaintyPrinciple.quartic_nonneg`: `2w⁴ - 77w³ + 1018w² - 4312w + 4800 ≥ 0` for `w ≥ 12`,
  the inequality controlling the boundary coefficient.
* `UncertaintyPrinciple.delta_fStep` and `qexp_delta_fStep`: the recurrence for `F̃`, in the
  polynomial model and on `q`-expansions.
* `UncertaintyPrinciple.mldeF`: the third-order equation `L_{3,w-2}^{((w-4)/4,0)}F_w = 0`, proved by
  the intertwining criterion from an explicit check on `F₈`.
* `UncertaintyPrinciple.coeff_fSeries_eq_zero` and `coeff_fSeries_eq_one`: the vanishing order and
  the normalisation of `F_w`.
* `UncertaintyPrinciple.coeff_ftildeSeries_pos` and `coeff_ftildeSeries_boundary`: the conclusion,
  with every hypothesis discharged.

Only the first layer is axiom-free.  The second uses the Ramanujan axioms of
`DifferentialOperators/Ramanujan.lean`, since `qexp` is what turns `DE₂, DE₄, DE₆` back into
polynomials in `E₂, E₄, E₆`.
-/

open Finset PowerSeries

namespace UncertaintyPrinciple

noncomputable section

section QExpansion

open ArithmeticFunction KanekoZagier
open scoped sigma

/-! ### The operators and the recurrence step -/

/-- `α_w = -(w-10)(w-4)/48`, the parameter for which `𝒮_w = -L_{2,w-2}^{α_w}`. -/
def alphaF (w : ℝ) : ℝ := -((w - 10) * (w - 4)) / 48

/-- `𝒮_w = (w-6)(w-5)/36 E₄ - ∂_w∂_{w-2} = -L_{2,w-2}^{α_w}`. -/
def SF (w : ℝ) (f : ℝ⟦X⟧) : ℝ⟦X⟧ := -L2 (w - 2) (alphaF w) f

/-- The positive scalar `c_w = 3(w-4)w / (16(w-10)(w-5)(w-3)(w+2))` in the recurrence. -/
def cF (w : ℝ) : ℝ := 3 * (w - 4) * w / (16 * (w - 10) * (w - 5) * (w - 3) * (w + 2))

/-- The right-hand side of the recurrence for `F̃`: `c_w(𝒮_w F̃_{w-2} - (1/3)∂_{w-1}F_w)`. -/
def ftildeStep (w : ℝ) (F Ft : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  cF w • (SF w Ft - (1 / 3 : ℝ) • serreD (w - 1) F)

/-! ### The specialised coefficient functions -/

/-- The diagonal coefficient of `L_{2,w-2}^{α_w}`, factored. -/
lemma kappa2_F (w : ℝ) (n : ℕ) :
    kappa2 (w - 2) (alphaF w) n = (12 * n + w - 10) * (4 * n - w + 4) / 48 := by
  rw [kappa2, alphaF]; ring

/-- The lower triangular coefficient of `L_{2,w-2}^{α_w}`, in the paper's form. -/
lemma K2_F (w : ℝ) (n j : ℕ) :
    K2 (w - 2) (alphaF w) n j
      = -2 * (w - 1) * (w * ((n : ℝ) - j) - 2 * n) * (σ 1 (n - j) : ℝ)
        - 5 * (w - 10) * (w - 4) * (σ 3 (n - j) : ℝ) := by
  rw [K2, alphaF]; ring

private lemma denomF_pos {w : ℝ} (hw : 12 ≤ w) :
    0 < 16 * (w - 10) * (w - 5) * (w - 3) * (w + 2) :=
  mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith))
    (by linarith)) (by linarith)

lemma cF_pos {w : ℝ} (hw : 12 ≤ w) : 0 < cF w :=
  div_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)) (denomF_pos hw)

/-! ### Signs on the interior range -/

/-- On the range `1 ≤ n ≤ w/4 - 2` the diagonal coefficient is negative. -/
lemma kappa2_F_neg {w : ℝ} {n : ℕ} (hw : 12 ≤ w) (hn1 : 1 ≤ n) (hn : 4 * (n : ℝ) ≤ w - 8) :
    kappa2 (w - 2) (alphaF w) n < 0 := by
  have hn1' : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  rw [kappa2_F]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (by linarith) (by linarith)) (by norm_num)

/-- On the range `1 ≤ j < n ≤ w/4 - 1` the lower triangular coefficient is negative. -/
lemma K2_F_neg {w : ℝ} {n j : ℕ} (hw : 12 ≤ w) (hj : j < n) (hn : 4 * (n : ℝ) ≤ w - 4) :
    K2 (w - 2) (alphaF w) n j < 0 := by
  have hnj : 1 ≤ n - j := by omega
  have hgap : 1 ≤ (n : ℝ) - j := by
    rw [← Nat.cast_sub hj.le]; exact_mod_cast hnj
  have hn' : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [K2_F]
  have t1 : 0 < 2 * (w - 1) * (w * ((n : ℝ) - j) - 2 * n) * (σ 1 (n - j) : ℝ) :=
    mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by nlinarith)) (sigma_pos hnj)
  have t2 : 0 < 5 * (w - 10) * (w - 4) * (σ 3 (n - j) : ℝ) :=
    mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)) (sigma_pos hnj)
  linarith

/-! ### The boundary estimate -/

/-- `2w⁴ - 77w³ + 1018w² - 4312w + 4800 ≥ 0` for `w ≥ 12`.  Writing `u = w - 12 ≥ 0` the quartic
becomes `2u⁴ + u(19u² - 26u + 680) + 8064`, and the inner quadratic has negative discriminant. -/
theorem quartic_nonneg {w : ℝ} (hw : 12 ≤ w) :
    0 ≤ 2 * w ^ 4 - 77 * w ^ 3 + 1018 * w ^ 2 - 4312 * w + 4800 := by
  have hu : 0 ≤ w - 12 := by linarith
  have hq : 0 ≤ 19 * (w - 12) ^ 2 - 26 * (w - 12) + 680 := by
    nlinarith [sq_nonneg (19 * (w - 12) - 13)]
  nlinarith [mul_nonneg hu hq, pow_nonneg hu 4]

/-- The value of `K_{2,w-2}^{α_w}` at the boundary pair `(w/4-1, w/4-2)`, whose indices differ by
`1`, so that both divisor sums are `1`. -/
lemma K2_F_boundary {N : ℕ} {w : ℝ} (hw : w = 4 * N + 12) :
    K2 (w - 2) (alphaF w) (N + 2) (N + 1) = -(6 * w ^ 2 - 67 * w + 196) := by
  have h1 : (σ 1 1 : ℝ) = 1 := by norm_num
  have h3 : (σ 3 1 : ℝ) = 1 := by norm_num
  rw [K2_F, show N + 2 - (N + 1) = 1 by omega, h1, h3, hw]
  push_cast
  ring

/-- The paper's boundary computation: after substituting `ã_{w/4-2} ≥ 1/360`, what survives is
`(w-6)(w-4)w(2w-17) / (640(w-10)(w-5)(w-3)(w+2))`, which is again at least `1/360`. -/
theorem boundary_bound {w : ℝ} (hw : 12 ≤ w) :
    1 / 360 ≤ cF w * ((6 * w ^ 2 - 67 * w + 196) / 360 - (2 * w - 11) / 36) := by
  rw [cF, div_mul_eq_mul_div, le_div_iff₀ (denomF_pos hw)]
  nlinarith [quartic_nonneg hw]

/-! ### Coefficients of the recurrence step -/

lemma coeff_ftildeStep (w : ℝ) (F Ft : ℝ⟦X⟧) (n : ℕ) :
    coeff n (ftildeStep w F Ft)
      = cF w * (-(kappa2 (w - 2) (alphaF w) n * coeff n Ft
            + ∑ j ∈ range n, K2 (w - 2) (alphaF w) n j * coeff j Ft)
          - 1 / 3 * ((n : ℝ) * coeff n F
            - (w - 1) / 12 * (coeff n F
              - 24 * ∑ j ∈ range n, (σ 1 (n - j) : ℝ) * coeff j F))) := by
  rw [ftildeStep, PowerSeries.coeff_smul, smul_eq_mul, map_sub, PowerSeries.coeff_smul,
    smul_eq_mul, SF, map_neg, coeff_L2, coeff_serreD]

/-! ### One induction step, interior range -/

private lemma weight_ge {N : ℕ} {w : ℝ} (hw : w = 4 * N + 12) : 12 ≤ w := by
  rw [hw]; have : 0 ≤ (N : ℝ) := Nat.cast_nonneg N; linarith

/-- The `K`-sum is nonpositive on the range where every coefficient of `F̃` is known positive. -/
private lemma K_sum_nonpos {N : ℕ} {w : ℝ} (hw : w = 4 * N + 12) {Ft : ℝ⟦X⟧}
    (hFt0 : coeff 0 Ft = 0) (hpos : ∀ j, 1 ≤ j → j ≤ N + 1 → 0 < coeff j Ft)
    {n m : ℕ} (hn : n ≤ N + 2) (hm : m ≤ n) :
    ∑ j ∈ range m, K2 (w - 2) (alphaF w) n j * coeff j Ft ≤ 0 := by
  refine Finset.sum_nonpos fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · rw [hFt0, mul_zero]
  · refine mul_nonpos_of_nonpos_of_nonneg (K2_F_neg (weight_ge hw) (by omega) ?_).le
      (hpos j hj1 (by omega)).le
    rw [hw]
    have : (n : ℝ) ≤ (N : ℝ) + 2 := by exact_mod_cast hn
    linarith

/-- **One induction step, interior range.**  On `1 ≤ n ≤ w/4 - 2` the contribution of `F_w`
vanishes, and what is left is a positive combination of the inductive hypotheses. -/
theorem ftildeStep_pos {N : ℕ} {w : ℝ} (hw : w = 4 * N + 12) {F Ft : ℝ⟦X⟧}
    (hF0 : ∀ k, k ≤ N + 1 → coeff k F = 0) (hFt0 : coeff 0 Ft = 0)
    (hpos : ∀ j, 1 ≤ j → j ≤ N + 1 → 0 < coeff j Ft)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ N + 1) : 0 < coeff n (ftildeStep w F Ft) := by
  have hnR : (n : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hn
  have hFsum : ∑ j ∈ range n, (σ 1 (n - j) : ℝ) * coeff j F = 0 :=
    Finset.sum_eq_zero fun j hj ↦ by
      rw [Finset.mem_range] at hj; rw [hF0 j (by omega), mul_zero]
  have hval : coeff n (ftildeStep w F Ft)
      = cF w * (-(kappa2 (w - 2) (alphaF w) n * coeff n Ft
          + ∑ j ∈ range n, K2 (w - 2) (alphaF w) n j * coeff j Ft)) := by
    rw [coeff_ftildeStep, hF0 n hn, hFsum]; ring
  have hkap : kappa2 (w - 2) (alphaF w) n * coeff n Ft < 0 :=
    mul_neg_of_neg_of_pos
      (kappa2_F_neg (weight_ge hw) hn1 (by rw [hw]; linarith)) (hpos n hn1 (by omega))
  rw [hval]
  exact mul_pos (cF_pos (weight_ge hw))
    (by linarith [K_sum_nonpos hw hFt0 hpos (n := n) (m := n) (by omega) le_rfl])

/-! ### One induction step, boundary index -/

/-- **One induction step, boundary index.**  At `n = w/4 - 1` the diagonal coefficient vanishes,
`F_w` contributes `-(2w-11)/36`, and the single surviving `K`-term carries the `1/360` forward. -/
theorem ftildeStep_boundary {N : ℕ} {w : ℝ} (hw : w = 4 * N + 12) {F Ft : ℝ⟦X⟧}
    (hF0 : ∀ k, k ≤ N + 1 → coeff k F = 0) (hF1 : coeff (N + 2) F = 1)
    (hFt0 : coeff 0 Ft = 0) (hpos : ∀ j, 1 ≤ j → j ≤ N + 1 → 0 < coeff j Ft)
    (hbdry : 1 / 360 ≤ coeff (N + 1) Ft) :
    1 / 360 ≤ coeff (N + 2) (ftildeStep w F Ft) := by
  have hw12 : 12 ≤ w := weight_ge hw
  have hNw : (N : ℝ) = (w - 12) / 4 := by rw [hw]; ring
  have hkap : kappa2 (w - 2) (alphaF w) (N + 2) = 0 := by
    rw [kappa2_F]; push_cast; rw [hNw]; ring
  have hFsum : ∑ j ∈ range (N + 2), (σ 1 (N + 2 - j) : ℝ) * coeff j F = 0 :=
    Finset.sum_eq_zero fun j hj ↦ by
      rw [Finset.mem_range] at hj; rw [hF0 j (by omega), mul_zero]
  have hval : coeff (N + 2) (ftildeStep w F Ft)
      = cF w * (-(∑ j ∈ range (N + 1), K2 (w - 2) (alphaF w) (N + 2) j * coeff j Ft)
          + (6 * w ^ 2 - 67 * w + 196) * coeff (N + 1) Ft - (2 * w - 11) / 36) := by
    rw [coeff_ftildeStep, hkap, hF1, hFsum, Finset.sum_range_succ, K2_F_boundary hw]
    push_cast
    rw [hNw]
    ring
  have hquad : 0 < 6 * w ^ 2 - 67 * w + 196 := by nlinarith [sq_nonneg (12 * w - 67)]
  have hhead := K_sum_nonpos hw hFt0 hpos (n := N + 2) (m := N + 1) le_rfl (by omega)
  rw [hval]
  calc 1 / 360 ≤ cF w * ((6 * w ^ 2 - 67 * w + 196) / 360 - (2 * w - 11) / 36) :=
        boundary_bound hw12
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (cF_pos hw12).le
        nlinarith [hhead, hbdry, hquad]

/-! ### The base case `F̃₁₀ = (1/360) E₄ X_{6,1}` -/

private lemma coeff_E₄_of_pos {m : ℕ} (hm : 1 ≤ m) : coeff m E₄ = 240 * (σ 3 m : ℝ) := by
  rw [E₄, map_add, PowerSeries.coeff_smul, smul_eq_mul, coeff_qSigma, PowerSeries.coeff_one,
    if_neg (by omega), zero_add]

private lemma coeff_E₄_nonneg (m : ℕ) : 0 ≤ coeff m E₄ := by
  rw [E₄, map_add, PowerSeries.coeff_smul, smul_eq_mul, coeff_qSigma, PowerSeries.coeff_one]
  split_ifs <;> positivity

/-- `F̃₁₀ = (1/360)E₄X_{6,1}`, where `X_{6,1} = ∑_{n ≥ 1} nσ₃(n)qⁿ = E₄'/240`. -/
def ftilde₁₀ : ℝ⟦X⟧ := (1 / 86400 : ℝ) • (E₄ * D E₄)

@[simp]
lemma coeff_ftilde₁₀_zero : coeff 0 ftilde₁₀ = 0 := by
  rw [ftilde₁₀, PowerSeries.coeff_smul, smul_eq_mul, coeff_E₄_mul]
  simp

lemma coeff_ftilde₁₀_one : coeff 1 ftilde₁₀ = 1 / 360 := by
  rw [ftilde₁₀, PowerSeries.coeff_smul, smul_eq_mul, coeff_E₄_mul, coeff_D,
    coeff_E₄_of_pos le_rfl]
  norm_num

/-- `F̃₁₀` is completely positive: every Fourier coefficient of index `≥ 1` is positive. -/
theorem ftilde₁₀_pos {n : ℕ} (hn : 1 ≤ n) : 0 < coeff n ftilde₁₀ := by
  rw [ftilde₁₀, PowerSeries.coeff_smul, smul_eq_mul, coeff_E₄_mul, coeff_D, coeff_E₄_of_pos hn]
  have hsum : 0 ≤ ∑ j ∈ range n, (σ 3 (n - j) : ℝ) * coeff j (D E₄) :=
    Finset.sum_nonneg fun j _ ↦ by
      rw [coeff_D]
      have := coeff_E₄_nonneg j
      positivity
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [one_le_sigma (k := 3) hn]

/-! ### The induction -/

private lemma ftilde_induction {F Ft : ℕ → ℝ⟦X⟧} (hbase : Ft 0 = ftilde₁₀)
    (hrec : ∀ N, Ft (N + 1) = ftildeStep (4 * (N : ℝ) + 12) (F N) (Ft N))
    (hF0 : ∀ N k, k ≤ N + 1 → coeff k (F N) = 0) (hF1 : ∀ N, coeff (N + 2) (F N) = 1) (N : ℕ) :
    coeff 0 (Ft N) = 0 ∧ (∀ j, 1 ≤ j → j ≤ N + 1 → 0 < coeff j (Ft N))
      ∧ 1 / 360 ≤ coeff (N + 1) (Ft N) := by
  induction N with
  | zero =>
    exact ⟨by simp [hbase], fun j hj1 _ ↦ hbase ▸ ftilde₁₀_pos hj1,
      by rw [hbase, coeff_ftilde₁₀_one]⟩
  | succ N ih =>
    obtain ⟨hcusp, hpos, hbdry⟩ := ih
    have hstepPos : ∀ j, 1 ≤ j → j ≤ N + 1 → 0 < coeff j (Ft (N + 1)) := fun j hj1 hj ↦ by
      rw [hrec N]; exact ftildeStep_pos rfl (hF0 N) hcusp hpos hj1 hj
    have hstepBdry : 1 / 360 ≤ coeff (N + 2) (Ft (N + 1)) := by
      rw [hrec N]; exact ftildeStep_boundary rfl (hF0 N) (hF1 N) hcusp hpos hbdry
    refine ⟨?_, fun j hj1 hj ↦ ?_, hstepBdry⟩
    · rw [hrec N, coeff_ftildeStep, hcusp, hF0 N 0 (by omega)]; simp
    · obtain hlt | rfl : j < N + 2 ∨ j = N + 2 := by omega
      · exact hstepPos j hj1 (by omega)
      · linarith [hstepBdry]

/-- **Positivity of the interior coefficients.**  For `w = 4N + 12`, every Fourier coefficient
`ã_j` of `F̃_{w-2}` with `1 ≤ j ≤ w/4 - 3 = N` is positive. -/
theorem ftildePos {F Ft : ℕ → ℝ⟦X⟧} (hbase : Ft 0 = ftilde₁₀)
    (hrec : ∀ N, Ft (N + 1) = ftildeStep (4 * (N : ℝ) + 12) (F N) (Ft N))
    (hF0 : ∀ N k, k ≤ N + 1 → coeff k (F N) = 0) (hF1 : ∀ N, coeff (N + 2) (F N) = 1)
    (N j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ N + 1) : 0 < coeff j (Ft N) :=
  (ftilde_induction hbase hrec hF0 hF1 N).2.1 j hj1 hj

/-- **The boundary coefficient.**  For `w = 4N + 12`, the coefficient `ã_{w/4-2} = ã_{N+1}` of
`F̃_{w-2}` is at least `1/360`. -/
theorem ftildeBoundary {F Ft : ℕ → ℝ⟦X⟧} (hbase : Ft 0 = ftilde₁₀)
    (hrec : ∀ N, Ft (N + 1) = ftildeStep (4 * (N : ℝ) + 12) (F N) (Ft N))
    (hF0 : ∀ N k, k ≤ N + 1 → coeff k (F N) = 0) (hF1 : ∀ N, coeff (N + 2) (F N) = 1)
    (N : ℕ) : 1 / 360 ≤ coeff (N + 1) (Ft N) :=
  (ftilde_induction hbase hrec hF0 hF1 N).2.2

/-- The hypotheses of `ftildePos` and `ftildeBoundary` are satisfiable, so neither statement is
vacuous: any family of `F`'s with the right vanishing order will do, and `Ft` is then determined
by the recurrence. -/
example : ∃ F Ft : ℕ → ℝ⟦X⟧, Ft 0 = ftilde₁₀ ∧
    (∀ N, Ft (N + 1) = ftildeStep (4 * (N : ℝ) + 12) (F N) (Ft N)) ∧
    (∀ N k, k ≤ N + 1 → coeff k (F N) = 0) ∧ (∀ N, coeff (N + 2) (F N) = 1) :=
  ⟨fun N ↦ X ^ (N + 2),
   fun N ↦ Nat.rec ftilde₁₀ (fun n ih ↦ ftildeStep (4 * (n : ℝ) + 12) (X ^ (n + 2)) ih) N,
   rfl, fun _ ↦ rfl,
   fun _ _ hk ↦ by rw [PowerSeries.coeff_X_pow]; exact if_neg (by omega),
   fun _ ↦ by rw [PowerSeries.coeff_X_pow]; exact if_pos rfl⟩

end QExpansion

section PolynomialModel

open QuasiModular

/-! ### The operators and the recurrence step, polynomially -/

/-- `𝒮_w = ((w-6)(w-5)/36)E₄ - ∂_w∂_{w-2}` on the polynomial model. -/
def SFp (w : ℝ) (G : QM) : QM :=
  ((w - 6) * (w - 5) / 36 : ℝ) • (E₄ * G) - serreD w (serreD (w - 2) G)

/-- The right-hand side of the recurrence defining `F_{w+4}` from `F_w`. -/
def fStep (w : ℝ) (Fw : QM) : QM := cF w • SFp w Fw

lemma qexp_SFp (w : ℝ) (G : QM) : qexp (SFp w G) = SF w (qexp G) := by
  rw [SFp, SF, KanekoZagier.L2_eq_serre, KanekoZagier.serreDIter_two,
    show w - 2 + 2 = w by ring, alphaF, map_sub, map_smul, map_mul, qexp_E₄, qexp_serreD,
    qexp_serreD]
  module

lemma hasWeight_SFp {w : ℝ} {G : QM} (h : HasWeight G w) : HasWeight (SFp w G) (w + 4) :=
  HasWeight.sub (HasWeight.congr_weight ((hasWeight_E₄.mul h).smul _) (by ring))
    (HasWeight.congr_weight (hasWeight_serreD w (hasWeight_serreD (w - 2) h)) (by ring))

lemma hasWeight_fStep {w : ℝ} {G : QM} (h : HasWeight G w) : HasWeight (fStep w G) (w + 4) :=
  (hasWeight_SFp h).smul _

/-! ### Applying `δ` -/

/-- **The recurrence for `F̃`.**  Applying `δ` to the defining recurrence of `F_w` produces it
for `F̃`.  The two uses of `delta_serreD` contribute `(1/6)∂_wF_w` and `(1/6)∂_{w-2}F_w`, which
combine into `(1/3)∂_{w-1}F_w`. -/
theorem delta_fStep {w : ℝ} {Fw : QM} (h : HasWeight Fw w) :
    delta (fStep w Fw) = cF w • (SFp w (delta Fw) - (1 / 3 : ℝ) • serreD (w - 1) Fw) := by
  rw [fStep, Derivation.map_smul, SFp, map_sub, Derivation.map_smul, Derivation.leibniz, delta_E₄,
    delta_serreD w (hasWeight_serreD (w - 2) h), delta_serreD (w - 2) h, serreD_add, serreD_smul,
    SFp, ← serreD_collapse w Fw, smul_zero, add_zero, smul_eq_mul]
  module

/-- The recurrence, transported to `q`-expansions: it lands exactly on `ftildeStep`. -/
theorem qexp_delta_fStep {w : ℝ} {Fw : QM} (h : HasWeight Fw w) :
    qexp (delta (fStep w Fw)) = ftildeStep w (qexp Fw) (qexp (delta Fw)) := by
  rw [delta_fStep h, ftildeStep, map_smul, map_sub, qexp_SFp, map_smul, qexp_serreD]

/-! ### The family and its base case -/

/-- `F₈ = (1/1728)(E₂²E₄ - 2E₂E₆ + E₄²)`. -/
def F₈ : QM := (1 / 1728 : ℝ) • (E₂ ^ 2 * E₄ - (2 : ℝ) • (E₂ * E₆) + E₄ ^ 2)

lemma hasWeight_F₈ : HasWeight F₈ 8 :=
  have h1 : HasWeight (E₂ ^ 2 * E₄) 8 := HasWeight.congr_weight
    ((HasWeight.pow hasWeight_E₂ 2).mul hasWeight_E₄) (by norm_num)
  have h2 : HasWeight ((2 : ℝ) • (E₂ * E₆)) 8 := HasWeight.smul _
    (HasWeight.congr_weight (hasWeight_E₂.mul hasWeight_E₆) (by norm_num))
  HasWeight.smul _ <| (h1.sub h2).add
    (HasWeight.congr_weight (HasWeight.pow hasWeight_E₄ 2) (by norm_num))

/-- `F₁₂ = (1/518400)(E₂²E₄² - 2E₂E₄E₆ + E₆²)`. -/
def F₁₂ : QM :=
  (1 / 518400 : ℝ) • (E₂ ^ 2 * E₄ ^ 2 - (2 : ℝ) • (E₂ * E₄ * E₆) + E₆ ^ 2)

lemma hasWeight_F₁₂ : HasWeight F₁₂ 12 :=
  have h1 : HasWeight (E₂ ^ 2 * E₄ ^ 2) 12 := HasWeight.congr_weight
    ((HasWeight.pow hasWeight_E₂ 2).mul (HasWeight.pow hasWeight_E₄ 2)) (by norm_num)
  have h2 : HasWeight ((2 : ℝ) • (E₂ * E₄ * E₆)) 12 := HasWeight.smul _
    (HasWeight.congr_weight ((hasWeight_E₂.mul hasWeight_E₄).mul hasWeight_E₆) (by norm_num))
  HasWeight.smul _ <| (h1.sub h2).add
    (HasWeight.congr_weight (HasWeight.pow hasWeight_E₆ 2) (by norm_num))

/-- **The base case, computed rather than assumed.**  `δF₁₂ = (1/259200)E₄(E₂E₄-E₆)`, and
Ramanujan's identity `E₂E₄-E₆ = 3E₄'` turns this into `(1/86400)E₄E₄' = (1/360)E₄X_{6,1}`, which is
the `ftilde₁₀` of the `QExpansion` section. -/
theorem qexp_delta_F₁₂ : qexp (delta F₁₂) = ftilde₁₀ := by
  simp only [F₁₂, ftilde₁₀, KanekoZagier.ramanujan_E₄, pow_succ, pow_zero, one_mul,
    Derivation.map_smul, map_add, map_sub, Derivation.leibniz, delta_E₂, delta_E₄, delta_E₆,
    smul_eq_mul, mul_zero, add_zero, zero_add, mul_one, mul_add, mul_sub, map_smul, map_mul,
    qexp_E₂, qexp_E₄, qexp_E₆, mul_smul_comm, smul_smul]
  simp only [mul_comm, mul_left_comm]
  module

-- The Serre-derivative chain of `F₈` is expanded one derivative at a time: doing all three in a
-- single `simp` call exceeds the default heartbeat budget.
private lemma serreD_F₈ : serreD 6 F₈ =
    (2 / 3456 : ℝ) • (E₂ * E₄ ^ 2) - (1 / 3456 : ℝ) • (E₂ ^ 2 * E₆)
      - (1 / 3456 : ℝ) • (E₄ * E₆) := by
  simp only [F₈, pow_succ, pow_zero, one_mul, serreD, Derivation.map_smul, map_sub, map_add,
    Derivation.leibniz, smul_eq_mul, D_E₂, D_E₄, D_E₆, smul_smul, smul_sub, smul_add,
    mul_smul_comm, mul_sub, mul_add]
  simp only [mul_comm, mul_left_comm]
  module

private lemma serreD_serreD_F₈ : serreD 8 (serreD 6 F₈) =
    (2 / 10368 : ℝ) • (E₂ ^ 2 * E₄ ^ 2) - (4 / 10368 : ℝ) • (E₂ * E₄ * E₆)
      + (1 / 10368 : ℝ) • E₄ ^ 3 + (1 / 10368 : ℝ) • E₆ ^ 2 := by
  rw [serreD_F₈]
  simp only [pow_succ, pow_zero, one_mul, serreD, Derivation.map_smul, map_sub,
    Derivation.leibniz, smul_eq_mul, D_E₂, D_E₄, D_E₆, smul_smul, smul_sub, smul_add,
    mul_smul_comm, mul_sub, mul_add]
  simp only [mul_comm, mul_left_comm]
  module

private lemma serreD_serreD_serreD_F₈ : serreD 10 (serreD 8 (serreD 6 F₈)) =
    (11 / 62208 : ℝ) • (E₂ * E₄ ^ 3) + (9 / 62208 : ℝ) • (E₂ * E₆ ^ 2)
      - (10 / 62208 : ℝ) • (E₂ ^ 2 * E₄ * E₆) - (10 / 62208 : ℝ) • (E₄ ^ 2 * E₆) := by
  rw [serreD_serreD_F₈]
  simp only [pow_succ, pow_zero, one_mul, serreD, Derivation.map_smul, map_sub, map_add,
    Derivation.leibniz, smul_eq_mul, D_E₂, D_E₄, D_E₆, smul_smul, smul_sub, smul_add,
    mul_smul_comm, mul_sub, mul_add]
  simp only [mul_comm, mul_left_comm]
  module

/-- The family `F_{4N}` of Feigenbaum--Grabner--Hardin, generated from `F₈` by the recurrence.

`F₀` and `F₄` are not part of the family; setting them to zero makes the index match the weight, so
that `fFam N` is `F_{4N}` and the statements below can be read directly against the paper. -/
def fFam : ℕ → QM
  | 0 => 0
  | 1 => 0
  | 2 => F₈
  | N + 3 => fStep (4 * ((N + 2 : ℕ) : ℝ)) (fFam (N + 2))

lemma hasWeight_fFam : ∀ N : ℕ, HasWeight (fFam N) (4 * N)
  | 0 => hasWeight_zero
  | 1 => hasWeight_zero
  | 2 => by norm_num; exact hasWeight_F₈
  | N + 3 => HasWeight.congr_weight (hasWeight_fStep (hasWeight_fFam (N + 2)))
      (by push_cast; ring)

private lemma fStep_F₈ : fStep 8 F₈ = F₁₂ := by
  rw [fStep, SFp, show (8 : ℝ) - 2 = 6 by norm_num, serreD_serreD_F₈, F₈, F₁₂, cF]
  norm_num
  simp only [smul_smul, smul_sub, smul_add, mul_smul_comm, mul_sub, mul_add,
    pow_succ, pow_zero, one_mul]
  simp only [mul_comm, mul_left_comm]
  module

/-- The recurrence carries `F₈` to `F₁₂`, so the family generated here agrees with the second
explicit form in the paper. -/
lemma fFam_three : fFam 3 = F₁₂ := by
  change fStep (4 * (((0 + 2 : ℕ) : ℝ))) (fFam 2) = F₁₂
  rw [show (4 : ℝ) * (((0 + 2 : ℕ) : ℝ)) = 8 by norm_num]
  exact fStep_F₈

/-- The `q`-expansion of `F̃`, i.e. of `δF_w`. -/
def ftildeSeries (N : ℕ) : ℝ⟦X⟧ := qexp (delta (fFam N))

/-- The `q`-expansion of `F_w`. -/
def fSeries (N : ℕ) : ℝ⟦X⟧ := qexp (fFam N)

/-- **The recurrence hypothesis of `ftildePos`, discharged.**  It holds from `F₈` on, that is for
`N ≥ 2`. -/
theorem ftildeSeries_succ {N : ℕ} (hN : 2 ≤ N) :
    ftildeSeries (N + 1) = ftildeStep (4 * (N : ℝ)) (fSeries N) (ftildeSeries N) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  change qexp (delta (fFam (M + 3))) = _
  rw [fFam, qexp_delta_fStep (hasWeight_fFam (M + 2))]
  rfl

/-- **The base case of `ftildePos`, discharged**: `F̃₁₀ = δF₁₂`. -/
theorem ftildeSeries_three : ftildeSeries 3 = ftilde₁₀ := by
  rw [ftildeSeries, fFam_three]; exact qexp_delta_F₁₂

/-! ### Vanishing order of `F_w`

The paper's `F_w` vanishes to order `⌊w/4⌋ - 1` at the cusp, so `fFam N`, of weight `4N`, vanishes
to order `N - 1`: its coefficients below index `N - 1` are zero and the one at `N - 1` is `1`. -/

lemma qexp_fStep (w : ℝ) (F : QM) : qexp (fStep w F) = cF w • SF w (qexp F) := by
  rw [fStep, map_smul, qexp_SFp]

lemma coeff_SF (w : ℝ) (f : ℝ⟦X⟧) (n : ℕ) :
    coeff n (SF w f) = -(KanekoZagier.kappa2 (w - 2) (alphaF w) n * coeff n f
      + ∑ j ∈ range n, KanekoZagier.K2 (w - 2) (alphaF w) n j * coeff j f) := by
  rw [SF, map_neg, KanekoZagier.coeff_L2]

/-- The diagonal coefficient vanishes at the cusp index `w/4 - 1`; this is what makes the vanishing
order of `F_w` increase by one at each step of the recurrence. -/
lemma kappa2_F_zero {N : ℕ} {w : ℝ} (hw : w = 4 * N + 8) :
    KanekoZagier.kappa2 (w - 2) (alphaF w) (N + 1) = 0 := by
  rw [kappa2_F, hw]; push_cast; ring

/-- `F₈ = E₄''/240`, so `F₈ = ∑_{n ≥ 1} n²σ₃(n)qⁿ`. -/
lemma F₈_eq : F₈ = (1 / 240 : ℝ) • D (D E₄) := by
  simp only [F₈, D_E₂, D_E₄, D_E₆, Derivation.map_smul, map_sub, Derivation.leibniz, smul_eq_mul,
    smul_smul, smul_sub, mul_smul_comm, mul_sub, pow_succ, pow_zero, one_mul]
  simp only [mul_comm, mul_left_comm]
  module

lemma coeff_qexp_F₈ {n : ℕ} (hn : 1 ≤ n) :
    coeff n (qexp F₈) = (n : ℝ) ^ 2 * (ArithmeticFunction.sigma 3 n : ℝ) := by
  rw [F₈_eq, map_smul, qexp_D, qexp_D, qexp_E₄, PowerSeries.coeff_smul, smul_eq_mul,
    KanekoZagier.coeff_D, KanekoZagier.coeff_D, coeff_E₄_of_pos hn]
  ring

@[simp] lemma coeff_qexp_F₈_zero : coeff 0 (qexp F₈) = 0 := by
  rw [F₈_eq, map_smul, qexp_D, PowerSeries.coeff_smul, smul_eq_mul, KanekoZagier.coeff_D]
  simp

/-- **The vanishing order of `F_w`**, proved rather than assumed. -/
theorem coeff_fSeries_eq_zero : ∀ N k : ℕ, k + 2 ≤ N → coeff k (fSeries N) = 0
  | 0, _, h => absurd h (by omega)
  | 1, _, h => absurd h (by omega)
  | 2, k, h => by
    obtain rfl : k = 0 := by omega
    exact coeff_qexp_F₈_zero
  | N + 3, k, h => by
    have ih : ∀ j, j + 2 ≤ N + 2 → coeff j (qexp (fFam (N + 2))) = 0 :=
      fun j hj ↦ coeff_fSeries_eq_zero (N + 2) j hj
    rw [fSeries, fFam, qexp_fStep, PowerSeries.coeff_smul, smul_eq_mul, coeff_SF,
      Finset.sum_eq_zero fun j hj ↦ by
        rw [Finset.mem_range] at hj; rw [ih j (by omega), mul_zero]]
    obtain hlt | rfl : k + 2 ≤ N + 2 ∨ k = N + 1 := by omega
    · rw [ih k hlt]; ring
    · rw [show (4 : ℝ) * ((N + 2 : ℕ) : ℝ) = 4 * (N : ℝ) + 8 by push_cast; ring,
        kappa2_F_zero rfl]
      ring

/-! ### The modular linear differential equation for `F_w`

The vanishing order above needed nothing but the recurrence.  The normalisation does: the
recurrence expresses the leading coefficient of `F_{w+4}` in terms of the *second* nonzero
coefficient of `F_w`, which the recurrence alone does not determine.  What determines it is the
third-order equation `L_{3,w-2}^{((w-4)/4,0)}F_w = 0` of the paper, which relates the coefficients
of a single `F_w`.

That equation propagates along the recurrence by the intertwining criterion: the triples
`(α,β,γ) = (w/4, 0, -(w-10)(w-4)/48)` and `(α',β',γ') = ((w-4)/4, 0, -w(w-10)/48)` satisfy the
four constraints, so `L_{3,w+2}` composed with the recurrence operator is the recurrence operator
composed with `L_{3,w-2}`, and an operator annihilating `F_w` annihilates `F_{w+4}`. -/

/-- The third-order Kaneko--Zagier operator on the polynomial model, in Serre form. -/
def L3p (k α β : ℝ) (G : QM) : QM :=
  serreD (k + 4) (serreD (k + 2) (serreD k G))
    + (α - (3 * k ^ 2 + 12 * k + 8) / 144) • (E₄ * serreD k G)
    + (β + k * α / 12 - k ^ 2 * (k + 3) / 864) • (E₆ * G)

lemma qexp_L3p (k α β : ℝ) (G : QM) :
    qexp (L3p k α β G) = KanekoZagier.L3 k α β (qexp G) := by
  rw [L3p, KanekoZagier.L3_eq_serre, KanekoZagier.serreDIter_three, KanekoZagier.serreDIter_two,
    map_add, map_add, map_smul, map_smul, map_mul, map_mul, qexp_E₄, qexp_E₆, qexp_serreD,
    qexp_serreD, qexp_serreD]

/-- The base case of the differential equation, checked on the explicit `F₈`. -/
lemma L3p_F₈ : L3p 6 1 0 F₈ = 0 := by
  rw [L3p, show (6 : ℝ) + 4 = 10 by norm_num, show (6 : ℝ) + 2 = 8 by norm_num,
    serreD_serreD_serreD_F₈, serreD_F₈, F₈]
  simp only [pow_succ, pow_zero, one_mul, smul_smul, smul_sub, smul_add,
    mul_smul_comm, mul_sub, mul_add, sub_mul, add_mul]
  simp only [mul_comm, mul_left_comm]
  module

lemma mldeF_zero : KanekoZagier.L3 6 1 0 (fSeries 2) = 0 := by
  rw [fSeries, show fFam 2 = F₈ from rfl, ← qexp_L3p, L3p_F₈, map_zero]

/-- The differential equation propagates along the recurrence, by the intertwining criterion. -/
lemma mldeF_step {w : ℝ} {f : ℝ⟦X⟧} (h : KanekoZagier.L3 (w - 2) ((w - 4) / 4) 0 f = 0) :
    KanekoZagier.L3 (w + 2) (w / 4) 0 (cF w • SF w f) = 0 := by
  rw [SF, smul_neg, ← neg_smul, KanekoZagier.L3_smul, show w + 2 = w - 2 + 4 by ring,
    KanekoZagier.L3_comp_L2_eq_L2_comp_L3 (w - 2) (w / 4) 0 (alphaF w) ((w - 4) / 4) 0
      (-(w * (w - 10)) / 48) ?_ ?_ ?_ ?_, h, KanekoZagier.L2_zero, smul_zero]
  all_goals
    simp only [KanekoZagier.shiftA, KanekoZagier.shiftB, KanekoZagier.shiftC,
      KanekoZagier.shiftA', KanekoZagier.shiftB', KanekoZagier.shiftC', alphaF]
    ring

/-- **The differential equation for `F_w`**, for every `w = 4N + 8`. -/
theorem mldeF (N : ℕ) :
    KanekoZagier.L3 (4 * (N : ℝ) + 6) ((4 * (N : ℝ) + 4) / 4) 0 (fSeries (N + 2)) = 0 := by
  induction N with
  | zero => simpa using mldeF_zero
  | succ N ih =>
    have := mldeF_step (w := 4 * (N : ℝ) + 8) (by
      rw [show 4 * (N : ℝ) + 8 - 2 = 4 * (N : ℝ) + 6 by ring,
        show (4 * (N : ℝ) + 8 - 4) / 4 = (4 * (N : ℝ) + 4) / 4 by ring]
      exact ih)
    rw [show 4 * (N : ℝ) + 8 + 2 = 4 * ((N : ℝ) + 1) + 6 by ring,
      show (4 * (N : ℝ) + 8) / 4 = (4 * ((N : ℝ) + 1) + 4) / 4 by ring] at this
    rw [fSeries, fFam, qexp_fStep,
      show (4 : ℝ) * ((N + 2 : ℕ) : ℝ) = 4 * (N : ℝ) + 8 by push_cast; ring]
    push_cast
    exact this

/-! ### The normalisation of `F_w`

At the index `w/4` the diagonal coefficient `κ₃` of the third-order equation is `(N+1)(N+2)`, which
is nonzero, so the equation determines the second nonzero coefficient of `F_w` from the first.
Feeding that value back into the recurrence produces `1` again, one index further along. -/

lemma kappa3_F (N : ℕ) :
    KanekoZagier.kappa3 (4 * (N : ℝ) + 6) ((4 * (N : ℝ) + 4) / 4) 0 (N + 2)
      = ((N : ℝ) + 1) * ((N : ℝ) + 2) := by
  rw [KanekoZagier.kappa3]; push_cast; ring

lemma K3_F (N : ℕ) :
    KanekoZagier.K3 (4 * (N : ℝ) + 6) ((4 * (N : ℝ) + 4) / 4) 0 (N + 2) (N + 1)
      = -8 * ((N : ℝ) ^ 3 + 3 * N ^ 2 + 14 * N + 9) := by
  rw [KanekoZagier.K3, show N + 2 - (N + 1) = 1 by omega]
  norm_num
  ring

lemma kappa2_F_cusp (N : ℕ) :
    KanekoZagier.kappa2 (4 * (N : ℝ) + 8 - 2) (alphaF (4 * (N : ℝ) + 8)) (N + 2)
      = (8 * (N : ℝ) + 11) / 6 := by
  rw [kappa2_F]; push_cast; ring

lemma K2_F_cusp (N : ℕ) :
    KanekoZagier.K2 (4 * (N : ℝ) + 8 - 2) (alphaF (4 * (N : ℝ) + 8)) (N + 2) (N + 1)
      = -4 * (24 * (N : ℝ) ^ 2 + 25 * N + 4) := by
  rw [K2_F, show N + 2 - (N + 1) = 1 by omega]
  norm_num
  ring

/-- The second nonzero coefficient of `F_{4N+8}`, read off from the third-order equation.  This is
the `b_{w/4}` of the paper. -/
lemma coeff_fSeries_succ {N : ℕ} (h : coeff (N + 1) (fSeries (N + 2)) = 1) :
    coeff (N + 2) (fSeries (N + 2))
      = 8 * ((N : ℝ) ^ 3 + 3 * N ^ 2 + 14 * N + 9) / (((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
  have key := congrArg (coeff (N + 2)) (mldeF N)
  rw [KanekoZagier.coeff_L3, map_zero, kappa3_F,
    Finset.sum_eq_single (N + 1)
      (fun j hj hne ↦ by
        rw [coeff_fSeries_eq_zero (N + 2) j (by rw [Finset.mem_range] at hj; omega), mul_zero])
      (fun hj ↦ absurd (Finset.mem_range.2 (by omega)) hj),
    K3_F, h, mul_one] at key
  rw [eq_div_iff (by positivity)]
  linarith [key]

/-- The recurrence turns the normalisation at index `N+1` into the normalisation at index `N+2`:
this is where `b_{w/4}` cancels against the two coefficient functions of `𝒮_w`. -/
private lemma cusp_normalization (N : ℕ) :
    cF (4 * (N : ℝ) + 8) * -((8 * (N : ℝ) + 11) / 6
        * (8 * ((N : ℝ) ^ 3 + 3 * N ^ 2 + 14 * N + 9) / (((N : ℝ) + 1) * ((N : ℝ) + 2)))
      + -4 * (24 * (N : ℝ) ^ 2 + 25 * N + 4)) = 1 := by
  have h0 : (0 : ℝ) ≤ N := N.cast_nonneg
  have e1 : ((N : ℝ) + 1) ≠ 0 := by positivity
  have e2 : ((N : ℝ) + 2) ≠ 0 := by positivity
  have e4 : 4 * (N : ℝ) + 8 - 10 ≠ 0 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · norm_num
    · have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      exact ne_of_gt (by linarith)
  have e5 : 4 * (N : ℝ) + 8 - 5 ≠ 0 := ne_of_gt (by linarith)
  have e6 : 4 * (N : ℝ) + 8 - 3 ≠ 0 := ne_of_gt (by linarith)
  have e7 : 4 * (N : ℝ) + 8 + 2 ≠ 0 := ne_of_gt (by linarith)
  rw [cF]
  field_simp
  ring

/-- **The normalisation of `F_w`**, proved rather than assumed: the leading coefficient of
`F_{4N+8}`, at index `N+1`, is `1`. -/
theorem coeff_fSeries_eq_one (N : ℕ) : coeff (N + 1) (fSeries (N + 2)) = 1 := by
  induction N with
  | zero => simpa using coeff_qexp_F₈ (n := 1) le_rfl
  | succ N ih =>
    have hz : ∀ j, j + 2 ≤ N + 2 → coeff j (qexp (fFam (N + 2))) = 0 :=
      fun j hj ↦ coeff_fSeries_eq_zero (N + 2) j hj
    have h2 : coeff (N + 1) (qexp (fFam (N + 2))) = 1 := ih
    have hb : coeff (N + 2) (qexp (fFam (N + 2)))
        = 8 * ((N : ℝ) ^ 3 + 3 * N ^ 2 + 14 * N + 9) / (((N : ℝ) + 1) * ((N : ℝ) + 2)) :=
      coeff_fSeries_succ ih
    change coeff (N + 2) (fSeries (N + 3)) = 1
    rw [fSeries, fFam, qexp_fStep,
      show (4 : ℝ) * ((N + 2 : ℕ) : ℝ) = 4 * (N : ℝ) + 8 by push_cast; ring,
      PowerSeries.coeff_smul, smul_eq_mul, coeff_SF,
      Finset.sum_eq_single (N + 1)
        (fun j hj hne ↦ by rw [hz j (by rw [Finset.mem_range] at hj; omega), mul_zero])
        (fun hj ↦ absurd (Finset.mem_range.2 (by omega)) hj),
      hb, h2, mul_one, kappa2_F_cusp, K2_F_cusp, cusp_normalization]

/-! ### The conclusion -/

/-- **Positivity of the Fourier coefficients of `F̃_{w-2}`**, with every hypothesis of `ftildePos`
discharged: the recurrence, the base case, the vanishing order and the normalisation are all proved
from the definition of the `F_w` family in the polynomial model.  The weight is `w = 4(N+3)`, that
is `w ≥ 12`. -/
theorem coeff_ftildeSeries_pos (N j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ N + 1) :
    0 < coeff j (ftildeSeries (N + 3)) :=
  ftildePos (F := fun N ↦ fSeries (N + 3)) (Ft := fun N ↦ ftildeSeries (N + 3))
    ftildeSeries_three
    (fun N ↦ by
      rw [show (4 : ℝ) * (N : ℝ) + 12 = 4 * ((N + 3 : ℕ) : ℝ) by push_cast; ring]
      exact ftildeSeries_succ (by omega))
    (fun N k hk ↦ coeff_fSeries_eq_zero (N + 3) k (by omega))
    (fun N ↦ coeff_fSeries_eq_one (N + 1)) N j hj1 hj

/-- The boundary estimate, likewise. -/
theorem coeff_ftildeSeries_boundary (N : ℕ) : 1 / 360 ≤ coeff (N + 1) (ftildeSeries (N + 3)) :=
  ftildeBoundary (F := fun N ↦ fSeries (N + 3)) (Ft := fun N ↦ ftildeSeries (N + 3))
    ftildeSeries_three
    (fun N ↦ by
      rw [show (4 : ℝ) * (N : ℝ) + 12 = 4 * ((N + 3 : ℕ) : ℝ) by push_cast; ring]
      exact ftildeSeries_succ (by omega))
    (fun N k hk ↦ coeff_fSeries_eq_zero (N + 3) k (by omega))
    (fun N ↦ coeff_fSeries_eq_one (N + 1)) N

end PolynomialModel

end

end UncertaintyPrinciple
