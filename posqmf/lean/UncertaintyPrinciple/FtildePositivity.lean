import posqmf.lean.DifferentialOperators.Coefficients
import posqmf.lean.SigmaBounds

/-!
# Positivity of the Fourier coefficients of `F̃_{w-2}`

In *Positive quasimodular forms and the sign uncertainty principle*, the value of `M_{d,+}` at the
origin is `-6 b_{0,+}/π`, and `b_{0,+}` is a positive combination of the Fourier coefficients
`ã_j` of `F̃_{w-2}` for `1 ≤ j ≤ n_{d,+}`.  Nonpositivity of `M_{d,+}(0)` therefore reduces to

`ã_j > 0` for `1 ≤ j ≤ w/4 - 3`,  and  `ã_{w/4-2} ≥ 1/360`,

for every `w ≡ 0 (mod 4)` with `w ≥ 12`, which is what this file proves.

## What is and is not formalized

The paper's proof runs an induction on `w` in steps of `4`, driven by the recurrence

`F̃_{w+2} = c_w (𝒮_w F̃_{w-2} - (1/3) ∂_{w-1} F_w)`,  `𝒮_w = -L_{2,w-2}^{α_w}`,
`α_w = -(w-10)(w-4)/48`.

Everything downstream of that recurrence is proved here, unconditionally: the specialised
coefficient formulas, all the sign analysis, the boundary estimate, the base case, and the
induction itself.  Two inputs are taken as hypotheses, exactly as the paper takes them:

* the recurrence itself, whose derivation needs the operator `δ = ∂/∂E₂` on `ℝ[E₂,E₄,E₆]` and the
  `sl₂`-relation `δ(∂_k G) = ∂_k(δ G) + ((w-k)/12) G`.  `δ` is not an operator on `q`-expansions,
  so it cannot even be stated in the present setting;
* the normalisation of `F_w`, namely `b_k = 0` for `k < w/4 - 1` and `b_{w/4-1} = 1`, which is
  Feigenbaum--Grabner--Hardin's.

Both appear as explicit hypotheses of `ftildePos` and `ftildeBoundary`, so nothing is assumed
silently.  In particular no axiom of `Ramanujan.lean` is used: the whole argument rides on
`coeff_L2`, which is itself unconditional.

## Main results

* `UncertaintyPrinciple.ftildeStep_pos` and `ftildeStep_boundary`: one induction step.
* `UncertaintyPrinciple.ftildePos` and `ftildeBoundary`: the conclusion for every `w = 4N + 12`.
* `UncertaintyPrinciple.quartic_nonneg`: `2w⁴ - 77w³ + 1018w² - 4312w + 4800 ≥ 0` for `w ≥ 12`,
  the inequality controlling the boundary coefficient.

Weights are indexed by `N : ℕ` with `w = 4N + 12`, so that `w/4 - 3 = N`, `w/4 - 2 = N + 1` and
`w/4 - 1 = N + 2`; this keeps every index a genuine natural number.
-/

open ArithmeticFunction Finset KanekoZagier PowerSeries
open scoped sigma

namespace UncertaintyPrinciple

noncomputable section

/-! ### The operator `𝒮_w` and the recurrence step -/

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

private lemma denom_pos {w : ℝ} (hw : 12 ≤ w) :
    0 < 16 * (w - 10) * (w - 5) * (w - 3) * (w + 2) :=
  mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith))
    (by linarith)) (by linarith)

lemma cF_pos {w : ℝ} (hw : 12 ≤ w) : 0 < cF w :=
  div_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)) (denom_pos hw)

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
  rw [cF, div_mul_eq_mul_div, le_div_iff₀ (denom_pos hw)]
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

/-! ### One induction step -/

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

private lemma coeff_E4_of_pos {m : ℕ} (hm : 1 ≤ m) : coeff m E4 = 240 * (σ 3 m : ℝ) := by
  rw [E4, map_add, PowerSeries.coeff_smul, smul_eq_mul, coeff_qSigma, PowerSeries.coeff_one,
    if_neg (by omega), zero_add]

private lemma coeff_E4_nonneg (m : ℕ) : 0 ≤ coeff m E4 := by
  rw [E4, map_add, PowerSeries.coeff_smul, smul_eq_mul, coeff_qSigma, PowerSeries.coeff_one]
  split_ifs <;> positivity

/-- `F̃₁₀ = (1/360)E₄X_{6,1}`, where `X_{6,1} = ∑_{n ≥ 1} nσ₃(n)qⁿ = E₄'/240`. -/
def ftilde10 : ℝ⟦X⟧ := (1 / 86400 : ℝ) • (E4 * D E4)

@[simp]
lemma coeff_ftilde10_zero : coeff 0 ftilde10 = 0 := by
  rw [ftilde10, PowerSeries.coeff_smul, smul_eq_mul, coeff_E4_mul]
  simp

lemma coeff_ftilde10_one : coeff 1 ftilde10 = 1 / 360 := by
  rw [ftilde10, PowerSeries.coeff_smul, smul_eq_mul, coeff_E4_mul, coeff_D,
    coeff_E4_of_pos le_rfl]
  norm_num

/-- `F̃₁₀` is completely positive: every Fourier coefficient of index `≥ 1` is positive. -/
theorem ftilde10_pos {n : ℕ} (hn : 1 ≤ n) : 0 < coeff n ftilde10 := by
  rw [ftilde10, PowerSeries.coeff_smul, smul_eq_mul, coeff_E4_mul, coeff_D, coeff_E4_of_pos hn]
  have hsum : 0 ≤ ∑ j ∈ range n, (σ 3 (n - j) : ℝ) * coeff j (D E4) :=
    Finset.sum_nonneg fun j _ ↦ by
      rw [coeff_D]
      have := coeff_E4_nonneg j
      positivity
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [one_le_sigma (k := 3) hn]

/-! ### The induction -/

private lemma ftilde_induction {F Ft : ℕ → ℝ⟦X⟧} (hbase : Ft 0 = ftilde10)
    (hrec : ∀ N, Ft (N + 1) = ftildeStep (4 * (N : ℝ) + 12) (F N) (Ft N))
    (hF0 : ∀ N k, k ≤ N + 1 → coeff k (F N) = 0) (hF1 : ∀ N, coeff (N + 2) (F N) = 1) (N : ℕ) :
    coeff 0 (Ft N) = 0 ∧ (∀ j, 1 ≤ j → j ≤ N + 1 → 0 < coeff j (Ft N))
      ∧ 1 / 360 ≤ coeff (N + 1) (Ft N) := by
  induction N with
  | zero =>
    exact ⟨by simp [hbase], fun j hj1 _ ↦ hbase ▸ ftilde10_pos hj1,
      by rw [hbase, coeff_ftilde10_one]⟩
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
theorem ftildePos {F Ft : ℕ → ℝ⟦X⟧} (hbase : Ft 0 = ftilde10)
    (hrec : ∀ N, Ft (N + 1) = ftildeStep (4 * (N : ℝ) + 12) (F N) (Ft N))
    (hF0 : ∀ N k, k ≤ N + 1 → coeff k (F N) = 0) (hF1 : ∀ N, coeff (N + 2) (F N) = 1)
    (N j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ N + 1) : 0 < coeff j (Ft N) :=
  (ftilde_induction hbase hrec hF0 hF1 N).2.1 j hj1 hj

/-- **The boundary coefficient.**  For `w = 4N + 12`, the coefficient `ã_{w/4-2} = ã_{N+1}` of
`F̃_{w-2}` is at least `1/360`. -/
theorem ftildeBoundary {F Ft : ℕ → ℝ⟦X⟧} (hbase : Ft 0 = ftilde10)
    (hrec : ∀ N, Ft (N + 1) = ftildeStep (4 * (N : ℝ) + 12) (F N) (Ft N))
    (hF0 : ∀ N k, k ≤ N + 1 → coeff k (F N) = 0) (hF1 : ∀ N, coeff (N + 2) (F N) = 1)
    (N : ℕ) : 1 / 360 ≤ coeff (N + 1) (Ft N) :=
  (ftilde_induction hbase hrec hF0 hF1 N).2.2

/-- The hypotheses of `ftildePos` and `ftildeBoundary` are satisfiable, so neither statement is
vacuous: any family of `F`'s with the right vanishing order will do, and `Ft` is then determined
by the recurrence. -/
example : ∃ F Ft : ℕ → ℝ⟦X⟧, Ft 0 = ftilde10 ∧
    (∀ N, Ft (N + 1) = ftildeStep (4 * (N : ℝ) + 12) (F N) (Ft N)) ∧
    (∀ N k, k ≤ N + 1 → coeff k (F N) = 0) ∧ (∀ N, coeff (N + 2) (F N) = 1) :=
  ⟨fun N ↦ X ^ (N + 2),
   fun N ↦ Nat.rec ftilde10 (fun n ih ↦ ftildeStep (4 * (n : ℝ) + 12) (X ^ (n + 2)) ih) N,
   rfl, fun _ ↦ rfl,
   fun _ _ hk ↦ by rw [PowerSeries.coeff_X_pow]; exact if_neg (by omega),
   fun _ ↦ by rw [PowerSeries.coeff_X_pow]; exact if_pos rfl⟩

end

end UncertaintyPrinciple
