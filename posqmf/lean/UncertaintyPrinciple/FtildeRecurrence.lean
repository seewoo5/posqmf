import posqmf.lean.DifferentialOperators.Intertwine
import posqmf.lean.DifferentialOperators.QuasiModular
import posqmf.lean.UncertaintyPrinciple.FtildePositivity

/-!
# The `F_w` family and the recurrence for `F̃_{w-2}`

`FtildePositivity.lean` proves the positivity of the coefficients of `F̃_{w-2}` *given* the
recurrence `F̃_{w+2} = c_w(𝒮_w F̃_{w-2} - (1/3)∂_{w-1}F_w)`, which it takes as a hypothesis because
its derivation needs `δ = ∂/∂E₂`, an operator on the polynomial model rather than on `q`-series.
`DifferentialOperators/QuasiModular.lean` now supplies `δ`, so this file discharges that
hypothesis.

This is where the two layers meet, and the division of labour is worth spelling out:

* the `F_w` family is *defined* in the polynomial model by the recurrence `eqn:poseig4`, so that
  recurrence is definitional and `F̃_{w-2} := δF_w` is an honest definition rather than a
  hypothesis;
* `delta_fStep` applies `δ` to that definition, using `QuasiModular.delta_serreD` twice; the
  paper's collapse `(1/6)∂_wF_w + (1/6)∂_{w-2}F_w = (1/3)∂_{w-1}F_w` happens here;
* `qexp_delta_fStep` transports the resulting polynomial identity to `ℝ⟦X⟧` along `qexp`, landing
  exactly on the `ftildeStep` of `FtildePositivity.lean`.

## Main results

* `UncertaintyPrinciple.delta_fStep`: **`lem:Ftilde_rec`** in the polynomial model.
* `UncertaintyPrinciple.qexp_delta_fStep`: the same identity on `q`-expansions.
* `UncertaintyPrinciple.qexp_delta_F12`: the base case `F̃₁₀ = (1/360)E₄X_{6,1}`, computed from the
  explicit `F₁₂` rather than assumed.
* `UncertaintyPrinciple.mlde`: the third-order equation `L_{3,w-2}^{((w-4)/4,0)}F_w = 0`, proved by
  the intertwining criterion from an explicit check on `F₁₂`.
* `UncertaintyPrinciple.coeff_fSeries_eq_zero` and `coeff_fSeries_eq_one`: the vanishing order and
  the normalisation of `F_w`.
* `UncertaintyPrinciple.coeff_ftildeSeries_pos`: positivity of the coefficients of `F̃`, with every
  hypothesis of `FtildePositivity.ftildePos` discharged.
-/

open Finset PowerSeries QuasiModular

namespace UncertaintyPrinciple

noncomputable section

/-! ### The operator `𝒮_w` and the recurrence step, polynomially -/

/-- `𝒮_w = ((w-6)(w-5)/36)E₄ - ∂_w∂_{w-2}` on the polynomial model. -/
def SFp (w : ℝ) (G : QM) : QM :=
  ((w - 6) * (w - 5) / 36 : ℝ) • (E4 * G) - serreD w (serreD (w - 2) G)

/-- The right-hand side of `eqn:poseig4`, defining `F_{w+4}` from `F_w`. -/
def fStep (w : ℝ) (Fw : QM) : QM := cF w • SFp w Fw

lemma qexp_SFp (w : ℝ) (G : QM) : qexp (SFp w G) = SF w (qexp G) := by
  rw [SFp, SF, KanekoZagier.L2_eq_serre, KanekoZagier.serreDIter_two,
    show w - 2 + 2 = w by ring, alphaF, map_sub, map_smul, map_mul, qexp_E4, qexp_serreD,
    qexp_serreD]
  module

lemma hasWeight_SFp {w : ℝ} {G : QM} (h : HasWeight G w) : HasWeight (SFp w G) (w + 4) :=
  HasWeight.sub (HasWeight.congr_weight ((hasWeight_E4.mul h).smul _) (by ring))
    (HasWeight.congr_weight (hasWeight_serreD w (hasWeight_serreD (w - 2) h)) (by ring))

lemma hasWeight_fStep {w : ℝ} {G : QM} (h : HasWeight G w) : HasWeight (fStep w G) (w + 4) :=
  (hasWeight_SFp h).smul _

/-! ### Applying `δ` -/

/-- **`lem:Ftilde_rec`.**  Applying `δ` to the defining recurrence of `F_w` produces the recurrence
for `F̃`.  The two uses of `delta_serreD` contribute `(1/6)∂_wF_w` and `(1/6)∂_{w-2}F_w`, which
combine into `(1/3)∂_{w-1}F_w`. -/
theorem delta_fStep {w : ℝ} {Fw : QM} (h : HasWeight Fw w) :
    delta (fStep w Fw) = cF w • (SFp w (delta Fw) - (1 / 3 : ℝ) • serreD (w - 1) Fw) := by
  have hinner : delta (serreD (w - 2) Fw)
      = serreD (w - 2) (delta Fw) + (1 / 6 : ℝ) • Fw := by
    rw [delta_serreD (w - 2) h]
    congr 2
    ring
  have houter : delta (serreD w (serreD (w - 2) Fw))
      = serreD w (delta (serreD (w - 2) Fw)) + (1 / 6 : ℝ) • serreD (w - 2) Fw := by
    rw [delta_serreD w (hasWeight_serreD (w - 2) h)]
    congr 2
    ring
  rw [fStep, Derivation.map_smul, SFp, map_sub, Derivation.map_smul, Derivation.leibniz,
    delta_E4, houter, hinner, serreD_add, serreD_smul, SFp, ← serreD_collapse w Fw]
  simp only [smul_eq_mul, mul_zero, add_zero]
  module

/-- The recurrence, transported to `q`-expansions: it lands exactly on `ftildeStep`. -/
theorem qexp_delta_fStep {w : ℝ} {Fw : QM} (h : HasWeight Fw w) :
    qexp (delta (fStep w Fw)) = ftildeStep w (qexp Fw) (qexp (delta Fw)) := by
  rw [delta_fStep h, ftildeStep, map_smul, map_sub, qexp_SFp, map_smul, qexp_serreD]

/-! ### The family and its base case -/

/-- `F₁₂ = (1/518400)(E₂²E₄² - 2E₂E₄E₆ + E₆²)`. -/
def F12 : QM :=
  (1 / 518400 : ℝ) • (E2 * E2 * E4 * E4 - (E2 * E4 * E6 + E2 * E4 * E6) + E6 * E6)

lemma hasWeight_F12 : HasWeight F12 12 :=
  have h1 : HasWeight (E2 * E2 * E4 * E4) 12 := HasWeight.congr_weight
    (((hasWeight_E2.mul hasWeight_E2).mul hasWeight_E4).mul hasWeight_E4) (by norm_num)
  have h2 : HasWeight (E2 * E4 * E6) 12 :=
    HasWeight.congr_weight ((hasWeight_E2.mul hasWeight_E4).mul hasWeight_E6) (by norm_num)
  have h3 : HasWeight (E6 * E6) 12 :=
    HasWeight.congr_weight (hasWeight_E6.mul hasWeight_E6) (by norm_num)
  HasWeight.smul _ ((h1.sub (h2.add h2)).add h3)

/-- **The base case, computed rather than assumed.**  `δF₁₂ = (1/259200)E₄(E₂E₄-E₆)`, and
Ramanujan's identity `E₂E₄-E₆ = 3E₄'` turns this into `(1/86400)E₄E₄' = (1/360)E₄X_{6,1}`, which is
the `ftilde10` of `FtildePositivity.lean`. -/
theorem qexp_delta_F12 : qexp (delta F12) = ftilde10 := by
  have key : delta (E2 * E2 * E4 * E4 - (E2 * E4 * E6 + E2 * E4 * E6) + E6 * E6)
      = E4 * (E2 * E4 - E6) + E4 * (E2 * E4 - E6) := by
    simp only [map_add, map_sub, Derivation.leibniz, delta_E2, delta_E4, delta_E6, smul_eq_mul,
      mul_zero, add_zero, zero_add, mul_one]
    ring
  rw [F12, Derivation.map_smul, key, ftilde10, KanekoZagier.ramanujan_E4]
  simp only [map_smul, map_add, map_mul, map_sub, qexp_E2, qexp_E4, qexp_E6, mul_smul_comm,
    smul_smul]
  module

/-- The family `F_{4N+12}`, generated from `F₁₂` by `eqn:poseig4`. -/
def Ffam : ℕ → QM
  | 0 => F12
  | N + 1 => fStep (4 * (N : ℝ) + 12) (Ffam N)

lemma hasWeight_Ffam (N : ℕ) : HasWeight (Ffam N) (4 * (N : ℝ) + 12) := by
  induction N with
  | zero => simpa using hasWeight_F12
  | succ N ih => exact HasWeight.congr_weight (hasWeight_fStep ih) (by push_cast; ring)

/-- The `q`-expansion of `F̃`, i.e. of `δF_w`. -/
def ftildeSeries (N : ℕ) : ℝ⟦X⟧ := qexp (delta (Ffam N))

/-- The `q`-expansion of `F_w`. -/
def fSeries (N : ℕ) : ℝ⟦X⟧ := qexp (Ffam N)

/-- **The recurrence hypothesis of `ftildePos`, discharged.** -/
theorem ftildeSeries_succ (N : ℕ) :
    ftildeSeries (N + 1) = ftildeStep (4 * (N : ℝ) + 12) (fSeries N) (ftildeSeries N) := by
  rw [ftildeSeries, ftildeSeries, fSeries, Ffam, qexp_delta_fStep (hasWeight_Ffam N)]

/-- **The base case of `ftildePos`, discharged.** -/
theorem ftildeSeries_zero : ftildeSeries 0 = ftilde10 := qexp_delta_F12

/-! ### Vanishing order of `F_w` -/

lemma qexp_fStep (w : ℝ) (F : QM) : qexp (fStep w F) = cF w • SF w (qexp F) := by
  rw [fStep, map_smul, qexp_SFp]

lemma coeff_SF (w : ℝ) (f : ℝ⟦X⟧) (n : ℕ) :
    coeff n (SF w f) = -(KanekoZagier.kappa2 (w - 2) (alphaF w) n * coeff n f
      + ∑ j ∈ range n, KanekoZagier.K2 (w - 2) (alphaF w) n j * coeff j f) := by
  rw [SF, map_neg, KanekoZagier.coeff_L2]

/-- The diagonal coefficient vanishes at the cusp index; this is what makes the vanishing order
of `F_w` increase by one at each step of the recurrence. -/
lemma kappa2_F_zero {N : ℕ} {w : ℝ} (hw : w = 4 * N + 12) :
    KanekoZagier.kappa2 (w - 2) (alphaF w) (N + 2) = 0 := by
  rw [kappa2_F, hw]; push_cast; ring

/-- `F₁₂ = (1/57600)(E₄')²`: the quadratic `E₂²E₄² - 2E₂E₄E₆ + E₆²` is `(E₂E₄-E₆)²`, and
Ramanujan turns `E₂E₄-E₆` into `3E₄'`. -/
lemma qexp_F12_eq : qexp F12
    = (PowerSeries.mk fun m ↦ (m : ℝ) * (ArithmeticFunction.sigma 3 m : ℝ))
      * (PowerSeries.mk fun m ↦ (m : ℝ) * (ArithmeticFunction.sigma 3 m : ℝ)) := by
  have h : qexp F12 = (1 / 57600 : ℝ) • (KanekoZagier.D KanekoZagier.E4
      * KanekoZagier.D KanekoZagier.E4) := by
    rw [F12, map_smul, map_add, map_sub, map_add, map_mul, map_mul, map_mul, map_mul, map_mul,
      map_mul, qexp_E2, qexp_E4, qexp_E6, KanekoZagier.ramanujan_E4]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    ring_nf
  rw [h, KanekoZagier.D_E4]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  norm_num

lemma coeff_qexp_F12 (n : ℕ) : coeff n (qexp F12)
    = ∑ j ∈ range n, (((n - j : ℕ) : ℝ) * (ArithmeticFunction.sigma 3 (n - j) : ℝ))
        * ((j : ℝ) * (ArithmeticFunction.sigma 3 j : ℝ)) := by
  rw [qexp_F12_eq, KanekoZagier.coeff_mk_mul _ (by simp) _ n]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [coeff_mk]

/-- **The vanishing order of `F_w`**, proved rather than assumed: `F_{4N+12}` vanishes to order
`N+2` at the cusp. -/
theorem coeff_fSeries_eq_zero (N : ℕ) : ∀ k, k ≤ N + 1 → coeff k (fSeries N) = 0 := by
  induction N with
  | zero =>
    intro k hk
    interval_cases k <;> rw [fSeries, Ffam, coeff_qexp_F12] <;> simp
  | succ N ih =>
    intro k hk
    have ih' : ∀ j, j ≤ N + 1 → coeff j (qexp (Ffam N)) = 0 := ih
    rw [fSeries, Ffam, qexp_fStep, PowerSeries.coeff_smul, smul_eq_mul, coeff_SF,
      Finset.sum_eq_zero fun j hj ↦ by
        rw [Finset.mem_range] at hj; rw [ih' j (by omega), mul_zero]]
    obtain hlt | rfl : k ≤ N + 1 ∨ k = N + 2 := by omega
    · rw [ih' k hlt]; ring
    · rw [kappa2_F_zero (N := N) rfl]; ring

/-! ### The modular linear differential equation for `F_w`

The vanishing order above needed nothing but the recurrence.  The normalisation `b_{w/4-1} = 1`
does: the recurrence expresses `[q^{w/4}]F_{w+4}` in terms of the *second* nonzero coefficient of
`F_w`, which the recurrence alone does not determine.  What determines it is the third-order
equation `L_{3,w-2}^{((w-4)/4,0)}F_w = 0`, which relates the coefficients of a single `F_w`.

That equation propagates along the recurrence by the intertwining criterion: the triples
`(α,β,γ) = (w/4, 0, -(w-10)(w-4)/48)` and `(α',β',γ') = ((w-4)/4, 0, -w(w-10)/48)` satisfy the
four constraints, so `L_{3,w+2}` composed with the recurrence operator is the recurrence operator
composed with `L_{3,w-2}`, and an operator annihilating `F_w` annihilates `F_{w+4}`. -/

/-- The third-order Kaneko--Zagier operator on the polynomial model, in Serre form. -/
def L3p (k α β : ℝ) (G : QM) : QM :=
  serreD (k + 4) (serreD (k + 2) (serreD k G))
    + (α - (3 * k ^ 2 + 12 * k + 8) / 144) • (E4 * serreD k G)
    + (β + k * α / 12 - k ^ 2 * (k + 3) / 864) • (E6 * G)

lemma qexp_L3p (k α β : ℝ) (G : QM) :
    qexp (L3p k α β G) = KanekoZagier.L3 k α β (qexp G) := by
  rw [L3p, KanekoZagier.L3_eq_serre, KanekoZagier.serreDIter_three, KanekoZagier.serreDIter_two,
    map_add, map_add, map_smul, map_smul, map_mul, map_mul, qexp_E4, qexp_E6, qexp_serreD,
    qexp_serreD, qexp_serreD]

private lemma serreD_F12 : serreD 10 F12 =
    -(1 / 622080 : ℝ) • (E2 ^ 2 * E4 * E6) + (1 / 622080 : ℝ) • (E2 * E4 ^ 3)
      + (1 / 622080 : ℝ) • (E2 * E6 ^ 2) - (1 / 622080 : ℝ) • (E4 ^ 2 * E6) := by
  simp only [F12, pow_succ, pow_zero, one_mul, serreD, Derivation.map_smul, map_sub, map_add,
    Derivation.leibniz, smul_eq_mul, D_E2, D_E4, D_E6, smul_smul, smul_sub, smul_add,
    mul_smul_comm, mul_sub, mul_add]
  simp only [mul_comm, mul_left_comm]
  module

private lemma serreD_serreD_F12 : serreD 12 (serreD 10 F12) =
    (7 / 7464960 : ℝ) • (E2 ^ 2 * E4 ^ 3) + (5 / 7464960 : ℝ) • (E2 ^ 2 * E6 ^ 2)
      - (24 / 7464960 : ℝ) • (E2 * E4 ^ 2 * E6) + (5 / 7464960 : ℝ) • E4 ^ 4
      + (7 / 7464960 : ℝ) • (E4 * E6 ^ 2) := by
  rw [serreD_F12]
  simp only [pow_succ, pow_zero, one_mul, serreD, Derivation.map_smul, map_sub, map_add,
    Derivation.leibniz, smul_eq_mul, D_E2, D_E4, D_E6, smul_smul, smul_sub, smul_add,
    mul_smul_comm, mul_sub, mul_add]
  simp only [mul_comm, mul_left_comm]
  module

private lemma serreD_serreD_serreD_F12 : serreD 14 (serreD 12 (serreD 10 F12)) =
    (35 / 22394880 : ℝ) • (E2 * E4 ^ 4) + (49 / 22394880 : ℝ) • (E2 * E4 * E6 ^ 2)
      - (42 / 22394880 : ℝ) • (E2 ^ 2 * E4 ^ 2 * E6) - (35 / 22394880 : ℝ) • (E4 ^ 3 * E6)
      - (7 / 22394880 : ℝ) • E6 ^ 3 := by
  rw [serreD_serreD_F12]
  simp only [pow_succ, pow_zero, one_mul, serreD, Derivation.map_smul, map_sub, map_add,
    Derivation.leibniz, smul_eq_mul, D_E2, D_E4, D_E6, smul_smul, smul_sub, smul_add,
    mul_smul_comm, mul_sub, mul_add]
  simp only [mul_comm, mul_left_comm]
  module

/-- The base case of the differential equation, checked on the explicit `F₁₂`. -/
lemma L3p_F12 : L3p 10 2 0 F12 = 0 := by
  rw [L3p, show (10 : ℝ) + 4 = 14 by norm_num, show (10 : ℝ) + 2 = 12 by norm_num,
    serreD_serreD_serreD_F12, serreD_F12, F12]
  simp only [pow_succ, pow_zero, one_mul, smul_smul, smul_sub, smul_add, smul_neg, neg_smul,
    mul_neg, mul_smul_comm, mul_sub, mul_add, sub_mul, add_mul]
  simp only [mul_comm, mul_left_comm]
  module

lemma mlde_zero : KanekoZagier.L3 10 2 0 (fSeries 0) = 0 := by
  rw [fSeries, Ffam, ← qexp_L3p, L3p_F12, map_zero]

/-- The differential equation propagates along the recurrence, by the intertwining criterion. -/
lemma mlde_step {w : ℝ} {f : ℝ⟦X⟧} (h : KanekoZagier.L3 (w - 2) ((w - 4) / 4) 0 f = 0) :
    KanekoZagier.L3 (w + 2) (w / 4) 0 (cF w • SF w f) = 0 := by
  have hint := KanekoZagier.L3_comp_L2_eq_L2_comp_L3 (w - 2) (w / 4) 0 (alphaF w)
    ((w - 4) / 4) 0 (-(w * (w - 10)) / 48)
    (by simp only [KanekoZagier.shiftA, KanekoZagier.shiftC, KanekoZagier.shiftA',
      KanekoZagier.shiftC', alphaF]; ring)
    (by simp only [KanekoZagier.shiftB, KanekoZagier.shiftC, KanekoZagier.shiftB',
      KanekoZagier.shiftA', alphaF]; ring)
    (by simp only [KanekoZagier.shiftC, KanekoZagier.shiftA, KanekoZagier.shiftA',
      KanekoZagier.shiftC', KanekoZagier.shiftB', alphaF]; ring)
    (by simp only [KanekoZagier.shiftC, KanekoZagier.shiftB, KanekoZagier.shiftA,
      KanekoZagier.shiftB', KanekoZagier.shiftC', alphaF]; ring) f
  rw [show w - 2 + 4 = w + 2 by ring, show w - 2 + 6 = w + 4 by ring, h,
    KanekoZagier.L2_zero] at hint
  rw [SF, smul_neg, ← neg_smul, KanekoZagier.L3_smul, hint, smul_zero]

/-- **The differential equation for `F_w`**, for every `w = 4N + 12`. -/
theorem mlde (N : ℕ) :
    KanekoZagier.L3 (4 * (N : ℝ) + 10) ((4 * (N : ℝ) + 8) / 4) 0 (fSeries N) = 0 := by
  induction N with
  | zero => norm_num; exact mlde_zero
  | succ N ih =>
    have := mlde_step (w := 4 * (N : ℝ) + 12) (by
      rw [show 4 * (N : ℝ) + 12 - 2 = 4 * (N : ℝ) + 10 by ring,
        show (4 * (N : ℝ) + 12 - 4) / 4 = (4 * (N : ℝ) + 8) / 4 by ring]
      exact ih)
    rw [show 4 * (N : ℝ) + 12 + 2 = 4 * ((N : ℝ) + 1) + 10 by ring,
      show (4 * (N : ℝ) + 12) / 4 = (4 * ((N : ℝ) + 1) + 8) / 4 by ring] at this
    rw [fSeries, Ffam, qexp_fStep]
    push_cast
    exact this

/-! ### The normalisation of `F_w`

At the index `n = w/4` the diagonal coefficient `κ₃` of the third-order equation is `(N+2)(N+3)`,
which is nonzero, so the equation determines the second nonzero coefficient of `F_w` from the first.
Feeding that value back into the recurrence produces `1` again, one index further along. -/

lemma kappa3_F (N : ℕ) :
    KanekoZagier.kappa3 (4 * (N : ℝ) + 10) ((4 * (N : ℝ) + 8) / 4) 0 (N + 3)
      = ((N : ℝ) + 2) * ((N : ℝ) + 3) := by
  rw [KanekoZagier.kappa3]; push_cast; ring

lemma K3_F (N : ℕ) :
    KanekoZagier.K3 (4 * (N : ℝ) + 10) ((4 * (N : ℝ) + 8) / 4) 0 (N + 3) (N + 2)
      = -8 * ((N : ℝ) ^ 3 + 6 * N ^ 2 + 23 * N + 27) := by
  have h1 : (ArithmeticFunction.sigma 1 1 : ℝ) = 1 := by norm_num
  have h3 : (ArithmeticFunction.sigma 3 1 : ℝ) = 1 := by norm_num
  rw [KanekoZagier.K3, show N + 3 - (N + 2) = 1 by omega, h1, h3]
  push_cast
  ring

lemma kappa2_F_cusp (N : ℕ) :
    KanekoZagier.kappa2 (4 * (N : ℝ) + 12 - 2) (alphaF (4 * (N : ℝ) + 12)) (N + 3)
      = (8 * (N : ℝ) + 19) / 6 := by
  rw [kappa2_F]; push_cast; ring

lemma K2_F_cusp (N : ℕ) :
    KanekoZagier.K2 (4 * (N : ℝ) + 12 - 2) (alphaF (4 * (N : ℝ) + 12)) (N + 3) (N + 2)
      = -4 * (24 * (N : ℝ) ^ 2 + 73 * N + 53) := by
  have h1 : (ArithmeticFunction.sigma 1 1 : ℝ) = 1 := by norm_num
  have h3 : (ArithmeticFunction.sigma 3 1 : ℝ) = 1 := by norm_num
  rw [K2_F, show N + 3 - (N + 2) = 1 by omega, h1, h3]
  push_cast
  ring

/-- The second nonzero coefficient of `F_{4N+12}`, read off from the third-order equation.  This is
the `b_{w/4}` of the paper. -/
lemma coeff_fSeries_succ {N : ℕ} (h : coeff (N + 2) (fSeries N) = 1) :
    coeff (N + 3) (fSeries N)
      = 8 * ((N : ℝ) ^ 3 + 6 * N ^ 2 + 23 * N + 27) / (((N : ℝ) + 2) * ((N : ℝ) + 3)) := by
  have key := congrArg (coeff (N + 3)) (mlde N)
  rw [KanekoZagier.coeff_L3, map_zero, kappa3_F,
    Finset.sum_eq_single (N + 2)
      (fun j hj hne ↦ by
        rw [coeff_fSeries_eq_zero N j (by rw [Finset.mem_range] at hj; omega), mul_zero])
      (fun hj ↦ absurd (Finset.mem_range.2 (by omega)) hj),
    K3_F, h, mul_one] at key
  rw [eq_div_iff (by positivity)]
  linarith [key]

/-- The recurrence turns the normalisation at index `N+2` into the normalisation at index `N+3`:
this is where `b_{w/4}` cancels against the two coefficient functions of `𝒮_w`. -/
private lemma cusp_normalisation (N : ℕ) :
    cF (4 * (N : ℝ) + 12) * -((8 * (N : ℝ) + 19) / 6
        * (8 * ((N : ℝ) ^ 3 + 6 * N ^ 2 + 23 * N + 27) / (((N : ℝ) + 2) * ((N : ℝ) + 3)))
      + -4 * (24 * (N : ℝ) ^ 2 + 73 * N + 53)) = 1 := by
  have h0 : (0 : ℝ) ≤ N := N.cast_nonneg
  have e2 : ((N : ℝ) + 2) ≠ 0 := by positivity
  have e3 : ((N : ℝ) + 3) ≠ 0 := by positivity
  have e4 : 4 * (N : ℝ) + 12 - 10 ≠ 0 := ne_of_gt (by linarith)
  have e5 : 4 * (N : ℝ) + 12 - 5 ≠ 0 := ne_of_gt (by linarith)
  have e6 : 4 * (N : ℝ) + 12 - 3 ≠ 0 := ne_of_gt (by linarith)
  have e7 : 4 * (N : ℝ) + 12 + 2 ≠ 0 := ne_of_gt (by linarith)
  rw [cF]
  field_simp
  ring

/-- **The normalisation of `F_w`**, proved rather than assumed: the leading coefficient of
`F_{4N+12}` is `1`. -/
theorem coeff_fSeries_eq_one (N : ℕ) : coeff (N + 2) (fSeries N) = 1 := by
  induction N with
  | zero => rw [fSeries, Ffam, coeff_qexp_F12]; norm_num [Finset.sum_range_succ]
  | succ N ih =>
    have hz : ∀ j, j ≤ N + 1 → coeff j (qexp (Ffam N)) = 0 := coeff_fSeries_eq_zero N
    have h2 : coeff (N + 2) (qexp (Ffam N)) = 1 := ih
    have hb : coeff (N + 3) (qexp (Ffam N))
        = 8 * ((N : ℝ) ^ 3 + 6 * N ^ 2 + 23 * N + 27) / (((N : ℝ) + 2) * ((N : ℝ) + 3)) :=
      coeff_fSeries_succ ih
    change coeff (N + 3) (fSeries (N + 1)) = 1
    rw [fSeries, Ffam, qexp_fStep, PowerSeries.coeff_smul, smul_eq_mul, coeff_SF,
      Finset.sum_eq_single (N + 2)
        (fun j hj hne ↦ by rw [hz j (by rw [Finset.mem_range] at hj; omega), mul_zero])
        (fun hj ↦ absurd (Finset.mem_range.2 (by omega)) hj),
      hb, h2, mul_one, kappa2_F_cusp, K2_F_cusp, cusp_normalisation]

/-! ### The conclusion -/

/-- **Positivity of the Fourier coefficients of `F̃_{w-2}`**, with every hypothesis of `ftildePos`
discharged: the recurrence, the base case, the vanishing order and the normalisation are all proved
from the definition of the `F_w` family in the polynomial model. -/
theorem coeff_ftildeSeries_pos (N j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ N + 1) :
    0 < coeff j (ftildeSeries N) :=
  ftildePos ftildeSeries_zero ftildeSeries_succ coeff_fSeries_eq_zero coeff_fSeries_eq_one N j hj1
    hj

/-- The boundary estimate, likewise. -/
theorem coeff_ftildeSeries_boundary (N : ℕ) : 1 / 360 ≤ coeff (N + 1) (ftildeSeries N) :=
  ftildeBoundary ftildeSeries_zero ftildeSeries_succ coeff_fSeries_eq_zero coeff_fSeries_eq_one N

end

end UncertaintyPrinciple
