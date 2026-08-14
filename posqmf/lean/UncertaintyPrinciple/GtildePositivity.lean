import posqmf.lean.DifferentialOperators.Coefficients
import posqmf.lean.SigmaBounds

/-!
# Nonnegativity of the Fourier coefficients of `G̃_w`

The value of `M_{d,-}` at the origin is `-π b_{0,-}`, and `b_{0,-}` is a nonnegative combination
of the Fourier coefficients `ã_j` of `G̃_{w-12}`.  Nonpositivity of `M_{d,-}(0)` therefore reduces
to

`ã_n ≥ 0` for `0 ≤ n ≤ w/4 + 1`,

for every `w ≡ 0 (mod 4)` with `w ≥ 0`, which is what this file proves.

## Shape of the argument

The induction on `w` in steps of `4` is driven by the recurrence

`G̃_{w+4} = c_w ((w+8)(w+9)/36 E₄ G̃_w - ∂_w² G̃_w) = c_w (-L_{2,w}^{α_w} G̃_w)`,
`α_w = -(w+6)(w+16)/48`.

For `0 ≤ n ≤ w/4 + 1` the diagonal coefficient `κ` and the lower triangular coefficients `K` are
both negative, so the recurrence propagates nonnegativity directly.  The top index `n = w/4 + 2`
is *not* covered by that: there `κ > 0`.  The paper's fix, reproduced here, is to eliminate
`ã_{w/4+2}` using the third-order equation `L_{3,w}^{(-(w+6)/4,0)} G̃_w = 0`, which expresses it in
terms of the lower coefficients.  What survives is a single combined kernel

`K''(j) = A_w(r) σ₁(r) + B_w(r) σ₃(r)`,  `r = w/4 + 2 - j`,

and the whole boundary case comes down to `A_w(r) ≥ 0`, `B_w(r) > 0` for `r ≥ 1`.

## What is and is not formalized

Everything downstream of the recurrence and the third-order equation is proved here,
unconditionally.  Two inputs are hypotheses, exactly as the paper takes them:

* the recurrence, whose derivation needs the uniqueness of the decomposition
  `G_w = G̃_{w-12} Δ 𝓛_S + Ψ_w`, an argument about modular functions for `Γ(2)` rather than about
  `q`-expansions;
* the third-order equation for `G̃_w`, which the paper deduces from the intertwining criterion.
  (`KanekoZagier.L3_comp_L2_eq_L2_comp_L3` is the sufficiency half of that criterion, so this
  hypothesis is within reach of the present development; deriving it would additionally need the
  two parameter triples to be checked against the four constraints.)

Both appear as explicit hypotheses of `gtildePos`, so nothing is assumed silently.  No axiom of
`Ramanujan.lean` is used: the argument rides on `coeff_L2` and `coeff_L3`, both unconditional.

## Main results

* `UncertaintyPrinciple.Aw_nonneg`, `Bw_pos`, `Kpp_pos`: the kernel estimates.
* `UncertaintyPrinciple.gtildeStep_nonneg` and `gtildeStep_boundary`: one induction step.
* `UncertaintyPrinciple.gtildePos`: `ã_n ≥ 0` for `0 ≤ n ≤ w/4 + 1`, every `w = 4N`.
* `UncertaintyPrinciple.gtildeConstant_pos`: the constant term stays strictly positive, which is
  what makes the resulting bound strict.

Weights are indexed by `N : ℕ` with `w = 4N`, so `w/4 + 1 = N + 1` and `w/4 + 2 = N + 2`.
-/

open ArithmeticFunction Finset KanekoZagier PowerSeries
open scoped sigma

namespace UncertaintyPrinciple

noncomputable section

/-! ### The operators and the recurrence step -/

/-- `α_w = -(w+6)(w+16)/48`, the parameter for which `𝒩_w = L_{2,w}^{α_w}`. -/
def alphaG (w : ℝ) : ℝ := -((w + 6) * (w + 16)) / 48

/-- The parameter `α = -(w+6)/4` of the third-order operator annihilating `G̃_w`. -/
def alphaOde (w : ℝ) : ℝ := -(w + 6) / 4

/-- The positive scalar `c_w = 3(w+10)(w+14) / (16(w+4)(w+9)(w+11)(w+16))`. -/
def cG (w : ℝ) : ℝ := 3 * (w + 10) * (w + 14) / (16 * (w + 4) * (w + 9) * (w + 11) * (w + 16))

/-- The right-hand side of the recurrence for `G̃`: `c_w(-L_{2,w}^{α_w} G̃_w)`. -/
def gtildeStep (w : ℝ) (Gt : ℝ⟦X⟧) : ℝ⟦X⟧ := cG w • (-L2 w (alphaG w) Gt)

private lemma denomG_pos {w : ℝ} (hw : 0 ≤ w) :
    0 < 16 * (w + 4) * (w + 9) * (w + 11) * (w + 16) :=
  mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith))
    (by linarith)) (by linarith)

lemma cG_pos {w : ℝ} (hw : 0 ≤ w) : 0 < cG w :=
  div_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)) (denomG_pos hw)

lemma coeff_gtildeStep (w : ℝ) (Gt : ℝ⟦X⟧) (n : ℕ) :
    coeff n (gtildeStep w Gt)
      = cG w * (-(kappa2 w (alphaG w) n * coeff n Gt
          + ∑ j ∈ range n, K2 w (alphaG w) n j * coeff j Gt)) := by
  rw [gtildeStep, PowerSeries.coeff_smul, smul_eq_mul, map_neg, coeff_L2]

/-! ### The specialised coefficient functions -/

/-- The diagonal coefficient of `L_{2,w}^{α_w}`, factored. -/
lemma kappa2_G (w : ℝ) (n : ℕ) :
    kappa2 w (alphaG w) n = (12 * n + w + 16) * (4 * n - w - 6) / 48 := by
  rw [kappa2, alphaG]; ring

/-- The lower triangular coefficient of `L_{2,w}^{α_w}`, in the paper's form. -/
lemma K2_G (w : ℝ) (n j : ℕ) :
    K2 w (alphaG w) n j
      = -2 * (w + 1) * (w * ((n : ℝ) - j) - 2 * j) * (σ 1 (n - j) : ℝ)
        - 5 * (w + 6) * (w + 16) * (σ 3 (n - j) : ℝ) := by
  rw [K2, alphaG]; ring

/-- The diagonal coefficient of the third-order operator, factored as `n(n+1)(4n-w-6)/4`. -/
lemma kappa3_G (w : ℝ) (n : ℕ) :
    kappa3 w (alphaOde w) 0 n = (n : ℝ) * ((n : ℝ) + 1) * (4 * n - w - 6) / 4 := by
  rw [kappa3, alphaOde]; ring

/-- The lower triangular coefficient of the third-order operator. -/
lemma K3_G (w : ℝ) (n j : ℕ) :
    K3 w (alphaOde w) 0 n j
      = (w + 2) * (6 * (j : ℝ) ^ 2 - 6 * (w + 1) * ((n : ℝ) - j) * j
            + w * (w + 1) * ((n : ℝ) - j) ^ 2) * (σ 1 (n - j) : ℝ)
        + 15 * (w + 6) * (w * ((n : ℝ) - j) - 4 * j) * (σ 3 (n - j) : ℝ) := by
  rw [K3, alphaOde]; ring

/-! ### Signs on the interior range -/

/-- On `0 ≤ n ≤ w/4 + 1` the diagonal coefficient is negative. -/
lemma kappa2_G_neg {w : ℝ} {n : ℕ} (hw : 0 ≤ w) (hn : 4 * (n : ℝ) ≤ w + 4) :
    kappa2 w (alphaG w) n < 0 := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [kappa2_G]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (by linarith) (by linarith)) (by norm_num)

/-- The gap estimate `w(n-j) - 2j ≥ 0` for `0 ≤ j < n ≤ w/4 + 1`: writing it as
`(w+2)(n-j) - 2n`, it is at least `w + 2 - 2n ≥ w/2 ≥ 0`. -/
theorem weight_gap_nonneg {w : ℝ} {n j : ℕ} (hw : 0 ≤ w) (hj : j < n) (hn : 4 * (n : ℝ) ≤ w + 4) :
    0 ≤ w * ((n : ℝ) - j) - 2 * j := by
  have hgap : 1 ≤ (n : ℝ) - j := by
    rw [← Nat.cast_sub hj.le]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  nlinarith

/-- On `0 ≤ j < n ≤ w/4 + 1` the lower triangular coefficient is negative. -/
lemma K2_G_neg {w : ℝ} {n j : ℕ} (hw : 0 ≤ w) (hj : j < n) (hn : 4 * (n : ℝ) ≤ w + 4) :
    K2 w (alphaG w) n j < 0 := by
  have hnj : 1 ≤ n - j := by omega
  rw [K2_G]
  have t1 : 0 ≤ 2 * (w + 1) * (w * ((n : ℝ) - j) - 2 * j) * (σ 1 (n - j) : ℝ) :=
    mul_nonneg (mul_nonneg (by linarith) (weight_gap_nonneg hw hj hn)) (sigma_pos hnj).le
  have t2 : 0 < 5 * (w + 6) * (w + 16) * (σ 3 (n - j) : ℝ) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (sigma_pos hnj)
  linarith

/-! ### One induction step, interior range -/

/-- **Interior step.**  On `0 ≤ n ≤ w/4 + 1` both `κ` and `K` are negative, so the recurrence
turns nonnegativity at weight `w` into nonnegativity at weight `w + 4`. -/
theorem gtildeStep_nonneg {N : ℕ} {w : ℝ} (hw : w = 4 * N) {Gt : ℝ⟦X⟧}
    (hnn : ∀ j, j ≤ N + 1 → 0 ≤ coeff j Gt) {n : ℕ} (hn : n ≤ N + 1) :
    0 ≤ coeff n (gtildeStep w Gt) := by
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hnR : 4 * (n : ℝ) ≤ w + 4 := by
    rw [hw]; have : (n : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hn
    linarith
  have hdiag : kappa2 w (alphaG w) n * coeff n Gt ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (kappa2_G_neg hw0 hnR).le (hnn n hn)
  have hsum : ∑ j ∈ range n, K2 w (alphaG w) n j * coeff j Gt ≤ 0 :=
    Finset.sum_nonpos fun j hj ↦ by
      rw [Finset.mem_range] at hj
      exact mul_nonpos_of_nonpos_of_nonneg (K2_G_neg hw0 hj hnR).le (hnn j (by omega))
  rw [coeff_gtildeStep]
  exact mul_nonneg (cG_pos hw0).le (by linarith)

/-! ### The kernel `K''` at the boundary index -/

/-- `A_w(r)`, the `σ₁`-part of the combined boundary kernel. -/
def Aw (w r : ℝ) : ℝ :=
  (w + 4) / (3 * (w + 8) * (w + 12))
    * (16 * w ^ 3 * r ^ 2 - 18 * w ^ 3 * r + 3 * w ^ 3 + 240 * w ^ 2 * r ^ 2 - 342 * w ^ 2 * r
      + 69 * w ^ 2 + 896 * w * r ^ 2 - 1908 * w * r + 528 * w + 960 * r ^ 2 - 2592 * r + 1344)

/-- `B_w(r)`, the `σ₃`-part of the combined boundary kernel. -/
def Bw (w r : ℝ) : ℝ :=
  5 * (w + 4) * (w + 6) / ((w + 8) * (w + 12))
    * (w ^ 2 + 16 * w * r + 16 * w + 160 * r + 64)

/-- `B_w(r) > 0` for `r ≥ 1`: every term of the second factor is nonnegative and the constant is
positive. -/
theorem Bw_pos {w r : ℝ} (hw : 0 ≤ w) (hr : 1 ≤ r) : 0 < Bw w r := by
  refine mul_pos (div_pos (by nlinarith) (by nlinarith)) ?_
  nlinarith [sq_nonneg w, mul_nonneg hw (by linarith : 0 ≤ r)]

/-- `A_w(r) ≥ 0` for `r ≥ 2`: substituting `r = u + 2` makes every coefficient of the second
factor nonnegative. -/
theorem Aw_nonneg {w r : ℝ} (hw : 0 ≤ w) (hr : 2 ≤ r) : 0 ≤ Aw w r := by
  have hu : 0 ≤ r - 2 := by linarith
  refine mul_nonneg (div_nonneg (by linarith) (by nlinarith)) ?_
  have hw2 : 0 ≤ w ^ 2 := sq_nonneg w
  have hw3 : 0 ≤ w ^ 3 := by positivity
  have hu2 : 0 ≤ (r - 2) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hw3 hu2, mul_nonneg hw3 hu, mul_nonneg hw2 hu2, mul_nonneg hw2 hu,
    mul_nonneg hw hu2, mul_nonneg hw hu]

/-- At `r = 1` the two parts combine to `(w+4)(16w²+409w+2484)/(3(w+12))`, which is positive. -/
theorem Aw_add_Bw_one {w : ℝ} (hw : 0 ≤ w) :
    Aw w 1 + Bw w 1 = (w + 4) * (16 * w ^ 2 + 409 * w + 2484) / (3 * (w + 12)) := by
  have h8 : (w + 8) ≠ 0 := by positivity
  have h12 : (w + 12) ≠ 0 := by positivity
  rw [Aw, Bw]
  field_simp
  ring

/-- The combined boundary kernel is positive at every index that occurs. -/
theorem Kpp_pos {w : ℝ} (hw : 0 ≤ w) {m : ℕ} (hm : 1 ≤ m) :
    0 < Aw w (m : ℝ) * (σ 1 m : ℝ) + Bw w (m : ℝ) * (σ 3 m : ℝ) := by
  rcases eq_or_lt_of_le hm with rfl | h2
  · rw [Nat.cast_one, show (σ 1 1 : ℝ) = 1 by norm_num, show (σ 3 1 : ℝ) = 1 by norm_num,
      mul_one, mul_one, Aw_add_Bw_one hw]
    exact div_pos (by nlinarith [sq_nonneg w]) (by linarith)
  · have hm2 : 2 ≤ (m : ℝ) := by exact_mod_cast h2
    nlinarith [Aw_nonneg hw hm2, Bw_pos (r := (m : ℝ)) hw (by linarith),
      sigma_pos (k := 1) hm, sigma_pos (k := 3) hm]

/-! ### One induction step, boundary index -/

/-- The identity behind the boundary case: eliminating `ã_{w/4+2}` between the recurrence and the
third-order equation leaves the kernel `A_w(r)σ₁(r) + B_w(r)σ₃(r)` with `r = w/4 + 2 - j`. -/
lemma Kpp_eq {N j : ℕ} {w : ℝ} (hw : w = 4 * N) (hj : j ≤ N + 1) :
    16 * (w + 10) / (3 * (w + 8) * (w + 12)) * K3 w (alphaOde w) 0 (N + 2) j
        - K2 w (alphaG w) (N + 2) j
      = Aw w ((N + 2 - j : ℕ) : ℝ) * (σ 1 (N + 2 - j) : ℝ)
        + Bw w ((N + 2 - j : ℕ) : ℝ) * (σ 3 (N + 2 - j) : ℝ) := by
  have hcast : ((N + 2 - j : ℕ) : ℝ) = (N : ℝ) + 2 - j := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h8 : (w + 8) ≠ 0 := by rw [hw]; positivity
  have h12 : (w + 12) ≠ 0 := by rw [hw]; positivity
  rw [K3_G, K2_G, Aw, Bw, hcast, hw]
  push_cast
  field_simp
  ring

/-- Eliminating `ã_{w/4+2}` between the recurrence and the third-order equation: at the boundary
index the coefficient of `gtildeStep` is `c_w` times the pairing of the combined kernel with the
lower coefficients. -/
private lemma coeff_gtildeStep_boundary {N : ℕ} {w : ℝ} (hw : w = 4 * N) {Gt : ℝ⟦X⟧}
    (hode : L3 w (alphaOde w) 0 Gt = 0) :
    coeff (N + 2) (gtildeStep w Gt)
      = cG w * ∑ j ∈ range (N + 2),
          (16 * (w + 10) / (3 * (w + 8) * (w + 12)) * K3 w (alphaOde w) 0 (N + 2) j
            - K2 w (alphaG w) (N + 2) j) * coeff j Gt := by
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hlin : kappa3 w (alphaOde w) 0 (N + 2) * coeff (N + 2) Gt
      + ∑ j ∈ range (N + 2), K3 w (alphaOde w) 0 (N + 2) j * coeff j Gt = 0 := by
    rw [← coeff_L3, hode, _root_.map_zero]
  have hk3 : kappa3 w (alphaOde w) 0 (N + 2) = (w + 8) * (w + 12) / 32 := by
    rw [kappa3_G, hw]; push_cast; ring
  have hk2 : kappa2 w (alphaG w) (N + 2) = (w + 10) / 6 := by
    rw [kappa2_G, hw]; push_cast; ring
  rw [hk3] at hlin
  have hsplit : ∑ j ∈ range (N + 2),
      (16 * (w + 10) / (3 * (w + 8) * (w + 12)) * K3 w (alphaOde w) 0 (N + 2) j
        - K2 w (alphaG w) (N + 2) j) * coeff j Gt
      = 16 * (w + 10) / (3 * (w + 8) * (w + 12))
          * (∑ j ∈ range (N + 2), K3 w (alphaOde w) 0 (N + 2) j * coeff j Gt)
        - ∑ j ∈ range (N + 2), K2 w (alphaG w) (N + 2) j * coeff j Gt := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [coeff_gtildeStep, hk2, hsplit,
    show ∑ j ∈ range (N + 2), K3 w (alphaOde w) 0 (N + 2) j * coeff j Gt
      = -((w + 8) * (w + 12) / 32 * coeff (N + 2) Gt) from by linarith]
  field_simp
  ring

/-- **Boundary step.**  At `n = w/4 + 2` the diagonal coefficient is positive, so the recurrence
alone does not suffice; the third-order equation supplies the missing relation. -/
theorem gtildeStep_boundary {N : ℕ} {w : ℝ} (hw : w = 4 * N) {Gt : ℝ⟦X⟧}
    (hode : L3 w (alphaOde w) 0 Gt = 0) (hnn : ∀ j, j ≤ N + 1 → 0 ≤ coeff j Gt) :
    0 ≤ coeff (N + 2) (gtildeStep w Gt) := by
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  rw [coeff_gtildeStep_boundary hw hode]
  refine mul_nonneg (cG_pos hw0).le (Finset.sum_nonneg fun j hj ↦ ?_)
  rw [Finset.mem_range] at hj
  refine mul_nonneg ?_ (hnn j (by omega))
  rw [Kpp_eq hw (by omega)]
  exact (Kpp_pos hw0 (by omega)).le

/-! ### The base case `G̃₀ = 3/(2¹¹·7)` -/

/-- `G̃₀ = 3/(2¹¹·7)`, a positive constant. -/
def gtilde0 : ℝ⟦X⟧ := (3 / 14336 : ℝ) • 1

lemma coeff_gtilde0 (n : ℕ) : coeff n gtilde0 = if n = 0 then 3 / 14336 else 0 := by
  rw [gtilde0, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_one]
  split_ifs <;> norm_num

lemma coeff_gtilde0_nonneg (n : ℕ) : 0 ≤ coeff n gtilde0 := by
  rw [coeff_gtilde0]; split_ifs <;> norm_num

lemma coeff_gtilde0_zero_pos : 0 < coeff 0 gtilde0 := by
  rw [coeff_gtilde0]; norm_num

/-! ### The induction -/

/-- **Nonnegativity of the Fourier coefficients of `G̃_w`.**  For `w = 4N`, every coefficient
`ã_n` with `0 ≤ n ≤ w/4 + 1 = N + 1` is nonnegative. -/
theorem gtildePos {Gt : ℕ → ℝ⟦X⟧} (hbase : Gt 0 = gtilde0)
    (hrec : ∀ N : ℕ, Gt (N + 1) = gtildeStep (4 * (N : ℝ)) (Gt N))
    (hode : ∀ N : ℕ, L3 (4 * (N : ℝ)) (alphaOde (4 * (N : ℝ))) 0 (Gt N) = 0)
    (N : ℕ) : ∀ n, n ≤ N + 1 → 0 ≤ coeff n (Gt N) := by
  induction N with
  | zero => intro n _; rw [hbase]; exact coeff_gtilde0_nonneg n
  | succ N ih =>
    intro n hn
    rw [hrec N]
    obtain hlt | rfl : n ≤ N + 1 ∨ n = N + 2 := by omega
    · exact gtildeStep_nonneg rfl ih hlt
    · exact gtildeStep_boundary rfl (hode N) ih

/-- **The constant term is strictly positive.**  Taking `n = 0` in the recurrence gives the ratio
`ã₀^{(w+4)} / ã₀^{(w)} = (w+6)(w+10)(w+14) / (256(w+4)(w+9)(w+11))`, which is positive; this is
what makes the resulting bound on `A₊(d)` strict. -/
theorem gtildeConstant_pos {Gt : ℕ → ℝ⟦X⟧} (hbase : Gt 0 = gtilde0)
    (hrec : ∀ N : ℕ, Gt (N + 1) = gtildeStep (4 * (N : ℝ)) (Gt N)) (N : ℕ) :
    0 < coeff 0 (Gt N) := by
  induction N with
  | zero => rw [hbase]; exact coeff_gtilde0_zero_pos
  | succ N ih =>
    have hw0 : 0 ≤ 4 * (N : ℝ) := by positivity
    rw [hrec N, coeff_gtildeStep, Finset.range_zero, Finset.sum_empty, add_zero]
    refine mul_pos (cG_pos hw0) ?_
    have := kappa2_G_neg (w := 4 * (N : ℝ)) (n := 0) hw0 (by push_cast; linarith)
    nlinarith [ih]

end

end UncertaintyPrinciple
