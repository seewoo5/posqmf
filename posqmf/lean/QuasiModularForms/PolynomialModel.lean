import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie
import posqmf.lean.QuasiModularForms.Serre

/-!
# The polynomial model `ℝ[E₂,E₄,E₆]` and the operator `δ = ∂/∂E₂`

The ring of quasimodular forms of level `1` is a polynomial ring in `E₂`, `E₄`, `E₆`, and some of
the operators of the theory are visible only in that presentation.  The one we need is

`δ G = ∂G/∂E₂`,

which extracts the depth filtration: `δ` lowers weight by `2` and depth by `1`, and `δG = 0`
exactly when `G` is a genuine modular form.  It is *not* an operator on `q`-expansions --- it reads
the polynomial, not the series --- so it cannot be defined in `Basic.lean`, and this file supplies
the missing layer.

Everything is done with derivations, which keeps the proofs to generator checks.  In particular
weighted homogeneity is handled through the Euler operator rather than through
`MvPolynomial.IsWeightedHomogeneous`: `HasWeight G w` is by definition `eulerOp G = w • G`, and
since `eulerOp` is itself a derivation, weight bookkeeping is closed under products and under `D`
by pure algebra, with no need for the weighted Euler identity.

## Main results

* `PolynomialModel.euler_D`: `⁅eulerOp, D⁆ = 2D`, i.e. `D` raises the weight by `2`.
* `PolynomialModel.delta_D`: `⁅δ, D⁆ = (1/12) eulerOp`, the `sl₂`-relation of Kaneko--Koike.
* `PolynomialModel.delta_serreD`: `δ(∂_k G) = ∂_k(δG) + ((w-k)/12) G` for `G` of weight `w`.
* `PolynomialModel.qexp_D`, `qexp_serreD`: the `q`-expansion map intertwines the polynomial `D` and
  `∂_k` with the ones on `ℝ⟦X⟧`.  This is where Ramanujan's identities enter.
-/

open MvPolynomial

namespace PolynomialModel

/-- The ring of level-`1` quasimodular forms, modelled as `ℝ[E₂,E₄,E₆]`. -/
abbrev QM := MvPolynomial (Fin 3) ℝ

noncomputable section

/-- The generator `E₂`. -/
def E₂ : QM := X 0

/-- The generator `E₄`. -/
def E₄ : QM := X 1

/-- The generator `E₆`. -/
def E₆ : QM := X 2

/-! ### The derivation `D` -/

/-- Ramanujan's identities, read as the values of `D` on the three generators. -/
def dGen : Fin 3 → QM
  | 0 => (1 / 12 : ℝ) • (E₂ * E₂ - E₄)
  | 1 => (1 / 3 : ℝ) • (E₂ * E₄ - E₆)
  | 2 => (1 / 2 : ℝ) • (E₂ * E₆ - E₄ * E₄)

/-- `D = q d/dq` on the polynomial model: the derivation determined by Ramanujan's identities. -/
def D : Derivation ℝ QM QM := mkDerivation ℝ dGen

@[simp] lemma D_E₂ : D E₂ = (1 / 12 : ℝ) • (E₂ * E₂ - E₄) := mkDerivation_X ℝ dGen 0

@[simp] lemma D_E₄ : D E₄ = (1 / 3 : ℝ) • (E₂ * E₄ - E₆) := mkDerivation_X ℝ dGen 1

@[simp] lemma D_E₆ : D E₆ = (1 / 2 : ℝ) • (E₂ * E₆ - E₄ * E₄) := mkDerivation_X ℝ dGen 2

/-! ### `δ`, the Euler operator, and weights -/

/-- `δ = ∂/∂E₂`, the operator extracting the depth filtration. -/
def delta : Derivation ℝ QM QM := pderiv 0

@[simp] lemma delta_E₂ : delta E₂ = 1 := by simp [delta, E₂]

@[simp] lemma delta_E₄ : delta E₄ = 0 := by simp [delta, E₄]

@[simp] lemma delta_E₆ : delta E₆ = 0 := by simp [delta, E₆]

/-- The weighted Euler operator `2E₂∂/∂E₂ + 4E₄∂/∂E₄ + 6E₆∂/∂E₆`. -/
def eulerOp : Derivation ℝ QM QM :=
  ((2 : ℝ) • E₂) • pderiv 0 + ((4 : ℝ) • E₄) • pderiv 1 + ((6 : ℝ) • E₆) • pderiv 2

@[simp] lemma eulerOp_E₂ : eulerOp E₂ = (2 : ℝ) • E₂ := by simp [eulerOp, E₂, E₄, E₆]

@[simp] lemma eulerOp_E₄ : eulerOp E₄ = (4 : ℝ) • E₄ := by simp [eulerOp, E₂, E₄, E₆]

@[simp] lemma eulerOp_E₆ : eulerOp E₆ = (6 : ℝ) • E₆ := by simp [eulerOp, E₂, E₄, E₆]

/-- `G` is weighted homogeneous of weight `w`, expressed through the Euler operator. -/
def HasWeight (G : QM) (w : ℝ) : Prop := eulerOp G = w • G

lemma HasWeight.mul {G H : QM} {a b : ℝ} (hG : HasWeight G a) (hH : HasWeight H b) :
    HasWeight (G * H) (a + b) := by
  simp only [HasWeight, Derivation.leibniz] at *
  rw [hG, hH]
  simp only [smul_eq_mul, mul_smul_comm, mul_comm H G]
  module

lemma HasWeight.smul {G : QM} {a : ℝ} (c : ℝ) (hG : HasWeight G a) : HasWeight (c • G) a := by
  simp only [HasWeight] at *
  rw [Derivation.map_smul, hG, smul_comm]

lemma HasWeight.add {G H : QM} {a : ℝ} (hG : HasWeight G a) (hH : HasWeight H a) :
    HasWeight (G + H) a := by
  simp only [HasWeight, map_add] at *
  rw [hG, hH, smul_add]

lemma HasWeight.sub {G H : QM} {a : ℝ} (hG : HasWeight G a) (hH : HasWeight H a) :
    HasWeight (G - H) a := by
  simp only [HasWeight, map_sub] at *
  rw [hG, hH, smul_sub]

/-- Weights may be rewritten by any equality of reals; this absorbs the arithmetic that
accumulates when weights are added up. -/
lemma HasWeight.congr_weight {G : QM} {a b : ℝ} (h : HasWeight G a) (hab : a = b) : HasWeight G b :=
  hab ▸ h

lemma hasWeight_zero {a : ℝ} : HasWeight (0 : QM) a := by simp [HasWeight]

lemma hasWeight_one : HasWeight (1 : QM) 0 := by simp [HasWeight]

lemma HasWeight.pow {G : QM} {a : ℝ} (hG : HasWeight G a) (n : ℕ) :
    HasWeight (G ^ n) (n * a) := by
  induction n with
  | zero => simpa using hasWeight_one
  | succ n ih =>
    rw [pow_succ]
    exact HasWeight.congr_weight (ih.mul hG) (by push_cast; ring)

lemma hasWeight_E₂ : HasWeight E₂ 2 := eulerOp_E₂

lemma hasWeight_E₄ : HasWeight E₄ 4 := eulerOp_E₄

lemma hasWeight_E₆ : HasWeight E₆ 6 := eulerOp_E₆

/-! ### The two commutator identities -/

/-- `⁅eulerOp, D⁆ = 2D`: the operator `D` raises the weight by `2`. -/
theorem euler_D : ⁅eulerOp, D⁆ = (2 : ℝ) • D := by
  refine derivation_ext fun i ↦ ?_
  have h0 : ⁅eulerOp, D⁆ E₂ = ((2 : ℝ) • D) E₂ := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, D_E₂, eulerOp_E₂]
    simp only [Derivation.map_smul, map_sub, Derivation.leibniz, D_E₂, eulerOp_E₂, eulerOp_E₄,
      smul_eq_mul, mul_smul_comm]
    module
  have h1 : ⁅eulerOp, D⁆ E₄ = ((2 : ℝ) • D) E₄ := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, D_E₄, eulerOp_E₄]
    simp only [Derivation.map_smul, map_sub, Derivation.leibniz, D_E₄, eulerOp_E₂, eulerOp_E₄,
      eulerOp_E₆, smul_eq_mul, mul_smul_comm, mul_comm E₄ E₂]
    module
  have h2 : ⁅eulerOp, D⁆ E₆ = ((2 : ℝ) • D) E₆ := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, D_E₆, eulerOp_E₆]
    simp only [Derivation.map_smul, map_sub, Derivation.leibniz, D_E₆, eulerOp_E₂, eulerOp_E₄,
      eulerOp_E₆, smul_eq_mul, mul_smul_comm, mul_comm E₆ E₂]
    module
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- `⁅δ, D⁆ = (1/12) eulerOp`, the `sl₂`-relation of Kaneko--Koike. -/
theorem delta_D : ⁅delta, D⁆ = (1 / 12 : ℝ) • eulerOp := by
  refine derivation_ext fun i ↦ ?_
  have h0 : ⁅delta, D⁆ E₂ = ((1 / 12 : ℝ) • eulerOp) E₂ := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, D_E₂, delta_E₂, eulerOp_E₂]
    simp only [Derivation.map_smul, map_sub, Derivation.leibniz, delta_E₂, delta_E₄,
      Derivation.map_one_eq_zero, smul_eq_mul, mul_one]
    module
  have h1 : ⁅delta, D⁆ E₄ = ((1 / 12 : ℝ) • eulerOp) E₄ := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, D_E₄, delta_E₄, eulerOp_E₄]
    simp only [Derivation.map_smul, map_sub, Derivation.leibniz, delta_E₂, delta_E₄, delta_E₆,
      map_zero, smul_eq_mul, mul_one, mul_zero]
    module
  have h2 : ⁅delta, D⁆ E₆ = ((1 / 12 : ℝ) • eulerOp) E₆ := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, D_E₆, delta_E₆, eulerOp_E₆]
    simp only [Derivation.map_smul, map_sub, Derivation.leibniz, delta_E₂, delta_E₄, delta_E₆,
      map_zero, smul_eq_mul, mul_one, mul_zero]
    module
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- `δ` lowers the weight by `2`: `[E, δ] = -2δ`.  Only the `E₂` generator contributes, since
`δE₄ = δE₆ = 0`. -/
theorem euler_delta : ⁅eulerOp, delta⁆ = (-2 : ℝ) • delta := by
  refine derivation_ext fun i ↦ ?_
  have h0 : ⁅eulerOp, delta⁆ E₂ = ((-2 : ℝ) • delta) E₂ := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, delta_E₂, eulerOp_E₂]
    simp [Derivation.map_smul]
  have h1 : ⁅eulerOp, delta⁆ E₄ = ((-2 : ℝ) • delta) E₄ := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, delta_E₄, eulerOp_E₄]
    simp [Derivation.map_smul]
  have h2 : ⁅eulerOp, delta⁆ E₆ = ((-2 : ℝ) • delta) E₆ := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, delta_E₆, eulerOp_E₆]
    simp [Derivation.map_smul]
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

lemma hasWeight_delta {G : QM} {w : ℝ} (h : HasWeight G w) : HasWeight (delta G) (w - 2) := by
  have key := congrArg (fun T : Derivation ℝ QM QM ↦ T G) euler_delta
  simp only [Derivation.commutator_apply, Derivation.smul_apply] at key
  simp only [HasWeight] at h ⊢
  rw [h, Derivation.map_smul, sub_eq_iff_eq_add] at key
  rw [key]
  module

lemma hasWeight_D {G : QM} {w : ℝ} (h : HasWeight G w) : HasWeight (D G) (w + 2) := by
  have key := congrArg (fun T : Derivation ℝ QM QM ↦ T G) euler_D
  simp only [Derivation.commutator_apply, Derivation.smul_apply] at key
  simp only [HasWeight] at h ⊢
  rw [h, Derivation.map_smul] at key
  rw [add_smul, ← key]
  abel

/-- **`eqn:D_delta`**: `D(δG) - δ(DG) = -(w/12)G` for `G` of weight `w`. -/
theorem D_delta {G : QM} {w : ℝ} (h : HasWeight G w) :
    D (delta G) - delta (D G) = (-(w / 12) : ℝ) • G := by
  have key := congrArg (fun T : Derivation ℝ QM QM ↦ T G) delta_D
  simp only [Derivation.commutator_apply, Derivation.smul_apply] at key
  simp only [HasWeight] at h
  rw [h, smul_smul] at key
  rw [← neg_sub (delta (D G)), key, ← neg_smul]
  congr 1
  ring

/-! ### The Serre derivative on the polynomial model -/

/-- The Serre derivative `∂_k G = DG - (k/12)E₂G` on the polynomial model. -/
def serreD (k : ℝ) (G : QM) : QM := D G - (k / 12 : ℝ) • (E₂ * G)

lemma serreD_add (k : ℝ) (G H : QM) : serreD k (G + H) = serreD k G + serreD k H := by
  simp only [serreD, map_add, mul_add, smul_add]; abel

lemma serreD_smul (k c : ℝ) (G : QM) : serreD k (c • G) = c • serreD k G := by
  simp only [serreD, Derivation.map_smul, mul_smul_comm, smul_sub, smul_smul]
  ring_nf

/-- The collapse `(1/6)∂_w G + (1/6)∂_{w-2} G = (1/3)∂_{w-1} G`, which is what turns the two
`delta_serreD` correction terms into the single `∂_{w-1}` term of the `F̃` recurrence. -/
lemma serreD_collapse (w : ℝ) (G : QM) :
    (1 / 6 : ℝ) • serreD w G + (1 / 6 : ℝ) • serreD (w - 2) G
      = (1 / 3 : ℝ) • serreD (w - 1) G := by
  simp only [serreD, smul_sub, smul_smul]
  module

lemma hasWeight_serreD {G : QM} {w : ℝ} (k : ℝ) (h : HasWeight G w) :
    HasWeight (serreD k G) (w + 2) :=
  (hasWeight_D h).sub (HasWeight.congr_weight ((hasWeight_E₂.mul h).smul (k / 12)) (by ring))

/-- **`lem:delta_serre`**: `δ(∂_k G) = ∂_k(δG) + ((w-k)/12)G` for `G` of weight `w`. -/
theorem delta_serreD {G : QM} {w : ℝ} (k : ℝ) (h : HasWeight G w) :
    delta (serreD k G) = serreD k (delta G) + ((w - k) / 12 : ℝ) • G := by
  have hD : delta (D G) = D (delta G) + ((w / 12 : ℝ)) • G := by
    have h1 := D_delta h
    rw [sub_eq_iff_eq_add] at h1
    rw [h1]
    module
  simp only [serreD, map_sub, Derivation.map_smul, Derivation.leibniz, delta_E₂, smul_eq_mul,
    mul_one]
  rw [hD]
  module

/-! ### Relation to the `q`-series `E₂`, `E₄`, `E₆`

There are two families of objects called `E₂`, `E₄`, `E₆` in this development, and they are
genuinely different:

* `QExpansion.E₂ : ℝ⟦X⟧` is the concrete divisor-sum series `1 - 24∑σ₁(n)qⁿ`;
* `PolynomialModel.E₂ : QM` is an indeterminate of a polynomial ring, carrying no `q`-expansion.

They are related, but not equal, by the evaluation map `qexp` below.  Identifying them would
require `qexp` to be injective, i.e. the algebraic independence of `E₂`, `E₄`, `E₆` over `ℝ`,
which is a genuine theorem not formalized here; and even with it, `δ` would still have to be
transported along the isomorphism rather than defined directly on series.  So the two-level setup
is not redundancy but the usual "free object plus realization map" arrangement, exactly like
`MvPolynomial.X` versus the element it is evaluated at.

In practice one works polynomially --- where `δ` and `HasWeight` make sense --- and transports the
result with `qexp`.  The `qexp_*` lemmas below are `simp`, so `qexp` pushes through any expression
built from the generators, `D` and `∂_k`, landing on the `q`-series side automatically.  The one
operator with no counterpart is `δ` itself: that is the whole point of the polynomial model.
-/

/-- The `q`-expansion homomorphism `ℝ[E₂,E₄,E₆] → ℝ⟦X⟧`, sending each generator to the
corresponding divisor-sum series. -/
def qexp : QM →ₐ[ℝ] PowerSeries ℝ :=
  aeval ![QExpansion.E₂, QExpansion.E₄, QExpansion.E₆]

@[simp] lemma qexp_E₂ : qexp E₂ = QExpansion.E₂ := by simp [qexp, E₂]

@[simp] lemma qexp_E₄ : qexp E₄ = QExpansion.E₄ := by simp [qexp, E₄]

@[simp] lemma qexp_E₆ : qexp E₆ = QExpansion.E₆ := by simp [qexp, E₆]

/-- **Ramanujan's identities, packaged.**  The values of the polynomial `D` on the generators
evaluate to the derivatives of the corresponding `q`-series.  This single statement is what the
three axioms of `Ramanujan.lean` amount to, and it is the only place they are used here. -/
theorem qexp_dGen (i : Fin 3) : qexp (dGen i) = QExpansion.D (qexp (X i)) := by
  have h0 : qexp (dGen 0) = QExpansion.D (qexp E₂) := by
    rw [show dGen 0 = (1 / 12 : ℝ) • (E₂ * E₂ - E₄) from rfl, qexp_E₂,
      QExpansion.ramanujan_E₂, map_smul, map_sub, map_mul, qexp_E₂, qexp_E₄]
  have h1 : qexp (dGen 1) = QExpansion.D (qexp E₄) := by
    rw [show dGen 1 = (1 / 3 : ℝ) • (E₂ * E₄ - E₆) from rfl, qexp_E₄,
      QExpansion.ramanujan_E₄, map_smul, map_sub, map_mul, qexp_E₂, qexp_E₄, qexp_E₆]
  have h2 : qexp (dGen 2) = QExpansion.D (qexp E₆) := by
    rw [show dGen 2 = (1 / 2 : ℝ) • (E₂ * E₆ - E₄ * E₄) from rfl, qexp_E₆,
      QExpansion.ramanujan_E₆, map_smul, map_sub, map_mul, map_mul, qexp_E₂, qexp_E₄, qexp_E₆]
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The `q`-expansion map intertwines the two `D`'s. -/
@[simp] theorem qexp_D (p : QM) : qexp (D p) = QExpansion.D (qexp p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [QExpansion.D_C]
  | add p q hp hq => simp [QExpansion.D_add, hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp,
      show D (X i) = dGen i from mkDerivation_X ℝ dGen i, qexp_dGen i, map_mul,
      QExpansion.D_mul]
    ring

/-- The `q`-expansion map intertwines the two Serre derivatives. -/
@[simp] theorem qexp_serreD (k : ℝ) (p : QM) :
    qexp (serreD k p) = QExpansion.serreD k (qexp p) := by
  rw [serreD, QExpansion.serreD, map_sub, map_smul, map_mul, qexp_D, qexp_E₂]

end

end PolynomialModel
