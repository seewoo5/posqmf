import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie
import posqmf.lean.DifferentialOperators.Serre

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

* `QuasiModular.euler_D`: `⁅eulerOp, D⁆ = 2D`, i.e. `D` raises the weight by `2`.
* `QuasiModular.delta_D`: `⁅δ, D⁆ = (1/12) eulerOp`, the `sl₂`-relation of Kaneko--Koike.
* `QuasiModular.delta_serreD`: `δ(∂_k G) = ∂_k(δG) + ((w-k)/12) G` for `G` of weight `w`.
* `QuasiModular.qexp_D`, `qexp_serreD`: the `q`-expansion map intertwines the polynomial `D` and
  `∂_k` with the ones on `ℝ⟦X⟧`.  This is where Ramanujan's identities enter.
-/

open MvPolynomial

namespace QuasiModular

/-- The ring of level-`1` quasimodular forms, modelled as `ℝ[E₂,E₄,E₆]`. -/
abbrev QM := MvPolynomial (Fin 3) ℝ

noncomputable section

/-- The generator `E₂`. -/
def E2 : QM := X 0

/-- The generator `E₄`. -/
def E4 : QM := X 1

/-- The generator `E₆`. -/
def E6 : QM := X 2

/-! ### The derivation `D` -/

/-- Ramanujan's identities, read as the values of `D` on the three generators. -/
def dGen : Fin 3 → QM
  | 0 => (1 / 12 : ℝ) • (E2 * E2 - E4)
  | 1 => (1 / 3 : ℝ) • (E2 * E4 - E6)
  | 2 => (1 / 2 : ℝ) • (E2 * E6 - E4 * E4)

/-- `D = q d/dq` on the polynomial model: the derivation determined by Ramanujan's identities. -/
def D : Derivation ℝ QM QM := mkDerivation ℝ dGen

@[simp] lemma D_E2 : D E2 = (1 / 12 : ℝ) • (E2 * E2 - E4) := mkDerivation_X ℝ dGen 0

@[simp] lemma D_E4 : D E4 = (1 / 3 : ℝ) • (E2 * E4 - E6) := mkDerivation_X ℝ dGen 1

@[simp] lemma D_E6 : D E6 = (1 / 2 : ℝ) • (E2 * E6 - E4 * E4) := mkDerivation_X ℝ dGen 2

/-! ### `δ`, the Euler operator, and weights -/

/-- `δ = ∂/∂E₂`, the operator extracting the depth filtration. -/
def delta : Derivation ℝ QM QM := pderiv 0

@[simp] lemma delta_E2 : delta E2 = 1 := by simp [delta, E2]

@[simp] lemma delta_E4 : delta E4 = 0 := by simp [delta, E4]

@[simp] lemma delta_E6 : delta E6 = 0 := by simp [delta, E6]

/-- The weighted Euler operator `2E₂∂/∂E₂ + 4E₄∂/∂E₄ + 6E₆∂/∂E₆`. -/
def eulerOp : Derivation ℝ QM QM :=
  ((2 : ℝ) • E2) • pderiv 0 + ((4 : ℝ) • E4) • pderiv 1 + ((6 : ℝ) • E6) • pderiv 2

@[simp] lemma eulerOp_E2 : eulerOp E2 = (2 : ℝ) • E2 := by simp [eulerOp, E2, E4, E6]

@[simp] lemma eulerOp_E4 : eulerOp E4 = (4 : ℝ) • E4 := by simp [eulerOp, E2, E4, E6]

@[simp] lemma eulerOp_E6 : eulerOp E6 = (6 : ℝ) • E6 := by simp [eulerOp, E2, E4, E6]

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

lemma hasWeight_E2 : HasWeight E2 2 := eulerOp_E2

lemma hasWeight_E4 : HasWeight E4 4 := eulerOp_E4

lemma hasWeight_E6 : HasWeight E6 6 := eulerOp_E6

/-! ### The two commutator identities -/

/-- `⁅eulerOp, D⁆ = 2D`: the operator `D` raises the weight by `2`. -/
theorem euler_D : ⁅eulerOp, D⁆ = (2 : ℝ) • D := by
  refine derivation_ext fun i ↦ ?_
  have h0 : ⁅eulerOp, D⁆ E2 = ((2 : ℝ) • D) E2 := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, D_E2, eulerOp_E2]
    simp only [Derivation.map_smul, map_sub, Derivation.leibniz, D_E2, eulerOp_E2, eulerOp_E4,
      smul_eq_mul, mul_smul_comm]
    module
  have h1 : ⁅eulerOp, D⁆ E4 = ((2 : ℝ) • D) E4 := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, D_E4, eulerOp_E4]
    simp only [Derivation.map_smul, map_sub, Derivation.leibniz, D_E4, eulerOp_E2, eulerOp_E4,
      eulerOp_E6, smul_eq_mul, mul_smul_comm, mul_comm E4 E2]
    module
  have h2 : ⁅eulerOp, D⁆ E6 = ((2 : ℝ) • D) E6 := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, D_E6, eulerOp_E6]
    simp only [Derivation.map_smul, map_sub, Derivation.leibniz, D_E6, eulerOp_E2, eulerOp_E4,
      eulerOp_E6, smul_eq_mul, mul_smul_comm, mul_comm E6 E2]
    module
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- `⁅δ, D⁆ = (1/12) eulerOp`, the `sl₂`-relation of Kaneko--Koike. -/
theorem delta_D : ⁅delta, D⁆ = (1 / 12 : ℝ) • eulerOp := by
  refine derivation_ext fun i ↦ ?_
  have h0 : ⁅delta, D⁆ E2 = ((1 / 12 : ℝ) • eulerOp) E2 := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, D_E2, delta_E2, eulerOp_E2]
    simp only [Derivation.map_smul, map_sub, Derivation.leibniz, delta_E2, delta_E4,
      Derivation.map_one_eq_zero, smul_eq_mul, mul_one]
    module
  have h1 : ⁅delta, D⁆ E4 = ((1 / 12 : ℝ) • eulerOp) E4 := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, D_E4, delta_E4, eulerOp_E4]
    simp only [Derivation.map_smul, map_sub, Derivation.leibniz, delta_E2, delta_E4, delta_E6,
      map_zero, smul_eq_mul, mul_one, mul_zero]
    module
  have h2 : ⁅delta, D⁆ E6 = ((1 / 12 : ℝ) • eulerOp) E6 := by
    rw [Derivation.commutator_apply, Derivation.smul_apply, D_E6, delta_E6, eulerOp_E6]
    simp only [Derivation.map_smul, map_sub, Derivation.leibniz, delta_E2, delta_E4, delta_E6,
      map_zero, smul_eq_mul, mul_one, mul_zero]
    module
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

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
def serreD (k : ℝ) (G : QM) : QM := D G - (k / 12 : ℝ) • (E2 * G)

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
  (hasWeight_D h).sub (HasWeight.congr_weight ((hasWeight_E2.mul h).smul (k / 12)) (by ring))

/-- **`lem:delta_serre`**: `δ(∂_k G) = ∂_k(δG) + ((w-k)/12)G` for `G` of weight `w`. -/
theorem delta_serreD {G : QM} {w : ℝ} (k : ℝ) (h : HasWeight G w) :
    delta (serreD k G) = serreD k (delta G) + ((w - k) / 12 : ℝ) • G := by
  have hD : delta (D G) = D (delta G) + ((w / 12 : ℝ)) • G := by
    have h1 := D_delta h
    rw [sub_eq_iff_eq_add] at h1
    rw [h1]
    module
  simp only [serreD, map_sub, Derivation.map_smul, Derivation.leibniz, delta_E2, smul_eq_mul,
    mul_one]
  rw [hD]
  module

/-! ### Relation to the `q`-series `E₂`, `E₄`, `E₆`

There are two families of objects called `E₂`, `E₄`, `E₆` in this development, and they are
genuinely different:

* `KanekoZagier.E2 : ℝ⟦X⟧` is the concrete divisor-sum series `1 - 24∑σ₁(n)qⁿ`;
* `QuasiModular.E2 : QM` is an indeterminate of a polynomial ring, carrying no `q`-expansion.

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
  aeval ![KanekoZagier.E2, KanekoZagier.E4, KanekoZagier.E6]

@[simp] lemma qexp_E2 : qexp E2 = KanekoZagier.E2 := by simp [qexp, E2]

@[simp] lemma qexp_E4 : qexp E4 = KanekoZagier.E4 := by simp [qexp, E4]

@[simp] lemma qexp_E6 : qexp E6 = KanekoZagier.E6 := by simp [qexp, E6]

/-- **Ramanujan's identities, packaged.**  The values of the polynomial `D` on the generators
evaluate to the derivatives of the corresponding `q`-series.  This single statement is what the
three axioms of `Ramanujan.lean` amount to, and it is the only place they are used here. -/
theorem qexp_dGen (i : Fin 3) : qexp (dGen i) = KanekoZagier.D (qexp (X i)) := by
  have h0 : qexp (dGen 0) = KanekoZagier.D (qexp E2) := by
    rw [show dGen 0 = (1 / 12 : ℝ) • (E2 * E2 - E4) from rfl, qexp_E2,
      KanekoZagier.ramanujan_E2, map_smul, map_sub, map_mul, qexp_E2, qexp_E4]
  have h1 : qexp (dGen 1) = KanekoZagier.D (qexp E4) := by
    rw [show dGen 1 = (1 / 3 : ℝ) • (E2 * E4 - E6) from rfl, qexp_E4,
      KanekoZagier.ramanujan_E4, map_smul, map_sub, map_mul, qexp_E2, qexp_E4, qexp_E6]
  have h2 : qexp (dGen 2) = KanekoZagier.D (qexp E6) := by
    rw [show dGen 2 = (1 / 2 : ℝ) • (E2 * E6 - E4 * E4) from rfl, qexp_E6,
      KanekoZagier.ramanujan_E6, map_smul, map_sub, map_mul, map_mul, qexp_E2, qexp_E4, qexp_E6]
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The `q`-expansion map intertwines the two `D`'s. -/
@[simp] theorem qexp_D (p : QM) : qexp (D p) = KanekoZagier.D (qexp p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [KanekoZagier.D_C]
  | add p q hp hq => simp [KanekoZagier.D_add, hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp,
      show D (X i) = dGen i from mkDerivation_X ℝ dGen i, qexp_dGen i, map_mul,
      KanekoZagier.D_mul]
    ring

/-- The `q`-expansion map intertwines the two Serre derivatives. -/
@[simp] theorem qexp_serreD (k : ℝ) (p : QM) :
    qexp (serreD k p) = KanekoZagier.serreD k (qexp p) := by
  rw [serreD, KanekoZagier.serreD, map_sub, map_smul, map_mul, qexp_D, qexp_E2]

end

end QuasiModular
