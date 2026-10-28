import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Module

/-!
# Comparator challenge: the polynomial model `ℝ[E₂,E₄,E₆]`

Statements of the results on the polynomial model of level `1` quasimodular forms that
`QuasiModularForms/PolynomialModel.lean` formalizes for *Positive quasimodular forms and the sign
uncertainty principle* (arXiv:2608.15415):

* the `𝔰𝔩₂`-triple formed by `D`, the weight operator `H` and `-12δ`, where `δ = ∂/∂E₂`:
  `PolynomialModel.sl2_lie_h_e`, `PolynomialModel.sl2_lie_h_f` and `PolynomialModel.sl2_lie_e_f`;
* equation (64), `D(δG) - δ(DG) = -(w/12)G` for `G` of weight `w`: `PolynomialModel.D_delta`;
* Lemma 4.7, `δ(∂_k G) = ∂_k(δG) + ((w-k)/12)G`: `PolynomialModel.delta_serreD`;
* the compatibility of `D` and `∂_k` with the `q`-expansion map: `PolynomialModel.qexp_D` and
  `PolynomialModel.qexp_serreD`.

Only Mathlib is imported. The definitions are copied verbatim from `QuasiModularForms/`, under the
same namespaces and `open`s, and Comparator checks that the solution uses identical ones.

Only the two `qexp` statements use Ramanujan's identities, the axioms of
`QuasiModularForms/Ramanujan.lean`, which are therefore restated below and permitted in
`comparator/PolynomialModel.json`; `comparator/PolynomialModelSl2.json` checks that the other
four statements need nothing beyond the standard axioms.
-/

open Lean in
/-- Starts a new module as far as Lean's cache of auxiliary lemmas is concerned.

Lean moves the proofs nested in a definition, such as the `Nat.AtLeastTwo` instances behind numerals
like `(12 : ℝ)`, into auxiliary theorems `<definition>._proof_<i>`, and reuses an auxiliary theorem
created earlier in the same module whenever the statements agree. The definitions below come from
several modules of the solution but are collected in this one file, so each section starts by
clearing that cache, `Lean.Meta.auxLemmasExt`, as a new module would. This changes nothing but which
auxiliary theorems the definitions refer to, and it is what makes them elaborate exactly as in the
solution. -/
elab "reset_aux_lemmas" : command => modifyEnv fun env => Meta.auxLemmasExt.setState env {}

section Basic

open Finset PowerSeries

namespace QExpansion

noncomputable section

/-- The operator `D = q d/dq` on formal `q`-expansions: `D (∑ₙ aₙ qⁿ) = ∑ₙ n aₙ qⁿ`. -/
def D (f : ℝ⟦X⟧) : ℝ⟦X⟧ := mk fun n ↦ (n : ℝ) * coeff n f

end

end QExpansion

end Basic

section Eisenstein

reset_aux_lemmas

open ArithmeticFunction Finset PowerSeries
open scoped sigma

namespace QExpansion

noncomputable section

/-- The cuspidal series `∑_{n ≥ 1} σ_k(n) qⁿ`. -/
def qSigma (k : ℕ) : ℝ⟦X⟧ := mk fun n ↦ (σ k n : ℝ)

/-- The quasimodular Eisenstein series `E₂ = 1 - 24 ∑_{n ≥ 1} σ₁(n) qⁿ`. -/
def E₂ : ℝ⟦X⟧ := 1 - (24 : ℝ) • qSigma 1

/-- The Eisenstein series `E₄ = 1 + 240 ∑_{n ≥ 1} σ₃(n) qⁿ`. -/
def E₄ : ℝ⟦X⟧ := 1 + (240 : ℝ) • qSigma 3

/-- The Eisenstein series `E₆ = 1 - 504 ∑_{n ≥ 1} σ₅(n) qⁿ`. -/
def E₆ : ℝ⟦X⟧ := 1 - (504 : ℝ) • qSigma 5

end

end QExpansion

end Eisenstein

section Ramanujan

reset_aux_lemmas

namespace QExpansion

/-- **Ramanujan's identity** `E₂' = (E₂² - E₄)/12`, taken as an axiom. -/
axiom ramanujan_E₂ : D E₂ = (1 / 12 : ℝ) • (E₂ * E₂ - E₄)

/-- **Ramanujan's identity** `E₄' = (E₂E₄ - E₆)/3`, taken as an axiom. -/
axiom ramanujan_E₄ : D E₄ = (1 / 3 : ℝ) • (E₂ * E₄ - E₆)

/-- **Ramanujan's identity** `E₆' = (E₂E₆ - E₄²)/2`, taken as an axiom. -/
axiom ramanujan_E₆ : D E₆ = (1 / 2 : ℝ) • (E₂ * E₆ - E₄ * E₄)

end QExpansion

end Ramanujan

section Serre

reset_aux_lemmas

open ArithmeticFunction Finset PowerSeries
open scoped sigma

namespace QExpansion

noncomputable section

/-- The Serre derivative `∂_k F = F' - (k/12) E₂ F`. -/
def serreD (k : ℝ) (f : ℝ⟦X⟧) : ℝ⟦X⟧ := D f - (k / 12) • (E₂ * f)

end

end QExpansion

end Serre

section Polynomial

reset_aux_lemmas

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

/-- Ramanujan's identities, read as the values of `D` on the three generators. -/
def dGen : Fin 3 → QM
  | 0 => (1 / 12 : ℝ) • (E₂ * E₂ - E₄)
  | 1 => (1 / 3 : ℝ) • (E₂ * E₄ - E₆)
  | 2 => (1 / 2 : ℝ) • (E₂ * E₆ - E₄ * E₄)

/-- `D = q d/dq` on the polynomial model: the derivation determined by Ramanujan's identities. -/
def D : Derivation ℝ QM QM := mkDerivation ℝ dGen

/-- `δ = ∂/∂E₂`, the operator extracting the depth filtration. -/
def delta : Derivation ℝ QM QM := pderiv 0

/-- The weighted Euler operator `2E₂∂/∂E₂ + 4E₄∂/∂E₄ + 6E₆∂/∂E₆`. -/
def eulerOp : Derivation ℝ QM QM :=
  ((2 : ℝ) • E₂) • pderiv 0 + ((4 : ℝ) • E₄) • pderiv 1 + ((6 : ℝ) • E₆) • pderiv 2

/-- `G` is weighted homogeneous of weight `w`, expressed through the Euler operator. -/
def HasWeight (G : QM) (w : ℝ) : Prop := eulerOp G = w • G

/-- `⁅h, e⁆ = 2e` for `e = D` and `h` the weight operator: `D` raises the weight by `2`. -/
theorem sl2_lie_h_e : ⁅eulerOp, D⁆ = (2 : ℝ) • D := sorry

/-- `⁅h, f⁆ = -2f` for `f = -12δ`: `δ` lowers the weight by `2`. -/
theorem sl2_lie_h_f : ⁅eulerOp, (-12 : ℝ) • delta⁆ = (-2 : ℝ) • ((-12 : ℝ) • delta) := sorry

/-- `⁅e, f⁆ = h`: the bracket of `D` with `-12δ` is the weight operator. -/
theorem sl2_lie_e_f : ⁅D, (-12 : ℝ) • delta⁆ = eulerOp := sorry

/-- **Equation (64)**: `D(δG) - δ(DG) = -(w/12)G` for `G` of weight `w`. -/
theorem D_delta {G : QM} {w : ℝ} (h : HasWeight G w) :
    D (delta G) - delta (D G) = (-(w / 12) : ℝ) • G := sorry

/-- The Serre derivative `∂_k G = DG - (k/12)E₂G` on the polynomial model. -/
def serreD (k : ℝ) (G : QM) : QM := D G - (k / 12 : ℝ) • (E₂ * G)

/-- **Lemma 4.7**: `δ(∂_k G) = ∂_k(δG) + ((w-k)/12)G` for `G` of weight `w`. -/
theorem delta_serreD {G : QM} {w : ℝ} (k : ℝ) (h : HasWeight G w) :
    delta (serreD k G) = serreD k (delta G) + ((w - k) / 12 : ℝ) • G := sorry

/-- The `q`-expansion homomorphism `ℝ[E₂,E₄,E₆] → ℝ⟦X⟧`, sending each generator to the
corresponding divisor-sum series. -/
def qexp : QM →ₐ[ℝ] PowerSeries ℝ :=
  aeval ![QExpansion.E₂, QExpansion.E₄, QExpansion.E₆]

/-- The `q`-expansion map intertwines the two `D`'s. Uses Ramanujan's identities. -/
theorem qexp_D (p : QM) : qexp (D p) = QExpansion.D (qexp p) := sorry

/-- The `q`-expansion map intertwines the two Serre derivatives. Uses Ramanujan's identities. -/
theorem qexp_serreD (k : ℝ) (p : QM) :
    qexp (serreD k p) = QExpansion.serreD k (qexp p) := sorry

end

end PolynomialModel

end Polynomial
