import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-!
# Comparator challenge: the families `F_w`, `F̃_{w-2}` and `G̃_w`

Statements of the coefficient-positivity results of *Positive quasimodular forms and the sign
uncertainty principle* (arXiv:2608.15415) that `UncertaintyPrinciple/F.lean` and
`UncertaintyPrinciple/G.lean` formalize.

The `(-1)^{d/4}`-family. `fFam N` is the paper's `F_{4N}`, generated from `F₈` by the recurrence
(41) in the polynomial model `ℝ[E₂,E₄,E₆]`, and `ftildeFam N = δ(fFam N)` is `F̃_{4N-2}`.

* Theorem 4.1, the parts used later: the recurrence reproduces the paper's `F₁₂`
  (`UncertaintyPrinciple.fFam_three`), `F_{4N}` has weight `4N` (`hasWeight_fFam`), it vanishes to
  order `N - 1` at the cusp with leading coefficient `1` (`coeff_fSeries_eq_zero`,
  `coeff_fSeries_eq_one`), and it satisfies the third-order equation (42) (`mldeF`);
* `F̃_{4N-2}` has weight `4N - 2` (`hasWeight_ftildeFam`), and `F̃₁₀ = E₄E₄'/86400`
  (`ftildeSeries_three`);
* Lemma 4.8, the recurrence for `F̃`, in the polynomial model for any form of weight `w`
  (`delta_SFp`) and on `q`-expansions for the family (`ftildeSeries_succ`);
* Proposition 4.9: `ã_j > 0` for `1 ≤ j ≤ w/4 - 2` and `ã_{w/4-2} ≥ 1/360`, for `w = 4N`
  (`coeff_ftildeSeries_pos`, `coeff_ftildeSeries_boundary`).

The `(-1)^{d/4+1}`-family. `gtildeFam N` is `G̃_{4N}`, generated from `G̃₀ = 3/(2¹¹·7)` by the
recurrence (99).

* Proposition 4.21, as far as it concerns `G̃_w`: `G̃_w` is a modular form of weight `w`
  (`hasWeight_gtildeFam`, `delta_gtildeFam`), and its `q`-expansion satisfies (99)
  (`gtildeSeries_succ`);
* Proposition 4.22, the third-order equation (100) (`mldeG`);
* Propositions 4.23 and 4.24: `ã_n ≥ 0` for `0 ≤ n ≤ w/4 + 1` (`coeff_gtildeSeries_nonneg`);
* the positivity of the constant term used for the strictness in Corollary 4.25
  (`coeff_gtildeSeries_zero_pos`).

Only Mathlib is imported. The definitions are copied verbatim from `QuasiModularForms/` and
`UncertaintyPrinciple/`, under the same namespaces and `open`s, and Comparator checks that the
solution uses identical ones. Everything that passes through the `q`-expansion map `qexp` uses
Ramanujan's identities, the axioms of `QuasiModularForms/Ramanujan.lean`, which are therefore
restated below and permitted in `comparator/UncertaintyPrinciple.json`.
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

section Operators

reset_aux_lemmas

open PowerSeries QExpansion

namespace KanekoZagier

noncomputable section

/-- The second-order Kaneko–Zagier operator in `D`-form:
`L_{2,k}^α = D² - ((k+1)/6)E₂D + (k(k+1)/12)E₂' + αE₄`. -/
def L₂ (k α : ℝ) (f : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  D (D f) - ((k + 1) / 6) • (E₂ * D f) + (k * (k + 1) / 12) • (D E₂ * f) + α • (E₄ * f)

/-- The third-order Kaneko–Zagier operator in `D`-form:
`L_{3,k}^{(α,β)} = D³ - ((k+2)/4)E₂D² + ((((k+1)(k+2))/4)E₂' + αE₄)D`
`- ((k(k+1)(k+2)/24)E₂'' + (kα/4)E₄' - βE₆)`. -/
def L₃ (k α β : ℝ) (f : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  D (D (D f)) - ((k + 2) / 4) • (E₂ * D (D f))
    + (((k + 1) * (k + 2) / 4) • D E₂ + α • E₄) * D f
    - ((k * (k + 1) * (k + 2) / 24) • D (D E₂) + (k * α / 4) • D E₄ - β • E₆) * f

end

end KanekoZagier

end Operators

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

/-- The Serre derivative `∂_k G = DG - (k/12)E₂G` on the polynomial model. -/
def serreD (k : ℝ) (G : QM) : QM := D G - (k / 12 : ℝ) • (E₂ * G)

/-- The `q`-expansion homomorphism `ℝ[E₂,E₄,E₆] → ℝ⟦X⟧`, sending each generator to the
corresponding divisor-sum series. -/
def qexp : QM →ₐ[ℝ] PowerSeries ℝ :=
  aeval ![QExpansion.E₂, QExpansion.E₄, QExpansion.E₆]

end

end PolynomialModel

end Polynomial

section F

reset_aux_lemmas

open Finset PowerSeries

namespace UncertaintyPrinciple

noncomputable section

section QExpansion

open ArithmeticFunction QExpansion KanekoZagier
open scoped sigma

/-- `α_w = -(w-10)(w-4)/48`, the parameter for which `𝒮_w = -L_{2,w-2}^{α_w}`. -/
def alphaF (w : ℝ) : ℝ := -((w - 10) * (w - 4)) / 48

/-- `𝒮_w = (w-6)(w-5)/36 E₄ - ∂_w∂_{w-2} = -L_{2,w-2}^{α_w}`. -/
def SF (w : ℝ) (f : ℝ⟦X⟧) : ℝ⟦X⟧ := -L₂ (w - 2) (alphaF w) f

/-- The positive scalar `c_w = 3(w-4)w / (16(w-10)(w-5)(w-3)(w+2))` in the recurrence. -/
def cF (w : ℝ) : ℝ := 3 * (w - 4) * w / (16 * (w - 10) * (w - 5) * (w - 3) * (w + 2))

/-- The right-hand side of the recurrence for `F̃`: `c_w(𝒮_w F̃_{w-2} - (1/3)∂_{w-1}F_w)`. -/
def ftildeStep (w : ℝ) (F Ft : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  cF w • (SF w Ft - (1 / 3 : ℝ) • serreD (w - 1) F)

/-- `F̃₁₀ = (1/360)E₄X_{6,1}`, where `X_{6,1} = ∑_{n ≥ 1} nσ₃(n)qⁿ = E₄'/240`. -/
def ftilde₁₀ : ℝ⟦X⟧ := (1 / 86400 : ℝ) • (E₄ * D E₄)

end QExpansion

section PolynomialModel

open PolynomialModel

/-- `𝒮_w = ((w-6)(w-5)/36)E₄ - ∂_w∂_{w-2}` on the polynomial model. -/
def SFp (w : ℝ) (G : QM) : QM :=
  ((w - 6) * (w - 5) / 36 : ℝ) • (E₄ * G) - serreD w (serreD (w - 2) G)

/-- **Lemma 4.8, polynomially**: applying `δ` to `𝒮_w F_w` for `F_w` of weight `w` gives
`𝒮_w(δF_w) - (1/3)∂_{w-1}F_w`. -/
theorem delta_SFp {w : ℝ} {Fw : QM} (h : HasWeight Fw w) :
    delta (SFp w Fw) = SFp w (delta Fw) - (1 / 3 : ℝ) • serreD (w - 1) Fw := sorry

/-- `F₈ = (1/1728)(E₂²E₄ - 2E₂E₆ + E₄²)`. -/
def F₈ : QM := (1 / 1728 : ℝ) • (E₂ ^ 2 * E₄ - (2 : ℝ) • (E₂ * E₆) + E₄ ^ 2)

/-- `F₁₂ = (1/518400)(E₂²E₄² - 2E₂E₄E₆ + E₆²)`. -/
def F₁₂ : QM := (1 / 518400 : ℝ) • (E₂ ^ 2 * E₄ ^ 2 - (2 : ℝ) • (E₂ * E₄ * E₆) + E₆ ^ 2)

/-- The family `F_{4N}` of Feigenbaum--Grabner--Hardin, generated from `F₈` by the recurrence.

`F₀` and `F₄` are not part of the family; setting them to zero makes the index match the weight, so
that `fFam N` is `F_{4N}` and the statements below can be read directly against the paper. -/
def fFam : ℕ → QM
  | 0 => 0
  | 1 => 0
  | 2 => F₈
  | N + 3 => cF (4 * N + 8) • SFp (4 * N + 8) (fFam (N + 2))

/-- `F_{4N}` has weight `4N`. -/
theorem hasWeight_fFam : ∀ N : ℕ, HasWeight (fFam N) (4 * N) := sorry

/-- The recurrence carries `F₈` to the paper's `F₁₂`. -/
theorem fFam_three : fFam 3 = F₁₂ := sorry

/-- `F̃_{4N-2} = δF_{4N}` in the polynomial model. -/
def ftildeFam (N : ℕ) : QM := delta (fFam N)

/-- `F̃_{4N-2}` has weight `4N - 2`. -/
theorem hasWeight_ftildeFam (N : ℕ) : HasWeight (ftildeFam N) (4 * N - 2) := sorry

/-- The `q`-expansion of `F̃_{4N-2}`. -/
def ftildeSeries (N : ℕ) : ℝ⟦X⟧ := qexp (ftildeFam N)

/-- The `q`-expansion of `F_{4N}`. -/
def fSeries (N : ℕ) : ℝ⟦X⟧ := qexp (fFam N)

/-- **Lemma 4.8**, the recurrence for `F̃` on `q`-expansions, from `F₈` on. -/
theorem ftildeSeries_succ {N : ℕ} (hN : 2 ≤ N) :
    ftildeSeries (N + 1) = ftildeStep (4 * (N : ℝ)) (fSeries N) (ftildeSeries N) := sorry

/-- The base case `F̃₁₀ = δF₁₂ = (1/360)E₄X_{6,1}`. -/
theorem ftildeSeries_three : ftildeSeries 3 = ftilde₁₀ := sorry

/-- **Theorem 4.1, vanishing order**: `F_{4N}` vanishes to order `N - 1` at the cusp. -/
theorem coeff_fSeries_eq_zero : ∀ N k : ℕ, k + 2 ≤ N → coeff k (fSeries N) = 0 := sorry

/-- **Theorem 4.1, equation (42)**: `L_{3,w-2}^{((w-4)/4,0)}F_w = 0` for `w = 4N`. -/
theorem mldeF (N : ℕ) (hN : 2 ≤ N) :
    KanekoZagier.L₃ (4 * (N : ℝ) - 2) ((4 * (N : ℝ) - 4) / 4) 0 (fSeries N) = 0 := sorry

/-- **Theorem 4.1, normalization**: the first nonzero coefficient of `F_{4N}`, at the cusp index
`N - 1`, is `1`. -/
theorem coeff_fSeries_eq_one (N : ℕ) (hN : 2 ≤ N) : coeff (N - 1) (fSeries N) = 1 := sorry

/-- **Proposition 4.9, positivity**: for `w = 4N`, `ã_j > 0` for `1 ≤ j ≤ w/4 - 2`. -/
theorem coeff_ftildeSeries_pos (N j : ℕ) (hN : 2 ≤ N) (hj1 : 1 ≤ j) (hj : j ≤ N - 2) :
    0 < coeff j (ftildeSeries N) := sorry

/-- **Proposition 4.9, boundary index**: for `w = 4N ≥ 12`, `ã_{w/4-2} ≥ 1/360`. -/
theorem coeff_ftildeSeries_boundary (N : ℕ) (hN : 3 ≤ N) :
    1 / 360 ≤ coeff (N - 2) (ftildeSeries N) := sorry

end PolynomialModel

end

end UncertaintyPrinciple

end F

section G

reset_aux_lemmas

open Finset PowerSeries

namespace UncertaintyPrinciple

noncomputable section

section QExpansion

open ArithmeticFunction QExpansion KanekoZagier
open scoped sigma

/-- `α_w = -(w+6)(w+16)/48`, the parameter for which `𝒩_w = L_{2,w}^{α_w}`. -/
def alphaG (w : ℝ) : ℝ := -((w + 6) * (w + 16)) / 48

/-- The parameter `α = -(w+6)/4` of the third-order operator annihilating `G̃_w`. -/
def alphaOdeG (w : ℝ) : ℝ := -(w + 6) / 4

/-- The positive scalar `c_w = 3(w+10)(w+14) / (16(w+4)(w+9)(w+11)(w+16))`. -/
def cG (w : ℝ) : ℝ := 3 * (w + 10) * (w + 14) / (16 * (w + 4) * (w + 9) * (w + 11) * (w + 16))

/-- The right-hand side of the recurrence for `G̃`: `c_w(-L_{2,w}^{α_w} G̃_w)`. -/
def gtildeStep (w : ℝ) (Gt : ℝ⟦X⟧) : ℝ⟦X⟧ := cG w • (-L₂ w (alphaG w) Gt)

/-- `A_w(r)`, the `σ₁`-part of the combined boundary kernel. -/
def Aw (w r : ℝ) : ℝ :=
  (w + 4) / (3 * (w + 8) * (w + 12))
    * (16 * w ^ 3 * r ^ 2 - 18 * w ^ 3 * r + 3 * w ^ 3 + 240 * w ^ 2 * r ^ 2 - 342 * w ^ 2 * r
      + 69 * w ^ 2 + 896 * w * r ^ 2 - 1908 * w * r + 528 * w + 960 * r ^ 2 - 2592 * r + 1344)

/-- `B_w(r)`, the `σ₃`-part of the combined boundary kernel. -/
def Bw (w r : ℝ) : ℝ :=
  5 * (w + 4) * (w + 6) / ((w + 8) * (w + 12))
    * (w ^ 2 + 16 * w * r + 16 * w + 160 * r + 64)

/-- `G̃₀ = 3/(2¹¹·7)`, a positive constant. -/
def gtilde₀ : ℝ⟦X⟧ := (3 / 14336 : ℝ) • 1

end QExpansion

section PolynomialModel

open PolynomialModel

/-- `-L_{2,w}^{α_w} = ((w+8)(w+9)/36)E₄ - ∂_w²` on the polynomial model. -/
def SGp (w : ℝ) (G : QM) : QM :=
  ((w + 8) * (w + 9) / 36 : ℝ) • (E₄ * G) - serreD (w + 2) (serreD w G)

/-- The family `G̃_{4N}` in the polynomial model. -/
def gtildeFam : ℕ → QM
  | 0 => (3 / 14336 : ℝ) • 1
  | N + 1 => cG (4 * N) • SGp (4 * N) (gtildeFam N)

/-- `G̃_{4N}` has weight `4N`. -/
theorem hasWeight_gtildeFam : ∀ N : ℕ, HasWeight (gtildeFam N) (4 * N) := sorry

/-- **`G̃_w` has depth `0`**: it is a modular form, a polynomial in `E₄` and `E₆` alone. -/
theorem delta_gtildeFam : ∀ N : ℕ, delta (gtildeFam N) = 0 := sorry

/-- The `q`-expansion of `G̃_{4N}`. -/
def gtildeSeries (N : ℕ) : ℝ⟦X⟧ := qexp (gtildeFam N)

/-- **Equation (99)**, the recurrence for `G̃` on `q`-expansions. -/
theorem gtildeSeries_succ (N : ℕ) :
    gtildeSeries (N + 1) = gtildeStep (4 * (N : ℝ)) (gtildeSeries N) := sorry

end PolynomialModel

section Conclusion

open ArithmeticFunction QExpansion KanekoZagier

/-- **Proposition 4.22**, the third-order equation (100), `L_{3,w}^{(-(w+6)/4,0)} G̃_w = 0`, for
every `w = 4N`. -/
theorem mldeG (N : ℕ) : L₃ (4 * (N : ℝ)) (alphaOdeG (4 * (N : ℝ))) 0 (gtildeSeries N) = 0 := sorry

/-- **Propositions 4.23 and 4.24**: for `w = 4N`, every coefficient `ã_n` of `G̃_w` with
`0 ≤ n ≤ w/4 + 1 = N + 1` is nonnegative. -/
theorem coeff_gtildeSeries_nonneg (N : ℕ) : ∀ n, n ≤ N + 1 → 0 ≤ coeff n (gtildeSeries N) :=
  sorry

/-- The constant term of `G̃_w` is strictly positive, which gives the strictness in
Corollary 4.25. -/
theorem coeff_gtildeSeries_zero_pos (N : ℕ) : 0 < coeff 0 (gtildeSeries N) := sorry

end Conclusion

end

end UncertaintyPrinciple

end G
