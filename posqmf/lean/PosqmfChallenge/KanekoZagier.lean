import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Module

/-!
# Comparator challenge: the Kaneko–Zagier operators

Statements of the results on Kaneko–Zagier operators in *Positive quasimodular forms and the sign
uncertainty principle* (arXiv:2608.15415) that `QuasiModularForms/` formalizes, at the level of
formal `q`-expansions `ℝ⟦X⟧`:

* the Serre-derivative forms (18) and (20) of the two operators: `KanekoZagier.L₂_eq_serre` and
  `KanekoZagier.L₃_eq_serre`;
* Lemma 2.2 and Lemma 2.3, the Fourier coefficients of `L_{2,k}^α G` and `L_{3,k}^{(α,β)} G`:
  `KanekoZagier.coeff_L₂` and `KanekoZagier.coeff_L₃`;
* Lemma 2.4, the intertwining criterion: `KanekoZagier.L₃_comp_L₂_eq_L₂_comp_L₃`.

Only Mathlib is imported. The definitions are copied verbatim from `QuasiModularForms/`, under the
same namespaces and `open`s, and Comparator checks that the solution uses identical ones.

The development takes Ramanujan's identities as axioms (`QuasiModularForms/Ramanujan.lean`), so they
are restated below. `comparator/KanekoZagier.json` permits them, and Comparator checks that the
solution's axioms of these names state exactly what is written here; the coefficient formulas do not
use them, which `comparator/KanekoZagierCoefficients.json` checks.
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

/-- The `r`-fold Serre derivative `∂_k^r F = ∂_{k+2(r-1)} ∂_{k+2(r-2)} ⋯ ∂_k F`. -/
def serreDIter (k : ℝ) : ℕ → ℝ⟦X⟧ → ℝ⟦X⟧
  | 0, f => f
  | r + 1, f => serreD (k + 2 * r) (serreDIter k r f)

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

/-- **Serre form of the second-order operator**, equation (18):
`L_{2,k}^α = ∂_k² - (k(k+2)/144 - α)E₄`. Uses Ramanujan's identities. -/
theorem L₂_eq_serre (k α : ℝ) (f : ℝ⟦X⟧) :
    L₂ k α f = serreDIter k 2 f - (k * (k + 2) / 144 - α) • (E₄ * f) := sorry

/-- **Serre form of the third-order operator**, equation (20):
`L_{3,k}^{(α,β)} = ∂_k³ + (α - (3k²+12k+8)/144)E₄∂_k + (β + kα/12 - k²(k+3)/864)E₆`.
Uses Ramanujan's identities. -/
theorem L₃_eq_serre (k α β : ℝ) (f : ℝ⟦X⟧) :
    L₃ k α β f = serreDIter k 3 f + (α - (3 * k ^ 2 + 12 * k + 8) / 144) • (E₄ * serreD k f)
      + (β + k * α / 12 - k ^ 2 * (k + 3) / 864) • (E₆ * f) := sorry

end

end KanekoZagier

end Operators

section Coefficients

reset_aux_lemmas

open ArithmeticFunction Finset PowerSeries QExpansion
open scoped sigma

namespace KanekoZagier

noncomputable section

/-- `κ_{2,k}^α(n) = n² - ((k+1)/6)n + α`, the diagonal coefficient of
`L_{2,k}^α`. -/
def κ₂ (k α : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ 2 - (k + 1) / 6 * n + α

/-- `K_{2,k}^α(n,j) = 2(k+1)(2j - k(n-j))σ₁(n-j) + 240ασ₃(n-j)`, the strictly lower
triangular part of `L_{2,k}^α`. -/
def K₂ (k α : ℝ) (n j : ℕ) : ℝ :=
  2 * (k + 1) * (2 * (j : ℝ) - k * ((n : ℝ) - (j : ℝ))) * (σ 1 (n - j) : ℝ)
    + 240 * α * (σ 3 (n - j) : ℝ)

/-- `κ_{3,k}^{(α,β)}(n) = n³ - ((k+2)/4)n² + αn + β`. -/
def κ₃ (k α β : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ 3 - (k + 2) / 4 * (n : ℝ) ^ 2 + α * n + β

/-- The strictly lower triangular part `K_{3,k}^{(α,β)}(n,j)` of `L_{3,k}^{(α,β)}`. -/
def K₃ (k α β : ℝ) (n j : ℕ) : ℝ :=
  (k + 2) * (6 * (j : ℝ) ^ 2 - 6 * (k + 1) * ((n : ℝ) - (j : ℝ)) * (j : ℝ)
      + k * (k + 1) * ((n : ℝ) - (j : ℝ)) ^ 2) * (σ 1 (n - j) : ℝ)
    + 60 * α * (4 * (j : ℝ) - k * ((n : ℝ) - (j : ℝ))) * (σ 3 (n - j) : ℝ)
    - 504 * β * (σ 5 (n - j) : ℝ)

/-- **Lemma 2.2**, the coefficients of the second-order operator:
`[qⁿ](L_{2,k}^α G) = κ_{2,k}^α(n) aₙ + ∑_{j<n} K_{2,k}^α(n,j) a_j`. -/
theorem coeff_L₂ (k α : ℝ) (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (L₂ k α G) = κ₂ k α n * coeff n G + ∑ j ∈ range n, K₂ k α n j * coeff j G := sorry

/-- **Lemma 2.3**, the coefficients of the third-order operator:
`[qⁿ](L_{3,k}^{(α,β)} G) = κ_{3,k}^{(α,β)}(n) aₙ + ∑_{j<n} K_{3,k}^{(α,β)}(n,j) a_j`. -/
theorem coeff_L₃ (k α β : ℝ) (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (L₃ k α β G)
      = κ₃ k α β n * coeff n G + ∑ j ∈ range n, K₃ k α β n j * coeff j G := sorry

end

end KanekoZagier

end Coefficients

section Intertwine

reset_aux_lemmas

namespace KanekoZagier

open PowerSeries QExpansion

noncomputable section

/-- `L_{2,k}^γ` in Serre form, `∂_k² + C E₄`, with `C = γ - k(k+2)/144`. -/
def L₂S (k C : ℝ) (f : ℝ⟦X⟧) : ℝ⟦X⟧ := serreDIter k 2 f + C • (E₄ * f)

/-- `L_{3,k}^{(α,β)}` in Serre form, `∂_k³ + A E₄∂_k + B E₆`. -/
def L₃S (k A B : ℝ) (f : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  serreDIter k 3 f + A • (E₄ * serreD k f) + B • (E₆ * f)

/-- `A := α - (3k²+36k+104)/144`, the `E₄∂` coefficient of `L_{3,k+4}^{(α,β)}`. -/
def shiftA (k α : ℝ) : ℝ := α - (3 * k ^ 2 + 36 * k + 104) / 144

/-- `B := β + ((k+4)/12)α - (k+4)²(k+7)/864`, the `E₆` coefficient of `L_{3,k+4}^{(α,β)}`. -/
def shiftB (k α β : ℝ) : ℝ := β + (k + 4) / 12 * α - (k + 4) ^ 2 * (k + 7) / 864

/-- `C := γ - k(k+2)/144`, the `E₄` coefficient of `L_{2,k}^{γ}`. -/
def shiftC (k γ : ℝ) : ℝ := γ - k * (k + 2) / 144

/-- `A' := α' - (3k²+12k+8)/144`, the `E₄∂` coefficient of `L_{3,k}^{(α',β')}`. -/
def shiftA' (k α' : ℝ) : ℝ := α' - (3 * k ^ 2 + 12 * k + 8) / 144

/-- `B' := β' + (k/12)α' - k²(k+3)/864`, the `E₆` coefficient of `L_{3,k}^{(α',β')}`. -/
def shiftB' (k α' β' : ℝ) : ℝ := β' + k / 12 * α' - k ^ 2 * (k + 3) / 864

/-- `C' := γ' - (k+6)(k+8)/144`, the `E₄` coefficient of `L_{2,k+6}^{γ'}`. -/
def shiftC' (k γ' : ℝ) : ℝ := γ' - (k + 6) * (k + 8) / 144

/-- **Lemma 2.4**, the intertwining criterion: the four constraints on the shifted parameters
imply `L_{3,k+4}^{(α,β)} L_{2,k}^{γ} = L_{2,k+6}^{γ'} L_{3,k}^{(α',β')}`. Uses Ramanujan's
identities. -/
theorem L₃_comp_L₂_eq_L₂_comp_L₃ (k α β γ α' β' γ' : ℝ)
    (h₁ : shiftA k α + shiftC k γ = shiftA' k α' + shiftC' k γ')
    (h₂ : shiftB k α β - shiftC k γ = shiftB' k α' β' - 2 * shiftA' k α' / 3)
    (h₃ : shiftC k γ * (shiftA k α + 1 / 2)
      = shiftA' k α' * (shiftC' k γ' + 1 / 6) - shiftB' k α' β')
    (h₄ : shiftC k γ * (shiftB k α β - shiftA k α / 3 - 1 / 9)
      = shiftB' k α' β' * (shiftC' k γ' + 1 / 3))
    (f : ℝ⟦X⟧) :
    L₃ (k + 4) α β (L₂ k γ f) = L₂ (k + 6) γ' (L₃ k α' β' f) := sorry

end

end KanekoZagier

end Intertwine
