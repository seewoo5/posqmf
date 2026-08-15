import posqmf.lean.QuasiModularForms.Basic
import posqmf.lean.QuasiModularForms.Coefficients
import posqmf.lean.QuasiModularForms.Eisenstein
import posqmf.lean.QuasiModularForms.Intertwine
import posqmf.lean.QuasiModularForms.KanekoZagier
import posqmf.lean.QuasiModularForms.PolynomialModel
import posqmf.lean.QuasiModularForms.Ramanujan
import posqmf.lean.QuasiModularForms.Serre

/-!
# Quasimodular forms, on `q`-expansions and as polynomials

This directory formalises the operator bookkeeping of §2 of *Positive quasimodular forms and the
sign uncertainty principle*, at the level of formal `q`-series rather than of functions on the
complex upper half plane.  Concretely, `ℝ⟦X⟧` is the ring of `q`-expansions (`X` is `q`),
`D = q d/dq`, and `E₂`, `E₄`, `E₆` are the explicit divisor-sum series.  Everything is then an
identity of formal power series, which is exactly the level at which the paper's computations
take place.  A second model, `ℝ[E₂,E₄,E₆]`, is set up in `PolynomialModel`; it is needed because
`δ = ∂/∂E₂` is not an operator on `q`-series.  The two are joined by the algebra map `qexp`.

The `q`-expansion layer lives in namespace `QExpansion` and the polynomial one in
`PolynomialModel`; `KanekoZagier` is reserved for what is actually Kaneko--Zagier's, namely the
operators `L_{2,k}^α` and `L_{3,k}^{(α,β)}`, their Fourier coefficients, and the intertwining
criterion.

## Contents

| file | contents |
| --- | --- |
| `Basic` | `D = q d/dq`, the Leibniz rule, and the convolution lemma `coeff_mk_mul` |
| `Eisenstein` | `E₂`, `E₄`, `E₆`, their derivatives, and coefficients of products with them |
| `Ramanujan` | Ramanujan's identities (axioms) and the reductions they give |
| `Serre` | `∂_k`, `∂_k^r`, the product rule, and `∂_k²`, `∂_k³` written out in `D`-form |
| `KanekoZagier` | `L_{2,k}^α`, `L_{3,k}^{(α,β)}` and the `D`-form `=` Serre-form theorems |
| `Coefficients` | Fourier coefficients of the two operators |
| `Intertwine` | `∂_k⁵` normal forms of the composed operators, intertwining criterion (`⟸`) |
| `PolynomialModel` | `ℝ[E₂,E₄,E₆]` with `D`, `δ`, the weight operator, `∂_k`, and `qexp` |

## Verification-plan items covered

* **1.1** the `D`-form and Serre form of the third-order operator agree:
  `KanekoZagier.L₃_eq_serre` (together with `KanekoZagier.L₂_eq_serre` for the second-order case).
* **1.2** Fourier coefficients of `L_{2,k}^α`: `KanekoZagier.coeff_L₂`.
* **1.3** Fourier coefficients of `L_{3,k}^{(α,β)}`: `KanekoZagier.coeff_L₃`.
* **1.4** the two `∂_k⁵` normal forms: `KanekoZagier.L₃S_comp_L₂S` and
  `KanekoZagier.L₂S_comp_L₃S`.
* **1.5**, `⟸` half: `KanekoZagier.L₃_comp_L₂_eq_L₂_comp_L₃` — the four constraints on the
  shifted parameters imply the intertwining relation.  The `⟹` half needs uniqueness of the
  Serre-derivative normal form and is not formalized here.

## Axioms

Ramanujan's identities are taken as axioms (`QExpansion.ramanujan_E₂`,
`ramanujan_E₄`, `ramanujan_E₆`); see `Ramanujan.lean`.  What each result actually uses:

```
#print axioms KanekoZagier.coeff_L₂                     -- none beyond Lean's own three
#print axioms KanekoZagier.coeff_L₃                     -- none beyond Lean's own three
#print axioms KanekoZagier.L₂_eq_serre                  -- ramanujan_E₂
#print axioms KanekoZagier.L₃_eq_serre                  -- ramanujan_E₂, ramanujan_E₄
#print axioms KanekoZagier.L₃S_comp_L₂S                 -- ramanujan_E₄, ramanujan_E₆
#print axioms KanekoZagier.L₂S_comp_L₃S                 -- ramanujan_E₄, ramanujan_E₆
#print axioms KanekoZagier.L₃_comp_L₂_eq_L₂_comp_L₃     -- all three
```

The coefficient formulas are unconditional: they read the `D`-forms of the two operators directly
off the `q`-expansions.  The `*_eq_serre` theorems need Ramanujan to convert powers of `E₂` into
derivatives, and the intertwining normal forms need it only through `∂₄E₄ = -E₆/3` and
`∂₆E₆ = -E₄²/2` — the whole `∂_k⁵` computation stays inside the Serre calculus and never touches
`E₂` again.
-/
