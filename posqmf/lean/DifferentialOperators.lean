import posqmf.lean.DifferentialOperators.Basic
import posqmf.lean.DifferentialOperators.Coefficients
import posqmf.lean.DifferentialOperators.Eisenstein
import posqmf.lean.DifferentialOperators.Intertwine
import posqmf.lean.DifferentialOperators.KanekoZagier
import posqmf.lean.DifferentialOperators.Ramanujan
import posqmf.lean.DifferentialOperators.Serre

/-!
# Kaneko--Zagier operators on formal `q`-expansions

This directory formalises the operator bookkeeping of §2 of *Positive quasimodular forms and the
sign uncertainty principle*, at the level of formal `q`-series rather than of functions on the
complex upper half plane.  Concretely, `ℝ⟦X⟧` is the ring of `q`-expansions (`X` is `q`),
`D = q d/dq`, and `E₂`, `E₄`, `E₆` are the explicit divisor-sum series.  Everything is then an
identity of formal power series, which is exactly the level at which the paper's computations
take place.

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

## Verification-plan items covered

* **1.1** the `D`-form and Serre form of the third-order operator agree:
  `KanekoZagier.L3_eq_serre` (together with `KanekoZagier.L2_eq_serre` for the second-order case).
* **1.2** Fourier coefficients of `L_{2,k}^α`: `KanekoZagier.coeff_L2`.
* **1.3** Fourier coefficients of `L_{3,k}^{(α,β)}`: `KanekoZagier.coeff_L3`.
* **1.4** the two `∂_k⁵` normal forms: `KanekoZagier.L3S_comp_L2S` and
  `KanekoZagier.L2S_comp_L3S`.
* **1.5**, `⟸` half: `KanekoZagier.L3_comp_L2_eq_L2_comp_L3` — the four constraints on the
  shifted parameters imply the intertwining relation.  The `⟹` half needs uniqueness of the
  Serre-derivative normal form and is not formalized here.

## Axioms

Ramanujan's identities are taken as axioms (`KanekoZagier.ramanujan_E₂`,
`ramanujan_E₄`, `ramanujan_E₆`); see `Ramanujan.lean`.  What each result actually uses:

```
#print axioms KanekoZagier.coeff_L2                     -- none beyond Lean's own three
#print axioms KanekoZagier.coeff_L3                     -- none beyond Lean's own three
#print axioms KanekoZagier.L2_eq_serre                  -- ramanujan_E₂
#print axioms KanekoZagier.L3_eq_serre                  -- ramanujan_E₂, ramanujan_E₄
#print axioms KanekoZagier.L3S_comp_L2S                 -- ramanujan_E₄, ramanujan_E₆
#print axioms KanekoZagier.L2S_comp_L3S                 -- ramanujan_E₄, ramanujan_E₆
#print axioms KanekoZagier.L3_comp_L2_eq_L2_comp_L3     -- all three
```

The coefficient formulas are unconditional: they read the `D`-forms of the two operators directly
off the `q`-expansions.  The `*_eq_serre` theorems need Ramanujan to convert powers of `E₂` into
derivatives, and the intertwining normal forms need it only through `∂₄E₄ = -E₆/3` and
`∂₆E₆ = -E₄²/2` — the whole `∂_k⁵` computation stays inside the Serre calculus and never touches
`E₂` again.
-/
