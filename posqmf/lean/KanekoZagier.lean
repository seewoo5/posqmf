import posqmf.lean.KanekoZagier.Basic
import posqmf.lean.KanekoZagier.Coefficients
import posqmf.lean.KanekoZagier.Eisenstein
import posqmf.lean.KanekoZagier.Intertwine
import posqmf.lean.KanekoZagier.Operators
import posqmf.lean.KanekoZagier.Ramanujan
import posqmf.lean.KanekoZagier.Serre

/-!
# Kaneko--Zagier operators on formal `q`-expansions

This directory formalises the operator bookkeeping of §2 of *Positive quasimodular forms and the
sign uncertainty principle*, at the level of formal `q`-series rather than of functions on the
complex upper half plane.  Concretely, `ℝ⟦X⟧` is the ring of `q`-expansions (`X` is `q`),
`D = q d/dq`, and `E₂`, `E₄`, `E₆` are the explicit divisor-sum series `eqn:e2fourier`
--`eqn:e6fourier`.  Everything is then an identity of formal power series, which is exactly the
level at which the paper's computations take place.

## Contents

| file | contents |
| --- | --- |
| `Basic` | `D = q d/dq`, the Leibniz rule, and the convolution lemma `coeff_mk_mul` |
| `Eisenstein` | `E₂`, `E₄`, `E₆`, their derivatives, and coefficients of products with them |
| `Ramanujan` | Ramanujan's identities `eqn:ramanujan` (axioms) and the reductions they give |
| `Serre` | `∂_k`, `∂_k^r`, the product rule, `eqn:ramanujan_serre`, `∂_k²` and `∂_k³` in `D`-form |
| `Operators` | `L_{2,k}^α`, `L_{3,k}^{(α,β)}` and the `D`-form `=` Serre-form theorems |
| `Coefficients` | `lem:KZ2_coeff` and `lem:KZ3_coeff` |
| `Intertwine` | the `∂_k⁵` normal forms of the composed operators, and `lem:intertwine` (`⟸`) |

## Verification-plan items covered

* **1.1** `eqn:KZ3_def = eqn:KZ3_def_serre`: `KanekoZagier.L3_eq_serre`
  (together with `KanekoZagier.L2_eq_serre` for the second-order case).
* **1.2** `lem:KZ2_coeff`, `eqn:kappa2`, `eqn:K2`: `KanekoZagier.coeff_L2`.
* **1.3** `lem:KZ3_coeff`, `eqn:KZ3_kappa`, `eqn:KZ3_K`: `KanekoZagier.coeff_L3`.
* **1.4** `eqn:intertwine_lhs`, `eqn:intertwine_rhs`: `KanekoZagier.L3S_comp_L2S` and
  `KanekoZagier.L2S_comp_L3S`.
* **1.5**, `⟸` half: `KanekoZagier.L3_comp_L2_eq_L2_comp_L3` — the four constraints
  `eqn:intertwine_constraints` imply `eqn:intertwine`.  The `⟹` half needs uniqueness of the
  Serre-derivative normal form and is not formalized here.

## Axioms

Ramanujan's identities `eqn:ramanujan` are taken as axioms (`KanekoZagier.ramanujan_E2`,
`ramanujan_E4`, `ramanujan_E6`); see `Ramanujan.lean`.  What each result actually uses:

```
#print axioms KanekoZagier.coeff_L2                     -- none beyond Lean's own three
#print axioms KanekoZagier.coeff_L3                     -- none beyond Lean's own three
#print axioms KanekoZagier.L2_eq_serre                  -- ramanujan_E2
#print axioms KanekoZagier.L3_eq_serre                  -- ramanujan_E2, ramanujan_E4
#print axioms KanekoZagier.L3S_comp_L2S                 -- ramanujan_E4, ramanujan_E6
#print axioms KanekoZagier.L2S_comp_L3S                 -- ramanujan_E4, ramanujan_E6
#print axioms KanekoZagier.L3_comp_L2_eq_L2_comp_L3     -- all three
```

The coefficient formulas are unconditional: they read off `eqn:KZ2_def` and `eqn:KZ3_def` directly
from the `q`-expansions.  The `*_eq_serre` theorems need Ramanujan to convert powers of `E₂` into
derivatives, and the intertwining normal forms need it only through `∂₄E₄ = -E₆/3` and
`∂₆E₆ = -E₄²/2` — the whole `∂_k⁵` computation stays inside the Serre calculus and never touches
`E₂` again.
-/
