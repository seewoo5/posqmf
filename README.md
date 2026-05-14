# `posqmf`

This repository contains sage codes related to (positivity of) quasimodular forms, along with supplementary Jupyter notebooks for some of my papers and thesis.

Requirements: SageMath version >= 10.6

## `preparse.sh`

Running `sh preparse.sh` will generate python scripts (including `__init__.py`) under the directory `posqmf`, from the `sage` files in `posqmf/sage`. This allows you to use import them directly as

```
from posqmf import *
```

## `sphere_packing_ineq.ipynb`

`sphere_packing_ineq.ipynb` checks the identities in the paper [Algebraic proof of modular form inequalities for optimal sphere packings](https://arxiv.org/abs/2406.14659).

## `polymod.ipynb`

`polymod.ipynb` checkes the identities in the paper [Inequalities involving polynomials and quasimodular forms](https://arxiv.org/abs/2602.10536).

## `extremal_qm_high_level.ipynb`

`extremal_qm_high_level.ipynb` contains codes related to Chapter 7 of my thesis, which checks the uniqueness and identities related to the extremal quasimodular forms of level $\Gamma_0(N)$ and depth $s$, where $(N, s) \in \{(2, 1), (2, 2), (3, 1), (4, 1)\}$. It also computes Victor-Miller basis for level $\Gamma_0(2)$ and $\Gamma_0(3)$.

## `uncertainty_principle.ipynb`

`uncertainty_principle.ipynb` contains computations related to Chapter 8 and 9 of my thesis. It checks certain identities related to the Feigenbaum-Grabner-Hardin's family of quasiomodular forms $\{F_w\}$ and $\{G_w\}$ for their Fourier eigenfunctions, which are used to prove new upper bounds for the Bourgain-Clozel-Kahane's sign uncertainty principle constant in certain dimensions.
Also, it contains codes checking signs of Fourier coefficients of extremal eisenstein series, which are used to prove new lower bounds.

## `miscellaneous.ipynb`

`miscellaneous.ipynb` contains some miscellaneous codes related to quasimodular forms, including

- Uniqueness of extremal quasimodular forms of weight $\le 200$ and depth $5 \le s \le 10$.
- Non-positiveness of $X_{16, 5}$.
