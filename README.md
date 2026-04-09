# `posqmf`

This repository contains sage codes related to (positivity of) quasimodular forms, along with supplementary Jupyter notebooks for some of my papers.

Requirements: SageMath version >= 10.6

## `preparse.sh`

Running `sh preparse.sh` will generate python scripts (including `__init__.py`) under the directory `posqmf`, from the `sage` files in `posqmf/sage`. This allows you to use import them directly as

```
from posqmf import *
```

## Algebraic proof of modular form inequalities for optimal sphere packings

`sphere_packing_ineq.ipynb` checks the identities in the paper [Algebraic proof of modular form inequalities for optimal sphere packings](https://arxiv.org/abs/2406.14659).

## Inequalities involving polynomials and quasimodular forms

`polymod.ipynb` checkes the identities in the paper [Inequalities involving polynomials and quasimodular forms](https://arxiv.org/abs/2602.10536), where the `.lean` files under `posqmf/lean` provides formal proof of some inequalities in the paper. 
Lean files are initially written by AxiomProver and manually golfed afterwards., which can be checked by `lake exe cache get && lake build`.

## Miscellaneous

`miscellaneous.ipynb` contains some miscellaneous codes related to quasimodular forms, including

- Depth $s \ge 5$ extremal quasimodular forms. Uniqueness check for $5 \le s \le 10$ and $w \le 200$. Non-positiveness of $X_{16, 5}$.