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

`polymod.ipynb` checkes the identities in the paper [Inequalities involving polynomials and quasimodular forms](arxivlink), where the `.lean` files under `posqmf/lean` provides formal proof of some inequalities in the paper. 
Lean files are initially written by AxiomProver and manually golfed afterwards., which can be checked by `lake exe cache get && lake build`.
