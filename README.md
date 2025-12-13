# `posqmf`

This repository contains sage codes related to quasimodular forms, along with supplementary Jupyter notebooks for some of my papers.

Requirements: SageMath version >= 10.6

## `preparse.sh`

Running `sh preparse.sh` will generate python scripts (including `__init__.py`) under the directory `posqmf`, from the `sage` files in `posqmf/sage`. This allows you to use import them directly as

```
from posqmf import *
```

## Algebraic proof of modular form inequalities for optimal sphere packings

`sphere_packing_ineq.ipynb` checks the identities in the paper [Algebraic proof of modular form inequalities for optimal sphere packings](https://arxiv.org/abs/2406.14659).
