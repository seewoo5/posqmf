# `posqmf`

This repository contains Sage and Lean code related to (positivity of) quasimodular forms, along with supplementary Jupyter notebooks for some of my papers and thesis.

Requirements: SageMath version >= 10.9

## `preparse.sh`

Running `sh preparse.sh` will generate python scripts (including `__init__.py`) under the directory `posqmf`, from the `sage` files in `posqmf/sage`. This allows you to use import them directly as

```
from posqmf import *
```

## `notebooks`

The directory `notebooks` contains the Jupyter notebooks; see [`notebooks/README.md`](notebooks/README.md) for what each of them checks.
