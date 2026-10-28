# `posqmf`

This repository contains Sage and Lean code related to (positivity of) quasimodular forms, along with supplementary Jupyter notebooks for some of my papers and thesis.

Requirements: SageMath version >= 10.9

## `posqmf`

The directory `posqmf` contains the Sage and Lean code; see [`posqmf/README.md`](posqmf/README.md) for how to generate its Python modules with `preparse.sh` and what each file provides.
The Lean code has a [blueprint](https://seewoo5.github.io/posqmf/blueprint/), and its main results are checked by [Comparator](https://github.com/leanprover/comparator) against self-contained statements in [`posqmf/lean/PosqmfChallenge`](posqmf/lean/PosqmfChallenge).

## `notebooks`

The directory `notebooks` contains the Jupyter notebooks; see [`notebooks/README.md`](notebooks/README.md) for what each of them checks.
