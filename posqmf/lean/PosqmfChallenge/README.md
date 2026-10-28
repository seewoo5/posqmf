# Comparator challenges

Each file here states main results of the Lean development in self-contained form: it imports only
Mathlib, so it restates every definition, and every axiom, that its statements need.
[Comparator](https://github.com/leanprover/comparator) then checks, without trusting the proof files,
that the theorems of the same names in the library (`Posqmf.lean`, which imports everything)

1. prove exactly the statements written here, with the definitions written here,
2. use no axioms beyond the permitted ones, and
3. are accepted by the Lean kernel.

The configurations are in [`../comparator`](../comparator), one or two per challenge file, and CI
(`.github/workflows/comparator.yml`) runs all of them.

| Challenge | Results | Configurations |
| --- | --- | --- |
| `KanekoZagier.lean` | Lemmas 2.2, 2.3, 2.4 and equations (18), (20) of [*Positive quasimodular forms and the sign uncertainty principle*](https://arxiv.org/abs/2608.15415) | `KanekoZagier.json` (Ramanujan), `KanekoZagierCoefficients.json` (Lemmas 2.2, 2.3; standard axioms only) |
| `PolynomialModel.lean` | the `sl₂`-triple, equation (64), Lemma 4.7, and the compatibility of `D` and `∂_k` with `q`-expansions | `PolynomialModel.json` (Ramanujan), `PolynomialModelSl2.json` (all but the `q`-expansion statements; standard axioms only) |
| `UncertaintyPrinciple.lean` | Theorem 4.1 (vanishing order, normalization, equation (42)), Lemma 4.8, Proposition 4.9, Propositions 4.21–4.24 and the positivity used in Corollary 4.25 | `UncertaintyPrinciple.json` (Ramanujan) |
| `LogInequalities.lean` | Lemma 4.17 and inequalities (95)–(97) | `LogInequalities.json` |
| `PolymodInequalities.lean` | inequalities (41), (60), (61) of [*Inequalities involving polynomials and quasimodular forms*](https://arxiv.org/abs/2602.10536) | `PolymodInequalities.json` |
| `X_16_5.lean` | negativity of the coefficients of `X_{16,5}` from the 250th on | `X_16_5.json` (Deligne's bound) |
| `D_6_3.lean` | positivity of the coefficients of `𝒟_{6,3}` | `D_6_3.json` |

Numbering refers to the second arXiv version of each paper.

## Axioms

The development takes Ramanujan's identities for `E₂`, `E₄`, `E₆` as axioms
(`QuasiModularForms/Ramanujan.lean`), and `X_16_5.lean` takes Deligne's bound for an opaque `τ` as an
axiom. The challenges restate these axioms, and the configurations that need them list them in
`permitted_axioms`. Comparator compares every permitted axiom between the challenge and the solution
just like a theorem statement, so a solution cannot permit itself a different axiom under the same
name. Every other configuration permits only `propext`, `Quot.sound` and `Classical.choice`.

## Keeping the challenges in sync

Comparator compares definitions syntactically, including the auxiliary theorems
`<definition>._proof_<i>` into which Lean moves the proofs nested in a definition (such as the
`Nat.AtLeastTwo` instances behind the numerals `(12 : ℝ)`). Within one module, Lean reuses such an
auxiliary theorem whenever a later definition needs one with the same statement, but it never reuses
one from another module. A challenge file collects definitions from several modules of the solution,
so it reproduces their module boundaries:

* the definitions coming from one module of the solution form one section, which starts with
  `reset_aux_lemmas` (a command defined at the top of the file that clears Lean's cache of
  auxiliary lemmas, as a new module would);
* each section repeats, verbatim and in order, every definition of that module up to the last one
  the statements need, under the same namespaces and `open`s;
* the imports of the challenge are the Mathlib imports of the solution modules involved.

When a definition in the library changes, change its copy here; when a module of the library gains
or loses a definition before the last one copied here, update the corresponding section. Comparator
reports a mismatch otherwise.

## Running Comparator locally

From `posqmf/lean`, build the library, the challenges, Comparator and `lean4export` (Comparator is a
Lake dependency, so it is built with the project's toolchain, as it has to be):

```sh
lake exe cache get
lake build Posqmf PosqmfChallenge
lake build Comparator/comparator lean4export/lean4export
```

Comparator runs the builds and exports in a [landrun](https://github.com/Zouuup/landrun) sandbox,
which needs Linux. On Linux, build landrun and put it on `PATH` (or point `COMPARATOR_LANDRUN` at it).
On other systems, use the unsandboxed shim that Comparator ships for development. Then run one
configuration at a time:

```sh
export COMPARATOR_LEAN4EXPORT=$PWD/.lake/packages/lean4export/.lake/build/bin/lean4export
export COMPARATOR_LANDRUN=$PWD/.lake/packages/Comparator/scripts/fake-landrun.sh  # not on Linux
lake exe comparator comparator/UncertaintyPrinciple.json
```

A successful run ends with `Your solution is okay!`.
