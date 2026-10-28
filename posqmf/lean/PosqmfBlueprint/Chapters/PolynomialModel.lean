import Verso
import VersoManual
import VersoBlueprint
import PosqmfBlueprint.Bibliography
import QuasiModularForms.PolynomialModel

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "The polynomial model and the operator δ" =>
%%%
tag := "polynomial-model"
file := "Polynomial-model"
%%%

:::group "grp:poly"
Quasimodular forms of level one as polynomials in $`E_2`, $`E_4`, $`E_6`, with the operators
$`D`, $`\delta` and the weight operator.
:::

The ring of quasimodular forms of level $`1` is isomorphic to a polynomial ring in $`E_2`, $`E_4`
and $`E_6`, and the depth of a quasimodular form is its degree in $`E_2`. For a quasimodular form
$`G = \sum_{j=0}^{r} E_2^j G_j`, with $`G_j` modular, define (equation (62) of
_Positive quasimodular forms and the sign uncertainty principle_ {Informal.citep lee2026sign}[])
$$`\delta G = \frac{\partial G}{\partial E_2} := \sum_{j=1}^{r} j E_2^{j-1} G_j.`
If $`G` has weight $`w` and depth $`r \geq 1`, then $`\delta G` has weight $`w - 2` and depth
$`r - 1`; $`\delta E_2 = 1`; $`\delta G = 0` if and only if $`G` is a modular form; and $`\delta`
satisfies the Leibniz rule. The operator $`\delta` reads the polynomial, not the $`q`-expansion, so
it cannot be defined on the power series model of the previous chapters. This chapter supplies the
missing layer: $`E_2`, $`E_4` and $`E_6` become the variables of the polynomial ring
$`\mathbb{R}[E_2, E_4, E_6]`, which is a faithful model since they are algebraically independent,
and a $`q`-expansion map connects it with the power series model.

Everything is done with derivations, which reduces the proofs to checks on the three generators.
Weighted homogeneity is expressed through the weight operator rather than through degrees, so that
weights are automatically compatible with products and with $`D`.

# Derivations on the polynomial model

:::definition "def:QM" (parent := "grp:poly") (lean := "PolynomialModel.QM, PolynomialModel.E₂, PolynomialModel.E₄, PolynomialModel.E₆")
The polynomial model of the ring of quasimodular forms of level $`1` is the polynomial ring
$`\mathcal{QM} := \mathbb{R}[E_2, E_4, E_6]` in three variables named $`E_2`, $`E_4` and $`E_6`.
:::

:::definition "def:poly_D" (parent := "grp:poly") (lean := "PolynomialModel.D, PolynomialModel.dGen, PolynomialModel.D_E₂, PolynomialModel.D_E₄, PolynomialModel.D_E₆")
$`D` is the derivation of $`\mathcal{QM}` ({uses "def:QM"}[]) determined by Ramanujan's identities
on the generators:
$$`D E_2 = \frac{E_2^2 - E_4}{12}, \quad D E_4 = \frac{E_2E_4 - E_6}{3}, \quad D E_6 = \frac{E_2 E_6 - E_4^2}{2}.`
In the polynomial model these are definitions, not axioms; compare {bpref "thm:ramanujan"}[].
:::

:::definition "def:delta" (parent := "grp:poly") (lean := "PolynomialModel.delta, PolynomialModel.delta_E₂, PolynomialModel.delta_E₄, PolynomialModel.delta_E₆")
$`\delta = \frac{\partial}{\partial E_2}` is the partial derivative of $`\mathcal{QM}`
({uses "def:QM"}[]) with respect to $`E_2`. So $`\delta E_2 = 1` and
$`\delta E_4 = \delta E_6 = 0`.
:::

:::definition "def:weight" (parent := "grp:poly") (lean := "PolynomialModel.eulerOp, PolynomialModel.HasWeight")
The weight operator is the weighted Euler derivation of $`\mathcal{QM}` ({uses "def:QM"}[])
$$`H = 2E_2 \frac{\partial}{\partial E_2} + 4E_4 \frac{\partial}{\partial E_4} + 6E_6 \frac{\partial}{\partial E_6},`
and $`G \in \mathcal{QM}` has weight $`w \in \mathbb{R}` if $`H G = w G`.
:::

:::lemma_ "lem:weight_closure" (parent := "grp:poly") (lean := "PolynomialModel.HasWeight.mul, PolynomialModel.HasWeight.add, PolynomialModel.HasWeight.sub, PolynomialModel.HasWeight.smul, PolynomialModel.HasWeight.pow, PolynomialModel.hasWeight_E₂, PolynomialModel.hasWeight_E₄, PolynomialModel.hasWeight_E₆, PolynomialModel.hasWeight_D, PolynomialModel.hasWeight_delta")
$`E_2`, $`E_4`, $`E_6` have weights $`2`, $`4`, $`6`; weights add under products and are preserved
by sums and scalar multiples (in the sense of {uses "def:weight"}[]); and $`D` and $`\delta` raise
and lower the weight by $`2`.
:::

:::proof "lem:weight_closure"
Since $`H` is a derivation, $`H(GG') = (HG)G' + G(HG')`, which gives the statements about
products. The statements about $`D` and $`\delta` follow from the commutators
{uses "lem:sl2"}[]: if $`HG = wG` then $`H(DG) = D(HG) + 2DG = (w+2)DG`, and similarly for
$`\delta`.
:::

# The sl₂-triple
%%%
file := "sl2-triple"
%%%

The three operators $`D`, $`\partial = -12\delta` and $`H` form an $`\mathfrak{sl}_2`-triple
{Informal.citep kaneko2006extremal}[].

:::lemma_ "lem:sl2" (parent := "grp:poly") (lean := "PolynomialModel.euler_D, PolynomialModel.euler_delta, PolynomialModel.delta_D, PolynomialModel.sl2_lie_h_e, PolynomialModel.sl2_lie_h_f, PolynomialModel.sl2_lie_e_f")
As derivations of $`\mathcal{QM}`, with $`D`, $`\delta` and $`H` of {uses "def:poly_D"}[],
{uses "def:delta"}[] and {uses "def:weight"}[],
$$`[H, D] = 2D, \qquad [H, \delta] = -2\delta, \qquad [\delta, D] = \frac{1}{12} H.`
Equivalently, $`e = D`, $`h = H` and $`f = -12\delta` satisfy $`[h, e] = 2e`, $`[h, f] = -2f` and
$`[e, f] = h`.
:::

:::proof "lem:sl2"
A commutator of derivations is a derivation, so each identity only needs to be checked on the
generators $`E_2`, $`E_4`, $`E_6`, where it is a direct computation. For example
$$`[\delta, D] E_2 = \delta\left(\frac{E_2^2 - E_4}{12}\right) - D(1) = \frac{E_2}{6} = \frac{1}{12} H E_2.`
:::

:::lemma_ "lem:D_delta" (parent := "grp:poly") (lean := "PolynomialModel.D_delta")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:D_delta", citation := "Equation (64)" }] }
%%%

For $`G` of weight $`w` (in the sense of {uses "def:weight"}[]),
$$`D(\delta G) - \delta(DG) = -\frac{w}{12} G.`
:::

:::proof "lem:D_delta"
Apply $`[\delta, D] = \frac{1}{12}H` from {uses "lem:sl2"}[] to $`G` and use $`HG = wG`.
:::

# The Serre derivative and δ
%%%
file := "Serre-derivative-and-delta"
%%%

:::definition "def:poly_serre" (parent := "grp:poly") (lean := "PolynomialModel.serreD")
On the polynomial model, the Serre derivative is $`\partial_k G = DG - \frac{k}{12} E_2 G`, with
$`D` from {uses "def:poly_D"}[].
:::

:::lemma_ "lem:delta_serre" (parent := "grp:poly") (lean := "PolynomialModel.delta_serreD")
%%%
source := { document := "sign", spans := #[{ anchor := "lem:delta_serre", citation := "Lemma 4.7" }] }
%%%

Let $`G` be a quasimodular form of homogeneous weight $`w`. Then, with $`\partial_k` as in
{uses "def:poly_serre"}[],
$$`\delta(\partial_k G) = \partial_k(\delta G) + \frac{w-k}{12} G.`
:::

:::proof "lem:delta_serre"
By {uses "lem:D_delta"}[], $`D(\delta G) - \delta(DG) = -\frac{w}{12} G`. By
$`D = \partial_k + \frac{k}{12} E_2`, we have
$$`\begin{aligned} D(\delta G) &= \partial_k (\delta G) + \frac{k}{12} E_2(\delta G), \\ \delta(DG) &= \delta(\partial_k G) + \frac{k}{12} \delta(E_2 G) = \delta(\partial_k G) + \frac{k}{12} E_2(\delta G) + \frac{k}{12} G, \end{aligned}`
and plugging these into the first identity gives the claim.
:::

:::lemma_ "lem:serre_collapse" (parent := "grp:poly") (lean := "PolynomialModel.serreD_collapse")
For every $`G` and $`w`,
$`\frac{1}{6}\partial_w G + \frac{1}{6}\partial_{w-2} G = \frac{1}{3}\partial_{w-1} G`, with the
Serre derivatives of {uses "def:poly_serre"}[].
:::

:::proof "lem:serre_collapse"
The Serre derivative is affine in its index: both sides equal
$`\frac{1}{3} DG - \frac{2w-2}{72} E_2 G`.
:::

# The q-expansion map

:::definition "def:qexp_map" (parent := "grp:poly") (lean := "PolynomialModel.qexp, PolynomialModel.qexp_E₂, PolynomialModel.qexp_E₄, PolynomialModel.qexp_E₆")
The $`q`-expansion map $`\mathcal{QM} \to \mathbb{R}[[q]]` is the $`\mathbb{R}`-algebra
homomorphism that evaluates a polynomial at the Eisenstein series $`E_2`, $`E_4`, $`E_6` of
{uses "def:eisenstein"}[]. Here $`\mathcal{QM}` is the ring of {uses "def:QM"}[].
:::

:::lemma_ "lem:qexp_compat" (parent := "grp:poly") (lean := "PolynomialModel.qexp_dGen, PolynomialModel.qexp_D, PolynomialModel.qexp_serreD")
The $`q`-expansion map {uses "def:qexp_map"}[] intertwines the derivatives and the Serre
derivatives of the two models: for every $`p \in \mathcal{QM}` and $`k`, the $`q`-expansion of
$`Dp` is $`D` applied to the $`q`-expansion of $`p`, and likewise for $`\partial_k`.
:::

:::proof "lem:qexp_compat"
Both sides are derivations along the $`q`-expansion map, so it suffices to compare them on the
generators, where the claim is exactly Ramanujan's identities {uses "thm:ramanujan"}[]. This is
the only place where the axioms enter the polynomial model, and it is what transports identities
proved polynomially (where $`\delta` and weights are available) to $`q`-expansions (where
coefficients can be computed). The statement for $`\partial_k` follows from the one for $`D`,
since the map sends $`E_2` to $`E_2`.
:::
