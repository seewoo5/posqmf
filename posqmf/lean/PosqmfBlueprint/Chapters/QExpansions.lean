import Verso
import VersoManual
import VersoBlueprint
import PosqmfBlueprint.Bibliography
import QuasiModularForms.Serre

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Eisenstein series and the Serre derivative" =>
%%%
tag := "eisenstein-series"
file := "Eisenstein-series"
%%%

:::group "grp:qexp"
Formal $`q`-expansions, the Eisenstein series, Ramanujan's identities and the Serre derivative.
:::

This chapter sets up the power series model of quasimodular forms of level $`1`, following
Section 2 of
_Positive quasimodular forms and the sign uncertainty principle_ {Informal.citep lee2026sign}[]. A quasimodular form $`F` has a Fourier expansion
$`F = \sum_{n \ge 0} a_n q^n` in $`q = e^{2\pi i z}`, and every identity used later is an identity
between such expansions. So $`F` is represented here by its formal $`q`-expansion, an element of
the ring $`\mathbb{R}[[q]]` of formal power series with real coefficients (`ℝ⟦X⟧` in Lean, with
`X` playing the role of $`q`).

# The derivative

:::definition "def:qexp_D" (parent := "grp:qexp") (lean := "QExpansion.D, QExpansion.coeff_D")
The derivative of quasimodular forms is (equation (7))
$$`D F = F' := \frac{1}{2\pi i}\frac{dF}{dz}, \qquad \sum_n a_n q^n \longmapsto \sum_n n a_n q^n.`
On formal $`q`-expansions it is the operator $`D = q \frac{d}{dq}`, which multiplies the $`n`-th
coefficient by $`n`.
:::

:::lemma_ "lem:qexp_D_mul" (parent := "grp:qexp") (lean := "QExpansion.D_mul, QExpansion.D_add, QExpansion.D_smul")
$`D` is linear and satisfies the Leibniz rule $`D(FG) = (DF)G + F(DG)`, with $`D` as in
{uses "def:qexp_D"}[].
:::

:::proof "lem:qexp_D_mul"
The $`n`-th coefficient of $`FG` is $`\sum_{i + j = n} a_i b_j`, and $`n = i + j` splits it into the
$`n`-th coefficients of $`(DF)G` and $`F(DG)`.
:::

:::lemma_ "lem:coeff_mk_mul" (parent := "grp:qexp") (lean := "QExpansion.coeff_mk_mul")
If $`f = \sum_{n \ge 1} c_n q^n` has vanishing constant term and $`G = \sum_{n \ge 0} a_n q^n`, then
$$`[q^n](fG) = \sum_{j=0}^{n-1} c_{n-j} a_j.`
:::

:::proof "lem:coeff_mk_mul"
This is the Cauchy product formula, in which the term $`j = n` vanishes because $`c_0 = 0`. Every
coefficient computation below is carried out in this shape: a diagonal term plus a strictly lower
triangular convolution.
:::

# Eisenstein series

For $`n \ge 1` let $`\sigma_k(n) = \sum_{d \mid n} d^k`, and set $`\sigma_k(0) = 0`, as Mathlib does.

:::definition "def:eisenstein" (parent := "grp:qexp") (lean := "QExpansion.qSigma, QExpansion.E₂, QExpansion.E₄, QExpansion.E₆")
The Eisenstein series of weights $`2`, $`4` and $`6` are (equations (4)–(6))
$$`\begin{aligned} E_2 &= 1 - 24 \sum_{n\geq 1}\sigma_1(n)q^n, \\ E_4 &= 1 + 240 \sum_{n \geq 1} \sigma_3(n)q^n, \\ E_6 &= 1 - 504 \sum_{n \geq 1} \sigma_5(n)q^n. \end{aligned}`
$`E_4` and $`E_6` are modular forms, whereas $`E_2` is a quasimodular form of weight $`2` and
level $`1`. In the power series model these formulas are the definitions.
:::

:::lemma_ "lem:coeff_eisenstein_mul" (parent := "grp:qexp") (lean := "QExpansion.coeff_E₂_mul, QExpansion.coeff_E₄_mul, QExpansion.coeff_E₆_mul, QExpansion.coeff_D_E₂_mul, QExpansion.coeff_D_D_E₂_mul, QExpansion.coeff_D_E₄_mul")
For $`G = \sum_{n \ge 0} a_n q^n` and $`n \ge 0`,
$$`\begin{aligned} [q^n](E_2 G) &= a_n - 24 \sum_{j=0}^{n-1} \sigma_1(n-j) a_j, \\ [q^n](E_2' G) &= -24 \sum_{j=0}^{n-1} (n-j) \sigma_1(n-j) a_j, \end{aligned}`
and similarly for $`E_4 G`, $`E_6 G`, $`E_2'' G` and $`E_4' G`.
:::

:::proof "lem:coeff_eisenstein_mul"
Combine the expansions of {uses "def:eisenstein"}[], the description of $`D` in
{uses "def:qexp_D"}[], and {uses "lem:coeff_mk_mul"}[].
:::

# Ramanujan's identities
%%%
file := "Ramanujan-identities"
%%%

:::theorem "thm:ramanujan" (parent := "grp:qexp") (lean := "QExpansion.ramanujan_E₂, QExpansion.ramanujan_E₄, QExpansion.ramanujan_E₆")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:ramanujan", citation := "Equation (8)" }] }
%%%

Ramanujan's identities hold:
$$`E_2' = \frac{E_2^2 - E_4}{12}, \quad E_4' = \frac{E_2E_4 - E_6}{3}, \quad E_6' = \frac{E_2 E_6 - E_4^2}{2}.`
In the formalization these three identities between the series of {uses "def:eisenstein"}[] are
_axioms_.
:::

:::proof "thm:ramanujan"
These are classical (see for instance the lectures of Bruinier, van der Geer, Harder and Zagier).
Comparing coefficients turns them into convolution identities for divisor sums, which is
orthogonal to everything else in the development; replacing the three axioms by theorems is the
only thing needed to make everything downstream unconditional.
:::

:::lemma_ "lem:ramanujan_reductions" (parent := "grp:qexp") (lean := "QExpansion.E₂_mul_E₂, QExpansion.E₂_mul_E₄, QExpansion.E₂_mul_D_E₂")
$`E_2^2 = 12 E_2' + E_4`, $`E_2 E_4 = 3 E_4' + E_6`, and
$`E_2 E_2' = 6 E_2'' + \frac{1}{2} E_4'`.
:::

:::proof "lem:ramanujan_reductions"
The first two are {uses "thm:ramanujan"}[] rearranged. The third follows by differentiating the
first with {uses "lem:qexp_D_mul"}[]: $`2 E_2 E_2' = 12 E_2'' + E_4'`. These are the rules that
remove the products of $`E_2` with $`E_2`, $`E_4` and $`E_2'` that appear when an iterated Serre
derivative is written out in terms of $`D`.
:::

# The Serre derivative

:::definition "def:serre" (parent := "grp:qexp") (lean := "QExpansion.serreD, QExpansion.serreDIter")
For $`k \in \mathbb{R}`, the Serre derivative is
$$`\partial_k F := F' - \frac{k}{12} E_2 F,`
and the $`r`-fold Serre derivative is
$$`\partial_k^r F := \partial_{k + 2(r-1)} \partial_{k + 2(r-2)} \cdots \partial_{k} F, \qquad \partial_k^0 F := F.`
Here $`D` and $`E_2` are as in {uses "def:qexp_D"}[] and {uses "def:eisenstein"}[]. The weight
$`k` may be any real number, since all identities below are polynomial in $`k`.
:::

The Serre derivative $`\partial_k` maps quasimodular forms of weight $`w` and depth at most $`s` to
quasimodular forms of weight $`w + 2` and depth at most $`s + 1`, and Kaneko and Koike proved that
$`\partial_{w-s}` preserves the space of forms of depth at most $`s`
{Informal.citep kaneko2006extremal}[]. It is equivariant
under $`\mathrm{SL}_2(\mathbb{Z})`, which is why the operators built from it below are modular
linear differential operators. These analytic facts play no role in the formal identities.

:::lemma_ "lem:serre_product_rule" (parent := "grp:qexp") (lean := "QExpansion.serreD_mul")
The Serre derivative of {uses "def:serre"}[] satisfies the product rule
$$`\partial_{w_1 + w_2} (FG) = (\partial_{w_1}F)G + F(\partial_{w_2}G).`
:::

:::proof "lem:serre_product_rule"
Expand both sides with the Leibniz rule {uses "lem:qexp_D_mul"}[]; the $`E_2`-terms match because
$`\frac{w_1 + w_2}{12} = \frac{w_1}{12} + \frac{w_2}{12}`.
:::

:::lemma_ "lem:ramanujan_serre" (parent := "grp:qexp") (lean := "QExpansion.serreD_E₂, QExpansion.serreD_E₄, QExpansion.serreD_E₆")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:ramanujan_serre", citation := "Equation (16)" }] }
%%%

Ramanujan's identities in Serre form:
$$`\partial_1 E_2 = - \frac{1}{12} E_4, \quad \partial_4 E_4 = -\frac{1}{3} E_6, \quad \partial_6 E_6 = - \frac{1}{2} E_4^2.`
:::

:::proof "lem:ramanujan_serre"
Substitute {uses "thm:ramanujan"}[] into the definition {uses "def:serre"}[].
:::

:::lemma_ "lem:serre_iter_D" (parent := "grp:qexp") (lean := "QExpansion.serreD_two_eq, QExpansion.serreD_three_eq")
The iterated Serre derivatives of {uses "def:serre"}[], written out in terms of $`D`:
$$`\partial_k^2 F = F'' - \frac{k+1}{6}E_2F' + \frac{k(k+1)}{12}E_2'F + \frac{k(k+2)}{144}E_4F,`
$$`\begin{aligned} \partial_k^3 F &= F''' - \frac{k+2}{4}E_2F'' + \frac{(k+1)(k+2)}{4}E_2'F' + \frac{3k^2+12k+8}{144}E_4F' \\ &\quad - \frac{k(k+1)(k+2)}{24}E_2''F - \frac{k(3k^2+12k+8)}{576}E_4'F - \frac{k(k+2)(k+4)}{1728}E_6F. \end{aligned}`
:::

:::proof "lem:serre_iter_D"
Expand the definitions with the Leibniz rule {uses "lem:qexp_D_mul"}[], and eliminate $`E_2^2`,
$`E_2E_4` and $`E_2E_2'` with {uses "lem:ramanujan_reductions"}[]. These two identities are the
computations behind the two Kaneko–Zagier operators of the next chapter.
:::
