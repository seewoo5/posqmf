import Verso
import VersoManual
import VersoBlueprint
import PosqmfBlueprint.Bibliography
import QuasiModularForms.Coefficients
import QuasiModularForms.Intertwine

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Kaneko–Zagier operators" =>
%%%
tag := "kaneko-zagier"
file := "Kaneko-Zagier-operators"
%%%

:::group "grp:kz"
The second- and third-order Kaneko–Zagier operators, their Fourier coefficients, and the
intertwining criterion.
:::

Modular linear differential operators (MLDOs) are differential operators that preserve modularity.
More precisely, a differential operator $`L` is an MLDO of weight $`K` and type $`(k, k+K)` on
$`\Gamma` if it is a finite-order linear differential operator with holomorphic coefficients such
that $`L(f|_k \gamma) = (Lf)|_{k+K} \gamma` for all $`\gamma \in \Gamma`. For example, the Serre
derivative $`\partial_k` is an MLDO of weight $`2` and type $`(k,k+2)` on
$`\mathrm{SL}_2(\mathbb{Z})`. Another important example comes from the study of supersingular
$`j`-invariants of elliptic curves {Informal.citep kaneko1998supersingular}[]: the Kaneko–Zagier
equation $`L_{2,k} F = 0` with
$$`L_{2,k} = D^2 - \frac{k+1}{6} E_2 D + \frac{k(k+1)}{12}E_2' = \partial_k^2 - \frac{k(k+2)}{144}E_4.`
This chapter follows Section 2 of
_Positive quasimodular forms and the sign uncertainty principle_ {Informal.citep lee2026sign}[]. All statements are identities
of formal $`q`-expansions, and the modularity of the operators plays no role in them.

# The operators

:::definition "def:KZ2" (parent := "grp:kz") (lean := "KanekoZagier.L₂")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:KZ2_def", citation := "Equation (18)" }] }
%%%

For $`k, \alpha \in \mathbb{R}`, the second-order Kaneko–Zagier operator is
$$`L_{2,k}^{\alpha} := L_{2,k} + \alpha E_4 = D^2 - \frac{k+1}{6} E_2 D + \frac{k(k+1)}{12}E_2' + \alpha E_4,`
with $`D` and the Eisenstein series of {uses "def:qexp_D"}[] and {uses "def:eisenstein"}[]. It is
an MLDO of weight $`4` and type $`(k, k+4)` on $`\mathrm{SL}_2(\mathbb{Z})`, and
$`\alpha = 0` gives the classical operator $`L_{2,k}`.
:::

:::lemma_ "lem:KZ2_serre" (parent := "grp:kz") (lean := "KanekoZagier.L₂_eq_serre")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:KZ2_def", citation := "Equation (18)" }] }
%%%

In terms of Serre derivatives, the operator of {uses "def:KZ2"}[] is
$$`L_{2,k}^{\alpha} = \partial_k^2 - \left(\frac{k(k+2)}{144} - \alpha\right) E_4.`
:::

:::proof "lem:KZ2_serre"
This is the expansion of $`\partial_k^2` in {uses "lem:serre_iter_D"}[].
:::

:::definition "def:KZ3" (parent := "grp:kz") (lean := "KanekoZagier.L₃")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:KZ3_def", citation := "Equation (19)" }] }
%%%

For $`k, \alpha, \beta \in \mathbb{R}`, the third-order Kaneko–Zagier operator of Kaneko, Nagatomo
and Sakai {Informal.citep kaneko2017third}[] is
$$`\begin{aligned} L_{3,k}^{(\alpha,\beta)} &:= D^3 - \frac{k+2}{4} E_2 D^2 + \left(\frac{(k+1)(k+2)}{4}E_2' + \alpha E_4\right) D \\ &\quad - \left(\frac{k(k+1)(k+2)}{24}E_2'' + \frac{k\alpha}{4} E_4' - \beta E_6\right), \end{aligned}`
with the series of {uses "def:eisenstein"}[]. It is an MLDO of weight $`6` and type
$`(k, k+6)` on $`\mathrm{SL}_2(\mathbb{Z})`. We write $`L_{3,k} := L_{3,k}^{(0,0)}`.
:::

:::lemma_ "lem:KZ3_serre" (parent := "grp:kz") (lean := "KanekoZagier.L₃_eq_serre")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:KZ3_def_serre", citation := "Equation (20)" }] }
%%%

In terms of Serre derivatives, the operator of {uses "def:KZ3"}[] is
$$`\begin{aligned} L_{3,k}^{(\alpha,\beta)} &= \partial_k^3 + \left(\alpha - \frac{3k^2 + 12k + 8}{144}\right) E_4 \partial_k \\ &\quad + \left(\beta + \frac{k\alpha}{12} - \frac{k^2(k+3)}{864}\right) E_6. \end{aligned}`
:::

:::proof "lem:KZ3_serre"
Substitute the expansion of $`\partial_k^3` in {uses "lem:serre_iter_D"}[], and of $`\partial_k`
itself, and simplify with $`E_2 E_4 = 3E_4' + E_6` from {uses "lem:ramanujan_reductions"}[].
:::

# Fourier coefficients

The following two lemmas give the Fourier coefficients of $`L_{2,k}^{\alpha} G` and
$`L_{3,k}^{(\alpha,\beta)} G` in terms of those of $`G`, as a diagonal term plus a strictly lower
triangular one. They drive every coefficient induction of the later chapters, and they do not
use Ramanujan's identities.

:::lemma_ "lem:KZ2_coeff" (parent := "grp:kz") (lean := "KanekoZagier.coeff_L₂, KanekoZagier.κ₂, KanekoZagier.K₂")
%%%
source := { document := "sign", spans := #[{ anchor := "lem:KZ2_coeff", citation := "Lemma 2.2" }] }
%%%

Let $`G = \sum_{n \ge 0} a_n q^n` and let $`n \ge 0`. For $`k, \alpha \in \mathbb{R}`, the
$`n`-th Fourier coefficient of $`L_{2,k}^{\alpha} G` (see {uses "def:KZ2"}[]) is
$$`[q^n] (L_{2,k}^{\alpha} G) = \kappa_{2,k}^{\alpha}(n) a_n + \sum_{j=0}^{n-1} K_{2,k}^{\alpha}(n,j) a_j,`
where
$$`\begin{aligned} \kappa_{2,k}^{\alpha}(n) &= n^2 - \frac{k+1}{6}n + \alpha, \\ K_{2,k}^{\alpha}(n,j) &= 2(k+1)(2j-k(n-j)) \sigma_1(n-j) + 240 \alpha \sigma_3(n-j). \end{aligned}`
:::

:::proof "lem:KZ2_coeff"
By the definition and {uses "lem:coeff_eisenstein_mul"}[], the $`n`-th coefficient of
$`L_{2,k}^{\alpha}G` is
$$`\begin{aligned} &n^2 a_n - \frac{k+1}{6}\left(na_n - 24 \sum_{j=0}^{n-1} j\sigma_1(n-j)a_j\right) - \frac{k(k+1)}{12} \cdot 24 \sum_{j=0}^{n-1} (n-j) \sigma_1(n-j) a_j \\ &\quad + \alpha a_n + 240\alpha \sum_{j=0}^{n-1} \sigma_3(n-j) a_j, \end{aligned}`
which rearranges to the claimed formula.
:::

:::lemma_ "lem:KZ3_coeff" (parent := "grp:kz") (lean := "KanekoZagier.coeff_L₃, KanekoZagier.κ₃, KanekoZagier.K₃")
%%%
source := { document := "sign", spans := #[{ anchor := "lem:KZ3_coeff", citation := "Lemma 2.3" }] }
%%%

Let $`G = \sum_{n \ge 0} a_n q^n` and let $`n \ge 0`. For $`k, \alpha, \beta \in \mathbb{R}`, the
$`n`-th Fourier coefficient of $`L_{3,k}^{(\alpha,\beta)}G` (see {uses "def:KZ3"}[]) is
$$`[q^n] (L_{3,k}^{(\alpha,\beta)}G) = \kappa_{3,k}^{(\alpha,\beta)}(n) a_n + \sum_{j=0}^{n-1} K_{3,k}^{(\alpha,\beta)}(n,j) a_j,`
where $`\kappa_{3,k}^{(\alpha,\beta)}(n) = n^3 - \frac{k+2}{4}n^2 + \alpha n + \beta` and
$$`\begin{aligned} K_{3,k}^{(\alpha,\beta)}(n,j) &= (k+2)(6j^2 - 6(k+1)(n-j)j + k(k+1)(n-j)^2) \sigma_1(n-j) \\ &\quad + 60\alpha(4j - k(n-j)) \sigma_3(n-j) - 504\beta \sigma_5(n-j). \end{aligned}`
:::

:::proof "lem:KZ3_coeff"
By the definition and {uses "lem:coeff_eisenstein_mul"}[], the $`n`-th coefficient of
$`L_{3,k}^{(\alpha,\beta)}G` is
$$`\begin{aligned} &n^3 a_n - \frac{k+2}{4}\left(n^2 a_n - 24 \sum_{j=0}^{n-1} \sigma_1(n-j)j^2 a_j\right) \\ &\quad - \frac{(k+1)(k+2)}{4}\cdot 24 \sum_{j=0}^{n-1} (n-j)\sigma_1(n-j) ja_j \\ &\quad + \alpha \left(na_n + 240 \sum_{j=0}^{n-1} \sigma_3(n-j) ja_j \right) + \frac{k(k+1)(k+2)}{24} \cdot 24\sum_{j=0}^{n-1} (n-j)^2 \sigma_1(n-j) a_j \\ &\quad - \frac{k\alpha}{4} \cdot240 \sum_{j=0}^{n-1} (n-j) \sigma_3(n-j) a_j + \beta \left(a_n - 504 \sum_{j=0}^{n-1} \sigma_5(n-j)a_j\right), \end{aligned}`
which rearranges to the claimed formula.
:::

# The intertwining criterion

The second- and third-order operators can be commuted past each other when their parameters are
suitably related. In the proof, and in the formalization, all four operators are written in their
Serre-derivative forms.

:::definition "def:intertwine_params" (parent := "grp:kz") (lean := "KanekoZagier.shiftA, KanekoZagier.shiftB, KanekoZagier.shiftC, KanekoZagier.shiftA', KanekoZagier.shiftB', KanekoZagier.shiftC', KanekoZagier.L₂S, KanekoZagier.L₃S")
For $`k, \alpha, \beta, \gamma, \alpha', \beta', \gamma' \in \mathbb{R}`, the shifted parameters are
$$`\begin{aligned} A &:= \alpha - \frac{3k^2+36k+104}{144}, & A' &:= \alpha' - \frac{3k^2+12k+8}{144}, \\ B &:= \beta + \frac{k+4}{12}\alpha - \frac{(k+4)^2(k+7)}{864}, & B' &:= \beta' + \frac{k}{12}\alpha' - \frac{k^2(k+3)}{864}, \\ C &:= \gamma - \frac{k(k+2)}{144}, & C' &:= \gamma' - \frac{(k+6)(k+8)}{144}. \end{aligned}`
By {uses "lem:KZ2_serre"}[] and {uses "lem:KZ3_serre"}[], the four operators below have the
Serre-derivative forms
$$`\begin{aligned} L_{2,k}^{\gamma} &= \partial_k^2 + C E_4, & L_{3,k+4}^{(\alpha,\beta)} &= \partial_{k+4}^3 + A E_4\partial_{k+4} + B E_6, \\ L_{2,k+6}^{\gamma'} &= \partial_{k+6}^2 + C' E_4, & L_{3,k}^{(\alpha',\beta')} &= \partial_k^3 + A' E_4\partial_k + B' E_6. \end{aligned}`
:::

:::lemma_ "lem:intertwine_normal_forms" (parent := "grp:kz") (lean := "KanekoZagier.L₃S_comp_L₂S, KanekoZagier.L₂S_comp_L₃S")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:intertwine_lhs", citation := "Equations (29) and (30)" }] }
%%%

With the notation of {uses "def:intertwine_params"}[], the two composites have the normal forms
$$`\begin{aligned} L_{3,k+4}^{(\alpha,\beta)} L_{2,k}^{\gamma} &= \partial_k^5 +(A+C)E_4\partial_k^3 +(B-C)E_6\partial_k^2 \\ &\quad + C\left(A+\frac{1}{2}\right)E_4^2\partial_k + C\left(B-\frac{A}{3}-\frac{1}{9}\right)E_4E_6, \end{aligned}`
$$`\begin{aligned} L_{2,k+6}^{\gamma'} L_{3,k}^{(\alpha',\beta')} &= \partial_k^5 +(A'+C')E_4\partial_k^3 + \left(B'-\frac{2A'}{3}\right)E_6\partial_k^2 \\ &\quad + \left(A'\left(C'+\frac{1}{6}\right)-B'\right)E_4^2\partial_k + B'\left(C'+\frac{1}{3}\right)E_4E_6. \end{aligned}`
:::

:::proof "lem:intertwine_normal_forms"
Repeatedly apply the product rule {uses "lem:serre_product_rule"}[] together with Ramanujan's
identities in Serre form {uses "lem:ramanujan_serre"}[], pushing each Serre derivative past the
modular factors $`E_4`, $`E_6` and $`E_4^2` until only iterated Serre derivatives of $`F` remain.
:::

:::lemma_ "lem:intertwine" (parent := "grp:kz") (lean := "KanekoZagier.L₃_comp_L₂_eq_L₂_comp_L₃, KanekoZagier.L₃S_comp_L₂S_eq_L₂S_comp_L₃S")
%%%
source := { document := "sign", spans := #[{ anchor := "lem:intertwine", citation := "Lemma 2.4" }] }
%%%

Let $`k, \alpha,\beta,\gamma,\alpha',\beta',\gamma' \in \mathbb{R}`, with the shifted parameters
of {uses "def:intertwine_params"}[]. Then the intertwining relation
$$`L_{3,k+4}^{(\alpha,\beta)} L_{2,k}^{\gamma} = L_{2,k+6}^{\gamma'} L_{3,k}^{(\alpha',\beta')}`
holds if
$$`\begin{aligned} A+C &= A'+C', & B-C &= B'-\frac{2}{3}A', \\ C\left(A+\frac{1}{2}\right) &= A'\left(C'+\frac{1}{6}\right)-B', & C\left(B-\frac{A}{3}-\frac{1}{9}\right) &= B'\left(C'+\frac{1}{3}\right). \end{aligned}`
:::

:::proof "lem:intertwine"
By {uses "lem:intertwine_normal_forms"}[] the two composites are combinations of the same five
operators $`\partial_k^5`, $`E_4\partial_k^3`, $`E_6\partial_k^2`, $`E_4^2\partial_k` and
$`E_4E_6`, and the four constraints say exactly that the last four coefficients agree.

The converse, that the intertwining relation forces the four constraints, needs the linear
independence of those five operators and is not formalized.
:::
