import Verso
import VersoManual
import VersoBlueprint
import PosqmfBlueprint.Bibliography
import UncertaintyPrinciple.G

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "The family G̃ and the nonnegativity of its coefficients" =>
%%%
tag := "g-family"
file := "G-family"
%%%

:::group "grp:G"
The $`(-1)^{d/4+1}`-eigenforms of Feigenbaum, Grabner and Hardin and the nonnegativity of the
coefficients of $`\widetilde{G}_{w}`.
:::

This chapter follows Section 4.2 of
_Positive quasimodular forms and the sign uncertainty principle_ {Informal.citep lee2026sign}[]. The
$`(-1)^{d/4+1}`-eigenfunctions of Feigenbaum, Grabner and Hardin arise from functions $`G_w` of
level $`\Gamma(2)` (Theorem 4.12 of {Informal.citet lee2026sign}[]), which are not modular forms:
they involve the Jacobi theta functions and the logarithm $`\mathcal{L}_S` of the modular
$`\lambda`-function. By Proposition 4.21 of {Informal.citet lee2026sign}[], for each even
$`w \geq 4` there are a level $`1` modular form $`\widetilde{G}_{w-12}` and a level $`\Gamma(2)`
modular form $`\Psi_w` such that
$$`G_w = \widetilde{G}_{w-12}\, \Delta\, \mathcal{L}_S + \Psi_w,`
with $`\widetilde{G}_{0} = \frac{3}{2^{11} \cdot 7}`, and for $`w \equiv 0 \pmod{4}` with $`w \ge 0`
$$`\widetilde{G}_{w+4} = \frac{3(w+10)(w+14)}{16(w+4)(w+9)(w+11)(w+16)} \left(\frac{(w+8)(w+9)}{36} E_4 \widetilde{G}_{w} - \partial_{w}^{2} \widetilde{G}_{w}\right).`
The value of the eigenfunction at the origin is $`M_{d,-}(\mathbf{0}) = -\pi b_{0,-}`, where
$$`\begin{aligned} b_{0,-} &= \sum_{j=0}^{n_{d,-} - 1} p_{24(n_{d,-} - 1)}(n_{d,-} - 1 - j)\, \tilde{a}_{j}^{(w-12)}, \\ \widetilde{G}_{w} &= \sum_{n \ge 0} \tilde{a}_{n}^{(w)} q^n, \end{aligned}`
and since $`n_{d,-}` is $`\frac{w}{4} - 2` or $`\frac{w}{4} - 1`, it is enough to show that
$`\tilde{a}_{n}^{(w)} \ge 0` for all $`0 \le n \le \frac{w}{4} + 1`. This is Propositions 4.23 and
4.24, the goal of the chapter.

The formalization takes the recurrence as the definition of $`\widetilde{G}_w`. Deriving the
recurrence from the decomposition above needs its uniqueness, an argument about modular functions
for $`\Gamma(2)` (if $`A \mathcal{L}_S + B = 0` with $`A`, $`B` nonzero modular forms then
$`\log(1-\lambda)` would be a rational function of $`\lambda`), which lies outside the
development. In Lean, `gtildeFam N` is $`\widetilde{G}_{4N}`.

# The family G̃
%%%
file := "The-family-Gtilde"
%%%

:::definition "def:Gtilde" (parent := "grp:G") (lean := "UncertaintyPrinciple.gtildeFam, UncertaintyPrinciple.SGp, UncertaintyPrinciple.cG, UncertaintyPrinciple.gtildeSeries")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:Gtilde_rec", citation := "Proposition 4.21, Equation (99)" }] }
%%%

Define $`\widetilde{G}_w \in \mathcal{QM}` (see {uses "def:QM"}[]) for $`w \equiv 0 \pmod 4` with
$`w \ge 0` by $`\widetilde{G}_0 = \frac{3}{2^{11} \cdot 7}` and
$$`\begin{aligned} \widetilde{G}_{w+4} &= c_w \left(\frac{(w+8)(w+9)}{36} E_4 \widetilde{G}_{w} - \partial_{w+2} \partial_{w} \widetilde{G}_{w}\right), \\ c_w &= \frac{3(w+10)(w+14)}{16(w+4)(w+9)(w+11)(w+16)}, \end{aligned}`
with the Serre derivatives of {uses "def:poly_serre"}[]. Write
$`\widetilde{G}_{w} = \sum_{n \ge 0} \tilde{a}_{n}^{(w)} q^n` for its $`q`-expansion.
:::

:::lemma_ "lem:Gtilde_modular" (parent := "grp:G") (lean := "UncertaintyPrinciple.hasWeight_gtildeFam, UncertaintyPrinciple.delta_gtildeFam")
%%%
source := { document := "sign", spans := #[{ anchor := "prop:Gw_comp", citation := "Proposition 4.21" }] }
%%%

$`\widetilde{G}_w` ({uses "def:Gtilde"}[]) has weight $`w` and $`\delta \widetilde{G}_w = 0`, so it is
a modular form of level $`1`: a polynomial in $`E_4` and $`E_6` alone.
:::

:::proof "lem:Gtilde_modular"
The weight is preserved by the recurrence as in {uses "lem:weight_closure"}[]. For the depth,
Lemma 4.7 ({uses "lem:delta_serre"}[]) carries the correction $`\frac{w-k}{12}G`, which vanishes
exactly when the Serre derivative is taken at the weight of the form, as it is here: if
$`\delta\widetilde{G}_w = 0` then $`\delta(\partial_w \widetilde{G}_w) = 0`, then
$`\delta(\partial_{w+2}\partial_w \widetilde{G}_w) = 0`, and so $`\delta \widetilde{G}_{w+4} = 0`.
The recurrence for $`F_w` instead applies $`\partial_{w-2}` to $`F_w`, which is off by the depth
$`2`; that is why $`E_2` enters there and $`\widetilde{F}_{w-2} = \delta F_w` is not zero.
:::

:::lemma_ "lem:Gtilde_rec" (parent := "grp:G") (lean := "UncertaintyPrinciple.gtildeSeries_succ, UncertaintyPrinciple.gtildeStep, UncertaintyPrinciple.alphaG, UncertaintyPrinciple.qexp_SGp, UncertaintyPrinciple.gtildeSeries_zero")
On $`q`-expansions, the recurrence of {uses "def:Gtilde"}[] reads
$$`\widetilde{G}_{w+4} = -c_w L_{2,w}^{\alpha_w} \widetilde{G}_w, \qquad \alpha_w = -\frac{(w+6)(w+16)}{48}.`
:::

:::proof "lem:Gtilde_rec"
By {uses "lem:KZ2_serre"}[],
$`L_{2,w}^{\alpha_w} = \partial_w^2 - \left(\frac{w(w+2)}{144} - \alpha_w\right)E_4 = \partial_w^2 - \frac{(w+8)(w+9)}{36} E_4`,
and the $`q`-expansion map is compatible with the Serre derivatives by {uses "lem:qexp_compat"}[].
:::

# The differential equation

:::proposition "prop:Gtilde_ode" (parent := "grp:G") (lean := "UncertaintyPrinciple.mldeG, UncertaintyPrinciple.mldeG_step, UncertaintyPrinciple.mldeG_zero, UncertaintyPrinciple.alphaOdeG")
%%%
source := { document := "sign", spans := #[{ anchor := "prop:Gtilde_ode", citation := "Proposition 4.22" }] }
%%%

For all $`w \equiv 0 \pmod{4}` with $`w \geq 0`, $`\widetilde{G}_{w}` ({uses "def:Gtilde"}[])
satisfies the third-order equation (with the operator of {uses "def:KZ3"}[])
$$`\begin{aligned} L_{3,w}^{(-\frac{w+6}{4},0)} \widetilde{G}_w &= \partial_w^3 \widetilde{G}_w - \frac{3w^2 + 48w + 224}{144} E_4 \partial_w \widetilde{G}_w \\ &\quad - \frac{w(w+9)(w+12)}{864} E_6 \widetilde{G}_w = 0. \end{aligned}`
:::

:::proof "prop:Gtilde_ode"
The triples of parameters
$$`\begin{aligned} (\alpha,\beta,\gamma) &= \left(-\frac{w+10}{4},0,-\frac{(w+6)(w+16)}{48}\right), \\ (\alpha',\beta',\gamma') &= \left(-\frac{w+6}{4},0,-\frac{(w+10)(w+16)}{48}\right) \end{aligned}`
satisfy the four constraints of Lemma 2.4 with $`k = w`, so with
$`\mathcal{M}_w := L_{3,w}^{(-\frac{w+6}{4},0)}` and $`\mathcal{N}_w := L_{2,w}^{\alpha_w}`,
$$`\mathcal{M}_{w+4} \mathcal{N}_w = L_{2,w+6}^{-\frac{(w+10)(w+16)}{48}} \mathcal{M}_w`
by {uses "lem:intertwine"}[]. By {uses "lem:Gtilde_rec"}[], $`\widetilde{G}_{w+4}` is a constant
multiple of $`\mathcal{N}_w \widetilde{G}_w`. Hence the equation follows by induction on $`w`, where
$`\mathcal{M}_0 \widetilde{G}_0 = 0` because $`\widetilde{G}_0` is a constant and, at $`k = 0` and
$`\beta = 0`, every coefficient of the undifferentiated term of $`L_{3,k}^{(\alpha,\beta)}` vanishes.
:::

# Nonnegativity of the coefficients

:::lemma_ "lem:kappa_K_G" (parent := "grp:G") (lean := "UncertaintyPrinciple.κ₂_G, UncertaintyPrinciple.K₂_G, UncertaintyPrinciple.κ₂_G_neg, UncertaintyPrinciple.weight_gap_nonneg, UncertaintyPrinciple.K₂_G_neg")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:kappa_G", citation := "Equations (114) and (115)" }] }
%%%

Let $`w \ge 0` and $`\alpha_w = -\frac{(w+6)(w+16)}{48}`. The coefficient functions of
{uses "lem:KZ2_coeff"}[] for $`L_{2,w}^{\alpha_w}` are
$$`\begin{aligned} \kappa_{2,w}^{\alpha_w}(n) &= \frac{(12n + w + 16)(4n-w-6)}{48}, \\ K_{2,w}^{\alpha_w}(n,j) &= -2(w+1)(w(n-j) - 2j) \sigma_1(n-j) - 5(w+6)(w+16) \sigma_3(n-j), \end{aligned}`
and for $`0 \le j < n \le \frac{w}{4} + 1` both $`\kappa_{2,w}^{\alpha_w}(n)` and
$`K_{2,w}^{\alpha_w}(n,j)` are negative.
:::

:::proof "lem:kappa_K_G"
In this range $`4n - w - 6 < 0`, and
$$`w(n-j)-2j=(w+2)(n-j)-2n\geq w+2-2n\geq \frac{w}{2}\geq0.`
:::

:::lemma_ "lem:Gtilde_step_interior" (parent := "grp:G") (lean := "UncertaintyPrinciple.gtildeStep_nonneg, UncertaintyPrinciple.coeff_gtildeStep, UncertaintyPrinciple.cG_pos")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:Gtilde_coeff_rec", citation := "Equation (113)" }] }
%%%

Let $`w \equiv 0 \pmod{4}` with $`w \ge 0`. The $`n`-th coefficient of $`\widetilde{G}_{w+4}` is
$$`\tilde{a}_{n}^{(w+4)} = c_w \left(-\kappa_{2,w}^{\alpha_w}(n) \tilde{a}_{n}^{(w)} - \sum_{j=0}^{n-1} K_{2,w}^{\alpha_w}(n,j) \tilde{a}_{j}^{(w)}\right),`
so if $`\tilde{a}_{n}^{(w)} \ge 0` for $`0 \le n \le \frac{w}{4} + 1`, then
$`\tilde{a}_{n}^{(w+4)} \ge 0` for $`0 \le n \le \frac{w}{4} + 1`.
:::

:::proof "lem:Gtilde_step_interior"
The formula is {uses "lem:KZ2_coeff"}[] applied to {uses "lem:Gtilde_rec"}[], and $`c_w > 0`. In
the range considered both $`\kappa` and $`K` are negative by {uses "lem:kappa_K_G"}[].
:::

The top index $`n = \frac{w}{4} + 2` is more delicate: there
$`\kappa_{2,w}^{\alpha_w}(n) = \frac{w+10}{6} > 0`, so it is not immediately clear that the
right-hand side is nonnegative. In this case the differential equation is used to express
$`\tilde{a}_{\frac{w}{4}+2}^{(w)}` as a linear combination of the lower coefficients.

:::lemma_ "lem:kappa3_G" (parent := "grp:G") (lean := "UncertaintyPrinciple.κ₃_G, UncertaintyPrinciple.K₃_G")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:Gtilde_coeff_linear", citation := "Equations (116) and (117)" }] }
%%%

Applying Lemma 2.3 ({uses "lem:KZ3_coeff"}[]) to the equation of {uses "prop:Gtilde_ode"}[] gives
the linear relations
$$`\frac{n(n+1)(4n-w-6)}{4} \tilde{a}_{n}^{(w)} + \sum_{j=0}^{n-1} K_w'(n,j) \tilde{a}_{j}^{(w)} = 0,`
$$`K_w'(n,j) = (w+2)(6j^2 - 6(w+1)(n-j)j + w(w+1)(n-j)^2) \sigma_1(n-j) + 15(w+6)(w(n-j) - 4j) \sigma_3(n-j).`
:::

:::proof "lem:kappa3_G"
Specialize the coefficient functions of {uses "lem:KZ3_coeff"}[] to $`k = w`,
$`\alpha = -\frac{w+6}{4}` and $`\beta = 0`.
:::

:::lemma_ "lem:Kpp" (parent := "grp:G") (lean := "UncertaintyPrinciple.Kpp_eq, UncertaintyPrinciple.Kpp_pos, UncertaintyPrinciple.Aw, UncertaintyPrinciple.Bw, UncertaintyPrinciple.Aw_nonneg, UncertaintyPrinciple.Bw_pos, UncertaintyPrinciple.Aw_add_Bw_one")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:Kprime2", citation := "Equations (119)–(122)" }] }
%%%

For $`0 \le j \le \frac{w}{4} + 1` let $`r = \frac{w}{4} + 2 - j`, so that
$`1 \le r \le \frac{w}{4} + 2`. Then the combined kernel
$$`\begin{aligned} K_w''(j) &:= \frac{16(w+10)}{3(w+8)(w+12)} K_w' \left(\frac{w}{4}+2,j\right) - K_{2,w}^{\alpha_w}\left(\frac{w}{4}+2,j\right) \\ &= A_w(r) \sigma_1(r) + B_w(r) \sigma_3(r) \end{aligned}`
with
$$`\begin{aligned} A_w(r) &= \frac{w+4}{3(w+8)(w+12)} (16w^3r^2 - 18w^3 r + 3w^3 + 240 w^2 r^2 - 342 w^2r + 69w^2 \\ &\qquad + 896wr^2 - 1908 wr + 528 w + 960r^2 - 2592r + 1344), \\ B_w(r) &= \frac{5(w+4)(w+6)}{(w+8)(w+12)} (w^2 + 16wr + 16w + 160r + 64), \end{aligned}`
and $`K_w''(j) > 0` for all $`0 \le j \le \frac{w}{4} + 1`. (The kernels are those of
{uses "lem:kappa_K_G"}[] and {uses "lem:kappa3_G"}[].)
:::

:::proof "lem:Kpp"
The expression of $`K_w''` in terms of $`A_w` and $`B_w` is a direct computation. It is clear that
$`B_w(r) > 0` for all $`r \ge 1`. If $`r \ge 2`, substituting $`r = u + 2` in the second factor of
$`A_w(r)` gives
$$`16w^3 u^2 + 46w^3 u + 31w^3 + 240 w^2 u^2 + 618w^2u + 345w^2 + 896wu^2 + 1676 wu + 296 w + 960 u^2 + 1248u,`
which is nonnegative. When $`r = 1`, $`\sigma_1(1) = \sigma_3(1) = 1` and
$$`K_w''\left(\frac{w}{4}+1\right) = A_w(1) + B_w(1) = \frac{(w+4)(16w^2 + 409w + 2484)}{3(w+12)} > 0.`
:::

:::lemma_ "lem:Gtilde_step_boundary" (parent := "grp:G") (lean := "UncertaintyPrinciple.gtildeStep_boundary")
Let $`w \equiv 0 \pmod{4}` with $`w \ge 0`. If $`\widetilde{G}_w` satisfies the equation of
{uses "prop:Gtilde_ode"}[] and $`\tilde{a}_{n}^{(w)} \ge 0` for $`0 \le n \le \frac{w}{4} + 1`, then
$`\tilde{a}_{\frac{w}{4}+2}^{(w+4)} \ge 0`.
:::

:::proof "lem:Gtilde_step_boundary"
For $`n = \frac{w}{4} + 2`, the first relation of {uses "lem:kappa3_G"}[] becomes
$$`\tilde{a}_{\frac{w}{4}+2}^{(w)} = - \frac{32}{(w+8)(w+12)} \sum_{j=0}^{\frac{w}{4}+1} K_w'\left(\frac{w}{4}+2,j\right) \tilde{a}_{j}^{(w)}.`
Combining this with $`\kappa_{2,w}^{\alpha_w}\left(\frac{w}{4}+2\right) = \frac{w+10}{6}` in
{uses "lem:Gtilde_step_interior"}[] gives
$$`\tilde{a}_{\frac{w}{4}+2}^{(w+4)} = c_w \sum_{j=0}^{\frac{w}{4}+1} K_w''(j)\, \tilde{a}_{j}^{(w)},`
which is nonnegative by {uses "lem:Kpp"}[].
:::

:::proposition "prop:Gtilde_pos" (parent := "grp:G") (lean := "UncertaintyPrinciple.coeff_gtildeSeries_nonneg")
%%%
source := { document := "sign", spans := #[{ anchor := "prop:Gtilde_pos", citation := "Proposition 4.23" }, { anchor := "prop:Gtilde_pos_boundary", citation := "Proposition 4.24" }] }
%%%

For all $`w \equiv 0 \pmod{4}` with $`w \ge 0`, the coefficients of $`\widetilde{G}_w`
({uses "def:Gtilde"}[]) satisfy
$$`\tilde{a}_{n}^{(w)} \ge 0 \quad \text{for all } 0 \le n \le \frac{w}{4} + 1.`
:::

:::proof "prop:Gtilde_pos"
Induction on $`w`. For $`w = 0`, $`\widetilde{G}_0 = \frac{3}{2^{11}\cdot7}` is a positive constant,
so $`\tilde{a}_{0}^{(0)} > 0` and $`\tilde{a}_{1}^{(0)} = 0`. If the claim holds at weight $`w`, then
{uses "lem:Gtilde_step_interior"}[] gives it for $`0 \le n \le \frac{w}{4} + 1` at weight $`w+4`
(Proposition 4.23), and {uses "lem:Gtilde_step_boundary"}[], with the differential equation
{uses "prop:Gtilde_ode"}[], gives the boundary case $`n = \frac{w}{4} + 2 = \frac{w+4}{4} + 1`
(Proposition 4.24).
:::

:::corollary "cor:Gtilde_constant" (parent := "grp:G") (lean := "UncertaintyPrinciple.coeff_gtildeSeries_zero_pos, UncertaintyPrinciple.coeff_gtilde₀_zero_pos")
%%%
source := { document := "sign", spans := #[{ anchor := "cor:Apos_4mod8", citation := "Corollary 4.25" }] }
%%%

The constant term of $`\widetilde{G}_w` ({uses "def:Gtilde"}[]) is positive for every
$`w \equiv 0 \pmod{4}` with $`w \geq 0`.
:::

:::proof "cor:Gtilde_constant"
Taking $`n = 0` in {uses "lem:Gtilde_step_interior"}[] gives
$$`\tilde{a}_{0}^{(w + 4)} = \frac{(w+6)(w+10)(w+14)}{256(w+4)(w+9)(w+11)}\, \tilde{a}_{0}^{(w)},`
and $`\tilde{a}_{0}^{(0)} = \frac{3}{2^{11} \cdot 7} > 0`.
:::

Every term of $`b_{0,-}` is therefore nonnegative, and the term $`j = 0` is positive as soon as
$`w_{d,-} \ge 12`, which holds for every $`d \equiv 4 \pmod{8}` other than $`12`. This is what makes
the bound of Corollary 4.25 of {Informal.citet lee2026sign}[] strict:
$$`\mathrm{A}_+(d) \le \sqrt{2n_{d,-}} = \sqrt{2\left(\left\lfloor \frac{d}{16} \right\rfloor + 1\right)} \quad \text{for } d \equiv 4 \pmod{8},`
with equality only possible for $`d = 12`. That deduction is not formalized.
