import Verso
import VersoManual
import VersoBlueprint
import PosqmfBlueprint.Bibliography
import PosqmfBlueprint.TitleMath
import UncertaintyPrinciple.F

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "The family $`F` and the coefficients of $`\\widetilde{F}`" =>
%%%
tag := "f-family"
file := "F-family"
%%%

:::group "grp:F"
The $`(-1)^{d/4}`-eigenforms of Feigenbaum, Grabner and Hardin and the positivity of the
coefficients of $`\widetilde{F}_{w-2}`.
:::

This chapter follows Section 4.1 of
_Positive quasimodular forms and the sign uncertainty principle_ {Informal.citep lee2026sign}[]. For a dimension
$`d \equiv 0 \pmod 4`, Feigenbaum, Grabner and Hardin {Informal.citep feigenbaum2021eigenfunctions}[]
construct $`(-1)^{d/4}`-eigenfunctions of the Fourier transform on $`\mathbb{R}^d` as Laplace
transforms of quasimodular forms $`F_w` of level $`1` and depth $`2`:
$$`M_{d,+}(\mathbf{x}) = 4 \sin^{2} \left(\frac{\pi \|\mathbf{x}\|^{2}}{2}\right) \int_{0}^{\infty} \frac{t^{2-w}F_{w}(i/t)}{\Delta(it)^{n_{d,+}}} e^{-\pi \|\mathbf{x}\|^{2} t} \, dt,`
where $`w = w_{d,+}` and $`n_{d,+} = \lfloor (d + 4)/16\rfloor + 1`. Write
$`F_w = A_w + E_2 B_{w - 2} + E_2^2 C_{w-4}` with modular forms $`A_w`, $`B_{w-2}`, $`C_{w-4}`,
and set
$$`\widetilde{F}_{w-2} := B_{w-2} + 2 E_2 C_{w-4} = \delta F_w = \sum_{n \ge 1} \tilde{a}_{n}^{(w-2)} q^n.`
The integral converges only for $`\|\mathbf{x}\| > \sqrt{2 n_{d,+}}`, and its analytic
continuation to the origin has the value $`M_{d,+}(\mathbf{0}) = -6 b_{0,+}/\pi`, where
$$`b_{0,+} = \sum_{j=1}^{n_{d,+}} p_{24 n_{d,+}}(n_{d,+} - j)\, \tilde{a}_{j}^{(w-2)}`
and $`p_k(n) > 0` are the coefficients of $`\prod_{m \ge 1} (1 - q^m)^{-k}`. So
$`M_{d,+}(\mathbf{0}) < 0`, which is what the bound on $`\mathrm{A}_+(d)` needs, follows from
$`\tilde{a}_{j}^{(w-2)} > 0` for $`1 \le j \le n_{d,+}`, and $`n_{d,+} \le \frac{w}{4} - 2`. This
is Proposition 4.9 below, the goal of the chapter.

The formalization only treats $`w \equiv 0 \pmod{4}`. It defines $`F_w` in the polynomial model by
the recurrence of Feigenbaum, Grabner and Hardin, proves that the family has the properties stated
in Theorem 4.1 of {Informal.citet lee2026sign}[] that the later argument uses (its weight, vanishing
order, normalization and differential equation), defines $`\widetilde{F}_{w-2} := \delta F_w`, and
then runs the coefficient induction on $`q`-expansions. In Lean, `fFam N` is $`F_{4N}` and
`ftildeFam N` is $`\widetilde{F}_{4N-2}`; the forms $`F_0` and $`F_4` do not exist and are set to
$`0`.

# The family $`F`
%%%
file := "The-family-F"
%%%

:::definition "def:F_family" (parent := "grp:F") (lean := "UncertaintyPrinciple.fFam, UncertaintyPrinciple.F₈, UncertaintyPrinciple.SFp, UncertaintyPrinciple.cF")
%%%
source := { document := "sign", spans := #[{ anchor := "thm:fghposeig", citation := "Theorem 4.1" }] }
%%%

For $`w \equiv 0 \pmod{4}` with $`w \geq 8`, define $`F_w \in \mathcal{QM}` (see
{uses "def:QM"}[]) by
$$`F_{8} = \frac{1}{1728}(E_2^2 E_4 - 2E_2 E_6 + E_4^2), \qquad F_{w + 4} = c_w \, \mathcal{S}_w F_w,`
where, with the Serre derivatives of {uses "def:poly_serre"}[],
$$`\begin{aligned} \mathcal{S}_w &= \frac{(w-6)(w-5)}{36} E_{4} - \partial_w \partial_{w-2}, \\ c_w &= \frac{3(w-4)w}{16(w-10)(w-5)(w-3)(w+2)}. \end{aligned}`
This is the recurrence (41) of Feigenbaum, Grabner and Hardin, normalized so that the first
nonzero Fourier coefficient of every $`F_w` is $`1` ({bpref "thm:F_normalization"}[]).
:::

:::lemma_ "lem:F_weight" (parent := "grp:F") (lean := "UncertaintyPrinciple.hasWeight_fFam, UncertaintyPrinciple.hasWeight_F₈, UncertaintyPrinciple.hasWeight_SFp")
$`F_w` ({uses "def:F_family"}[]) has weight $`w`.
:::

:::proof "lem:F_weight"
$`F_8` is a combination of monomials of weight $`8`, and $`\mathcal{S}_w` raises the weight by $`4`
by {uses "lem:weight_closure"}[].
:::

:::lemma_ "lem:F12" (parent := "grp:F") (lean := "UncertaintyPrinciple.fFam_three, UncertaintyPrinciple.F₁₂")
%%%
source := { document := "sign", spans := #[{ anchor := "thm:fghposeig", citation := "Theorem 4.1" }] }
%%%

The recurrence of {uses "def:F_family"}[] reproduces the explicit form
$$`F_{12} = \frac{1}{518400}(E_2^2 E_4^2 - 2 E_2 E_4 E_6 + E_6^2)`
listed by Feigenbaum, Grabner and Hardin.
:::

:::proof "lem:F12"
Compute $`\partial_6 F_8`, $`\partial_8 \partial_6 F_8` and $`c_8 \mathcal{S}_8 F_8` in the
polynomial model with $`D` from {uses "def:poly_D"}[].
:::

:::definition "def:F_series" (parent := "grp:F") (lean := "UncertaintyPrinciple.fSeries")
Write $`F_w = \sum_{n \ge 0} b_n^{(w)} q^n` for the $`q`-expansion ({uses "def:qexp_map"}[]) of the
form $`F_w` of {uses "def:F_family"}[].
:::

On $`q`-expansions, $`\mathcal{S}_w = -L_{2,w-2}^{\alpha_w}` with
$`\alpha_w = -\frac{(w-10)(w-4)}{48}`, by {bpref "lem:KZ2_serre"}[]. So Lemma 2.2
({bpref "lem:KZ2_coeff"}[]) computes the coefficients of $`\mathcal{S}_w G` with
$$`\begin{aligned} \kappa_{2,w-2}^{\alpha_w}(n) &= \frac{(12n + w - 10)(4n - w + 4)}{48}, \\ K_{2,w-2}^{\alpha_w}(n,j) &= -2(w-1)\bigl(w(n-j)-2n\bigr)\sigma_1(n-j) - 5(w-10)(w-4)\sigma_3(n-j). \end{aligned}`
The diagonal coefficient vanishes at $`n = \frac{w}{4} - 1`, which is why the vanishing order grows
by one with each step of the recurrence.

:::theorem "thm:F_vanishing" (parent := "grp:F") (lean := "UncertaintyPrinciple.coeff_fSeries_eq_zero, UncertaintyPrinciple.κ₂_F_zero, UncertaintyPrinciple.coeff_SF")
%%%
source := { document := "sign", spans := #[{ anchor := "thm:fghposeig", citation := "Theorem 4.1" }] }
%%%

The vanishing order of $`F_w` at the cusp is at least $`\frac{w}{4} - 1`: $`b_n^{(w)} = 0` for
$`0 \le n < \frac{w}{4} - 1` (notation of {uses "def:F_series"}[]).
:::

:::proof "thm:F_vanishing"
Induction on $`w`. $`F_8 = E_4''/240 = \sum_{n \ge 1} n^2 \sigma_3(n) q^n` vanishes at the cusp. If
$`b_j^{(w)} = 0` for $`j < \frac{w}{4} - 1`, then by {uses "lem:KZ2_coeff"}[] the $`n`-th
coefficient of $`\mathcal{S}_w F_w` is
$`-\kappa_{2,w-2}^{\alpha_w}(n) b_n^{(w)} - \sum_{j<n} K_{2,w-2}^{\alpha_w}(n,j) b_j^{(w)}`. For
$`n < \frac{w}{4} - 1` all of these vanish, and for $`n = \frac{w}{4} - 1` the diagonal coefficient
$`\kappa_{2,w-2}^{\alpha_w}(n)` vanishes. So $`F_{w+4}` vanishes to order $`\frac{w}{4}`. The
$`q`-expansion of the recurrence is computed with {uses "lem:qexp_compat"}[].
:::

:::theorem "thm:F_mlde" (parent := "grp:F") (lean := "UncertaintyPrinciple.mldeF, UncertaintyPrinciple.mldeF_step, UncertaintyPrinciple.mldeF_zero, UncertaintyPrinciple.L₃p_F₈")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:poseigde", citation := "Theorem 4.1, Equation (42)" }] }
%%%

For $`w \equiv 0 \pmod{4}` with $`w \ge 8`, the $`q`-expansion of $`F_w` ({uses "def:F_series"}[])
satisfies the third-order equation (with the operator of {uses "def:KZ3"}[])
$$`\begin{aligned} L_{3,w-2}^{(\frac{w-4}{4},0)} F_w &= \partial_{w-2}^{3}F_w - \frac{3w^2 - 36w + 140}{144}E_4 \partial_{w-2}F_{w} \\ &\quad - \frac{(w-14)(w-5)(w-2)}{864}E_6 F_w = 0. \end{aligned}`
:::

:::proof "thm:F_mlde"
For $`w = 8` this is a direct computation with the explicit $`F_8`. For the induction step, the
triples
$$`\begin{aligned} (\alpha,\beta,\gamma) &= \left(\frac{w}{4},0,-\frac{(w-10)(w-4)}{48}\right), \\ (\alpha',\beta',\gamma') &= \left(\frac{w-4}{4},0,-\frac{w(w-10)}{48}\right) \end{aligned}`
satisfy the four constraints of Lemma 2.4 with $`k = w - 2`, so
$$`L_{3,w+2}^{(\frac{w}{4},0)} L_{2,w-2}^{\alpha_w} = L_{2,w+4}^{\gamma'} L_{3,w-2}^{(\frac{w-4}{4},0)}`
by {uses "lem:intertwine"}[]. Since $`F_{w+4} = -c_w L_{2,w-2}^{\alpha_w} F_w`, an operator
annihilating $`F_w` gives one annihilating $`F_{w+4}`.
:::

:::theorem "thm:F_normalization" (parent := "grp:F") (lean := "UncertaintyPrinciple.coeff_fSeries_eq_one, UncertaintyPrinciple.κ₃_F, UncertaintyPrinciple.K₃_F, UncertaintyPrinciple.κ₂_F_cusp, UncertaintyPrinciple.K₂_F_cusp")
%%%
source := { document := "sign", spans := #[{ anchor := "thm:fghposeig", citation := "Theorem 4.1" }] }
%%%

$`F_w` is normalized: its first nonzero coefficient is $`b_{\frac{w}{4}-1}^{(w)} = 1`, in the
notation of {uses "def:F_series"}[].
:::

:::proof "thm:F_normalization"
Induction on $`w`, the base case $`w = 8` being immediate from the expression for $`F_8`. Assume
$`b_{\frac{w}{4}-1}^{(w)} = 1`. Applying Lemma 2.3 ({uses "lem:KZ3_coeff"}[]) to the equation of
{uses "thm:F_mlde"}[] at $`n = \frac{w}{4}`, and using {uses "thm:F_vanishing"}[], gives the
first identity below, and hence the second:
$$`\begin{aligned} 0 &= \frac{(w-4)w}{16} b_{\frac{w}{4}}^{(w)} - \frac{w^3 - 12w^2 + 224w - 960}{8} b_{\frac{w}{4}-1}^{(w)}, \\ F_w &= q^{\frac{w}{4} - 1} + \frac{2(w^3 - 12w^2 + 224w - 960)}{w(w-4)} q^{\frac{w}{4}} + \cdots. \end{aligned}`
Feeding these two coefficients into the recurrence with Lemma 2.2 ({uses "lem:KZ2_coeff"}[]) shows
that $`b_{\frac{w}{4}}^{(w+4)} = 1`: in the formalization, with $`w = 4N + 8`, the diagonal and
off-diagonal coefficients at the cusp index are $`\frac{8N + 11}{6}` and $`-4(24N^2 + 25N + 4)`, and
they combine with $`c_w` to exactly $`1`.
:::

# The forms $`\widetilde{F}` and their recurrence
%%%
file := "Ftilde-recurrence"
%%%

:::definition "def:Ftilde" (parent := "grp:F") (lean := "UncertaintyPrinciple.ftildeFam, UncertaintyPrinciple.ftildeSeries, UncertaintyPrinciple.hasWeight_ftildeFam")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:Ftilde", citation := "Equation (55)" }] }
%%%

For $`w \equiv 0 \pmod{4}` with $`w \ge 8`, let $`\widetilde{F}_{w-2} := \delta F_w`, with
$`\delta` from {uses "def:delta"}[] and $`F_w` from {uses "def:F_family"}[], and write
$`\widetilde{F}_{w-2} = \sum_{n \ge 0} \tilde{a}_{n}^{(w-2)} q^n` for its $`q`-expansion. It has
weight $`w - 2`, and depth $`1` since $`F_w` has depth $`2`.
:::

:::lemma_ "lem:Ftilde_rec" (parent := "grp:F") (lean := "UncertaintyPrinciple.ftildeSeries_succ, UncertaintyPrinciple.delta_SFp, UncertaintyPrinciple.qexp_delta_SFp, UncertaintyPrinciple.ftildeStep, UncertaintyPrinciple.SF, UncertaintyPrinciple.alphaF")
%%%
source := { document := "sign", spans := #[{ anchor := "lem:Ftilde_rec", citation := "Lemma 4.8" }] }
%%%

For $`w \geq 8` with $`w \equiv 0 \pmod{4}`, the forms of {uses "def:Ftilde"}[] satisfy
$$`\begin{aligned} \widetilde{F}_{w+2} &= c_w \left(\mathcal{S}_w \widetilde{F}_{w-2} - \frac{1}{3} \partial_{w-1} F_{w}\right), \\ \mathcal{S}_w &= \frac{(w-6)(w-5)}{36} E_4 - \partial_w \partial_{w-2} = -L_{2,w-2}^{-(w-10)(w-4)/48}. \end{aligned}`
In fact $`\delta(\mathcal{S}_w G) = \mathcal{S}_w(\delta G) - \frac{1}{3} \partial_{w-1} G` for every
$`G` of weight $`w`.
:::

:::proof "lem:Ftilde_rec"
Take $`\delta` of both sides of the recurrence {uses "def:F_family"}[], and apply Lemma 4.7
({uses "lem:delta_serre"}[]) twice, to $`F_w` of weight $`w` ({uses "lem:F_weight"}[]) and to
$`\partial_{w-2} F_w` of weight $`w+2`:
$$`\begin{aligned} \delta(\mathcal{S}_w F_w) &= \frac{(w-6)(w-5)}{36} E_4 (\delta F_w) - \partial_w(\delta (\partial_{w-2} F_w)) - \frac{1}{6} \partial_{w-2} F_w \\ &= \frac{(w-6)(w-5)}{36} E_4 (\delta F_w) - \partial_w(\partial_{w-2} (\delta F_w)) - \frac{1}{6} \partial_w F_w - \frac{1}{6} \partial_{w-2} F_w \\ &= \mathcal{S}_w \widetilde{F}_{w-2} - \frac{1}{3} \partial_{w-1} F_w, \end{aligned}`
where the last step is {uses "lem:serre_collapse"}[]. The $`q`-expansion map transports this to
$`q`-expansions by {uses "lem:qexp_compat"}[], and $`\mathcal{S}_w = -L_{2,w-2}^{\alpha_w}` there by
{uses "lem:KZ2_serre"}[].
:::

:::lemma_ "lem:Ftilde10" (parent := "grp:F") (lean := "UncertaintyPrinciple.ftildeSeries_three, UncertaintyPrinciple.qexp_delta_F₁₂, UncertaintyPrinciple.ftilde₁₀, UncertaintyPrinciple.ftilde₁₀_pos, UncertaintyPrinciple.coeff_ftilde₁₀_one, UncertaintyPrinciple.coeff_ftilde₁₀_zero")
$`\widetilde{F}_{10} = \frac{1}{360} E_4 X_{6,1}`, where $`X_{6,1} = \sum_{n \ge 1} n\sigma_3(n) q^n = E_4'/240`.
In particular $`\tilde{a}_{0}^{(10)} = 0`, $`\tilde{a}_{n}^{(10)} > 0` for all $`n \ge 1`, and
$`\tilde{a}_{1}^{(10)} = \frac{1}{360}`. (Notation of {uses "def:Ftilde"}[].)
:::

:::proof "lem:Ftilde10"
By {uses "lem:F12"}[], $`\widetilde{F}_{10} = \delta F_{12} = \frac{1}{259200} E_4 (E_2 E_4 - E_6)`, and
Ramanujan's identity $`E_2 E_4 - E_6 = 3E_4'` ({uses "thm:ramanujan"}[]) turns this into
$`\frac{1}{86400} E_4 E_4'`. Both factors have nonnegative coefficients, with
$`[q^n]E_4' = 240 n \sigma_3(n) > 0` for $`n \ge 1`.
:::

# Positivity of the coefficients of $`\widetilde{F}`
%%%
file := "Ftilde-positivity"
%%%

:::lemma_ "lem:kappa_K_F" (parent := "grp:F") (lean := "UncertaintyPrinciple.κ₂_F, UncertaintyPrinciple.K₂_F, UncertaintyPrinciple.κ₂_F_neg, UncertaintyPrinciple.K₂_F_neg")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:kappa_F", citation := "Equations (68) and (69)" }] }
%%%

Let $`w \ge 12` and $`\alpha_w = -\frac{(w-10)(w-4)}{48}`. The coefficient functions of
{uses "lem:KZ2_coeff"}[] for $`L_{2,w-2}^{\alpha_w}` are
$$`\begin{aligned} \kappa_{2,w-2}^{\alpha_w}(n) &= \frac{(12n + w - 10)(4n - w + 4)}{48}, \\ K_{2,w-2}^{\alpha_w}(n,j) &= -2(w-1)\bigl(w(n-j)-2n\bigr)\sigma_1(n-j) - 5(w-10)(w-4)\sigma_3(n-j), \end{aligned}`
and $`\kappa_{2,w-2}^{\alpha_w}(n) < 0` for $`1 \le n \le \frac{w}{4} - 2`, while
$`K_{2,w-2}^{\alpha_w}(n,j) < 0` for $`1 \le j < n \le \frac{w}{4} - 1`.
:::

:::proof "lem:kappa_K_F"
The formulas are the definitions specialized. In the first range $`4n - w + 4 < 0`. In the second,
$`w(n-j) - 2n \geq w - 2n > 0`, and $`(w-10)(w-4) > 0`.
:::

:::lemma_ "lem:Ftilde_step_interior" (parent := "grp:F") (lean := "UncertaintyPrinciple.ftildeStep_pos, UncertaintyPrinciple.coeff_ftildeStep")
Let $`w \equiv 0 \pmod 4` with $`w \ge 12`. If $`F_w` vanishes to order $`\frac{w}{4} - 1`,
$`\tilde{a}_{0}^{(w-2)} = 0` and $`\tilde{a}_{j}^{(w-2)} > 0` for $`1 \le j \le \frac{w}{4} - 2`,
then the right-hand side of the recurrence {uses "lem:Ftilde_rec"}[] has positive $`n`-th
coefficient for $`1 \le n \le \frac{w}{4} - 2`.
:::

:::proof "lem:Ftilde_step_interior"
By {uses "lem:KZ2_coeff"}[] and the coefficients of the Serre derivative, the $`n`-th coefficient
of the right-hand side is
$$`\begin{aligned} c_w\Biggl(&-\kappa_{2,w-2}^{\alpha_w}(n) \tilde{a}_{n}^{(w-2)} - \sum_{j=1}^{n-1} K_{2,w-2}^{\alpha_w}(n,j)\tilde{a}_{j}^{(w-2)} \\ &- \frac{1}{3}n b_n^{(w)} + \frac{w-1}{36}\left(b_n^{(w)} - 24 \sum_{k=1}^{n-1} \sigma_1(n-k) b_k^{(w)}\right)\Biggr), \end{aligned}`
where $`c_w > 0`. In the range $`1 \le n \le \frac{w}{4} - 2` the terms involving $`F_w` vanish, and
what is left is a positive combination of the $`\tilde{a}_{j}^{(w-2)}` by {uses "lem:kappa_K_F"}[].
:::

:::lemma_ "lem:boundary_quartic" (parent := "grp:F") (lean := "UncertaintyPrinciple.boundary_bound, UncertaintyPrinciple.quartic_nonneg, UncertaintyPrinciple.K₂_F_boundary")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:boundary_coeff", citation := "Equation (71)" }] }
%%%

For $`w \ge 12`,
$`K_{2,w-2}^{\alpha_w}\left(\frac{w}{4}-1, \frac{w}{4}-2\right) = -(6w^2 - 67w + 196)` and
$$`\begin{aligned} c_w \left(\frac{6w^2 - 67w + 196}{360} - \frac{2w - 11}{36}\right) &= \frac{(w-6)(w-4)w(2w-17)}{640(w-10)(w-5)(w-3)(w+2)} \\ &\ge \frac{1}{360}. \end{aligned}`
:::

:::proof "lem:boundary_quartic"
The two indices differ by $`1` and $`\sigma_1(1) = \sigma_3(1) = 1`, which gives the value of
$`K` from {uses "lem:kappa_K_F"}[]. The inequality is equivalent to
$`2w^4 - 77w^3 + 1018 w^2 - 4312 w + 4800 \ge 0`. Writing $`u = w - 12 \ge 0`, the quartic becomes
$`2u^4 + u(19u^2 - 26u + 680) + 8064`, and the inner quadratic has negative discriminant.
:::

:::lemma_ "lem:Ftilde_step_boundary" (parent := "grp:F") (lean := "UncertaintyPrinciple.ftildeStep_boundary")
Under the hypotheses of {uses "lem:Ftilde_step_interior"}[], if moreover $`F_w` is normalized and
$`\tilde{a}_{\frac{w}{4}-2}^{(w-2)} \ge \frac{1}{360}`, then the $`(\frac{w}{4}-1)`-th coefficient
of the right-hand side of the recurrence is at least $`\frac{1}{360}`.
:::

:::proof "lem:Ftilde_step_boundary"
For $`n = \frac{w}{4} - 1`, normalization gives $`b_n^{(w)}=1` and $`b_k^{(w)}=0` for $`k<n`, while
$`\kappa_{2,w-2}^{\alpha_w}(n) = 0`. So the coefficient is
$$`\begin{aligned} &c_w\left(-\sum_{j=1}^{n-1} K_{2,w-2}^{\alpha_w}(n,j)\tilde{a}_{j}^{(w-2)} - \frac{2w-11}{36}\right) \\ &\quad\ge c_w \left(-K_{2,w-2}^{\alpha_w}\left(\frac{w}{4}-1, \frac{w}{4}-2\right) \tilde{a}_{\frac{w}{4}-2}^{(w-2)} - \frac{2w-11}{36}\right), \end{aligned}`
since every other term is nonnegative by {uses "lem:kappa_K_F"}[]. With
$`\tilde{a}_{\frac{w}{4}-2}^{(w-2)} \ge \frac{1}{360}`, this is at least $`\frac{1}{360}` by
{uses "lem:boundary_quartic"}[].
:::

:::proposition "prop:Ftilde_pos" (parent := "grp:F") (lean := "UncertaintyPrinciple.coeff_ftildeSeries_pos, UncertaintyPrinciple.coeff_ftildeSeries_boundary")
%%%
source := { document := "sign", spans := #[{ anchor := "prop:Ftilde_pos", citation := "Proposition 4.9" }] }
%%%

For $`w \equiv 0 \pmod{4}` and $`w \ge 12`, the coefficients of $`\widetilde{F}_{w-2}`
({uses "def:Ftilde"}[]) satisfy
$$`\tilde{a}_{j}^{(w-2)} > 0 \quad \text{for all} \quad 1 \le j \le \frac{w}{4} - 2, \qquad \tilde{a}_{\frac{w}{4}-2}^{(w-2)} \ge \frac{1}{360}.`
:::

:::proof "prop:Ftilde_pos"
Induction on $`w`. For $`w = 12`, $`\widetilde{F}_{10}` is completely positive with
$`\tilde{a}_{1}^{(10)} = \frac{1}{360}` by {uses "lem:Ftilde10"}[]. Assume the claim at weight
$`w`, together with $`\tilde{a}_{0}^{(w-2)} = 0`. The recurrence {uses "lem:Ftilde_rec"}[] expresses
$`\widetilde{F}_{w+2}` in terms of $`\widetilde{F}_{w-2}` and $`F_w`, which vanishes to order
$`\frac{w}{4} - 1` and is normalized by {uses "thm:F_vanishing"}[] and
{uses "thm:F_normalization"}[]. So {uses "lem:Ftilde_step_interior"}[] gives
$`\tilde{a}_{n}^{(w+2)} > 0` for $`1 \le n \le \frac{w}{4} - 2`, and
{uses "lem:Ftilde_step_boundary"}[] gives $`\tilde{a}_{\frac{w}{4}-1}^{(w+2)} \ge \frac{1}{360}`.
Taking constant terms in the recurrence shows $`\tilde{a}_{0}^{(w+2)} = 0`, which completes the
induction.
:::

Since $`n_{d,+} \le \frac{w}{4} - 2`, Proposition 4.9 implies $`b_{0,+} > 0`, hence
$`M_{d,+}(\mathbf{0}) < 0`, and Corollary 4.10 of {Informal.citet lee2026sign}[] follows: for
$`d \equiv 0 \pmod{8}`,
$$`\mathrm{A}_+(d) < \sqrt{2n_{d,+}} = \sqrt{2\left(\left\lfloor\frac{d}{16}\right\rfloor + 1\right)}.`
That deduction, which also needs the positivity of $`F_w` on the imaginary axis, is not formalized.
Experimentally, $`\widetilde{F}_{w-2}` appears to be completely positive for all $`w \geq 8` with
$`w \equiv 0 \pmod{4}`.
