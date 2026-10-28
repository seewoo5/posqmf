import Verso
import VersoManual
import VersoBlueprint
import PosqmfBlueprint.Bibliography
import D_6_3
import X_16_5

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Extremal quasimodular forms X₁₆,₅ and 𝒟₆,₃" =>
%%%
tag := "extremal-forms"
file := "Extremal-forms"
%%%

:::group "grp:extremal"
Coefficient signs of two extremal quasimodular forms, from elementary bounds on divisor sums.
:::

Kaneko and Koike {Informal.citep kaneko2006extremal}[] defined _extremal quasimodular forms_, the
quasimodular forms of a given weight and depth with the maximum possible order of vanishing at the
cusp: $`f \in \mathcal{QM}_{w}^{s} \setminus \mathcal{QM}_{w}^{s-1}` is extremal if its first
$`m - 1` Fourier coefficients vanish, where $`m = \dim \mathcal{QM}_{w}^{s}`. They conjectured
their existence and uniqueness up to scalars for $`0 \le s \le w/2` with $`s \ne w/2 - 1`, which
Pellarin {Informal.citep pellarin2020extremal}[] established for $`s \le 4`, and they conjectured
that the Fourier coefficients of the extremal forms of depth $`s \le 4` are all positive. The two
results of this chapter concern what happens beyond that range. Both reduce to explicit formulas for
the Fourier coefficients and to the following trivial bounds for divisor sums.

:::lemma_ "lem:sigma_bounds" (parent := "grp:extremal") (lean := "pow_le_sigma, one_le_sigma, sigma_pos, sigma_le_two_mul_pow")
For $`n \ge 1` and $`k \ge 0`, $`n^k \le \sigma_k(n)`; and for $`k \ge 2`,
$`\sigma_k(n) \le 2 n^k`.
:::

:::proof "lem:sigma_bounds"
$`n` itself is a divisor of $`n`. For the upper bound,
$`\sigma_k(n) = n^k \sum_{d \mid n} d^{-k} \le n^k \left(1 + \sum_{d=2}^{n} \frac{1}{d^2}\right)`, and
$`\sum_{d=2}^{n} \frac{1}{d^2} \le \sum_{d=2}^{n} \left(\frac{1}{d-1} - \frac{1}{d}\right) < 1`.
:::

# All coefficients of X₁₆,₅ but the first are negative
%%%
file := "X16-5"
%%%

The naive extension of the conjecture of Kaneko and Koike to depth $`s \ge 5` fails, and the
smallest counterexample is the extremal form $`X_{16,5}` of weight $`16` and depth $`5`, a claim of
the author's PhD thesis {Informal.citep lee2026thesis}[]:
$$`X_{16,5} = q^7 - \frac{4809}{16} q^8 - 3913 q^9 - \frac{59577}{2} q^{10} - 166404 q^{11} - \cdots,`
and in fact every coefficient after the first is negative. The proof expresses $`X_{16,5}` as a
linear combination of derivatives of Eisenstein series and of $`\Delta E_4` and $`\Delta X_{4,2}`,
where $`\Delta = \sum_{n \ge 1} \tau(n) q^n` and $`X_{4,2} = \sum_{n \ge 1} n\sigma_1(n) q^n`:
$$`\begin{aligned} X_{16,5} &= \frac{E_{14}'}{4843238400} + \frac{4531 E_{12}''}{4533271142400} + \frac{149 E_{10}'''}{60217344000} \\ &\quad + \frac{49 E_{8}''''}{12317184000} + \frac{7 E_{6}'''''}{1791590400} + c_6 \Delta E_4 + c_7 \Delta X_{4,2}, \\ c_6 &= \frac{86619413}{139015844352000}, \qquad c_7 = -\frac{118801}{10746432000}. \end{aligned}`
This identity is checked in `notebooks/miscellaneous.ipynb`; the formalization starts from the
resulting formula for the coefficients.

:::definition "def:X165_coefficients" (parent := "grp:extremal") (lean := "aSeq, xSeq, ySeq, zSeq, c₆, c₇")
Taking the coefficient of $`q^n` in the expression for $`X_{16,5}` gives
$`X_{16,5} = \sum_{n \ge 7} a_n q^n` with
$$`a_n = x_n + 240 c_6 y_n + c_7 z_n + c_6 \tau(n),`
where
$$`\begin{aligned} x_n &= - \frac{n \sigma_{13}(n)}{201801600} + \frac{4531 n^2 \sigma_{11}(n)}{47809681920} - \frac{149 n^3 \sigma_9(n)}{228096000} \\ &\quad + \frac{49 n^4 \sigma_7(n)}{25660800} - \frac{49 n^5 \sigma_5(n)}{24883200}, \\ y_n &= \sum_{k=1}^{n-1} \tau(k) \sigma_3(n-k), \qquad z_n = \sum_{k=1}^{n-1} \tau(k) (n-k) \sigma_1(n-k). \end{aligned}`
:::

:::theorem "thm:deligne" (parent := "grp:extremal") (lean := "abs_tau_lt, τ")
Deligne's bound {Informal.citep deligne1974weil}[]: for $`n \ge 1`,
$$`|\tau(n)| \le \sigma_0(n)\, n^{11/2}.`
The formalization treats $`\tau` as an unspecified function $`\mathbb{N} \to \mathbb{Z}` and takes
this bound as an _axiom_; nothing else about $`\tau` is used.
:::

:::proof "thm:deligne"
This follows from the Weil conjectures, proved by Deligne, and is far beyond the scope of the
formalization.
:::

:::lemma_ "lem:X165_yz" (parent := "grp:extremal") (lean := "abs_ySeq_le, abs_zSeq_le")
For $`n \ge 1`, with $`y_n` and $`z_n` as in {uses "def:X165_coefficients"}[],
$$`|y_n| \le \frac{4}{15} n^{21/2}, \qquad |z_n| \le \frac{2}{15} n^{21/2}.`
:::

:::proof "lem:X165_yz"
By {uses "thm:deligne"}[] and $`\sigma_0(k) \le k`, $`|\tau(k)| \le k^{13/2}`. By
{uses "lem:sigma_bounds"}[], $`\sigma_3(n-k) \le 2n^3`, and $`\sigma_1(n-k) \le (n-k)^2 \le n^2`.
Finally $`\sum_{k=1}^{n-1} k^{13/2} \le \int_1^n x^{13/2}\,dx \le \frac{2}{15} n^{15/2}`, since the
integrand is increasing.
:::

:::lemma_ "lem:X165_x" (parent := "grp:extremal") (lean := "xSeq_le_sharp")
For $`n \ge 1`, with $`x_n` as in {uses "def:X165_coefficients"}[],
$$`x_n \le - \frac{n^{14}}{201801600} + \frac{9062\, n^{13}}{47809681920} + \frac{98\, n^{11}}{25660800}.`
:::

:::proof "lem:X165_x"
Use $`\sigma_{13}(n) \ge n^{13}` for the leading negative term, $`\sigma_{11}(n) \le 2n^{11}` and
$`\sigma_7(n) \le 2n^7` for the positive terms ({uses "lem:sigma_bounds"}[]), and drop the other two
negative terms.
:::

:::theorem "thm:X165" (parent := "grp:extremal") (lean := "aSeq_neg_of_large")
For every $`n \ge 250`, the coefficient $`a_n` of $`X_{16,5}` ({uses "def:X165_coefficients"}[]) is
negative.
:::

:::proof "thm:X165"
By {uses "lem:X165_x"}[], {uses "lem:X165_yz"}[] and {uses "thm:deligne"}[], with
$`n^{21/2} \le n^{11}` and $`|\tau(n)| \le n^{13/2} \le n^7`,
$$`\begin{aligned} a_n &\le -\frac{n^{14}}{201801600} + \frac{9062\, n^{13}}{47809681920} + \frac{98\, n^{11}}{25660800} \\ &\quad + 240 c_6 \cdot \frac{4}{15} n^{11} - c_7 \cdot \frac{2}{15} n^{11} + c_6 n^7. \end{aligned}`
For $`n \ge 250` each of the five correction terms is at most $`\frac{n^{14}}{1210809600}`, one sixth
of the leading term, so $`a_n \le -\frac{n^{14}}{1210809600} < 0`.
:::

The remaining range $`8 \le n < 250` is checked by computer in `notebooks/miscellaneous.ipynb` and
is not formalized: with $`\tau` known only through Deligne's bound, the formalization has no access
to its values.

# 𝒟₆,₃ is completely positive
%%%
file := "D6-3"
%%%

The following result comes from the author's manuscript _On extremal quasimodular forms of low
levels_, which studies extremal quasimodular forms of level $`\Gamma_0(N)` for $`N = 2, 3, 4`. In
depth $`3` and level $`\Gamma_0(2)` no analogue of the differential equations of lower depth is
available, but the extremal form of smallest weight, $`\mathcal{D}_{6,3}`, can be written in terms
of Eisenstein series of levels $`1` and $`2`:
$$`\begin{aligned} \mathcal{D}_{6, 3}(z) &= \frac{1}{4515840}\bigl(-700 E_2''(z) - 8400 E_2''(2z) - 91 E_4'(z) - 714 E_4'(2z) - 10 E_6(z) + 10 E_6(2z)\bigr) \\ &= q^5 + \frac{10}{7}q^6 + \frac{60}{7}q^7 + \frac{80}{7}q^8 + \cdots. \end{aligned}`

:::definition "def:D63_coefficients" (parent := "grp:extremal") (lean := "D63.aSeq, D63.A, D63.B")
Taking coefficients, $`\mathcal{D}_{6,3} = \sum_{n \ge 5} a_n q^n` with
$$`\begin{aligned} a_n &= \frac{A_n + B_{n/2}}{2688}, \\ A_n &= 10 n^2 \sigma_1(n) - 13 n \sigma_3(n) + 3 \sigma_5(n), \\ B_n &= 120 n^2 \sigma_1(n) - 102 n \sigma_3(n) - 3 \sigma_5(n), \end{aligned}`
where $`B_{n/2} = 0` when $`n` is odd.
:::

:::theorem "thm:D63" (parent := "grp:extremal") (lean := "D63.aSeq_pos")
$`a_n > 0` for every $`n \ge 5`, with $`a_n` as in {uses "def:D63_coefficients"}[]. In particular,
$`\mathcal{D}_{6,3}` is completely positive.
:::

:::proof "thm:D63"
Using the bounds $`n^k \le \sigma_k(n) \le 2 n^k` for $`k \ge 2` and $`n \le \sigma_1(n)`
({uses "lem:sigma_bounds"}[]), we have
$$`A_n \ge 3n^5 - 26 n^4 + 10n^3, \qquad B_n \ge -6n^5 - 204n^4 + 120 n^3,`
and this implies $`A_n > 0` for $`n \ge 9` and $`A_n + B_{n/2} > 0` for even $`n \ge 14`: when
$`n = 2m`, the bound becomes $`90 m^5 - 620 m^4 + 200 m^3 > 0` for $`m \ge 7`. Thus $`a_n > 0` for
$`n \ge 14`, and $`a_n > 0` for $`5 \le n \le 13` by direct computation.
:::
