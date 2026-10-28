import Verso
import VersoManual
import VersoBlueprint
import PosqmfBlueprint.Bibliography
import PolymodInequalities.polymod_ineq1
import PolymodInequalities.polymod_ineq2
import PolymodInequalities.polymod_monotone

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Inequalities involving polynomials and quasimodular forms" =>
%%%
tag := "polymod-inequalities"
file := "Polymod-inequalities"
%%%

:::group "grp:polymod"
The three inequalities formalized from *Inequalities involving polynomials and quasimodular forms*.
:::

The paper _Inequalities involving polynomials and quasimodular forms_
{Informal.citep lee2026polymod}[] studies the monotonicity of functions of the form
$`t \mapsto t^m F(it)` for a quasimodular form $`F` and $`m > 0`, motivated by the inequalities
behind the universal optimality of the $`\mathsf{E}_8` and Leech lattices
{Informal.citep cohn2022universal}[]. Two of its arguments end in explicit real inequalities, which
were found and formalized with the help of automated tools; they are the subject of this chapter.

# A monotonicity lemma via Lambert series

For certain low-weight quasimodular forms $`F`, the monotonicity of $`t^m F(it)` can be proved
through a Lambert series expansion $`F(z) = \sum_{n \ge 1} b_n \frac{q^n}{(1 - q^n)^k}`: once
$`b_n \ge 0`, it reduces to the monotonicity of $`t \mapsto t^m \frac{e^{-t}}{(1 - e^{-t})^k}`.
Lemma 3.5 of {Informal.citet lee2026polymod}[] states that $`t \mapsto t^{8} X_{10, 1}(it)` is
monotone decreasing for $`t > 0`, where $`X_{10,1} = \sum_{n \ge 1} n\sigma_7(n) q^n` is the extremal
quasimodular form of weight $`10` and depth $`1`. Its Lambert series is
$$`\begin{aligned} X_{10, 1}(z) = \sum_{m \ge 1} \frac{m q^m}{(1 - q^m)^9} \bigl(&(q^{7m} + 1) + 247 (q^{6m} + q^{m}) \\ &+ 4293 (q^{5m} + q^{2m}) + 15619 (q^{4m} + q^{3m})\bigr), \end{aligned}`
and the derivative of the corresponding function $`g_8(t)` is
$`-\frac{e^{-9t} t^7 (t P(e^t) - Q(e^t))}{(1 - e^{-t})^{10}}`, where
$$`\begin{aligned} P(x) &= (x^8 + 1) + 502 (x^7 + x) + 14608 (x^6 + x^2) + 88234 (x^5 + x^3) + 156190 x^4, \\ Q(x) &= 8 (x^8 - 1 + 246 (x^7 - x) + 4046 (x^6 - x^2) + 11326 (x^5 - x^3)). \end{aligned}`
So the lemma comes down to the inequality (41) below.

:::definition "def:fpos_function" (parent := "grp:polymod") (lean := "f, aCoeffs, bCoeffs")
%%%
source := { document := "polymod", spans := #[{ anchor := "eqn:fpos", citation := "Equation (41)" }] }
%%%

Let $`P(x) = \sum_{k=0}^{8} a_k x^k` and $`-Q(x) = \sum_{k=0}^{8} b_k x^k`, so that
$$`f(t) := t P(e^t) - Q(e^t) = \sum_{k=0}^{8} (a_k t + b_k) e^{kt},`
with $`(a_0, \dots, a_8) = (1, 502, 14608, 88234, 156190, 88234, 14608, 502, 1)` and
$`(b_0, \dots, b_8) = (8, 1968, 32368, 90608, 0, -90608, -32368, -1968, -8)`.
:::

:::lemma_ "lem:fpos_derivatives" (parent := "grp:polymod") (lean := "iteratedDeriv_f_formula, iteratedDeriv_f_zero_eq, f_zero")
For $`n \ge 1` and all $`t`, the function of {uses "def:fpos_function"}[] has
$$`\begin{aligned} f^{(n)}(t) &= \sum_{k=0}^{8} \left(n a_k k^{n-1} + b_k k^n + a_k k^n t\right) e^{kt}, \\ f^{(n)}(0) &= c_n := \sum_{k=0}^{8} \left(n a_k k^{n-1} + b_k k^n\right), \end{aligned}`
with $`0^0 = 1`, and $`f(0) = \sum_k b_k = 0`.
:::

:::proof "lem:fpos_derivatives"
$`\frac{d^n}{dt^n}\left(t e^{kt}\right) = (n k^{n-1} + k^n t) e^{kt}` by induction on $`n`, and
$`\frac{d^n}{dt^n} e^{kt} = k^n e^{kt}`. The Taylor expansion of $`f` at $`0` is therefore
$`f(t) = \sum_{n \ge 0} \frac{c_n}{n!} t^n`, where for $`n \ge 2`
$$`\begin{aligned} c_n &= (n - 64) 8^{n-1} + (502n - 13376) 7^{n-1} + (14608 n - 194208) 6^{n-1} \\ &\quad + (88234 n - 453040) 5^{n-1} + 156190 n 4^{n-1} + (88234n + 271824) 3^{n-1} \\ &\quad + (14608 n + 64736) 2^{n-1} + (502 n + 1968). \end{aligned}`
(The paper writes $`c_0 = f(0) = 8` and sums over $`1 \le k \le 8` only; in fact $`c_0 = Q(1) = 0`,
and the term $`k = 0` adds $`a_0 = 1` to $`c_1`. Neither affects the argument.)
:::

:::lemma_ "lem:fpos_cn" (parent := "grp:polymod") (lean := "iteratedDeriv_f_zero_pos, derivSumInt_pos_small, term_nonneg_large_n, term_one_pos_large_n")
$`c_n > 0` for every $`n \ge 1`, with $`c_n` as in {uses "lem:fpos_derivatives"}[].
:::

:::proof "lem:fpos_cn"
For $`n \ge 64`, every coefficient $`na_k + kb_k` is nonnegative, and the one for $`k = 1` is
positive, so $`c_n > 0`. For $`1 \le n \le 63` the integer $`c_n` is computed directly.
:::

:::lemma_ "lem:fpos_high" (parent := "grp:polymod") (lean := "iteratedDeriv_pos_high, coeff_nonneg_high_deriv")
For $`n \ge 64` and $`t > 0`, $`f^{(n)}(t) > 0`.
:::

:::proof "lem:fpos_high"
In the formula of {uses "lem:fpos_derivatives"}[], each summand
$`\left(k^{n-1}(na_k + kb_k) + a_k k^n t\right) e^{kt}` is nonnegative for $`n \ge 64` and
$`t \ge 0`, since $`a_k > 0`, and the summand $`k = 1` is positive.
:::

:::theorem "thm:fpos" (parent := "grp:polymod") (lean := "f_pos, pos_of_next_deriv_pos, iteratedDeriv_pos_aux, deriv_f_pos")
%%%
source := { document := "polymod", spans := #[{ anchor := "eqn:fpos", citation := "Equation (41)" }] }
%%%

The function $`f` of {uses "def:fpos_function"}[] satisfies $`f(t) > 0` for all $`t > 0`.
:::

:::proof "thm:fpos"
Since all Taylor coefficients of $`f` at $`0` are nonnegative, so is $`f` on $`t > 0`. The
formalization avoids power series and descends through the derivatives instead. By
{uses "lem:fpos_high"}[], $`f^{(64)} > 0` on $`(0, \infty)`. If $`f^{(n+1)} > 0` on $`(0, \infty)` and
$`f^{(n)}(0) = c_n > 0` ({uses "lem:fpos_cn"}[]), then
$`f^{(n)}(t) = c_n + \int_0^t f^{(n+1)}(s)\,ds > 0` for $`t > 0`. Descending from $`n = 63` to
$`n = 1` gives $`f' > 0` on $`(0, \infty)`, and $`f(t) = f(0) + \int_0^t f'(s)\,ds > 0` since
$`f(0) = 0` by {uses "lem:fpos_derivatives"}[].
:::

# Two inequalities for the coefficients of Y₁₂,₂
%%%
file := "Y12-2-inequalities"
%%%

Appendix A of {Informal.citet lee2026polymod}[] constructs completely positive quasimodular forms
of higher level. Proposition A.1 states that
$`Y_{w, s}(z) := X_{w, s}(z) - 2^{w-s} X_{w, s}(2z)` is completely positive for
$`(w, s) = (4, 2), (8, 2), (10, 2), (12, 2)`, where $`X_{w,s}` are the extremal quasimodular forms
of Kaneko and Koike {Informal.citep kaneko2006extremal}[]. For $`w = 12` it uses
$$`X_{12, 2} = \frac{1}{18000} \sum_{n \ge 3}\left(\frac{17 \tau(n)}{21} + \frac{6n\sigma_9(n)}{7} - \frac{5n^2 \sigma_7(n)}{3}\right) q^n,`
and the required coefficient inequality, after writing $`n = 2^k m` with $`m` odd and using the
multiplicativity of $`\sigma_7`, $`\sigma_9` and $`\tau`, Deligne's bound
$`|\tau(n)| \le \sigma_0(n) n^{11/2}` {Informal.citep deligne1974weil}[], and
$`\sigma_0(m) \le m`, reduces to the following two inequalities: (60) for $`k = 0`, and (61) for
$`k \ge 1`.

:::theorem "thm:appendix_ineq1" (parent := "grp:polymod") (lean := "main_theorem, divisorCount")
%%%
source := { document := "polymod", spans := #[{ anchor := "eqn:appendix_ineq1", citation := "Equation (60)" }] }
%%%

For every integer $`m \ge 3`, with $`d(m) = \sigma_0(m)` the number of divisors of $`m`,
$$`\frac{2520}{3} m^9 - \frac{18224}{21} d(m)\, m^{\frac{11}{2}} + \frac{12}{7} m^{10} > 0.`
:::

:::proof "thm:appendix_ineq1"
Since $`d(m) \le m`, we have $`d(m)\, m^{11/2} \le m^{13/2} \le m^7`, and
$$`840 m^9 - \frac{18224}{21} m^7 + \frac{12}{7} m^{10} = \frac{m^7}{21}\left(36 m^3 + 17640 m^2 - 18224\right) > 0`
for $`m \ge 3`.
:::

:::theorem "thm:appendix_ineq2" (parent := "grp:polymod") (lean := "main_inequality, factor_two_pow_2k, coeff_multiplied_bound")
%%%
source := { document := "polymod", spans := #[{ anchor := "eqn:appendix_ineq2", citation := "Equation (61)" }] }
%%%

For every integer $`k \ge 1`,
$$`\begin{aligned} &\frac{2560}{3} \cdot 2^{9k} - \frac{40}{3} \cdot 2^{2k} \\ &\quad - \frac{17}{21} \left((k+2)\, 2^{\frac{11}{2}(k+1)} + 1048 (k+1)\, 2^{\frac{11}{2}k}\right) > 0. \end{aligned}`
:::

:::proof "thm:appendix_ineq2"
Factor out $`2^{2k}` and put $`s = 2^{7k/2}`, so that $`2^{7k} = s^2`. Since
$`\frac{17}{21}\left((k+2) 2^{11/2} + 1048(k+1)\right) < 1812 k` for $`k \ge 1` (using
$`2^{11/2} < 46`), the remaining factor is larger than
$`R_k := \frac{2560}{3} s^2 - 1812 k s - \frac{40}{3}`. By induction, $`R_k > 0` for all
$`k \ge 1`: $`R_1 = \frac{2560}{3} \cdot 128 - 1812 \cdot 8\sqrt{2} - \frac{40}{3} > 0`, and
$$`R_{k+1} - 128 R_k = 1812\, s \left(k (128 - 2^{7/2}) - 2^{7/2}\right) + \frac{5080}{3} > 0.`
:::
