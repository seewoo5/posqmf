import Verso
import VersoManual
import VersoBlueprint
import PosqmfBlueprint.Bibliography
import UncertaintyPrinciple.LogInequalities

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Logarithm inequalities for the positivity of Y" =>
%%%
tag := "log-inequalities"
file := "Log-inequalities"
%%%

:::group "grp:log"
Elementary logarithm inequalities behind the base cases of the positivity of $`Y_w`.
:::

The positivity of the functions $`G_w` of the previous chapter on the imaginary axis is deduced in
Section 4.2.1 of
_Positive quasimodular forms and the sign uncertainty principle_ {Informal.citep lee2026sign}[] from that of a companion family $`Y_w` of level
$`\Gamma(2)`, which plays the role of the extremal quasimodular forms $`X_{w,2}` for the family
$`F_w`. The family is defined by $`Y_2 = H_2/2^4`, explicit expressions for $`Y_4`, $`Y_6 = 0` and
$`Y_8`, and recurrences in the weight, where $`H_2 = \Theta_2^4` and $`H_4 = \Theta_4^4` are fourth
powers of Jacobi theta functions. For instance
$$`Y_{4} = -\frac{3 E_4 \mathcal{L}_S}{2^{11} \cdot 5} -\frac{3}{2^{12} \cdot 5} (H_{2}^{2} + 2 H_{2} H_{4}).`
Theorem 4.18 of {Informal.citet lee2026sign}[] states that $`Y_w(it) > 0` for every even
$`w \ge 2` with $`w \ne 6` and all $`t > 0`, by induction from the base cases $`Y_8` and $`Y_{10}`,
after disposing of $`Y_2` and $`Y_4`. Under the substitution $`x = H_2(it)/H_4(it) > 0`, which turns
$`-\mathcal{L}_S(it)` into $`\log(1+x)`, and with $`E_4 = H_2^2 + H_2H_4 + H_4^2`, the three
nontrivial base cases become the elementary inequalities of this chapter. This is the one place
where the argument leaves modular forms for real-variable calculus. The rest of the proof of
Theorem 4.18 is not formalized.

:::lemma_ "lem:logineq1" (parent := "grp:log") (lean := "UncertaintyPrinciple.logIneq_basic")
%%%
source := { document := "sign", spans := #[{ anchor := "lem:logineq1", citation := "Lemma 4.17" }] }
%%%

For $`x > 0`, we have $`\log(1 + x) > \frac{2x}{x+2}`.
:::

:::proof "lem:logineq1"
Both sides vanish at $`x = 0`, so the claim follows from
$$`\frac{d}{dx} \left(\log(1+x) - \frac{2x}{x+2}\right) = \frac{x^2}{(x+1)(x+2)^2} > 0`
and the mean value theorem.
:::

:::lemma_ "lem:logineqY4" (parent := "grp:log") (lean := "UncertaintyPrinciple.logIneq_Y₄")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:logineqY4", citation := "Equation (95)" }] }
%%%

For $`x > 0`, we have $`\log(1 + x) > \frac{x(x+2)}{2(x^2 + x + 1)}`. This is the case $`Y_4`:
$`Y_4(it) > 0` is equivalent to it.
:::

:::proof "lem:logineqY4"
By {uses "lem:logineq1"}[],
$$`\begin{aligned} \log(1 + x) - \frac{x(x+2)}{2(x^2 + x + 1)} &> \frac{2x}{x+2} - \frac{x(x+2)}{2(x^2 + x + 1)} \\ &= \frac{3x^3}{2(x+2)(x^2 + x + 1)} > 0. \end{aligned}`
:::

:::lemma_ "lem:logineqY8" (parent := "grp:log") (lean := "UncertaintyPrinciple.logIneq_Y₈")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:logineqY8", citation := "Equation (96)" }] }
%%%

For $`x > 0`, we have
$`(x^2+x+1)^2 \log(1+x) > \frac{1}{12} (11 x^4 + 28 x^3 + 18 x^2 + 12 x)`. This is the case $`Y_8`.
:::

:::proof "lem:logineqY8"
This one does not follow from {bpref "lem:logineq1"}[]: the two sides agree to second order at
$`0`, and $`\frac{2x}{x+2}` already falls below the right-hand side divided by $`(x^2+x+1)^2` at
$`x = \frac{1}{10}`. Instead, divide both sides by $`(x^2+x+1)^2`; then both sides vanish at
$`x = 0`, and the claim follows from
$$`\begin{aligned} &\frac{d}{dx} \left(\log(1 + x) - \frac{11x^4 + 28x^3 + 18x^2 + 12x}{12(x^2 + x + 1)^2}\right) \\ &\quad = \frac{x^4 (2x^2 + 7x + 7)}{2(x+1)(x^2 + x + 1)^3} > 0. \end{aligned}`
:::

:::lemma_ "lem:logineqY10" (parent := "grp:log") (lean := "UncertaintyPrinciple.logIneq_Y₁₀")
%%%
source := { document := "sign", spans := #[{ anchor := "eqn:logineqY10", citation := "Equation (97)" }] }
%%%

For $`x \ge 1`, we have
$$`-(x^2+x+1)(2x+1)(x+2)(1-x) \log(1+x) > \frac{1}{6} (2 x^5 + 11 x^4 - x^3 - 24 x^2 - 12 x).`
This is the case $`Y_{10}`.
:::

:::proof "lem:logineqY10"
It is only needed for $`x \ge 1`, which corresponds to $`0 < t \le 1`; the case $`t > 1` follows
from a hypergeometric expression for $`Y_{10}`. For $`x \ge 1` the coefficient
$`-(x^2+x+1)(2x+1)(x+2)(1-x)` of $`\log(1+x)` is nonnegative, so {uses "lem:logineq1"}[] gives
$$`\begin{aligned} &-(x^2+x+1)(2x+1)(x+2)(1-x) \log(1+x) - \frac{1}{6} (2 x^5 + 11 x^4 - x^3 - 24 x^2 - 12 x) \\ &\quad\ge -(x^2+x+1)(2x+1)(x+2)(1-x) \cdot \frac{2x}{x+2} - \frac{1}{6} (2 x^5 + 11 x^4 - x^3 - 24 x^2 - 12 x) = \frac{1}{6}x^3(22x^2 +x + 1) > 0. \end{aligned}`
:::
