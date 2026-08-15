## Sage codes

The sage codes under the directory `sage` provides several functions for computations with quasimodular forms and extremal quasimodular forms.

### `extremal_eis.sage`

- `extremal_eisenstein_series` compute extremal Eisenstein series of given weight, i.e. a modular form of weight $w$ with $q$-expansion $1 + O(q^{l})$ where $l$ is the dimension of the space of modular forms of weight $w$. It simply solve linear system on the coefficients of basis of the corresponding space of modular forms.

- `jenkins_rouse_coeff_threshold` computes threshold $n_0$ for extremal Eisenstein series of given weight due to Jenkins and Rouse, where the coefficients $a_n$ has consistent signs for $n \ge n_0$. Note that there are some minor errors in the original paper, and we use the corrected version here with slightly larger constant.

- `check_extremal_eisenstein_series_completely_positive` checks if the Fourier coefficients of the extremal Eisenstein series of given weight have desired signs (positive for $w \equiv 0 \pmod{4}$, negative for $w \equiv 2 \pmod{4}$) using Jenkins-Rouse coefficient threshold.

### `extremal_qm.sage`

- `extremal_qm` computes an extremal quasimodular form of given weight and depth (Kaneko-Koike). For the case of depth 1 and 2, it uses the recurrence relations in Grabner's paper "Quasimodular forms as solutions of modular differential equations". For other weights and depths (possibly larger than 4), it simply solve linear system on the coefficients of basis of the corresponding space of quasimodular forms.

### `extremal_qm_high_level.sage`

Functions for extremal quasimodular forms of level $\Gamma_0(2)$ and $\Gamma_0(3)$.

- `extremal_qm_l2` and `extremal_qm_l3` compute extremal quasimodular forms of given weight and depth at levels $\Gamma_0(2)$ and $\Gamma_0(3)$.

- `qm_l2_basis` and `qm_l3_basis` return bases of the corresponding spaces of quasimodular forms.

- `is_extremal_qm_unique_level` checks uniqueness of extremal quasimodular forms at levels $1$, $2$, and $3$.

### `victor_miller_basis.sage`

- `l2_victor_miller_basis` and `l3_victor_miller_basis` compute Victor-Miller bases for modular forms of levels $\Gamma_0(2)$ and $\Gamma_0(3)$.

### `fgh.sage`

Functions for the Feigenbaum-Grabner-Hardin families of quasimodular forms used in the sign uncertainty principle computations.

- `F`, `G`, and `Y` compute $F_w$, $G_w$, and $Y_w$, respectively.

- `Ftilde` and `Gtilde` compute $\widetilde{F}_{w}$ and $\widetilde{G}_{w}$, respectively.

### `utils_l1.sage`

Functions for level 1 quasimodular forms, including depths, $q$-expansion, (Serre) derivative.

- `print_qm` gives $q$-expansion, weight, depth, cusp order, and the polynomial expression of a given quasimodular form.

- `qm_find_lin_comb` try to express a given quasimodular form `qm` as a linear combination of a list of quasimodular forms `ls` if possible.

- `qm_to_func` returns a function $t \mapsto F(it)$ defined on positive real numbers, for a given quasimodular form $F$.

- `modular_comp` extract modualr form components of a given quasimodular form, i.e. for $F = f_0 + f_1 E_2 + f_2 E_2^2 + \cdots + f_n E_2^n$, it returns the dictionary of modular forms `{k : f_k}`.

### `utils_l2.sage`

Functions for level $\Gamma(2)$ quasimodular forms.
These are implemented as polynomials in three variables, $H_2$ (`H2`), $H_4$ (`H4`), $E_2$ (`E2`).
$q$-expansions are given in terms of `qh`, which corresponds to $q^{1/2}$.

- `print_qm2` gives $q$-expansion, weight, depth, cusp order, and the polynomial expansion of a given quasimodular form.

- `l1_to_l2` rewrites a level 1 quasimodular form as level $\Gamma(2)$ quasimodular form.
It uses the identities between Eisenstein series and Jacobi theta functions.

- `double_argument` returns $F(2z)$ for a given level 1 quasimodular form $F(z)$.

### `utils_l2_LS.sage`

Functions for the ring `QM2_LS = QM2[LS]`, used to compute $G_w$ and $Y_w$ in `fgh.sage`.

- `ls_components` extracts the two components $A$ and $B$ from an element $A + B \cdot \mathcal{L}_S$.

- `ls_q_series`, `ls_coefficients`, and `ls_cusp_order` compute $q^{1/2}$-expansions, coefficients, and cusp orders.

- `ls_derivative` and `ls_serre_derivative` extend the derivative and Serre derivative to `QM2_LS`.

### `utils_rqm.sage`

For the proof of the "harder" 24-dimensional modular form inequality, we define auxiliary rings `RQM` and `RQM2`, which are

$$
\mathcal{RQM}(\Gamma) = \mathcal{QM}(\Gamma) \left[\frac{1}{\pi}, \frac{i}{z}\right]
$$

for $\Gamma = \mathrm{SL}_{2}(\mathbb{Z})$ and $\Gamma(2)$.
The variables `ip` and `ioz` are $1/\pi$ and $i/z = 1/t$, respectively, which are considered as "weight 1" objects. The derivative is extended to these rings using

$$
D\left(\frac{1}{\pi}\right) = 0, \quad D\left(\frac{i}{z}\right) = \frac{1}{2\pi i} \frac{\mathrm{d}}{\mathrm{d}z} \left(\frac{i}{z}\right) = \frac{1}{2} \frac{1}{\pi} \left(\frac{i}{z}\right)^2
$$

and product rule.

- `rqm_S_action` and `rqm2_S_action` compute the slash action by $S$ for homogeneous elements in `RQM` and `RQM2`. The action $|\_{w}S$ on $F \cdot \left(\frac{1}{\pi}\right)^a \cdot \left(\frac{i}{z}\right)^b$ becomes

$$
\begin{align*}&(F|\_{w-a-b}S) \cdot \left(\frac{1}{\pi}\right)^{a} \left(\frac{i}{-1/z}\right)^{b} z^{-a-b} \\ &= (-1)^{(a+b)/2} \cdot (F|\_{w-a-b}S) \cdot \left(\frac{1}{\pi}\right)^a \cdot \left(\frac{i}{z}\right)^a.\end{align*}
$$

- `rqm_homogeneous_comps` and `rqm2_homogeneous_comps` extract each of homogeneous components from possibly inhomogeneous input.

## Lean codes

The lean codes under the directory `lean` verifies several inequalities on quasimodular forms and their coefficients.
The first three files were initially written by AxiomProver and manually golfed afterwards.
`X_16_5.lean` and `D_6_3.lean` were written by Claude Opus 4.7.

- `polymod_monotone.lean` verifies (41) of "Inequalities involving polynomials and quasimodular forms".
- `polymod_ineq1.lean` verifies (60) of "Inequalities involving polynomials and quasimodular forms".
- `polymod_ineq2.lean` verifies (61) of "Inequalities involving polynomials and quasimodular forms".
- `X_16_5.lean` verifies that the extremal quasimodular form $X_{16, 5}$ of weight $16$ and depth $5$ has negative coefficients for $n \ge 250$. Negativity for $8 \le n < 250$ is checked separately in `miscellaneous.ipynb`.
- `D_6_3.lean` verifies the positivity of the coefficients of $\mathcal{D}_{6, 3}$.
- `SigmaBounds.lean` include basic inequalities for the divisor sum function, which are used in the above two files.

### `DifferentialOperators`

The directory `lean/DifferentialOperators` formalizes the operator bookkeeping of "Positive quasimodular forms and the sign uncertainty principle", at the level of formal $q$-expansions: $\mathbb{R}[[q]]$ is the ring of $q$-series, $D = q \frac{d}{dq}$, and $E_2, E_4, E_6$ are the explicit divisor-sum series. (Mathlib's `D` and Serre derivative are differential operators on functions on the upper half plane, which carry analytic content that none of these identities need.)

- `Basic.lean` defines $D$ and proves the Leibniz rule and the convolution lemma used in all coefficient computations.
- `Eisenstein.lean` defines $E_2, E_4, E_6$ and computes $[q^n](E \cdot G)$ for $E \in \\{E_2, E_4, E_6, E_2', E_2'', E_4'\\}$.
- `Ramanujan.lean` states Ramanujan's identities $E_2' = (E_2^2 - E_4)/12$, $E_4' = (E_2E_4 - E_6)/3$, $E_6' = (E_2E_6 - E_4^2)/2$ **as axioms**, together with the reductions they yield.
- `Serre.lean` defines $\partial_k$ and $\partial_k^r$, proves the product rule and Ramanujan's identities in Serre form, and expands $\partial_k^2$ and $\partial_k^3$ in terms of $D$.
- `KanekoZagier.lean` defines the Kaneko-Zagier operators $L_{2,k}^{\alpha}$ and $L_{3,k}^{(\alpha,\beta)}$ by their $D$-forms and proves that these agree with their Serre-derivative forms.
- `Coefficients.lean` proves the Fourier coefficient formulas `lem:KZ2_coeff` and `lem:KZ3_coeff` (Lemma 2.2 and Lemma 2.3). These do **not** depend on the Ramanujan axioms.
- `Intertwine.lean` proves the intertwining relation between second- and third-order Kaneko-Zagier operators under the four constraints on parameters (Lemma 2.4).
- `QuasiModular.lean` sets up the polynomial model $\mathbb{R}[E_2, E_4, E_6]$, which is needed because $\delta = \partial/\partial E_2$ is not an operator on $q$-series. It carries $D$, $\delta$, the Euler weight operator, and the Serre derivative, proves the commutator identities $[\delta, D] = \frac{1}{12}E$ and $\delta\partial_k F = \partial_k\delta F + \frac{w-k}{12}F$, and defines the algebra map to $q$-expansions that ties the two layers together.

### `UncertaintyPrinciple`

The directory `lean/UncertaintyPrinciple` formalizes the coefficient-positivity arguments of "Positive quasimodular forms and the sign uncertainty principle" that sit on top of the operator layer.

- `LogInequalities.lean` proves the four elementary logarithm inequalities behind the base cases of the positivity of $Y_w$ (Lemma 4.10 and the $Y_4$, $Y_8$, $Y_{10}$ cases of Theorem 4.11), via the mean value theorem.
- `F.lean` proves positivity of the Fourier coefficients of $\widetilde{F}_{w-2}$ (Proposition 4.5), assuming nothing. Its `QExpansion` section runs the induction in $\mathbb{R}[[q]]$ from the recurrence (Lemma 4.4); its `PolynomialModel` section defines $F_{4N+12}$ by that recurrence, sets $\widetilde{F}_{w-2} := \delta F_w$, and supplies the vanishing order and the normalization, the latter through the modular linear differential equation $L_{3,w-2}^{((w-4)/4,\,0)}F_w = 0$. The two sections open different namespaces, since `KanekoZagier` and `QuasiModular` both name $D$, $E_2, E_4, E_6$ and $\partial_k$.
- `G.lean` proves nonnegativity of the Fourier coefficients of $\widetilde{G}_w$ (Propositions 4.21 and 4.22), also assuming nothing, plus strict positivity of the constant term. Its third-order equation is proved by the intertwining criterion from a check on the constant $\widetilde{G}_0$. No polynomial model is needed here, since no $\delta$ appears.

Most results use the Ramanujan axioms of `DifferentialOperators/Ramanujan.lean`. The exceptions are `LogInequalities.lean`, the hypothesis-taking `ftildePos` and `ftildeBoundary` of `F.lean`, and `coeff_gtildeSeries_zero_pos`.

Neither file identifies its family with the paper's $F_w$ and $\widetilde{G}_w$. For $F$ the vanishing order, normalization and differential equation are all proved, which is what characterizes the extremal quasimodular form. For $\widetilde{G}$ the recurrence is taken as the definition; deriving it from $G_w = \widetilde{G}_{w-12} \Delta \mathcal{L}_S + \Psi_w$ is an argument about modular functions for $\Gamma(2)$ and lies outside the development.
