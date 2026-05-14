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
