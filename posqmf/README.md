# Utility codes

## Sage codes

The sage codes under the directory `sage` provides several functions for computations with quasimodular forms and extremal quasimodular forms.

### `extremal_qm.sage`

- `extremal_qm` computes an extremal quasimodular form of given weight and depth (Kaneko-Koike). For the case of depth 1 and 2, it uses the recurrence relations in Grabner's paper "Quasimodular forms as solutions of modular differential equations". For other weights and depths (possibly larger than 4), it simply solve linear system on the coefficients of basis of the corresponding space of quasimodular forms.

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

The lean codes under the directory `lean` verifies several inequalities arise in the paper "Inequalities involving polynomials and quasimodular forms".

- `polymod_monotone.lean` verifies (41).
- `polymod_ineq1.lean` verifies (60).
- `polymod_ineq2.lean` verifies (61).
