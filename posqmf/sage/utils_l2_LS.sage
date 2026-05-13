import os

load(os.path.dirname(os.path.abspath(__file__)) + "/sage/utils_l2.sage")


r"""
Module over QM2 with basis {1, LS}.

Elements are represented in the polynomial ring
    QM2_LS = QM2[LS].
In particular, a module element A + B * LS is represented as a *single*
element of QM2_LS.

The q-expansion of LS is (in terms of qh = q^{1/2}):
  LS = -16 * sum_{k >= 0} sigma_1(2k+1) / (2k+1) * qh^{2k+1}
where qh is the level-2 half-power parameter from utils_l2.sage.
"""

QM2_LS.<LS> = QM2['LS']


def ls_components(f, strict=True):
    r"""
    Return (A, B) in QM2 for f = A + B * LS.

    If strict=True, raise an error if f has LS-degree >= 2.
    """
    d = f.dict()
    A = QM2(d.get(0, 0))
    B = QM2(d.get(1, 0))
    if strict:
        for k, v in d.items():
            if k >= 2 and v != 0:
                raise ValueError("Expected a linear element A + B*LS, but LS^2 term exists")
    return A, B


def ls_weight(f):
    r"""
    Weight of a homogeneous QM2_LS element.

    LS is treated as weight 0, so all nonzero QM2 coefficients must have the
    same weight. Returns 0 for the zero element.
    """
    w = None
    for _, coeff in f.dict().items():
        c = QM2(coeff)
        if c == 0:
            continue
        try:
            w_c = qm2_weight(c)
        except AssertionError as err:
            raise ValueError("Coefficient is not homogeneous in QM2; please pass k explicitly") from err
        if w is None:
            w = w_c
        elif w != w_c:
            raise ValueError("Input is not homogeneous in weight; please pass k explicitly")
    if w is None:
        return 0
    return w


def ls_depth(f):
    r"""
    Depth of a QM2_LS element, defined as max depth among QM2 coefficients.
    """
    df = 0
    for _, coeff in f.dict().items():
        c = QM2(coeff)
        if c != 0:
            df = max(df, qm2_depth(c))
    return df


def ls_derivative(f):
    r"""
    Derivative on QM2_LS.

    Uses:
      D(C) = qm2_derivative(C) for C in QM2,
      D(LS) = -H2/2,
    and Leibniz rule.
    """
    r = QM2_LS(0)
    dLS = -H2 / 2
    for j, coeff in f.dict().items():
        c = QM2(coeff)
        if c == 0:
            continue
        # D(c * LS^j) = D(c) * LS^j + c * j * LS^(j-1) * D(LS)
        r += QM2_LS(qm2_derivative(c)) * LS^j
        if j >= 1:
            r += QM2_LS(c * j * dLS) * LS^(j - 1)
    return r


def ls_serre_derivative(f, k=None):
    r"""
    Serre derivative on QM2_LS:
      D_k(f) = D(f) - (k/12) * E2_ * f.

    If k is None, infer k from ls_weight(f).
    """
    if k is None:
        k = ls_weight(f)
    return ls_derivative(f) - QM2_LS((k / 12) * E2_) * f


def ls_basis_q_series(prec=40):
    r"""
    qh-expansion of LS up to O(qh^prec).

    Uses LSser from utils_l2.sage when possible. For larger precision requests,
    computes directly from
      LS = -16 * sum_{k >= 0} sigma_1(2k+1)/(2k+1) * qh^(2k+1).
    """
    N = int(prec)
    if N <= 0:
        return (qh - qh).series(qh, N)

    r = qh - qh
    for k in range((N - 1) // 2 + 1):
        m = 2 * k + 1
        if m >= N:
            break
        r += (-16) * (sigma(m, 1) / m) * qh^m
    return r.series(qh, N)


def ls_q_series(f, prec=40):
    r"""
    Compute qh-expansion of f in terms of qh = q^{1/2}.

    For f = sum_{j >= 0} C_j * LS^j with C_j in QM2,
    evaluates LS at ls_basis_q_series(prec) and returns O(qh^prec).
    """
    N = int(prec)
    if N <= 0:
        return (qh - qh).series(qh, N)

    LS_q = ls_basis_q_series(N)
    r = qh - qh
    for j, coeff in f.dict().items():
        if coeff == 0:
            continue
        r += qm2_q_series(QM2(coeff), N) * (LS_q^j)
    return r.series(qh, N)


def ls_coefficients(f, prec=40):
    """Return list of qh-expansion coefficients [a_0, a_1, ..., a_{prec-1}]."""
    N = int(prec)
    coeffs = ls_q_series(f, N).list()
    if len(coeffs) < N:
        coeffs += [0] * (N - len(coeffs))
    return coeffs[:N]


def ls_cusp_order(f, prec=50):
    """Find order of vanishing at the cusp (in terms of qh powers).

    Returns i/2 where i is the smallest power of qh with nonzero coefficient,
    matching the convention in utils_l2.sage.
    """
    c = ls_coefficients(f, prec)
    for i in range(len(c)):
        if c[i] != 0:
            return i / 2
    raise ValueError("Precision not sufficient to determine cusp order")


def ls_first_nonzero_coeff(f, prec=50):
    """Return the first nonzero coefficient in the qh-expansion."""
    c = ls_coefficients(f, prec)
    for i in range(len(c)):
        if c[i] != 0:
            return Rational(c[i])
    raise ValueError("Precision not sufficient")


def ls_normalize(f):
    """Normalize so that the first nonzero qh-coefficient is 1."""
    c = ls_first_nonzero_coeff(f)
    return f / c


def ls_to_func(f, prec=100):
    r"""
    QM2_LS element as a function on positive imaginary axis.

    If z = i t with t > 0, then qh = exp(-pi t), so
    f = sum_{n >= 0} c_n * qh^n becomes
    f(i t) = sum_{n >= 0} c_n * exp(-n * pi * t).
    """
    qser = ls_q_series(f, prec=prec)
    c = qser.list()
    func = c[0]
    for i in range(1, len(c)):
        func += c[i] * exp(-i * pi * t)
    return func


def print_ls(f, name, prec=30):
    """Print info about a QM2_LS element (expects linear form for A/B display)."""
    A, B = ls_components(f, strict=True)
    print(name + "\n")
    print("element", f)
    print("q_expansion", ls_q_series(f, prec), "\n")
    try:
        print("weight", ls_weight(f))
    except ValueError:
        print("weight", "inhomogeneous")
    print("depth", ls_depth(f))
    print("cusp order", ls_cusp_order(f))
    print("\n" + "=" * 35 + " Components (f = A + B * LS): " + "=" * 35 + "\n")
    print_qm2(A, "A (constant part)", prec)
    print_qm2(B, "B (LS part)", prec)
    print("=" * 100)


# Convenient named basis elements
E2_LS = QM2_LS(E2_)
E4_LS = QM2_LS(E4_)
E6_LS = QM2_LS(E6_)
Disc_LS = QM2_LS(Disc_)
