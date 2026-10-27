import os

load(os.path.dirname(os.path.abspath(__file__)) + "/sage/utils_l2.sage")


r"""
Module over QM2 with basis {1, LS}.

Elements are represented in the polynomial ring
    QM2_LS = QM2[LS].
In particular, a module element A + B * LS is represented as a *single*
element of QM2_LS.

The q-expansion of LS is the Puiseux series
  LS = -16 * sum_{k >= 0} sigma_1(2k+1) / (2k+1) * q^{(2k+1)/2}
in the variable q of utils_l2.sage.
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


def ls_basis_q_series(prec=20):
    r"""
    q-expansion of LS up to O(q^prec), as a Puiseux series in q:
      LS = -16 * sum_{k >= 0} sigma_1(2k+1)/(2k+1) * q^((2k+1)/2).
    """
    r = O(q^prec)
    for m in range(1, ceil(2 * prec), 2):
        r += (-16) * (sigma(m, 1) / m) * q^(m / 2)
    return r


def ls_q_series(f, prec=20):
    r"""
    Compute the q-expansion of f, as a Puiseux series in q.

    For f = sum_{j >= 0} C_j * LS^j with C_j in QM2,
    evaluates LS at ls_basis_q_series(prec) and returns O(q^prec).
    """
    LS_q = ls_basis_q_series(prec)
    r = O(q^prec)
    for j, coeff in f.dict().items():
        if coeff == 0:
            continue
        r += qm2_q_series(QM2(coeff), prec) * (LS_q^j)
    return r


def ls_coefficients(f, prec=20):
    """Return list of q-expansion coefficients [a_0, a_{1/2}, ..., a_{prec-1/2}]."""
    return q_series_coefficients(ls_q_series(f, prec), prec)


def ls_cusp_order(f, prec=25):
    """Find order of vanishing at the cusp, i.e. the smallest power of q with nonzero coefficient.

    This is a multiple of 1/2, matching the convention in utils_l2.sage.
    """
    qser = ls_q_series(f, prec)
    if qser.is_zero():
        raise ValueError("Precision not sufficient to determine cusp order")
    return qser.valuation()


def ls_first_nonzero_coeff(f, prec=25):
    """Return the first nonzero coefficient in the q-expansion."""
    qser = ls_q_series(f, prec)
    if qser.is_zero():
        raise ValueError("Precision not sufficient")
    return qser.coefficients()[0]


def ls_normalize(f):
    """Normalize so that the first nonzero q-coefficient is 1."""
    c = ls_first_nonzero_coeff(f)
    return f / c


def ls_to_func(f, prec=100):
    r"""
    QM2_LS element as a function on positive imaginary axis.

    If z = i t with t > 0, then q = exp(-2 pi t), so
    f = sum_{n in (1/2)Z, n >= 0} c_n * q^n becomes
    f(i t) = sum_{n} c_n * exp(-2 n pi t).
    """
    qser = ls_q_series(f, prec=prec)
    func = 0
    for n, c in zip(qser.exponents(), qser.coefficients()):
        func += c * exp(-2 * n * pi * t)
    return func


def print_ls(f, name, prec=15):
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
