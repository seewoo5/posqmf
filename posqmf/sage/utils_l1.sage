from sage.all import *

# Level 1 quasimodular forms
QM = QuasiModularForms(1)
E2, E4, E6 = QM.gen(0), QM.gen(1), QM.gen(2)  # generators, normalized as constant terms = 1
Disc = (1 / 1728) * (E4 ^ 3 - E6 ^ 2)  # discriminant form
t = var('t')  # variable for the positive imaginary axis


# Fourier coefficients
def qm_coefficients(qm, prec=20):
    """Return the first `prec` Fourier coefficients of a quasimodular form."""
    qexp = qm.q_expansion(prec)
    return q_expansion_to_list(qexp, prec)

def q_expansion_to_list(qexp, prec=20):
    """Convert a q-expansion to a list of coefficients up to precision `prec`."""
    return [qexp[i] for i in range(prec)]

def qm_derivative_fold(qm, k):
    """Apply iterative differentiation `k` times to a quasimodular form."""
    if k == 0:
        return qm
    else:
        return qm_derivative_fold(qm.derivative(), k - 1)

def qm_serre_derivative(qm, k=None):
    """
    Compute the Serre derivative with weight `k`.
    If `k` is omitted, use `weight - depth`, which preserves depth.
    """
    if k is None:
        k = qm.weight() - qm.depth()
    return qm.derivative() - E2 * qm * (k / 12)

def qm_serre_derivative_fold(qm, r, k=None):
    """
    Compute an iterative Serre derivative.
    This applies
    `\\partial_{k + 2(r-1)} \\circ \\partial_{k + 2(r-2)} \\circ \\cdots \\circ \\partial_{k}`
    for `r >= 1`, with the convention that `r = 0` returns `qm`.
    """
    assert r >= 0
    if r == 0:
        return qm
    elif r == 1:
        return qm_serre_derivative(qm, k)
    else:
        if k is None:
            k = qm.weight() - qm.depth()
        return qm_serre_derivative(qm_serre_derivative_fold(qm, r-1, k), k + 2 * (r-1))

def dim_m(w):
    """Return the dimension of level-1 modular forms of weight `w`."""
    assert w % 2 == 0
    if w % 12 == 2:
        return w // 12
    else:
        return w // 12 + 1

def dim_qm(w, s):
    """Return the dimension of level-1 quasimodular forms of weight `w` and depth `<= s`."""
    assert w % 2 == 0
    assert s >= 0
    d = (w * (s + 1)) // 12
    d -= ((s + 1) // 6) * (s - 3 * ((s + 1) // 6) - 1)
    d += s // 6 + 1
    if (w * (s + 1)) % 12 == 2:
        d -= 1
    return d

def qm_basis(w, s):
    """Return an Eisenstein-monomial basis for quasimodular forms of weight `w` and depth `s`."""
    basis = []
    for r in range(s + 1):
        w_ = w - 2 * r
        for i in range(w_ // 4 + 1):
            if (w_ - 4 * i) % 6 == 0:
                j = (w_ - 4 * i) // 6
                basis.append(E2 ** r * E4 ** i * E6 ** j)
    return basis

def qm_cusp_order(qm, prec=100):
    """Return the vanishing order at the cusp."""
    c_ = qm.coefficients(list(range(prec + 1)))
    r = 0
    for i in range(prec + 1):
        if c_[i] != 0:
            break
        r += 1
        if i == prec:
            raise ValueError("The precision is not enough to determine the cusp order")
    return r

def qm_first_nonzero_coeff(qm, prec=100):
    """Return the first nonzero Fourier coefficient."""
    c_ = qm.coefficients(list(range(prec + 1)))
    for i in range(prec + 1):
        if c_[i] != 0:
            return c_[i]
    raise ValueError("The precision is not enough to determine the first nonzero coefficient")

def qm_normalize(qm):
    """Normalize a quasimodular form so its first nonzero coefficient is 1."""
    return qm / qm_first_nonzero_coeff(qm)

def print_qm(qm, name, prec=20):
    """Print q-expansion, weight data, depth, cusp order, and polynomial factorization."""
    print(name + "\n")
    print("q_expansion", qm.q_expansion(prec), "\n")
    if qm.is_homogeneous():
        print("weight", qm.weight())
    else:
        print("weight", qm.weights_list())
    print("depth", qm.depth())
    print("cusp order", qm_cusp_order(qm))
    print("polynomial", qm.polynomial().factor(), "\n")

def qm_find_lin_comb_coeffs(w, s, coeffs, ls=None, prec=100):
    """
    Find a quasimodular form with prescribed coefficients in a given span.
    If `ls` is omitted, use the standard basis `qm_basis(w, s)`.
    """
    if ls is None:
        ls = qm_basis(w, s)
    m = matrix([qm_.coefficients(list(range(prec))) for qm_ in ls])
    c_ = vector(coeffs[:prec])
    try:
        x_ = m.solve_left(c_)
        r = sum(x_[j] * ls[j] for j in range(len(ls)))
        assert r.coefficients(list(range(prec))) == coeffs[:prec]
        return r
    except ValueError:
        raise ValueError("The given coefficients are not in the span of the given quasimodular forms")

def qm_find_lin_comb(qm, ls, prec=100):
    """Express `qm` as a linear combination of quasimodular forms in `ls`."""
    w = qm.weight()
    s = qm.depth()
    m = matrix([qm_.coefficients(list(range(prec))) for qm_ in ls])
    c_ = vector(qm.coefficients(list(range(prec))))
    x_ = m.solve_left(c_)
    r = sum(x_[j] * ls[j] for j in range(len(ls)))
    assert qm == r
    return x_

def qm_to_func(qm, prec=100):
    """Convert a quasimodular form to a function on the positive imaginary axis."""
    t = var('t')
    c = qm.q_expansion(prec).list()
    func = c[0]
    for i in range(1, len(c)):
        func += c[i] * exp(-i * 2 * pi * t)
    return func

def modular_comp(qm):
    """
    Extract modular components of a quasimodular form.
    If `F = f_0 + f_1 E2 + f_2 E2^2 + ... + f_n E2^n`, return
    a dictionary keyed by the `E2` exponent with values `f_i`.
    """
    comps = {}
    for k, v in qm._polynomial().dict().items():
        if k not in comps:
            comps[k] = QM(0)
        comps[k] += QM(v)
    return comps

def eisenstein(w):
    """Compute the Eisenstein series of weight `w`."""
    return ModularForms(weight=w).basis()[-1]
