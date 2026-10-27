import os
from functools import lru_cache

load(os.path.dirname(os.path.abspath(__file__)) + "/sage/utils_l1.sage")

# H2 = Theta_2^4, H4 = Theta_4^4, E2_ = E2
QM2.<H2, H4, E2_> = QQ['H2,H4,E2']
E4_ = H2^2 + H2 * H4 + H4^2
E6_ = (H2 + 2 * H4) * (2 * H2 + H4) * (H4 - H2) / 2
Disc_ = H2^2 * (H2 + H4)^2 * H4^2 / 256

E2_2z = (1/4) * (2 * E2_ + H2 + 2 * H4)  # E2(2z)
E4_2z = (1/16) * (H2^2 + 16 * H2 * H4 + 16 * H4^2)  # E4(2z)
E6_2z = (-1/64) * (H2 + 2 * H4) * (H2^2 - 32 * H2 * H4 - 32 * H4^2)  # E6(2z)

def qm2_weight(qm):
    """Return the weight of a homogeneous level Gamma(2) quasimodular form."""
    w = None
    for (a, b, e) in qm.dict().keys():
        if w is None:
            w = 2 * a + 2 * b + 2 * e
        else:
            assert w == 2 * a + 2 * b + 2 * e
    return w

def qm2_depth(qm):
    """Return the depth of a level Gamma(2) quasimodular form."""
    dp = 0
    for (_, _, e) in qm.dict().keys():
        dp = max(e, dp)
    return dp

def qm2_derivative(qm):
    """Return the derivative of a level Gamma(2) quasimodular form."""
    r = QM2(0)
    for (a, b, e), coeff in qm.dict().items():
        r += (coeff / 6) * H2^a * H4^b * ((a - 2 * b) * H2 + (2 * a - b) * H4 + (a + b) * E2_) * E2_^e
        if e >= 1:
            r += coeff * H2^a * H4^b * e * E2_^(e-1) * (E2_^2 - E4_) / 12
    return r

def qm2_serre_derivative(qm, k=None):
    """Compute the level Gamma(2) Serre derivative with weight `k`."""
    if k is None:
        k = qm2_weight(qm) - qm2_depth(qm)
    return qm2_derivative(qm) - (k / 12) * E2_ * qm


def qm2_serre_derivative_fold(qm, r, k=None):
    """Compute the iterative level Gamma(2) Serre derivative."""
    assert r >= 0
    if r == 0:
        return qm
    elif r == 1:
        return qm2_serre_derivative(qm, k)
    else:
        if k is None:
            k = qm.weight() - qm2_depth(qm)
        return qm2_serre_derivative(qm2_serre_derivative_fold(qm, r-1, k), k + 2 * (r-1))

# q-series
# Level Gamma(2) forms are expanded in powers of q^(1/2), so their q-expansions are Puiseux series
# in q = e^(2 * pi * i * z), e.g. H2 = 16 * q^(1/2) + 64 * q^(3/2) + O(q^(5/2)).
# The precision `prec` always refers to the error term O(q^prec), and may be a half-integer.
PS.<q> = PuiseuxSeriesRing(QQ)


def r4(k):
    if k == 0:
        return 1
    elif k % 4 == 0:
        return 8 * sigma(k, 1) - 32 * sigma(k / 4, 1)
    else:
        return 8 * sigma(k, 1)

@lru_cache
def qm2_gens_q_series(prec):
    """Return the q-series of the generators `H2`, `H4`, `E2_` up to `O(q^prec)`."""
    # Jacobi thetanulle functions, H3 = Theta_3^4 = H2 + H4
    H3ser = O(q^prec)
    H4ser = O(q^prec)
    for i in range(ceil(2 * prec)):
        H3ser += r4(i) * q^(i / 2)
        H4ser += (-1)^i * r4(i) * q^(i / 2)
    # Eisenstein series
    E2ser = 1 + O(q^prec)
    for i in range(1, ceil(prec)):
        E2ser -= 24 * sigma(i, 1) * q^i
    return H3ser - H4ser, H4ser, E2ser

def qm2_q_series(qm, prec=10):
    """Return the q-series expansion up to `O(q^prec)`, as a Puiseux series in `q`."""
    H2ser, H4ser, E2ser = qm2_gens_q_series(prec)
    r = O(q^prec)
    for (a, b, e), coeff in qm.dict().items():
        r += coeff * H2ser^a * H4ser^b * E2ser^e
    return r

def q_series_coefficients(qser, prec):
    """Return the coefficients of `q^0, q^(1/2), ..., q^(prec - 1/2)` in a Puiseux series."""
    # Index the underlying Laurent series in `q^(1/e)`, since `qser[n]` truncates `n * e` to an integer
    l = qser.laurent_part()
    e = qser.ramification_index()
    return [l[i * e // 2] if (i * e) % 2 == 0 else 0 for i in range(ceil(2 * prec))]

def qm2_coefficients(qm, prec=10):
    """Return the Fourier coefficients of `q^0, q^(1/2), ..., q^(prec - 1/2)`."""
    return q_series_coefficients(qm2_q_series(qm, prec), prec)

def qm2_cusp_order(qm):
    """Return the cusp order for a level Gamma(2) quasimodular form."""
    qser = qm2_q_series(qm, 25)
    if not qser.is_zero():
        return qser.valuation()

def qm2_first_nonzero_coeff(qm):
    """Return the first nonzero Fourier coefficient."""
    qser = qm2_q_series(qm, 50)
    if not qser.is_zero():
        return qser.coefficients()[0]

def qm2_normalize(qm):
    """Normalize so that the first nonzero Fourier coefficient is 1."""
    return qm / qm2_first_nonzero_coeff(qm)

def print_qm2(qm, name, prec=15):
    """Print q-expansion, weight, depth, cusp order, and polynomial data."""
    print(name + "\n")
    print("q_expansion", qm2_q_series(qm, prec), "\n")
    print("weight", qm2_weight(qm))
    print("depth", qm2_depth(qm))
    print("cusp order", qm2_cusp_order(qm))
    if qm == 0:
        print("polynomial", 0, "\n")
    else:
        print("polynomial", qm.factor(), "\n")

def dim_m2(w):
    """Return dimension of modular forms of level Gamma(2) and weight `w`."""
    return w / 2 + 1

def dim_qm2(w, s=None):
    """Return dimension of quasimodular forms of level Gamma(2), weight `w`, depth `<= s`."""
    if s is None:
        s = w / 2
    d = 0
    for k in range(s + 1):
        d += dim_m2(w - 2 * k)
    return d

def qm2_find_lin_comb(qm, ls):
    """Express `qm` as a linear combination of forms in `ls`."""
    w = qm2_weight(qm)
    s = qm2_depth(qm)
    N = dim_qm2(w, s)
    m = matrix([qm2_coefficients(qm_, N / 2) for qm_ in ls])
    c_ = vector(qm2_coefficients(qm, N / 2))
    x_ = m.solve_left(c_)
    r = sum(Rational(x_[j]) * ls[j] for j in range(len(ls)))
    assert r == qm
    return x_

def qm2_find_lin_comb_coeff(coeffs, ls):
    """Find a linear combination in `ls` from initial q-series coefficients."""
    N = len(coeffs)
    m = matrix([qm2_coefficients(qm_, N / 2) for qm_ in ls])
    c_ = vector(coeffs)
    print(f"m: {m}")
    print(f"c: {c_}")
    x_ = m.solve_left(c_)
    r = sum(Rational(x_[j]) * ls[j] for j in range(len(ls)))
    assert qm2_coefficients(r, N / 2) == coeffs
    return x_

def qm2_to_func(qm, prec=100):
    """Convert a level Gamma(2) quasimodular form to a function on the positive imaginary axis."""
    qser = qm2_q_series(qm, prec=prec)
    func = 0
    for n, c in zip(qser.exponents(), qser.coefficients()):
        func += c * exp(-2 * n * pi * t)  # note q^n = e^(2 * pi * sqrt(-1) * n * z)
    return func

def qm2_modular_components(qm):
    """Return placeholder modular-component pair `(tG, psi)` for a level Gamma(2) form."""
    d = qm.dict()
    tG = QM2(0)
    psi = QM2(0)
    for (a, b, e), coeff in d.items():
        psi += coeff * H2^a * H4^b * E2_^e
    return tG, psi

def l1_to_l2(qm):
    """Rewrite a level 1 quasimodular form as a level Gamma(2) form."""
    r = QM2(0)
    for (d2, d4, d6), coeff in qm.polynomial().dict().items():
        r += coeff * E2_^d2 * E4_^d4 * E6_^d6
    return r

def double_argument(qm):
    """Map `f(z)` to `f(2z)` for level 1 quasimodular forms represented at level Gamma(2)."""
    r = QM2(0)
    for (d2, d4, d6), coeff in qm.polynomial().dict().items():
        r += coeff * E2_2z^d2 * E4_2z^d4 * E6_2z^d6
    return r
