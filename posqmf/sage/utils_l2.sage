import os

load(os.path.dirname(os.path.abspath(__file__)) + "/sage/utils_l1.sage")

# H2 = Theta_2^4, H4 = Theta_4^4, E2_ = E2
QM2.<H2, H4, E2_> = QQ['H2,H4,E2']
E4_ = H2^2 + H2 * H4 + H4^2
E6_ = (H2 + 2 * H4) * (2 * H2 + H4) * (H4 - H2) / 2
Disc_ = H2^2 * (H2 + H4)^2 * H4^2 / 256


# Weight
def qm2_weight(qm):
    w = None
    for (a, b, e) in qm.dict().keys():
        if w is None:
            w = 2 * a + 2 * b + 2 * e
        else:
            assert w == 2 * a + 2 * b + 2 * e
    return w

# Depth
def qm2_depth(qm):
    dp = 0
    for (_, _, e) in qm.dict().keys():
        dp = max(e, dp)
    return dp

# Derivative of level 2 quasimodular form
def qm2_derivative(qm):
    r = QM2(0)
    for (a, b, e), coeff in qm.dict().items():
        r += (coeff / 6) * H2^a * H4^b * ((a - 2 * b) * H2 + (2 * a - b) * H4 + (a + b) * E2_) * E2_^e
        if e >= 1:
            r += coeff * H2^a * H4^b * e * E2_^(e-1) * (E2_^2 - E4_) / 12
    return r

# Serre derivative
def qm2_serre_derivative(qm, k=None):
    if k is None:
        # Serre derivative that preserves depth
        k = qm2_weight(qm) - qm2_depth(qm)
    return qm2_derivative(qm) - (k / 12) * E2_ * qm


# Iterative Serre derivative
def qm2_serre_derivative_fold(qm, r, k=None):
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
# Note that the variable `q` in the expansion is in fact e^(pi * i * z), which is `q^(1/2)`.
# The default precision is fixed (which is enough for our purpose), but you can increase it
prec = 80
qh = var('qh')  # q^1/2

def sigma(k, m):
    r = 0
    for i in range(1, k + 1):
        if k%i == 0:
            r += i^m
    return r

def r4(k):
    if k == 0:
        return 1
    elif k % 4 == 0:
        return 8 * sigma(k, 1) - 32 * sigma(k / 4, 1)
    else:
        return 8 * sigma(k, 1)

# q-series of Jacobi thetanulle functions
H3ser = 1
for i in range(1, prec):
    H3ser += r4(i) * qh^i
H4ser = 1
for i in range(1, prec):
    H4ser += (-1)^i * r4(i) * qh^i
H2ser = H3ser - H4ser

# q-series of log lambda_S
LSser = qh
for i in range(1, prec):
    LSser += (sigma(2 * i + 1, 1) / (2 * i + 1)) * qh^(2 * i + 1)
LSser *= (-16)

# q-series of Eisenstein series
E2ser = 1
for i in range(1, prec):
    E2ser -= 24 * sigma(i, 1) * qh^(2 * i)

E4ser = 1
for i in range(1, prec):
    E4ser += 240 * sigma(i, 3) * qh^(2 * i)
    
E6ser = 1
for i in range(1, prec):
    E6ser -= 504 * sigma(i, 5) * qh^(2 * i)

def qm2_q_series(qm, prec=20):
    # Recall that the series is in q^(1/2)
    r = qh - qh
    H2ser_ = H2ser.series(qh, prec)
    H4ser_ = H4ser.series(qh, prec)
    E2ser_ = E2ser.series(qh, prec)
    for (a, b, e), coeff in qm.dict().items():
        r += coeff * H2ser_^a * H4ser_^b * E2ser_^e
    return r.series(qh, prec)

# Fourier coefficients
def qm2_coefficients(qm, prec=20):
    return qm2_q_series(qm, prec).list()

# Cusp order
def qm2_cusp_order(qm):
    N = 50
    c = qm2_q_series(qm, N).list()
    for i in range(N):
        if c[i] != 0:
            return i / 2

# First nonzero Fourier coefficient
def qm2_first_nonzero_coeff(qm):
    N = 100
    c = qm2_q_series(qm, N).list()
    for i in range(N):
        if c[i] != 0:
            return Rational(c[i])

def qm2_normalize(qm):
    return qm / qm2_first_nonzero_coeff(qm)

def print_qm2(qm, name, prec=30):
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
    return w / 2 + 1

def dim_qm2(w, s=None):
    if s is None:
        s = w / 2
    d = 0
    for k in range(s + 1):
        d += dim_m2(w - 2 * k)
    return d

def qm2_find_lin_comb(qm, ls):
    w = qm2_weight(qm)
    s = qm2_depth(qm)
    N = dim_qm2(w, s)
    m = matrix([qm2_q_series(qm_, N).list()[:N] for qm_ in ls])
    c_ = vector(qm2_q_series(qm, N).list())
    x_ = m.solve_left(c_)
    # check if we get the right result
    r = sum(Rational(x_[j]) * ls[j] for j in range(len(ls)))
    assert r == qm
    return x_

def qm2_to_func(qm, prec=100):
    qser = qm2_q_series(qm, prec=prec)
    c = qser.list()
    func = c[0]
    for i in range(1, len(c)):
        func += c[i] * exp(-i * pi * t)  # note q^(1/2) = e^(sqrt(-1) * pi * z)
    return func

# components
def qm2_modular_components(qm):
    d = qm.dict()
    tG = QM2(0)
    psi = QM2(0)
    for (a, b, e), coeff in d.items():
        psi += coeff * H2^a * H4^b * E2_^e
    return tG, psi

# Rewrite level 1 quasimodular forms as level Gamma(2) forms
def l1_to_l2(qm):
    r = QM2(0)
    for (d2, d4, d6), coeff in qm.polynomial().dict().items():
        r += coeff * E2_^d2 * E4_^d4 * E6_^d6
    return r
