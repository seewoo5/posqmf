"""Utility functions for level 1 quasimodular forms"""
from sage.all import *


QM = QuasiModularForms(1)
E2, E4, E6 = QM.gen(0), QM.gen(1), QM.gen(2)  # generators, normalized as constant terms = 1
Disc = (1 / 1728) * (E4 ** 3 - E6 ** 2)  # discriminant form

# Depth
def qm_depth(qm):
    return qm.polynomial().degree(E2.polynomial())

# Fourier coefficients
def qm_coefficients(qm, prec=20):
    qexp = qm.q_expansion(prec)
    return q_expansion_to_list(qexp, prec)

def q_expansion_to_list(qexp, prec=20):
    return [qexp[i] for i in range(prec)]

# Iterative differentiation of quasimodular forms
def qm_derivative_fold(qm, k):
    if k == 0:
        return qm
    else:
        return qm_derivative_fold(qm.derivative(), k - 1)

# Serre derivative with given weight k
# If weight is not given, we use k = (weight - depth) that preserves depth.
def qm_serre_derivative(qm, k=None):
    if k is None:
        k = qm.weight() - qm_depth(qm)
    return qm.derivative() - E2 * qm * (k / 12)

# Iterative Serre derivative, which is 
# \partial_{k + 2(r-1)} \circ \partial_{k + 2(r-2)} \circ \cdots \circ \partial_{k} for given r >= 1.
def qm_serre_derivative_fold(qm, r, k=None):
    assert r >= 0
    if r == 0:
        return qm
    elif r == 1:
        return qm_serre_derivative(qm, k)
    else:
        if k is None:
            k = qm.weight() - qm_depth(qm)
        return qm_serre_derivative(qm_serre_derivative_fold(qm, r-1, k), k + 2 * (r-1))

# Dimension of the space of (genuine) modular forms of weight w and level 1
def dim_m(w):
    assert w % 2 == 0
    if w % 12 == 2:
        return w // 12
    else:
        return w // 12 + 1

# Dimension of the space of (genuine) modular forms of weight w, depth <= s and level 1
def dim_qm(w, s):
    assert w % 2 == 0
    assert s >= 0
    d = (w * (s + 1)) // 12
    d -= ((s + 1) // 6) * (s - 3 * ((s + 1) // 6) - 1)
    d += s // 6 + 1
    if (w * (s + 1)) % 12 == 2:
        d -= 1
    return d

# Basis of the space of quasimodular forms of given weight and depth, in terms of Eisenstein series
def qm_basis(w, s):
    basis = []
    for r in range(s + 1):
        w_ = w - 2 * r
        for i in range(w_ // 4 + 1):
            if (w_ - 4 * i) % 6 == 0:
                j = (w_ - 4 * i) // 6
                basis.append(E2^r * E4^i * E6^j)
    return basis

# Vanishing order at the cusp
def qm_cusp_order(qm):
    N = 1000
    c_ = qm_coefficients(qm, N)
    r = 0
    for i in range(N):
        if c_[i] != 0:
            break
        r += 1
    return r

# First nonzero Fourier coefficient
def qm_first_nonzero_coeff(qm):
    N = 1000
    c_ = qm_coefficients(qm, N)
    for i in range(N):
        if c_[i] != 0:
            return c_[i]

# Normalize to make the first nonzero coefficient as 1
def qm_normalize(qm):
    return qm / qm_first_nonzero_coeff(qm)

# Print q-expansion, weight, depth, cusp order, and its polynomial form
def print_qm(qm, name, prec=20):
    print(name + "\n")
    print("q_expansion", qm.q_expansion(prec), "\n")
    if qm.is_homogeneous():
        print("weight", qm.weight())
    else:
        print("weight", qm.weights_list())
    print("depth", qm_depth(qm))
    print("cusp order", qm_cusp_order(qm))
    print("polynomial", qm.polynomial().factor(), "\n")


# Express a given quasimodular form as a linear combination of other quasimodular forms.
def qm_find_lin_comb(qm, ls):
    w = qm.weight()
    s = qm_depth(qm)
    N = dim_qm(w, s)
    m = matrix([qm_coefficients(qm_, N) for qm_ in ls])
    c_ = vector(qm_coefficients(qm, N))
    x_ = m.solve_left(c_)
    r = sum(x_[j] * ls[j] for j in range(len(ls)))
    assert qm == r
    return x_
