# Use cache
import os
from functools import lru_cache

load(os.path.dirname(os.path.abspath(__file__)) + "/sage/utils_l1.sage")

## Level Gamma0(2)

_QM2 = QuasiModularForms(Gamma0(2))
E2_l2 = _QM2.gen(0)  # E2
A2_l2 = _QM2.gen(1)  # E2_0 = 2E2(2z) - E2(z)
E2_2z_l2 = (1/2) * (E2_l2 + A2_l2)  # E2(2z)
E2_u2_l2 = (E2_l2 + 2 * A2_l2) / 3  # E2^[2](z)
A4_0_l2 = _QM2.gen(2)  # E4_0 = E4(2z)
A4_1_l2 = (A2_l2^2 - A4_0_l2) / 48  # \eta(2z)^16 / \eta(z)^8
E4_l2 = 5 * A2_l2^2 - 4 * A4_0_l2  # E4(z)
E6_l2 = A2_l2 * (-11 * A2_l2^2 + 12 * A4_0_l2)  # E6(z)
E6_2z_l2 = (1/2) * A2_l2 * (-A2_l2^2 + 3 * A4_0_l2)  # E6(2z)


def qm_l2_serre_derivative(qm, k=None):
    if k is None:
        k = qm.weight() - qm.depth()
    return qm.derivative() - (k / 12) * E2_l2 * qm

# Basis of quasimodular forms of level Gamma0(2), weight w, and depth <= s
def qm_l2_basis(weight, depth):
    basis = []
    for r in range(depth + 1):
        w_ = weight - 2 * r
        for i in range(w_ // 2 + 1):
            if (w_ - 2 * i) % 4 == 0:
                j = (w_ - 2 * i) // 4
                basis.append(E2_l2^r * A2_l2^i * A4_0_l2^j)
    return basis

# Dimension of the space of quasimodular forms of level Gamma0(2), weight w, and depth <= s
def dim_qm_l2(weight, depth):
    d = 0
    for r in range(depth + 1):
        # dim M_w(Gamma0(2)) = w // 4 + 1
        d += (weight - 2 * r) // 4 + 1
    return d

def is_extremal_qm_l2(qm):
    # Check if a given quasimodular form is extremal
    d = dim_qm_l2(qm.weight(), qm.depth())
    order = qm_cusp_order(qm)
    return d - 1 == order

@lru_cache(maxsize=None)
def extremal_qm_l2_d1(w):
    if w == 2:
        D_2 = (A2_l2 - E2_l2) / 48
        return D_2
    else:
        # D_{w} = (w) / (8 (w-1)^2) * ((5w-9)/12 * A2 * D_{w-2} - \partial_{w-3} D_{w-2})
        D_wm2 = extremal_qm_l2_d1(w - 2)
        res = ((5 * w - 9) / 12) * A2_l2 * D_wm2 - qm_l2_serre_derivative(D_wm2, w - 3)
        res *= w / (8 * (w - 1)^2)
        return res

def extremal_qm_l2(weight, depth):
    if depth == 1:
        extqm = extremal_qm_l2_d1(weight)
    else:
        bs = qm_l2_basis(weight, depth)
        d = len(bs)
        m = matrix([qm_coefficients(b, d) for b in bs])
        c_ = vector([0] * (d - 1) + [1])
        x_ = m.solve_left(c_)
        extqm = sum(x_[j] * bs[j] for j in range(d))
    if not is_extremal_qm_l2(extqm):
        raise ValueError("The resulting quasimodular form is not extremal")
    return extqm

def qm_double_argument(qm):
    """f(z) -> f(2z)"""
    r = _QM2(0)
    for (d2, d4, d6), coeff in qm.polynomial().dict().items():
        r += coeff * E2_2z_l2^d2 * A4_0_l2^d4 * E6_2z_l2^d6
    return r

def qm_l1_to_l2(qm):
    """Embed QM(Gamma0(1)) into QM(Gamma0(2)) by sending E2, E4, E6 to their level 2 analogs"""
    r = _QM2(0)
    for (d2, d4, d6), coeff in qm.polynomial().dict().items():
        r += coeff * E2_l2^d2 * E4_l2^d4 * E6_l2^d6
    return r


## Level Gamma0(3)

_QM3 = QuasiModularForms(Gamma0(3))
E2_l3 = _QM3.gen(0)  # E2
B2_l3 = _QM3.gen(1)  # (3E2(3z) - E2(z)) / 2
B4_0_l3 = _QM3.gen(2)  # E4_0 = E4(3z)
B6_0_l3 = _QM3.gen(3)  # E6_0 = E6(3z)
B4_1_l3 = (B2_l3^2 - B4_0_l3) / 24  # q + 9q^2 = 27q^3 + 73q^4 + ...
B6_2_l3 = (B2_l3^3 - 3 * B2_l3 * B4_0_l3 + 2 * B6_0_l3) / 432  # q^2 + 6q^3 + 27q^4 + ...

# B_4,1 ^ 2 = B_2 * B_6,2
assert B4_1_l3^2 == B2_l3 * B6_2_l3, "B_4,1^2 should be equal to B_2 * B_6,2"

def qm_l3_serre_derivative(qm, k=None):
    if k is None:
        k = qm.weight() - qm.depth()
    return qm.derivative() - (k / 12) * E2_l3 * qm

def qm_l3_basis(weight, depth):
    """
    Basis of quasimodular forms of level Gamma0(3), weight w, and depth <= s
    E2^r * B2^i * B4_1^j * B6_2^k with 2r + 2i + 4j + 6k = w
    with r \le s and j \in {0, 1}.
    """
    basis = []
    for r in range(depth + 1):
        w_ = weight - 2 * r
        for i in range(w_ // 2 + 1):
            # j = 0
            if (w_ - 2 * i) % 6 == 0:
                k = (w_ - 2 * i) // 6
                basis.append(E2_l3^r * B2_l3^i * B6_2_l3^k)
            # j = 1
            if (w_ - 2 * i - 4) % 6 == 0:
                k = (w_ - 2 * i - 4) // 6
                basis.append(E2_l3^r * B2_l3^i * B4_1_l3 * B6_2_l3^k)
    return basis

def dim_qm_l3(weight, depth):
    """
    Dimension of the space of quasimodular forms of level Gamma0(3),
    weight w, and depth <= s
    """
    d = 0
    for r in range(depth + 1):
        w_ = weight - 2 * r
        for i in range(w_ // 2 + 1):
            d += ((w_ - 2 * i) % 6 == 0) + ((w_ - 2 * i - 4) % 6 == 0)
    return d

def is_extremal_qm_l3(qm):
    # Check if a given quasimodular form is extremal
    d = dim_qm_l3(qm.weight(), qm.depth())
    order = qm_cusp_order(qm)
    return d - 1 == order

def extremal_qm_l3(weight, depth):
    bs = qm_l3_basis(weight, depth)
    d = len(bs)
    m = matrix([qm_coefficients(b, d) for b in bs])
    c_ = vector([0] * (d - 1) + [1])
    x_ = m.solve_left(c_)
    extqm = sum(x_[j] * bs[j] for j in range(d))
    if not is_extremal_qm_l3(extqm):
        raise ValueError("The resulting quasimodular form is not extremal")
    return extqm


def is_extremal_qm_unique_level(weight, depth, level=1):
    """
    Check if the extremal quasimodular form of given weight, depth, and level is unique.
    Only supported for level Gamma0(N) for N = 1, 2, 3.
    """
    if level == 1:
        if depth <= 4:
            return True
        return is_extremal_qm_unique(weight, depth)
    elif level == 2:
        if depth <= 2:
            return True
        bs = qm_l2_basis(weight, depth)
        d = len(bs)
        m = matrix([qm_coefficients(b, d) for b in bs])
        return m.is_invertible()
    elif level == 3:
        if depth <= 1:
            return True
        bs = qm_l3_basis(weight, depth)
        d = len(bs)
        m = matrix([qm_coefficients(b, d) for b in bs])
        return m.is_invertible()
    else:
        raise NotImplementedError("Only level Gamma0(N) for N = 1, 2, 3 is supported")
