import os

load(os.path.dirname(os.path.abspath(__file__)) + "/sage/utils_l1.sage")
load(os.path.dirname(os.path.abspath(__file__)) + "/sage/utils_l2_LS.sage")


r"""
Kaneko-Zagier operators.

The second- and third-order Kaneko-Zagier operators are the modular linear
differential operators

    L_{2,k}^{alpha}         = D^2 - (k+1)/6 E2 D + k(k+1)/12 E2' + alpha E4
                            = d_k^2 - (k(k+2)/144 - alpha) E4,

    L_{3,k}^{(alpha,beta)}  = D^3 - (k+2)/4 E2 D^2
                              + ((k+1)(k+2)/4 E2' + alpha E4) D
                              - (k(k+1)(k+2)/24 E2'' + k alpha/4 E4' - beta E6)
                            = d_k^3 + (alpha - (3k^2+12k+8)/144) E4 d_k
                              + (beta + k alpha/12 - k^2(k+3)/864) E6,

where D = q d/dq and d_k is the Serre derivative of weight k, and where
d_k^r abbreviates d_{k+2(r-1)} ... d_{k+2} d_k.  The two expressions of each
operator are implemented separately (`*_D` for the D-form) so that they can be
checked against each other.  We write L_{2,k} = L_{2,k}^{0} and
L_{3,k} = L_{3,k}^{(0,0)}.

Each operator comes in a level 1 flavour (`qm_*`, acting on QM) and a flavour
for the module QM2_LS = QM2[LS] of level Gamma(2) forms with a log-lambda term
(`ls_*`), used for the families G_w and Y_w.
"""


# --- Level 1 --------------------------------------------------------------

def qm_L2(k, f, alpha=0):
    """Serre-derivative form of `L_{2,k}^alpha` on a level 1 quasimodular form."""
    return qm_serre_derivative_fold(f, 2, k) - (k * (k + 2) / 144 - alpha) * E4 * f

def qm_L2_D(k, f, alpha=0):
    """`D`-form of `L_{2,k}^alpha` on a level 1 quasimodular form."""
    Df = f.derivative()
    return (Df.derivative() - (k + 1) / 6 * E2 * Df
            + k * (k + 1) / 12 * E2.derivative() * f + alpha * E4 * f)

def qm_L3(k, f, alpha=0, beta=0):
    """Serre-derivative form of `L_{3,k}^{(alpha,beta)}` on a level 1 quasimodular form."""
    return (qm_serre_derivative_fold(f, 3, k)
            + (alpha - (3 * k^2 + 12 * k + 8) / 144) * E4 * qm_serre_derivative(f, k)
            + (beta + k * alpha / 12 - k^2 * (k + 3) / 864) * E6 * f)

def qm_L3_D(k, f, alpha=0, beta=0):
    """`D`-form of `L_{3,k}^{(alpha,beta)}` on a level 1 quasimodular form."""
    Df = f.derivative()
    DDf = Df.derivative()
    DE2 = E2.derivative()
    return (DDf.derivative() - (k + 2) / 4 * E2 * DDf
            + ((k + 1) * (k + 2) / 4 * DE2 + alpha * E4) * Df
            - (k * (k + 1) * (k + 2) / 24 * DE2.derivative()
               + k * alpha / 4 * E4.derivative() - beta * E6) * f)


# --- Level Gamma(2), with a log-lambda term --------------------------------

def ls_serre_derivative_fold(f, r, k):
    """Iterated Serre derivative `d_{k+2(r-1)} ... d_{k+2} d_k` on QM2_LS."""
    assert r >= 0
    for i in range(r):
        f = ls_serre_derivative(f, k + 2 * i)
    return f

def ls_L2(k, f, alpha=0):
    """Serre-derivative form of `L_{2,k}^alpha` on QM2_LS."""
    return ls_serre_derivative_fold(f, 2, k) - (k * (k + 2) / 144 - alpha) * E4_LS * f

def ls_L2_D(k, f, alpha=0):
    """`D`-form of `L_{2,k}^alpha` on QM2_LS."""
    Df = ls_derivative(f)
    return (ls_derivative(Df) - (k + 1) / 6 * E2_LS * Df
            + k * (k + 1) / 12 * ls_derivative(E2_LS) * f + alpha * E4_LS * f)

def ls_L3(k, f, alpha=0, beta=0):
    """Serre-derivative form of `L_{3,k}^{(alpha,beta)}` on QM2_LS."""
    return (ls_serre_derivative_fold(f, 3, k)
            + (alpha - (3 * k^2 + 12 * k + 8) / 144) * E4_LS * ls_serre_derivative(f, k)
            + (beta + k * alpha / 12 - k^2 * (k + 3) / 864) * E6_LS * f)

def ls_L3_D(k, f, alpha=0, beta=0):
    """`D`-form of `L_{3,k}^{(alpha,beta)}` on QM2_LS."""
    Df = ls_derivative(f)
    DDf = ls_derivative(Df)
    DE2 = ls_derivative(E2_LS)
    return (ls_derivative(DDf) - (k + 2) / 4 * E2_LS * DDf
            + ((k + 1) * (k + 2) / 4 * DE2 + alpha * E4_LS) * Df
            - (k * (k + 1) * (k + 2) / 24 * ls_derivative(DE2)
               + k * alpha / 4 * ls_derivative(E4_LS) - beta * E6_LS) * f)


# --- Intertwining criterion ------------------------------------------------

def kz_intertwine_params(k, alpha, beta, gamma, alpha_, beta_, gamma_):
    """
    Shifted parameters `(A, B, C, A', B', C')` of the intertwining criterion.

    These are defined so that the four operators of
    `L_{3,k+4}^{(alpha,beta)} L_{2,k}^{gamma} = L_{2,k+6}^{gamma'} L_{3,k}^{(alpha',beta')}`
    take the Serre-derivative forms
    `L_{2,k}^{gamma} = d_k^2 + C E4`, `L_{3,k+4}^{(alpha,beta)} = d_{k+4}^3 + A E4 d_{k+4} + B E6`,
    `L_{2,k+6}^{gamma'} = d_{k+6}^2 + C' E4`, `L_{3,k}^{(alpha',beta')} = d_k^3 + A' E4 d_k + B' E6`.
    """
    A = alpha - (3 * k^2 + 36 * k + 104) / 144
    B = beta + (k + 4) / 12 * alpha - (k + 4)^2 * (k + 7) / 864
    C = gamma - k * (k + 2) / 144
    A_ = alpha_ - (3 * k^2 + 12 * k + 8) / 144
    B_ = beta_ + k / 12 * alpha_ - k^2 * (k + 3) / 864
    C_ = gamma_ - (k + 6) * (k + 8) / 144
    return A, B, C, A_, B_, C_

def kz_intertwine_constraints(k, alpha, beta, gamma, alpha_, beta_, gamma_):
    """
    The four constraints of the intertwining criterion, as residues.

    The intertwining relation
    `L_{3,k+4}^{(alpha,beta)} L_{2,k}^{gamma} = L_{2,k+6}^{gamma'} L_{3,k}^{(alpha',beta')}`
    holds when all four returned values vanish.
    """
    A, B, C, A_, B_, C_ = kz_intertwine_params(k, alpha, beta, gamma, alpha_, beta_, gamma_)
    return [
        (A + C) - (A_ + C_),
        (B - C) - (B_ - 2 / 3 * A_),
        C * (A + 1 / 2) - (A_ * (C_ + 1 / 6) - B_),
        C * (B - A / 3 - 1 / 9) - B_ * (C_ + 1 / 3),
    ]
