import os
from functools import lru_cache

load(os.path.dirname(os.path.abspath(__file__)) + "/sage/utils_l1.sage")
load(os.path.dirname(os.path.abspath(__file__)) + "/sage/utils_l2.sage")
load(os.path.dirname(os.path.abspath(__file__)) + "/sage/utils_l2_LS.sage")


@lru_cache
def F(w):
    """FGH quasimodular form for the (-1)^(d/4)-eigenform family."""
    if w == 8:
        r = (E2^2 * E4 - 2 * E2 * E6 + E4^2) / 1728
    elif w == 10:
        r = (- E2^2 * E6 + 2 * E2 * E4^2 - E4 * E6) / 1728
    elif w == 12:
        r = (1 / 6000) * (E2 * E4 - E6)^2
        r /= 1728
        r *= 20
    elif w == 14:
        r = -(E2^2 * E4 * E6 - E2 * (E4^3 + E6^2) + E4^2 * E6)
        r /= 8400
        r /= 1728
        r *= 20
    elif w == 16:
        r = (1 / 2540160000) * (49 * E2^2 * E4^3 - 25 * E2^2 * E6^2 - 48 * E2 * E4^2 * E6 - 25 * E4^4 + 49 * E4 * E6^2)
        r /= 1728
        r *= 1200
    elif w == 18:
        r = (12 * E2^2 * E4^2 * E6 - E2 * (5 * E4^4 + 19 * E4 * E6^2) + 5 * E4^3 * E6 + 7 * E6^3)
        r /= -1995840000
        r /= 1728
        r *= 1200
    elif w % 4 == 0:
        w_ = w - 4
        fw_ = F(w_)
        ssfw_ = qm_serre_derivative(qm_serre_derivative(fw_, w_ - 2), w_)
        r = (w_ - 5) * (w_ - 6) * E4 * fw_ - 36 * ssfw_
        r *= w_ * (w_ - 4) / (192 * (w_ + 2) * (w_ - 3) * (w_ - 5) * (w_ - 10))
        assert qm_cusp_order(r, prec=(w - 4) / 4 + 5) == (w - 4) / 4
    else:  # w % 4 == 2:
        w_ = w - 2
        fw_ = F(w_ - 2)
        ssfw_ = qm_serre_derivative(qm_serre_derivative(fw_, w_ - 4), w_ - 2)
        r = (w_ - 10) * (w_ - 11) * E4 * fw_ - 36 * ssfw_
        r *= (w_ - 4) * (w_ - 8) / (192 * (w_ - 5) * (w_ - 6) * (w_ - 7) * (w_ - 18))
        assert qm_cusp_order(r, prec=(w - 6) / 4 + 5) == (w - 6) / 4
    
    return r

@lru_cache
def Ftilde(w):
    r"""
    Extract \tilde{F}_w from F_{w+2}.

    If F_{w+2} = A_{w+2} + B_w E_2 + C_{w-2} E_2^2, then
    \tilde{F}_w = B_w + 2 C_{w-2} E_2.
    """
    F_wp2 = F(w + 2)
    comps = modular_comp(F_wp2)
    B_w = comps[1]
    C_wm2 = comps[2]
    return B_w + 2 * C_wm2 * E2

@lru_cache
def G(w):
    """FGH quasimodular form for the (-1)^(d/4+1)-eigenform family."""
    assert w % 2 == 0 and w >= 4, "Weight must be even and >= 4"
    if w == 4:
        r = (H2 / 2^5) * (H2 + 2 * H4)
    elif w == 6:
        r = (H2 / 2^4) * (H2^2 + H2 * H4 + H4^2)
    elif w == 8:
        r = (H2^3 / 2^13) * (H2 + 2 * H4)
    elif w == 10:
        r = (H2^3 / (2^12 * 5)) * (2 * H2^2 + 5 * H2 * H4 + 5 * H4^2)
    elif w == 12:
        r = (3 * Disc_ * LS) / (2^11 * 7)
        r += (3 * H2^3 / (2^20 * 7)) * (H2^3 + 3 * H2^2 * H4 + 3 * H2 * H4^2 + 2 * H4^3)
    elif w == 14:
        r = (H2^5 / (2^20 * 7)) * (2 * H2^2 + 7 * H2 * H4 + 7 * H4^2)
    elif w == 16:
        r = (5 * E4_ * Disc_ * LS) / (2^18 * 11)
        r += (5 * H2^3 / (2^29 * 3 * 11)) * (5 * H2^5 + 20 * H2^4 * H4 + 42 * H2^3 * H4^2 + 68 * H2^2 * H4^3 + 60 * H2 * H4^4 + 24 * H4^5)
    elif w == 18:
        r = -(5 * E6_ * Disc_ * LS) / (2^17 * 11 * 13)
        r += (5 * H2^3 / (2^27 * 3 * 11 * 13)) * (10 * H2^6 + 45 * H2^5 * H4 + 68 * H2^4 * H4^2 + 34 * H2^3 * H4^3 - 13 * H2^2 * H4^4 - 36 * H2 * H4^5 - 12 * H4^6)
    elif w % 4 == 2:
        # Use: G_{u+2} from G_{u-2}, where u = w - 2 and u ≡ 0 (mod 4)
        u = w - 2
        Gum2 = G(u - 2)
        ss = ls_serre_derivative(ls_serre_derivative(Gum2, u - 2), u)
        r = ((u - 9) * (u - 8) / 36) * E4_ * Gum2 - ss
        r *= 3 * (u - 6) * (u - 2) / (16 * (u - 16) * (u - 5) * (u - 4) * (u - 3))
    else:  # w % 4 == 0
        # Use: G_{u+4} from G_u, where u = w - 4 and u ≡ 0 (mod 4)
        u = w - 4
        Gu = G(u)
        ss = ls_serre_derivative(ls_serre_derivative(Gu, u), u + 2)
        r = ((u - 4) * (u - 3) / 36) * E4_ * Gu - ss
        r *= 3 * (u - 2) * (u + 2) / (16 * (u - 8) * (u - 3) * (u - 1) * (u + 4))
    return QM2_LS(r)

@lru_cache
def Gtilde(w):
    assert w % 4 == 0, "Weight must be divisible by 4"
    if w < 0:
        return QM(0)
    elif w == 0:
        return QM(3 / (2^11 * 7))
    elif w == 4:
        return (5 / 2^18 / 11) * E4
    else:
        w_ = w - 4
        Gw_ = Gtilde(w_)
        ssGw_ = qm_serre_derivative(qm_serre_derivative(Gw_, w_), w_ + 2)
        r = ((w_ + 8) * (w_ + 9) / 36) * E4 * Gw_ - ssGw_
        r *= 3 * (w_ + 10) * (w_ + 14) / (16 * (w_ + 4) * (w_ + 9) * (w_ + 11) * (w_ + 16))
        return r

@lru_cache
def Y(w):
    r"""
    Family Y_w in QM2_LS with explicit initial values and recurrences:
      Y_{w+4} from Y_w for w >= 8, w == 0 (mod 4),
      Y_{w+2} from Y_w for w >= 8, w == 0 (mod 4).
    """
    assert w % 2 == 0 and w >= 2, "Weight must be even and >= 2"

    if w == 2:
        r = H2 / 2^4
    elif w == 4:
        r = -(3 * E4_ * LS) / (2^11 * 5)
        r -= (3 / (2^12 * 5)) * (H2^2 + 2 * H2 * H4)
    elif w == 6:
        r = 0
    elif w == 8:
        r = -(5 * E4_^2 * LS) / (2^19 * 7)
        r -= (5 / (2^21 * 3 * 7)) * (11 * H2^4 + 28 * H2^3 * H4 + 18 * H2^2 * H4^2 + 12 * H2 * H4^3)
    elif w % 4 == 0:
        # Use Y_{u+4} from Y_u, where u = w - 4 and u == 0 (mod 4), u >= 8.
        u = w - 4
        Yu = Y(u)
        ss = ls_serre_derivative(ls_serre_derivative(Yu, u), u + 2)
        r = ((u + 2) * (u + 3) / 36) * E4_ * Yu - ss
        r *= 3 * (u + 6)^2 / (16 * (u + 3) * (u + 4)^2 * (u + 5))
    else:
        # Use Y_{u+2} from Y_u, where u = w - 2 and u == 0 (mod 4), u >= 8.
        u = w - 2
        Yu = Y(u)
        r = (6 / (u + 3)) * ls_serre_derivative(Yu, u)

    return QM2_LS(r)
