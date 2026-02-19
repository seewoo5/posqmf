import os
from functools import lru_cache

load(os.path.dirname(os.path.abspath(__file__)) + "/sage/utils_l1.sage")
load(os.path.dirname(os.path.abspath(__file__)) + "/sage/utils_l2.sage")


@lru_cache
def pos_eigenform(weight):
    # quasimiodular form for (-1)^(d/4)-eigenform of Fourier transform by Feigenbaum-Grabner-Hardin
    w = weight
    if w == 8:
        r = (E2^2 * E4 - 2 * E2 * E6 + E4^2)
        r /= 1728
    elif w == 10:
        r = - E2^2 * E6 + 2 * E2 * E4^2 - E4 * E6
        r /= 1728
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
        fw_ = pos_eigenform(w_)
        ssfw_ = qm_serre_derivative(qm_serre_derivative(fw_, w_ - 2), w_)
        r = (w_ - 5) * (w_ - 6) * E4 * fw_ - 36 * ssfw_
        r *= w_ * (w_ - 4) / (192 * (w_ + 2) * (w_ - 3) * (w_ - 5) * (w_ - 10))
        assert qm_cusp_order(r, prec=(w - 4) / 4 + 5) == (w - 4) / 4
    else:  # w % 4 == 2:
        w_ = w - 2
        fw_ = pos_eigenform(w_ - 2)
        ssfw_ = qm_serre_derivative(qm_serre_derivative(fw_, w_ - 4), w_ - 2)
        r = (w_ - 10) * (w_ - 11) * E4 * fw_ - 36 * ssfw_
        r *= (w_ - 4) * (w_ - 8) / (192 * (w_ - 5) * (w_ - 6) * (w_ - 7) * (w_ - 18))
        assert qm_cusp_order(r, prec=(w - 6) / 4 + 5) == (w - 6) / 4
    
    return r

@lru_cache
def Ftilde(w):
    # For F_w = A_{w}  + B_{w-2} E_2 + C_{w-4} E_2^2, we have
    # \tilde{F}_{w-2} = B_{w-2} + 2 C_{w-4} E_2
    F_wp2 = pos_eigenform(w + 2)
    comps = modular_comp(F_wp2)
    B_w = comps[1]
    C_wm2 = comps[2]
    return B_w + 2 * C_wm2 * E2

@lru_cache
def Gtilde(w):
    assert w % 4 == 0, "Weight must be divisible by 4"
    if w == 0:
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
