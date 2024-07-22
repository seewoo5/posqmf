from functools import lru_cache

from sage.all import *
from .qm import E2, E4, E6, qm_cusp_order, qm_serre_derivative, qm_normalize, qm_basis, dim_qm


# Extremal quasimodular forms
def is_extremal_qm(qm):
    # Check if a given quasimodular form is extremal (in the sense of Kaneko-Koike)
    # s = qm_depth(qm)
    s = qm.depth()
    w = qm.weight()
    d = dim_qm(w, s)
    order = qm_cusp_order(qm)
    return d - 1 == order
    
@lru_cache(maxsize=None)
def _extremal_qm_d1(w):
    if w < 6:
        assert False, "weight should be >= 6"
    if w == 6:
        return (1 / 720) * (E2 * E4 - E6)
    else:
        if w % 6 == 0:
            _qm = _extremal_qm_d1(w - 6)
            res = E4 * qm_serre_derivative(_qm, w - 7) - ((w - 5) / 12) * E6 * _qm
            res *= w / (72 * (w - 5) * (w - 1))
            assert is_extremal_qm(res), "not extremal"
            return res
        elif w % 6 == 2:
            _qm = _extremal_qm_d1(w - 2)
            res = (12 / (w - 1)) * qm_serre_derivative(_qm, w - 3)
            assert is_extremal_qm(res), "not extremal"
            return res
        elif w % 6 == 4:
            _qm = _extremal_qm_d1(w - 4)
            res = E4 * _qm
            assert is_extremal_qm(res), "not extremal"
            return res
        else:
            assert False, "weight is odd"
    
@lru_cache(maxsize=None)
def _extremal_qm_d2(w):
    if w < 4:
        assert False, "weight should be >= 4"
    if w == 4:
        return (1 / 288) * (E4 - E2^2)
    elif w % 4 == 0:
        _qm = _extremal_qm_d2(w - 4)
        res = ((w - 3) * (w - 4) / 36) * E4 * _qm
        res -= qm_serre_derivative(qm_serre_derivative(_qm, w - 6), w - 4)
        res *= (3 * (w)^2) / (16 * (w - 1) * (w - 2)^2 * (w - 3))
        assert is_extremal_qm(res), "not extremal"
        return res
    elif w % 4 == 2:
        _qm = _extremal_qm_d2(w - 2)
        res = qm_serre_derivative(_qm, w - 4)
        res *= (6 / (w - 1))
        assert is_extremal_qm(res), "not extremal"
        return res
    else:
        assert False, "weight is odd"


@lru_cache(maxsize=None)
def extremal_qm(weight, depth):
    # Find the extremal qmf (if exists) for given weight and depth
    # The result is normalized so that first nonzero coefficient is 1
    assert (0 <= depth <= weight/2 and 2 * (depth + 1) != weight), "inappropriate weight and depths"
    
    if depth == 1:
        return _extremal_qm_d1(weight)
    if depth == 2:
        return _extremal_qm_d2(weight)

    # For depth >= 3, find it naively.
    # Existence or uniqueness is not guaranteed for depth >= 5.
    bs = qm_basis(weight, depth)
    d = dim_qm(weight, depth)
    m = matrix([coefficients(qm_, d) for qm_ in bs])
    c_ = vector([0] * (d - 1) + [1])
    x_ = m.solve_left(c_)
      
    ans = sum(x_[j] * bs[j] for j in range(d))
    return qm_normalize(ans)
