import os

load(os.path.dirname(os.path.abspath(__file__)) + "/sage/utils_l1.sage")
load(os.path.dirname(os.path.abspath(__file__)) + "/sage/utils_l2.sage")

# Level SL_2(Z)
# The following line is needed to fix a bug that `QM` is not belong to a commutative rings,
# see https://ask.sagemath.org/question/76909/ring-of-quasimodular-forms-as-a-commutative-ring/ and https://github.com/sagemath/sage/pull/37797
QM._refine_category_(QM.category().Commutative())  
RQM.<ip, ioz> = QM['ip','ioz']  # `ip` = 1 / pi, `ioz` = i / z


# Weight
def rqm_weight(rqm):
    w = 0
    for (dip, dioz), qm in rqm.dict().items():
        w = max(w, qm.weight() + dip + dioz)
    return w

def is_rqm_homogeneous(rqm):
    w = None
    for (dip, dioz), qm in rqm.dict().items():
        w_ = qm.weight() + dip + dioz
        if w is None:
            w = w_
        else:
            if w != w_:
                return False
    return True

# Depth
def rqm_depth(rqm):
    dp = 0
    for qm in rqm.dict().values():
        dp = max(dp, qm_depth(qm))
    return dp

def rqm_derivative(rqm):
    r = 0
    for (dip, dioz), qm in rqm.dict().items():
        r += qm.derivative() * ip^dip * ioz^dioz
        if dioz >= 1:
            r += qm * ip^dip * dioz * ioz^(dioz - 1) * ((1/2) * ip * ioz^2)
    return r

# Iterative differentiation of quasimodular forms
def rqm_derivative_fold(rqm, k):
    if k == 0:
        return rqm
    else:
        return rqm_derivative_fold(rqm_derivative(rqm), k - 1)

# Serre derivative with given weight k
# If weight is not given, we use k = (weight - depth) that preserves depth.
def rqm_serre_derivative(rqm, k=None):
    if k is None:
        k = rqm_weight(rqm) - rqm_depth(rqm)
    return rqm_derivative(rqm) - E2 * rqm * (k / 12)

# Iterative Serre derivative, which is 
# \partial_{k + 2(r-1)} \circ \partial_{k + 2(r-2)} \circ \cdots \circ \partial_{k} for given r >= 1.
def rqm_serre_derivative_fold(rqm, r, k=None):
    assert r >= 0
    if r == 0:
        return rqm
    elif r == 1:
        return rqm_serre_derivative(rqm, k)
    else:
        if k is None:
            k = rqm_weight(rqm) - rqm_depth(rqm)
        return rqm_serre_derivative(rqm_serre_derivative_fold(rqm, r-1, k), k + 2 * (r-1))

# Print its polynomial form, weight, and depth.
def print_rqm(rqm, name):
    print(name)
    poly_str = ""
    for (dip, dioz), qm in rqm.dict().items():
        if poly_str != "":
            poly_str += " + "
        if dip == 0:
            ip_str = ""
        elif dip == 1:
            ip_str = "*(1/π)"
        else:  # dip >= 2
            ip_str = "*(1/π)^" + str(dip)
        if dioz == 0:
            ioz_str = ""
        elif dioz == 1:
            ioz_str = "*(i/z)"
        else:  # dioz >= 2
            ioz_str = "*(i/z)^" + str(dioz)
        poly_str += "(" + str(qm.polynomial()) + ")" + ip_str + ioz_str
    print("polynomial", poly_str)
    print("weight", rqm_weight(rqm))
    print("depth", rqm_depth(rqm))
    print()

def rqm_to_func(rqm, prec=100):
    f = 0
    for (dip, dioz), qm in rqm.dict().items():
        f += (1/pi)^dip * (1/t)^dioz * qm_to_func(qm, prec=prec)
    return f


# Level \Gamma(2)
RQM2.<ip_, ioz_> = QM2['ip','ioz']  # `ip` = 1 / pi, `ioz` = i / z


# Weight
def rqm2_weight(rqm):
    w = 0
    for (dip, dioz), qm in rqm.dict().items():
        w = max(w, qm2_weight(qm) + dip + dioz)
    return w

def is_rqm2_homogeneous(rqm):
    w = None
    for (dip, dioz), qm in rqm.dict().items():
        w_ = qm2_weight(qm) + dip + dioz
        if w is None:
            w = w_
        else:
            if w != w_:
                return False
    return True

# Depth
def rqm2_depth(rqm):
    dp = 0
    for qm in rqm.dict().values():
        dp = max(dp, qm2_depth(qm))
    return dp

def rqm2_derivative(rqm):
    r = 0
    for (dip, dioz), qm in rqm.dict().items():
        r += qm2_derivative(qm) * ip_^dip * ioz_^dioz
        if dioz >= 1:
            r += qm * ip_^dip * dioz * ioz_^(dioz - 1) * ((1/2) * ip_ * ioz_^2)
    return r

# Iterative differentiation of quasimodular forms
def rqm2_derivative_fold(rqm, k):
    if k == 0:
        return rqm
    else:
        return rqm2_derivative_fold(rqm2_derivative(rqm), k - 1)

# Serre derivative with given weight k
# If weight is not given, we use k = (weight - depth) that preserves depth.
def rqm2_serre_derivative(rqm, k=None):
    if k is None:
        k = rqm2_weight(rqm) - rqm2_depth(rqm)
    return rqm2_derivative(rqm) - E2_ * rqm * (k / 12)

# Iterative Serre derivative, which is 
# \partial_{k + 2(r-1)} \circ \partial_{k + 2(r-2)} \circ \cdots \circ \partial_{k} for given r >= 1.
def rqm2_serre_derivative_fold(rqm, r, k=None):
    assert r >= 0
    if r == 0:
        return rqm
    elif r == 1:
        return rqm2_serre_derivative(rqm, k)
    else:
        if k is None:
            k = rqm2_weight(rqm) - rqm2_depth(rqm)
        return rqm2_serre_derivative(rqm2_serre_derivative_fold(rqm, r-1, k), k + 2 * (r-1))

# Print its polynomial form, weight, and depth.
def print_rqm2(rqm, name):
    print(name)
    poly_str = ""
    for (dip, dioz), qm in rqm.dict().items():
        if poly_str != "":
            poly_str += " + "
        if dip == 0:
            ip_str = ""
        elif dip == 1:
            ip_str = "*(1/π)"
        else:  # dip >= 2
            ip_str = "*(1/π)^" + str(dip)
        if dioz == 0:
            ioz_str = ""
        elif dioz == 1:
            ioz_str = "*(i/z)"
        else:  # dioz >= 2
            ioz_str = "*(i/z)^" + str(dioz)
        poly_str += "(" + str(qm) + ")" + ip_str + ioz_str
    print("polynomial", poly_str)
    print("weight", rqm2_weight(rqm))
    print("depth", rqm2_depth(rqm))
    print()

def rqm2_to_func(rqm, prec=100):
    f = 0
    for (dip, dioz), qm in rqm.dict().items():
        f += (1/pi)^dip * (1/t)^dioz * qm2_to_func(qm, prec=prec)
    return f


# S-action. If the input is a purely quasimodular form without rational terms, then the result is homogeneous (in weights).
# Otherwise, the result may not be homogeneous

# Level SL_2(Z)
E2S = E2 - 6 * ip * ioz
E4S = E4
E6S = E6

# For quasimodular forms
def qm_S_action(qm):
    r = 0
    for (d2, d4, d6), coeff in qm.polynomial().dict().items():
        r += coeff * E2S^d2 * E4S^d4 * E6S^d6
    return r

# For homogeneous inputs with rational terms
# For each monomial term rqm = qm * (1/π)^a * (i/z)^b, we get
# rqm|_w,S = qm|_{w-a-b},S * (1/π)^a * (z/i)^b * z^(-a-b) = (-1)^((a + b)/2) * qm|_{w-a-b},S * (1/π)^a * (i/z)^a
def rqm_S_action(rqm):
    r = 0
    assert is_rqm_homogeneous(rqm), "Input is not homogeneous."
    for (dip, dioz), qm in rqm.dict().items():
        r += (-1)^((dip + dioz)/2) * qm_S_action(qm) * ip^dip * ioz^dip
    return r

# Level Gamma(2)
H2S = -H4
H4S = -H2
E2S_ = E2_ - 6 * ip_ * ioz_

# For quasimodular forms
def qm2_S_action(qm):
    r = 0
    for (dh2, dh4, de2), coeff in qm.dict().items():
        r += coeff * H2S^dh2 * H4S^dh4 * E2S_^de2
    return r

# For homogeneous inputs with rational terms
# For each monomial term rqm = qm * (1/π)^a * (i/z)^b, we get
# rqm|_w,S = qm|_{w-a-b},S * (1/π)^a * (-iz)^b * z^(-a-b) = (-1)^b * qm|_{w-a-b},S * (1/π)^a * (i/z)^a
def rqm2_S_action(rqm):
    r = 0
    assert is_rqm2_homogeneous(rqm), "Input is not homogeneous."
    for (dip, dioz), qm in rqm.dict().items():
        r += (-1)^((dip + dioz)/2) * qm2_S_action(qm) * ip_^dip * ioz_^dip
    return r

# Extract each of homogeneous components
def rqm_homogeneous_comps(rqm):
    r = dict()
    for (dip, dioz), qm in rqm.dict().items():
        qm_comps = qm.homogeneous_components()
        for w_, qm_ in qm_comps.items():
            w = w_ + dip + dioz
            if w not in r:
                r[w] = qm_ * ip^dip * ioz^dioz
            else:
                r[w] += qm_ * ip^dip * ioz^dioz
    return r

def qm2_homogeneous_comps(qm):
    r = dict()
    for (dh2, dh4, de2), coeff in qm.dict().items():
        w = 2 * (dh2 + dh4 + de2)
        if w not in r:
            r[w] = coeff * H2^dh2 * H4^dh4 * E2_^de2
        else:
            r[w] += coeff * H2^dh2 * H4^dh4 * E2_^de2
    return r

def rqm2_homogeneous_comps(rqm):
    r = dict()
    for (dip, dioz), qm in rqm.dict().items():
        qm_comps = qm2_homogeneous_comps(qm)
        for w_, qm_ in qm_comps.items():
            w = w_ + dip + dioz
            if w not in r:
                r[w] = qm_ * ip_^dip * ioz_^dioz
            else:
                r[w] += qm_ * ip_^dip * ioz_^dioz
    return r

# embed RQM \to RQM2
def rqm_to_rqm2(rqm):
    r = 0
    for (dip, dioz), qm in rqm.dict().items():
        r += l1_to_l2(qm) * ip_^dip * ioz_^dioz
    return r
