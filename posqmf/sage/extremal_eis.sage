def cusp_dim(weight):
    """
    Dimension of the space of cusp forms of given weight and level 1.
    """
    if weight % 12 == 2:
        return weight // 12 - 1
    else:
        return weight // 12

def extremal_eisenstein_series(weight):
    """
    Compute extremal Eisenstein series of given weight, i.e. a modular form of weight $w$ with $q$-expansion
    $1 + O(q^{l})$ where $l$ is the dimension of the space of modular forms of weight $w$.
    """
    assert weight % 2 == 0 and weight >= 4, "Weight must be even and >= 4"
    w = weight
    basis = ModularForms(weight=weight).basis()
    # The last basis element is the Eisenstein series, and the rest are Victor-Miller basis.
    l = len(basis)
    cs = []
    for n in range(1, l):
        coeff = (2 * w) / bernoulli(w) * sigma(n, w - 1)
        cs.append(coeff)
    r = sum(c * b for (c, b) in zip(cs, basis[:-1]))
    r += basis[-1]
    return r

def jenkins_rouse_coeff_threshold(weight):
    """
    Coefficient threshold for extremal Eisenstein series of given weight due to Jenkins and Rouse.
    If n >= thres, then a_n > 0, where a_n is the n-th Fourier coefficient
    of the extremal Eisenstein series of given weight.
    Note that there are some minor errors in the original paper, and we use the corrected version
    here with slightly larger constant.
    """
    assert weight % 2 == 0 and weight >= 16, "Weight must be even >= 16"
    if weight % 12 == 2:
        cusp_dim = weight // 12 - 1
    else:
        cusp_dim = weight // 12
    thres = exp(59.169 / (weight - 2))
    thres *= (cusp_dim ^ 3 * log(weight)) ^ (1 / (weight - 2))
    thres *= 1.0242382 * cusp_dim
    return float(thres)

def check_extremal_eisenstein_series_completely_positive(weight):
    """
    Check if the Fourier coefficients of the extremal Eisenstein series of given weight have desired signs
    (positive for weight 0 mod 4, negative for weight 2 mod 4) using Jenkins-Rouse coefficient threshold.
    """
    assert weight % 2 == 0 and weight >= 16, "Weight must be even >= 16."
    E = extremal_eisenstein_series(weight)
    n_min = cusp_dim(weight) + 1
    n_max = int(jenkins_rouse_coeff_threshold(weight))
    E_coeffs = E.coefficients(list(range(n_min, n_max + 1)))
    sgn = (-1) ^ (weight // 2)
    for i, c in enumerate(E_coeffs, start=n_min):
        if sgn * c < 0:
            if weight % 4 == 0:
                print(f"Coefficient a_{i} is negative: {c}")
            else:
                print(f"Coefficient a_{i} is positive: {c}")
            return False
    return True
