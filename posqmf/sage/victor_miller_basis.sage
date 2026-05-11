"""Victor-Miller basis for modular forms of level Gamma0(2) and Gamma0(3)"""

def l2_victor_miller_basis(weight):
    """Return the Victor-Miller basis for level Gamma0(2) at given weight."""
    assert weight % 2 == 0, "Weight must be even"
    _M2 = ModularFormsRing(Gamma0(2))
    A2 = _M2.0  # 2E2(2z) - E2(z)
    A4_0 = _M2.1  # E4(2z)
    A4_1 = (A2 ^ 2 - A4_0) / 48
    if weight % 4 == 0:
        tri_basis = [A2 ^ (weight // 2 - 2 * i) * A4_1 ^ i for i in range(weight // 4 + 1)]
    else:  # weight % 4 == 2
        tri_basis = [A2 ^ (weight // 2 - 2 * i) * A4_1 ^ i for i in range((weight - 2) // 4 + 1)]
    d = len(tri_basis)
    T = identity_matrix(QQ, d)
    for i, f in enumerate(tri_basis):
        f_qexp = f.qexp(d).list()  # can be shorter than d
        for j in range(i + 1, len(f_qexp)):
            T[i, j] = f_qexp[j]
    Tinv = T.inverse()
    vm_basis = [sum(Tinv[i, j] * tri_basis[j] for j in range(d)) for i in range(d)]
    return vm_basis

def l3_victor_miller_basis(weight):
    """Return the Victor-Miller basis for level Gamma0(3) at given weight."""
    assert weight % 2 == 0, "Weight must be even"
    _M3 = ModularFormsRing(Gamma0(3))
    B2 = _M3.0  # (3E2(3z) - E2(z)) / 2
    B4_0 = _M3.1  # E4(3z)
    B6_0 = _M3.2  # E6(3z)
    B4_1 = (B2 ^ 2 - B4_0) / 24
    B6_2 = (B2 ^ 3 - 3 * B2 * B4_0 + 2 * B6_0) / 432
    tri_basis = []
    for i in range(weight // 2 + 1):
        if (weight - 2 * i) % 6 == 0:
            k = (weight - 2 * i) // 6
            tri_basis.append(((i, 0, k), B2 ^ i * B6_2 ^ k))
        if (weight - 2 * i - 4) % 6 == 0:
            k = (weight - 2 * i - 4) // 6
            tri_basis.append(((i, 1, k), B2 ^ i * B4_1 * B6_2 ^ k))
    tri_basis.sort(key=lambda x: x[0][1] + 2 * x[0][2])
    tri_basis = [f for _, f in tri_basis]
    d = len(tri_basis)
    T = identity_matrix(QQ, d)
    for i, f in enumerate(tri_basis):
        f_qexp = f.qexp(d).list()  # can be shorter than d
        for j in range(i + 1, len(f_qexp)):
            T[i, j] = f_qexp[j]
    Tinv = T.inverse()
    vm_basis = [sum(Tinv[i, j] * tri_basis[j] for j in range(d)) for i in range(d)]
    return vm_basis
