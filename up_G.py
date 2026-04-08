import argparse

from fractions import Fraction
from functools import lru_cache
from math import lcm

import flint
flint.ctx.cap = 100000  # max power series precision (must exceed largest prec used)
from sympy import symbols, QQ, Poly

r"""
Level 1 quasimodular forms in E2, E4, E6.

Same polynomial dict representation as up.py, but q-expansion uses
python-flint's fmpz_series (FLINT compiled C library) for power series
arithmetic instead of pure-Python integer lists.
"""
E2, E4, E6 = symbols('E2 E4 E6')
A2, A4 = symbols('A2 A4')
q = symbols('q')

# ============================================================================
# Polynomial dict representation: {(e2, e4, e6): Fraction}
# (Identical to up.py)
# ============================================================================

_F = Fraction

_R1_12 = _F(1, 12)
_R1_3 = _F(1, 3)
_R1_2 = _F(1, 2)
_ZERO = _F(0)


def _padd(a, b):
    """Add two polynomial dicts."""
    r = dict(a)
    for k, v in b.items():
        s = r.get(k, _ZERO) + v
        if s:
            r[k] = s
        elif k in r:
            del r[k]
    return r


def _psub(a, b):
    """Subtract two polynomial dicts."""
    r = dict(a)
    for k, v in b.items():
        s = r.get(k, _ZERO) - v
        if s:
            r[k] = s
        elif k in r:
            del r[k]
    return r


def _pscale(p, c):
    """Multiply polynomial by scalar Fraction."""
    if not c:
        return {}
    return {k: v * c for k, v in p.items()}


def _pmul(a, b):
    """Multiply two polynomial dicts."""
    r = {}
    for k1, c1 in a.items():
        for k2, c2 in b.items():
            k = (k1[0]+k2[0], k1[1]+k2[1], k1[2]+k2[2])
            s = r.get(k, _ZERO) + c1 * c2
            if s:
                r[k] = s
            elif k in r:
                del r[k]
    return r


def _pmulvar(p, idx):
    """Multiply by E2 (idx=0), E4 (idx=1), or E6 (idx=2)."""
    r = {}
    for (e2, e4, e6), v in p.items():
        if idx == 0:
            nk = (e2+1, e4, e6)
        elif idx == 1:
            nk = (e2, e4+1, e6)
        else:
            nk = (e2, e4, e6+1)
        r[nk] = v
    return r


# Base forms as dicts
_cE2 = {(1, 0, 0): _F(1)}
_cE4 = {(0, 1, 0): _F(1)}
_cE6 = {(0, 0, 1): _F(1)}


def derivative(f):
    """Compute derivative D on polynomial dict representation.
    D(E2) = (E2^2 - E4)/12
    D(E4) = (E2*E4 - E6)/3
    D(E6) = (E2*E6 - E4^2)/2
    """
    df = {}
    for (d2, d4, d6), coeff in f.items():
        if d2 > 0:
            c = coeff * d2
            k = (d2+1, d4, d6)
            df[k] = df.get(k, _ZERO) + c * _R1_12
            k = (d2-1, d4+1, d6)
            df[k] = df.get(k, _ZERO) - c * _R1_12
        if d4 > 0:
            c = coeff * d4
            k = (d2+1, d4, d6)
            df[k] = df.get(k, _ZERO) + c * _R1_3
            k = (d2, d4-1, d6+1)
            df[k] = df.get(k, _ZERO) - c * _R1_3
        if d6 > 0:
            c = coeff * d6
            k = (d2+1, d4, d6)
            df[k] = df.get(k, _ZERO) + c * _R1_2
            k = (d2, d4+2, d6-1)
            df[k] = df.get(k, _ZERO) - c * _R1_2
    return {k: v for k, v in df.items() if v}


def serre_derivative(f, k):
    """Serre derivative: D_k(f) = D(f) - k/12 * E2 * f"""
    return _psub(derivative(f), _pscale(_pmulvar(f, 0), _F(k, 12)))


def to_sympy(f):
    """Convert polynomial dict -> SymPy expression."""
    if not f:
        return 0
    terms = []
    for (e2, e4, e6), c in f.items():
        term = QQ(c.numerator, c.denominator)
        if e2:
            term *= E2**e2
        if e4:
            term *= E4**e4
        if e6:
            term *= E6**e6
        terms.append(term)
    return sum(terms)


def from_sympy(expr):
    """Convert SymPy expression -> polynomial dict."""
    p = Poly(expr, E2, E4, E6)
    result = {}
    for k, v in p.as_dict().items():
        result[k] = _F(int(v.p), int(v.q)) if hasattr(v, 'p') else _F(int(v))
    return result


def are_same(f, g):
    """Check if two polynomial dicts are equal."""
    return f == g


# ============================================================================
# q-expansion via FLINT fmpz_series (truncated integer power series)
# E2, E4, E6 have integer q-coefficients, so all their powers do too.
# We only convert to Fraction at the final weighted summation.
# ============================================================================

def _sigma_sieve(k, N):
    """Compute sigma_k(n) for n = 0, 1, ..., N using a sieve.
    Returns a list s where s[n] = sum_{d | n} d^k for n >= 1, s[0] = 0.
    """
    s = [0] * (N + 1)
    for d in range(1, N + 1):
        dk = d ** k
        for m in range(d, N + 1, d):
            s[m] += dk
    return s


@lru_cache(maxsize=32)
def _qexp_e2(prec):
    """E2(z) = 1 - 24 sum_{n>=1} sigma_1(n) q^n. Returns fmpz_series."""
    sig = _sigma_sieve(1, prec)
    c = [0] * (prec + 1)
    c[0] = 1
    for n in range(1, prec + 1):
        c[n] = -24 * sig[n]
    return flint.fmpz_series(c, prec=prec + 1)


@lru_cache(maxsize=32)
def _qexp_e4(prec):
    """E4(z) = 1 + 240 sum_{n>=1} sigma_3(n) q^n. Returns fmpz_series."""
    sig = _sigma_sieve(3, prec)
    c = [0] * (prec + 1)
    c[0] = 1
    for n in range(1, prec + 1):
        c[n] = 240 * sig[n]
    return flint.fmpz_series(c, prec=prec + 1)


@lru_cache(maxsize=32)
def _qexp_e6(prec):
    """E6(z) = 1 - 504 sum_{n>=1} sigma_5(n) q^n. Returns fmpz_series."""
    sig = _sigma_sieve(5, prec)
    c = [0] * (prec + 1)
    c[0] = 1
    for n in range(1, prec + 1):
        c[n] = -504 * sig[n]
    return flint.fmpz_series(c, prec=prec + 1)


_power_cache = {}  # (idx, exp) -> (prec, fmpz_series)


def _eisenstein_power(idx, exp, prec):
    """Cached computation of E_k^exp as fmpz_series truncated to prec+1 terms.
    idx: 0=E2, 1=E4, 2=E6.
    """
    sz = prec + 1
    key = (idx, exp)
    cached = _power_cache.get(key)
    if cached is not None:
        cached_prec, cached_series = cached
        if cached_prec >= prec:
            return cached_series

    if exp == 0:
        result = flint.fmpz_series([1], prec=sz)
    elif exp == 1:
        base_fn = (_qexp_e2, _qexp_e4, _qexp_e6)[idx]
        result = base_fn(prec)
    else:
        prev = _eisenstein_power(idx, exp - 1, prec)
        base_fn = (_qexp_e2, _qexp_e4, _qexp_e6)[idx]
        base = base_fn(prec)
        # FLINT truncated multiply: both series have prec=sz, product is truncated to sz
        result = prev * base

    _power_cache[key] = (prec, result)
    return result


def _eval_qexp(f, prec):
    """Evaluate polynomial dict at q-expansions of E2, E4, E6.
    Returns list [a_0, a_1, ..., a_prec] of Fraction coefficients.

    Uses FLINT fmpz_series for all power series arithmetic.
    Only the final weighted sum converts to Fraction.
    """
    if not f:
        return [_ZERO] * (prec + 1)

    sz = prec + 1

    me2 = max(k[0] for k in f)
    me4 = max(k[1] for k in f)
    me6 = max(k[2] for k in f)

    # Fetch cached FLINT power series
    e2p = [_eisenstein_power(0, i, prec) for i in range(me2 + 1)]
    e4p = [_eisenstein_power(1, i, prec) for i in range(me4 + 1)]
    e6p = [_eisenstein_power(2, i, prec) for i in range(me6 + 1)]

    # Compute LCD of all coefficient denominators so we can accumulate as ints.
    lcd = 1
    for coeff in f.values():
        lcd = lcm(lcd, coeff.denominator)

    # Group by (de4, de6) to reuse e4p*e6p products across de2 values.
    groups = {}
    for (de2, de4, de6), coeff in f.items():
        key46 = (de4, de6)
        if key46 not in groups:
            groups[key46] = []
        scaled_num = coeff.numerator * (lcd // coeff.denominator)
        groups[key46].append((de2, scaled_num))

    # Accumulate as a single fmpz_series (scaled by lcd).
    result_series = flint.fmpz_series([0], prec=sz)
    for (de4, de6), terms in groups.items():
        if de4 == 0:
            t46 = e6p[de6]
        elif de6 == 0:
            t46 = e4p[de4]
        else:
            t46 = e4p[de4] * e6p[de6]
        for de2, snum in terms:
            t = t46 if de2 == 0 else e2p[de2] * t46
            result_series += t * snum

    # Extract coefficients and convert to Fraction.
    raw = result_series.coeffs()
    result = [_ZERO] * sz
    for i in range(min(len(raw), sz)):
        result[i] = _F(int(raw[i]), lcd)
    return result


def q_exp(f, prec=10):
    """Compute q-expansion up to O(q^{prec+1}). f is a polynomial dict."""
    coeffs = _eval_qexp(f, prec)
    terms = []
    for i, c in enumerate(coeffs):
        if c:
            terms.append(QQ(c.numerator, c.denominator) * q**i)
    return Poly(sum(terms) if terms else 0, q)


def cusp_order(f, prec=10):
    """Find order of vanishing at the cusp (smallest n with a_n != 0)."""
    coeffs = _eval_qexp(f, prec)
    for i, c in enumerate(coeffs):
        if c:
            return i
    raise ValueError("Try to increase prec.")


def modular_comp(f):
    """Extract modular form components of a given quasimodular form.
    If F = f_0 + f_1 E2 + f_2 E2^2 + ... + f_n E2^n,
    return {0: f_0, 1: f_1, 2: f_2, ..., n: f_n}
    where each f_i is a polynomial dict in E4, E6 (with e2 exponent always 0).
    """
    result = {}
    for (d2, d4, d6), c in f.items():
        if d2 not in result:
            result[d2] = {}
        k = (0, d4, d6)
        result[d2][k] = result[d2].get(k, _ZERO) + c
    return result


@lru_cache(maxsize=None)
def pos_eigenform(weight):
    # quasimodular form for (-1)^(d/4)-eigenform of Fourier transform by Feigenbaum-Grabner-Hardin
    w = weight
    if w == 8:
        r = {(2, 1, 0): _F(1, 1728), (1, 0, 1): _F(-2, 1728), (0, 2, 0): _F(1, 1728)}
    elif w == 10:
        r = {(2, 0, 1): _F(-1, 1728), (1, 2, 0): _F(2, 1728), (0, 1, 1): _F(-1, 1728)}
    elif w == 12:
        c = _F(1, 518400)
        r = {(2, 2, 0): c, (1, 1, 1): -2 * c, (0, 0, 2): c}
    elif w == 14:
        c = _F(-1, 725760)
        r = {(2, 1, 1): c, (1, 3, 0): -c, (1, 0, 2): -c, (0, 2, 1): c}
    elif w == 16:
        d = _F(1, 3657830400)
        r = {
            (2, 3, 0): 49 * d, (2, 0, 2): -25 * d,
            (1, 2, 1): -48 * d,
            (0, 4, 0): -25 * d, (0, 1, 2): 49 * d,
        }
    elif w == 18:
        d = _F(1, -2880806400)
        r = {
            (2, 2, 1): 12 * d,
            (1, 4, 0): -5 * d, (1, 1, 2): -19 * d,
            (0, 3, 1): 5 * d, (0, 0, 3): 7 * d,
        }
    elif w % 4 == 0:
        w_ = w - 4
        fw_ = pos_eigenform(w_)
        ssfw_ = serre_derivative(serre_derivative(fw_, w_ - 2), w_)
        r = _psub(
            _pscale(_pmulvar(fw_, 1), _F((w_ - 5) * (w_ - 6))),
            _pscale(ssfw_, _F(36)),
        )
        r = _pscale(r, _F(w_ * (w_ - 4), 192 * (w_ + 2) * (w_ - 3) * (w_ - 5) * (w_ - 10)))
        assert cusp_order(r, prec=(w - 4) // 4 + 5) == (w - 4) // 4
    else:  # w % 4 == 2:
        w_ = w - 2
        fw_ = pos_eigenform(w_ - 2)
        ssfw_ = serre_derivative(serre_derivative(fw_, w_ - 4), w_ - 2)
        r = _psub(
            _pscale(_pmulvar(fw_, 1), _F((w_ - 10) * (w_ - 11))),
            _pscale(ssfw_, _F(36)),
        )
        r = _pscale(r, _F((w_ - 4) * (w_ - 8), 192 * (w_ - 5) * (w_ - 6) * (w_ - 7) * (w_ - 18)))
        assert cusp_order(r, prec=(w - 6) // 4 + 5) == (w - 6) // 4

    return r



def Ftilde(w):
    F_wp2 = pos_eigenform(w + 2)
    comps = modular_comp(F_wp2)
    B_w = comps.get(1, {})
    C_wm2 = comps.get(2, {})
    return _padd(B_w, _pscale(_pmulvar(C_wm2, 0), _F(2)))


@lru_cache(maxsize=None)
def Gtilde(w):
    assert w % 4 == 0, "Weight must be divisible by 4"
    if w < 0:
        return {(0, 0, 0): _ZERO}
    if w == 0:
        return {(0, 0, 0): _F(3, 14336)}
    elif w == 4:
        return {(0, 1, 0): _F(5, 2883584)}
    else:
        w_ = w - 4
        Gw_ = Gtilde(w_)
        ssGw_ = serre_derivative(serre_derivative(Gw_, w_), w_ + 2)
        r = _psub(
            _pscale(_pmulvar(Gw_, 1), _F((w_ + 8) * (w_ + 9), 36)),
            ssGw_,
        )
        r = _pscale(r, _F(3 * (w_ + 10) * (w_ + 14),
                          16 * (w_ + 4) * (w_ + 9) * (w_ + 11) * (w_ + 16)))
        return r


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-w", type=int, help="maximum weight to be tested", default=100)
    parser.add_argument("--log", type=str, help="path to log outputs")
    args = parser.parse_args()

    max_w = args.max_w
    log_path = args.log

    # Gtilde
    with open(log_path, "w") as f:
        for w in range(12, max_w + 1, 4):
            ds = (4 * w - 44, 4 * w - 20)
            gt = Gtilde(w - 12)
            num_coeffs = w // 4 - 1
            if num_coeffs <= 0:
                continue
            prec = num_coeffs + 5
            coeffs = _eval_qexp(gt, prec)
            all_nonneg = all(coeffs[n] >= 0 for n in range(num_coeffs))
            status = "PASS" if all_nonneg else "FAIL"
            if w % 100 == 0:
                print(f"w={w:5d}, d={ds}: first {num_coeffs} coeffs of Gtilde({w-12}) positive: {status}", file=f, flush=True)
            if not all_nonneg:
                print(f"  coeffs: {[coeffs[n] for n in range(num_coeffs)]}", file=f, flush=True)
                break