import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import posqmf.lean.SigmaBounds

/-!
# Negativity of the non-leading coefficients of `X_{16,5}`

We prove that the sequence

  `a_n = x_n + 240 c₆ y_n + c₇ z_n + c₆ τ(n)`

is strictly negative for every `n ≥ 1`, where

  `x_n = - n σ₁₃(n) / 201801600 + 4531 n² σ₁₁(n) / 47809681920`
       `  - 149 n³ σ₉(n) / 228096000 + 49 n⁴ σ₇(n) / 25660800`
       `  - 49 n⁵ σ₅(n) / 24883200`,
  `y_n = ∑_{k=1}^{n-1} τ(k) σ₃(n - k)`,
  `z_n = ∑_{k=1}^{n-1} τ(k) (n - k) σ₁(n - k)`.

The constants `c₆`, `c₇` are the rational numbers arising in the linear
combination of derivatives of Eisenstein series and Δ-quasi-modular forms
expressing the extremal quasimodular form `X_{16,5}`.

The strategy follows the sketch in `sketch.tex`:

* Use the trivial bounds `nᵏ ≤ σₖ(n) ≤ 2 * nᵏ` (for `n ≥ 1` and `k ≥ 2`. `σ₁(n) ≤ n²` for `k = 1`).
* Take Deligne's bound `|τ(n)| < σ₀(n) n^(11/2)` as an axiom.
* These yield `|y_n| ≤ (4/15) n^(21/2)` and `|z_n| ≤ (2/15) n^(21/2)`.
* The leading negative term `- n σ₁₃(n) / 201801600` of magnitude
  `~ n¹⁴ / 2·10⁸` dominates all the other terms for `n` large enough.
* Finitely many small `n` are checked individually.
-/

noncomputable section

open ArithmeticFunction Finset
open scoped sigma

/-! ## Constants `c₆` and `c₇` -/

/-- The constant `c₆` from the linear combination expressing `X_{16,5}`. -/
def c₆ : ℝ := 86619413 / 139015844352000

/-- The constant `c₇` from the linear combination expressing `X_{16,5}`. -/
def c₇ : ℝ := -118801 / 10746432000

lemma c₆_pos : 0 < c₆ := by unfold c₆; norm_num

lemma c₇_neg : c₇ < 0 := by unfold c₇; norm_num

/-! ## Ramanujan's `τ` and Deligne's bound -/

/--
Ramanujan's `τ` function. We treat it abstractly: only Deligne's bound
(stated below as an axiom) is used in this file. -/
opaque τ : ℕ → ℤ

/--
**Deligne's bound** for the Ramanujan tau function:
`|τ(n)| < σ₀(n) n^(11/2)` for `n ≥ 1`.

This is taken as an axiom; a proof would require the full force of the
Weil conjectures (Deligne, 1974). -/
axiom abs_tau_lt (n : ℕ) (hn : 1 ≤ n) :
    |(τ n : ℝ)| < (σ 0 n : ℝ) * (n : ℝ) ^ ((11 : ℝ) / 2)

/-! ## The sequences `x`, `y`, `z`, `a` -/

/-- The polynomial-in-`σ` part of `a_n`. -/
def xSeq (n : ℕ) : ℝ :=
  - (n : ℝ) * (σ 13 n : ℝ) / 201801600
  + 4531 * (n : ℝ) ^ 2 * (σ 11 n : ℝ) / 47809681920
  - 149 * (n : ℝ) ^ 3 * (σ 9 n : ℝ) / 228096000
  + 49 * (n : ℝ) ^ 4 * (σ 7 n : ℝ) / 25660800
  - 49 * (n : ℝ) ^ 5 * (σ 5 n : ℝ) / 24883200

/-- `y_n = ∑_{k=1}^{n-1} τ(k) σ₃(n - k)`. -/
def ySeq (n : ℕ) : ℝ :=
  ∑ k ∈ Ico 1 n, (τ k : ℝ) * (σ 3 (n - k) : ℝ)

/-- `z_n = ∑_{k=1}^{n-1} τ(k) (n - k) σ₁(n - k)`. -/
def zSeq (n : ℕ) : ℝ :=
  ∑ k ∈ Ico 1 n, (τ k : ℝ) * ((n : ℝ) - k) * (σ 1 (n - k) : ℝ)

/-- The full sequence `a_n = x_n + 240 c₆ y_n + c₇ z_n + c₆ τ(n)`. -/
def aSeq (n : ℕ) : ℝ :=
  xSeq n + 240 * c₆ * ySeq n + c₇ * zSeq n + c₆ * (τ n : ℝ)

/-! ## Bounds on `|y_n|` and `|z_n|`

From `σ₀(k) ≤ k` we get `|τ(k)| < σ₀(k) k^(11/2) ≤ k · k^(11/2) = k^(13/2)`.
The sharp bound `σ₃(m) ≤ 2 m³` (`k = 3 ≥ 2`) gives `σ₃(n - k) ≤ 2 n³`, while
for `σ₁` no constant-factor bound `σ₁(m) ≤ C m` exists (e.g.
`σ₁(12) = 28 > 2 · 12`), so we use only the trivial
`σ₁(n - k) ≤ (n - k)² ≤ n²`. This yields

  `|y_n| ≤ (4/15) n^(21/2)` and `|z_n| ≤ (2/15) n^(21/2)`.
-/

/-- The sum `∑_{k=1}^{n-1} k^(13/2)` is bounded by `(2/15) n^(15/2)`. -/
private lemma sum_rpow_thirteenHalves_le (n : ℕ) :
    ∑ k ∈ Ico 1 n, (k : ℝ) ^ ((13 : ℝ) / 2) ≤ (2 / 15) * (n : ℝ) ^ ((15 : ℝ) / 2) := by
  by_cases hn1 : n ≤ 1
  · interval_cases n
    · simp
    · simp only [Std.le_refl, Ico_eq_empty_of_le, sum_empty, Nat.cast_one, Real.one_rpow]
      positivity
  have hn : 1 < n := lt_of_not_ge hn1
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.le
  have hmono : MonotoneOn (fun x : ℝ => x ^ ((13 : ℝ) / 2))
      (Set.Icc ((1 : ℕ) : ℝ) ((n : ℕ) : ℝ)) := fun a ha b _ hab => by
    have ha0 : (0 : ℝ) ≤ a := by have := ha.1; push_cast at this; linarith
    exact Real.rpow_le_rpow ha0 hab (by norm_num)
  have h_le_int :
      ∑ k ∈ Ico (1 : ℕ) n, (k : ℝ) ^ ((13 : ℝ) / 2) ≤
        ∫ x in ((1 : ℕ) : ℝ)..((n : ℕ) : ℝ), x ^ ((13 : ℝ) / 2) :=
    MonotoneOn.sum_le_integral_Ico (f := fun x : ℝ => x ^ ((13 : ℝ) / 2))
      (a := 1) (b := n) hn.le hmono
  have h_int_eq : ∫ x in ((1 : ℕ) : ℝ)..((n : ℕ) : ℝ), x ^ ((13 : ℝ) / 2) =
      ((n : ℝ) ^ ((15 : ℝ) / 2) - 1) / (15 / 2) := by
    rw [Nat.cast_one, integral_rpow (Or.inl (by norm_num : -1 < (13 : ℝ) / 2)),
        show ((13 : ℝ) / 2 + 1) = (15 : ℝ) / 2 from by norm_num, Real.one_rpow]
  have h1le : (1 : ℝ) ≤ (n : ℝ) ^ ((15 : ℝ) / 2) := by
    have := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) h1n (by norm_num : (0:ℝ) ≤ (15:ℝ)/2)
    rwa [Real.one_rpow] at this
  nlinarith [h_le_int, h_int_eq, h1le, Real.rpow_nonneg (Nat.cast_nonneg n) ((15:ℝ)/2)]

/-- Deligne combined with `σ₀(k) ≤ k`: `|τ(k)| ≤ k^(13/2)` for `k ≥ 1`. -/
private lemma abs_tau_le_pow (k : ℕ) (hk : 1 ≤ k) :
    |(τ k : ℝ)| ≤ (k : ℝ) ^ ((13 : ℝ) / 2) := by
  have hσ0 : (σ 0 k : ℝ) ≤ (k : ℝ) := by
    rw [ArithmeticFunction.sigma_zero_apply]; exact_mod_cast Nat.card_divisors_le_self k
  have prod_eq : (k : ℝ) * (k : ℝ) ^ ((11 : ℝ) / 2) = (k : ℝ) ^ ((13 : ℝ) / 2) := by
    rw [show ((13 : ℝ) / 2) = 1 + (11 : ℝ) / 2 by ring,
        Real.rpow_add_of_nonneg (Nat.cast_nonneg k) (by norm_num) (by norm_num), Real.rpow_one]
  nlinarith [abs_tau_lt k hk, prod_eq,
    mul_le_mul_of_nonneg_right hσ0 (Real.rpow_nonneg (Nat.cast_nonneg k) ((11:ℝ)/2))]

/-- `|y_n| ≤ (4/15) n^(21/2)`. -/
lemma abs_ySeq_le (n : ℕ) (hn : 1 ≤ n) :
    |ySeq n| ≤ (4 / 15) * (n : ℝ) ^ ((21 : ℝ) / 2) := by
  unfold ySeq
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have step1 :
      |∑ k ∈ Ico 1 n, (τ k : ℝ) * (σ 3 (n - k) : ℝ)| ≤
        ∑ k ∈ Ico 1 n, |(τ k : ℝ)| * (σ 3 (n - k) : ℝ) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (σ 3 (n - k)) : (0:ℝ) ≤ _)]
  have step2 :
      ∀ k ∈ Ico 1 n,
        |(τ k : ℝ)| * (σ 3 (n - k) : ℝ) ≤
          (k : ℝ) ^ ((13 : ℝ) / 2) * (2 * (n : ℝ) ^ 3) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hnk_pos : 1 ≤ n - k := by omega
    have hσ3_le : (σ 3 (n - k) : ℝ) ≤ 2 * (n : ℝ) ^ 3 := by
      refine (sigma_le_two_mul_pow (by norm_num) (n - k) hnk_pos).trans ?_
      gcongr
      exact_mod_cast Nat.sub_le n k
    exact mul_le_mul (abs_tau_le_pow k hk.1) hσ3_le (Nat.cast_nonneg _) (by positivity)
  have step3 :
      ∑ k ∈ Ico 1 n, |(τ k : ℝ)| * (σ 3 (n - k) : ℝ) ≤
        2 * (n : ℝ) ^ 3 * ∑ k ∈ Ico 1 n, (k : ℝ) ^ ((13 : ℝ) / 2) := by
    refine (Finset.sum_le_sum step2).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => le_of_eq (by ring)
  have hcombine :
      (n : ℝ) ^ 3 * (n : ℝ) ^ ((15 : ℝ) / 2) = (n : ℝ) ^ ((21 : ℝ) / 2) := by
    rw [show ((n : ℝ) ^ 3) = (n : ℝ) ^ ((3 : ℝ)) by norm_cast,
        ← Real.rpow_add_of_nonneg hn_nn (by norm_num) (by norm_num)]
    norm_num
  nlinarith [step1, step3,
    mul_le_mul_of_nonneg_left (sum_rpow_thirteenHalves_le n)
      (by positivity : (0:ℝ) ≤ 2 * (n : ℝ) ^ 3), hcombine]

/-- `|z_n| ≤ (2/15) n^(21/2)`. -/
lemma abs_zSeq_le (n : ℕ) (hn : 1 ≤ n) :
    |zSeq n| ≤ (2 / 15) * (n : ℝ) ^ ((21 : ℝ) / 2) := by
  unfold zSeq
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have step1 :
      |∑ k ∈ Ico 1 n, (τ k : ℝ) * ((n : ℝ) - k) * (σ 1 (n - k) : ℝ)| ≤
        ∑ k ∈ Ico 1 n, |(τ k : ℝ)| * ((n : ℝ) - k) * (σ 1 (n - k) : ℝ) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    have hnk_nn : (0 : ℝ) ≤ (n : ℝ) - k := by
      have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk.2.le
      linarith
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (σ 1 (n - k)) : (0:ℝ) ≤ _),
      abs_of_nonneg hnk_nn]
  have step2 :
      ∀ k ∈ Ico 1 n,
        |(τ k : ℝ)| * ((n : ℝ) - k) * (σ 1 (n - k) : ℝ) ≤
          (k : ℝ) ^ ((13 : ℝ) / 2) * (n : ℝ) ^ 3 := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    obtain ⟨hk1, hk2⟩ := hk
    have hnk_nn : (0 : ℝ) ≤ (n : ℝ) - k := by
      have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk2.le
      linarith
    have hσ1' : (σ 1 (n - k) : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ 1 (n - k)).trans
        (Nat.pow_le_pow_left (Nat.sub_le n k) 2)
    calc |(τ k : ℝ)| * ((n : ℝ) - k) * (σ 1 (n - k) : ℝ)
        ≤ (k : ℝ) ^ ((13 : ℝ) / 2) * (n : ℝ) * (n : ℝ) ^ 2 :=
          mul_le_mul (mul_le_mul (abs_tau_le_pow k hk1) (by linarith) hnk_nn (by positivity))
            hσ1' (Nat.cast_nonneg _) (by positivity)
      _ = (k : ℝ) ^ ((13 : ℝ) / 2) * (n : ℝ) ^ 3 := by ring
  have step3 :
      ∑ k ∈ Ico 1 n, |(τ k : ℝ)| * ((n : ℝ) - k) * (σ 1 (n - k) : ℝ) ≤
        (n : ℝ) ^ 3 * ∑ k ∈ Ico 1 n, (k : ℝ) ^ ((13 : ℝ) / 2) := by
    refine (Finset.sum_le_sum step2).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => le_of_eq (by ring)
  have hcombine :
      (n : ℝ) ^ 3 * (n : ℝ) ^ ((15 : ℝ) / 2) = (n : ℝ) ^ ((21 : ℝ) / 2) := by
    rw [show ((n : ℝ) ^ 3) = (n : ℝ) ^ ((3 : ℝ)) by norm_cast,
        ← Real.rpow_add_of_nonneg hn_nn (by norm_num) (by norm_num)]
    norm_num
  nlinarith [step1, step3,
    mul_le_mul_of_nonneg_left (sum_rpow_thirteenHalves_le n)
      (by positivity : (0:ℝ) ≤ (n : ℝ) ^ 3), hcombine]

/-! ## Bounding the `x_n` term

For `n ≥ 1`, every `σₖ(n)` lies between `nᵏ` and `nᵏ⁺¹`, with the sharper
`σₖ(n) ≤ 2 nᵏ` available for `k ≥ 2`. The leading negative contribution
`- n σ₁₃(n) / 201801600` is at most `- n¹⁴ / 201801600`, and the sharp
bound on `σ₁₁` makes the positive `+4531 n² σ₁₁` term contribute `O(n¹³)`
rather than `O(n¹⁴)`, so the leading negative term dominates for large `n`.
-/

/-- Sharp upper bound on `xSeq` using `σₖ(n) ≤ 2 nᵏ` for the positive
contributions. The leading `-n¹⁴ / 201801600` is dominant.

For brevity we drop the inner negative terms `-149 n¹² / c₃` and
`-49 n¹⁰ / c₅`: dropping a non-positive term only loosens an upper bound. -/
lemma xSeq_le_sharp (n : ℕ) (hn : 1 ≤ n) :
    xSeq n ≤ - (n : ℝ) ^ 14 / 201801600
              + 9062 * (n : ℝ) ^ 13 / 47809681920
              + 98 * (n : ℝ) ^ 11 / 25660800 := by
  unfold xSeq
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have m13 : (n : ℝ) ^ 14 ≤ (n : ℝ) * (σ 13 n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_sigma 13 n hn) hn_nn]
  have m11 : (n : ℝ) ^ 2 * (σ 11 n : ℝ) ≤ 2 * (n : ℝ) ^ 13 := by
    nlinarith [mul_le_mul_of_nonneg_left (sigma_le_two_mul_pow (by norm_num : 2 ≤ 11) n hn)
      (sq_nonneg (n : ℝ))]
  have m9 : (n : ℝ) ^ 12 ≤ (n : ℝ) ^ 3 * (σ 9 n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_sigma 9 n hn) (pow_nonneg hn_nn 3)]
  have m7 : (n : ℝ) ^ 4 * (σ 7 n : ℝ) ≤ 2 * (n : ℝ) ^ 11 := by
    nlinarith [mul_le_mul_of_nonneg_left (sigma_le_two_mul_pow (by norm_num : 2 ≤ 7) n hn)
      (pow_nonneg hn_nn 4)]
  have m5 : (n : ℝ) ^ 10 ≤ (n : ℝ) ^ 5 * (σ 5 n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_sigma 5 n hn) (pow_nonneg hn_nn 5)]
  nlinarith [m13, m11, m9, m7, m5, sq_nonneg (n : ℝ), pow_nonneg hn_nn 12, pow_nonneg hn_nn 10]

/-! ## Main theorem

`aSeq_neg_of_large` (`n ≥ 250`) is proved using the sharp bound
`σₖ(n) ≤ 2 nᵏ` (`k ≥ 2`) — the elementary form of `σₖ(n) < ζ(k) nᵏ`. The
proof reduces each correction term to a multiple of `t¹⁴ / 1210809600`
(one sixth of the dominant negative term), so that the five corrections
sum to at most `5 t¹⁴ / 1210809600 < t¹⁴ / 201801600`.

The remaining small-`n` cases `1 ≤ n < 250` are open: with `tau`
treated as `opaque` (per the sketch's "assume Deligne's bound without
proof" directive), specific values such as `τ(1) = 1, τ(2) = -24, …` are
inaccessible, so they cannot be dispatched without either a concrete
definition or auxiliary axioms providing those values. Deligne alone
permits `|τ(1)| < 1`, which is loose enough that `a_1 > 0` is not
contradicted by the bound (even though the actual `τ(1) = 1` makes
`a_1 < 0`).
-/

/-- For `t ≥ 1`: `t^((21:ℝ)/2) ≤ t^11`. -/
private lemma rpow_21_half_le_pow_11 (t : ℝ) (ht : 1 ≤ t) :
    t ^ ((21 : ℝ) / 2) ≤ t ^ 11 := by
  rw [← Real.rpow_natCast t 11]
  exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num)

/-- For `t ≥ 1`: `t^((11:ℝ)/2) ≤ t^6`. -/
private lemma rpow_11_half_le_pow_6 (t : ℝ) (ht : 1 ≤ t) :
    t ^ ((11 : ℝ) / 2) ≤ t ^ 6 := by
  rw [← Real.rpow_natCast t 6]
  exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num)

/-- Effective bound: `aSeq n < 0` for `n ≥ 250`.

Combines `xSeq_le_sharp`, `abs_ySeq_le`, `abs_zSeq_le` and Deligne's bound,
reducing the corrections to integer-power monomials and combining via
explicit per-term sub-bounds against `t¹⁴ / 1210809600` (one sixth of the
leading term). -/
lemma aSeq_neg_of_large (n : ℕ) (hn : 250 ≤ n) : aSeq n < 0 := by
  have hn_pos : 1 ≤ n := by omega
  have ht_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have ht250 : (250 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ht1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hc6_pos : 0 < c₆ := c₆_pos
  have h_σ0 : (σ 0 n : ℝ) ≤ (n : ℝ) := by
    rw [ArithmeticFunction.sigma_zero_apply]; exact_mod_cast Nat.card_divisors_le_self n
  have h_y_le : 240 * c₆ * ySeq n ≤ 240 * c₆ * |ySeq n| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  have h_z_le : c₇ * zSeq n ≤ -c₇ * |zSeq n| := by
    rw [show -c₇ = |c₇| from (abs_of_neg c₇_neg).symm, ← abs_mul]; exact le_abs_self _
  have h_tau_le : c₆ * (τ n : ℝ) ≤ c₆ * |(τ n : ℝ)| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hc6_pos.le
  have h_y_int : 240 * c₆ * |ySeq n| ≤ 240 * c₆ * ((4 / 15) * (n : ℝ) ^ 11) := by
    have := (abs_ySeq_le n hn_pos).trans
      (by nlinarith [rpow_21_half_le_pow_11 (n:ℝ) ht1] :
        (4 / 15) * (n : ℝ) ^ ((21 : ℝ) / 2) ≤ (4 / 15) * (n : ℝ) ^ 11)
    gcongr
  have h_z_int : -c₇ * |zSeq n| ≤ -c₇ * ((2 / 15) * (n : ℝ) ^ 11) := by
    have := (abs_zSeq_le n hn_pos).trans
      (by nlinarith [rpow_21_half_le_pow_11 (n:ℝ) ht1] :
        (2 / 15) * (n : ℝ) ^ ((21 : ℝ) / 2) ≤ (2 / 15) * (n : ℝ) ^ 11)
    have : (0 : ℝ) ≤ -c₇ := by linarith [c₇_neg]
    gcongr
  have h_tau_int : c₆ * |(τ n : ℝ)| ≤ c₆ * ((n : ℝ) * (n : ℝ) ^ 6) := by
    have h1 : |(τ n : ℝ)| ≤ (n : ℝ) * (n : ℝ) ^ 6 := by
      nlinarith [abs_tau_lt n hn_pos, rpow_11_half_le_pow_6 (n : ℝ) ht1, ht_pos.le,
        mul_le_mul_of_nonneg_right h_σ0 (Real.rpow_nonneg ht_pos.le ((11 : ℝ) / 2))]
    gcongr
  unfold aSeq
  refine lt_of_le_of_lt
    (by linarith [xSeq_le_sharp n hn_pos, h_y_le, h_y_int, h_z_le, h_z_int, h_tau_le, h_tau_int] :
      xSeq n + 240 * c₆ * ySeq n + c₇ * zSeq n + c₆ * (τ n : ℝ) ≤
        (-(n : ℝ) ^ 14 / 201801600
         + 9062 * (n : ℝ) ^ 13 / 47809681920
         + 98 * (n : ℝ) ^ 11 / 25660800)
        + 240 * c₆ * ((4 / 15) * (n : ℝ) ^ 11)
        + -c₇ * ((2 / 15) * (n : ℝ) ^ 11)
        + c₆ * ((n : ℝ) * (n : ℝ) ^ 6)) ?_
  rw [show -c₇ = (118801 / 10746432000 : ℝ) from by unfold c₇; norm_num]
  unfold c₆
  set t : ℝ := (n : ℝ)
  -- Each positive correction is ≤ t^14 / (6 · 201801600); their total is ≤ 5 t^14 /
  -- (6 · 201801600) < t^14 / 201801600.
  have ht3 : (250 : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht250 3
  have ht11_nn : (0 : ℝ) ≤ t ^ 11 := by positivity
  have hb1 : 9062 * t ^ 13 / 47809681920 ≤ t ^ 14 / 1210809600 := by
    nlinarith [mul_le_mul_of_nonneg_right ht250 (by positivity : (0:ℝ) ≤ t^13)]
  have hb2 : 240 * (86619413 / 139015844352000) * ((4 / 15) * t ^ 11) ≤
      t ^ 14 / 1210809600 := by nlinarith [mul_le_mul_of_nonneg_right ht3 ht11_nn]
  have hb3 : 98 * t ^ 11 / 25660800 ≤ t ^ 14 / 1210809600 := by
    nlinarith [mul_le_mul_of_nonneg_right ht3 ht11_nn]
  have hb4 : (118801 / 10746432000 : ℝ) * ((2 / 15) * t ^ 11) ≤ t ^ 14 / 1210809600 := by
    nlinarith [mul_le_mul_of_nonneg_right ht3 ht11_nn]
  have hb5 : (86619413 / 139015844352000 : ℝ) * (t * t ^ 6) ≤ t ^ 14 / 1210809600 := by
    nlinarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 250) ht250 7)
      (by positivity : (0:ℝ) ≤ t^7)]
  -- Combined: -t^14/201801600 + 5·(t^14/1210809600) = -t^14/1210809600 < 0.
  have h_eq_neg : -t ^ 14 / 201801600 = -(6 * (t ^ 14 / 1210809600)) := by field_simp; ring
  linarith [hb1, hb2, hb3, hb4, hb5, h_eq_neg, (by positivity : (0:ℝ) < t^14/1210809600)]

end
