import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Negativity of the non-leading coefficients of `X_{16,5}`

We prove that the sequence

  a_n = x_n + 240 c₆ y_n + c₇ z_n + c₆ τ(n)

is strictly negative for every `n ≥ 1`, where

  x_n = - n σ₁₃(n) / 201801600 + 4531 n² σ₁₁(n) / 47809681920
        - 149 n³ σ_9(n) / 228096000 + 49 n⁴ σ_7(n) / 25660800
        - 49 n⁵ σ_5(n) / 24883200,
  y_n = ∑_{k=1}^{n-1} τ(k) σ_3(n - k),
  z_n = ∑_{k=1}^{n-1} τ(k) (n - k) σ_1(n - k).

The constants `c₆`, `c₇` are the rational numbers arising in the linear
combination of derivatives of Eisenstein series and Δ-quasi-modular forms
expressing the extremal quasimodular form `X_{16,5}`.

The strategy follows the sketch in `sketch.tex`:

* Use the trivial bounds `nᵏ ≤ σₖ(n) ≤ nᵏ⁺¹` (for `n ≥ 1`).
* Take Deligne's bound `|τ(n)| < σ_0(n) n^(11/2)` as an axiom.
* These yield `|y_n| ≤ (1/15) n^(23/2)` and `|z_n| ≤ (1/15) n^(21/2)`.
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
opaque ramanujanTau : ℕ → ℤ

@[inherit_doc]
local notation "τ" => ramanujanTau

/--
**Deligne's bound** for the Ramanujan tau function:
`|τ(n)| < σ₀(n) n^(11/2)` for `n ≥ 1`.

This is taken as an axiom; a proof would require the full force of the
Weil conjectures (Deligne, 1974). -/
axiom abs_ramanujanTau_lt (n : ℕ) (hn : 1 ≤ n) :
    |(τ n : ℝ)| < (σ 0 n : ℝ) * (n : ℝ) ^ ((11 : ℝ) / 2)

/-! ## The sequences `x`, `y`, `z`, `a` -/

/-- The polynomial-in-`σ` part of `a_n`. -/
def xSeq (n : ℕ) : ℝ :=
  - (n : ℝ) * (σ 13 n : ℝ) / 201801600
  + 4531 * (n : ℝ) ^ 2 * (σ 11 n : ℝ) / 47809681920
  - 149 * (n : ℝ) ^ 3 * (σ 9 n : ℝ) / 228096000
  + 49 * (n : ℝ) ^ 4 * (σ 7 n : ℝ) / 25660800
  - 49 * (n : ℝ) ^ 5 * (σ 5 n : ℝ) / 24883200

/-- `y_n = ∑_{k=1}^{n-1} τ(k) σ_3(n - k)`. -/
def ySeq (n : ℕ) : ℝ :=
  ∑ k ∈ Ico 1 n, (τ k : ℝ) * (σ 3 (n - k) : ℝ)

/-- `z_n = ∑_{k=1}^{n-1} τ(k) (n - k) σ_1(n - k)`. -/
def zSeq (n : ℕ) : ℝ :=
  ∑ k ∈ Ico 1 n, (τ k : ℝ) * ((n : ℝ) - k) * (σ 1 (n - k) : ℝ)

/-- The full sequence `a_n = x_n + 240 c₆ y_n + c₇ z_n + c₆ τ(n)`. -/
def aSeq (n : ℕ) : ℝ :=
  xSeq n + 240 * c₆ * ySeq n + c₇ * zSeq n + c₆ * (τ n : ℝ)

/-! ## Trivial bounds on `σₖ` -/

/-- Lower bound: `nᵏ ≤ σₖ(n)` for `n ≥ 1` (since `n` itself is a divisor). -/
lemma pow_le_sigma (k n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ k ≤ (σ k n : ℝ) := by
  rw [ArithmeticFunction.sigma_apply]
  exact_mod_cast Finset.single_le_sum (f := fun d => d ^ k) (s := n.divisors)
    (fun _ _ => Nat.zero_le _) (Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩)

/-- Upper bound: `σₖ(n) ≤ nᵏ⁺¹` (Mathlib lemma, restated for `ℝ`). -/
lemma sigma_le_pow_succ_real (k n : ℕ) :
    (σ k n : ℝ) ≤ (n : ℝ) ^ (k + 1) := by
  exact_mod_cast ArithmeticFunction.sigma_le_pow_succ k n

/-! ### Sharp bound `σₖ(n) ≤ 2 nᵏ` (`k ≥ 2`)

Following the user's hint, the bijection `d ↔ n/d` on divisors of `n` gives

  `σₖ(n) = ∑_{d|n} dᵏ = ∑_{d|n} (n/d)ᵏ = nᵏ · ∑_{d|n} 1/dᵏ`,

and for `k ≥ 2` the sum is bounded by `2`:

  `∑_{d|n} 1/dᵏ ≤ ∑_{d=1}^{n} 1/dᵏ ≤ 1 + ∑_{d=2}^{n}(1/(d-1) - 1/d) ≤ 2`.
-/

/-- Telescoping identity: `∑_{d=2}^{N} (1/(d-1) - 1/d) = 1 - 1/N` for `N ≥ 1`. -/
private lemma sum_telescope_one_div (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Icc 2 N, ((1 : ℝ) / ((d - 1 : ℕ) : ℝ) - (1 : ℝ) / (d : ℝ)) =
      1 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => rw [show Finset.Icc 2 1 = ∅ from Finset.Icc_eq_empty_of_lt (by omega)]; simp
  | succ m hm ih =>
    by_cases hm2 : 2 ≤ m
    · have h_split : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
        ext x; simp [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [h_split, Finset.sum_insert (by rw [Finset.mem_Icc]; omega), ih,
        show ((m + 1 - 1 : ℕ) : ℝ) = (m : ℝ) by rw [Nat.add_sub_cancel]]
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      push_cast; field_simp; ring
    · interval_cases m
      rw [show Finset.Icc 2 (1 + 1) = {2} from by
        ext x; rw [Finset.mem_Icc, Finset.mem_singleton]; omega]
      simp

/-- Bound: `∑_{d=2}^{N} 1/d² ≤ 1`. -/
private lemma sum_one_div_sq_le_one (N : ℕ) :
    ∑ d ∈ Finset.Icc 2 N, ((1 : ℝ) / (d : ℝ) ^ 2) ≤ 1 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · rw [Finset.Icc_eq_empty_of_lt hN]; simp
  have hbound : ∀ d ∈ Finset.Icc 2 N,
      ((1 : ℝ) / (d : ℝ) ^ 2) ≤ ((1 : ℝ) / ((d - 1 : ℕ) : ℝ) - (1 : ℝ) / (d : ℝ)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.1
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]; push_cast; ring
    rw [hcast, div_sub_div _ _ (by linarith) (by linarith), sq,
      div_le_div_iff₀ (by positivity) (by nlinarith)]
    nlinarith
  calc ∑ d ∈ Finset.Icc 2 N, ((1 : ℝ) / (d : ℝ) ^ 2)
      ≤ ∑ d ∈ Finset.Icc 2 N, ((1 : ℝ) / ((d - 1 : ℕ) : ℝ) - 1 / (d : ℝ)) :=
        Finset.sum_le_sum hbound
    _ = 1 - 1 / (N : ℝ) := sum_telescope_one_div N (by omega)
    _ ≤ 1 := by
        have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
        linarith

/-- For `d ≥ 1` and `k ≥ 2`: `1/dᵏ ≤ 1/d²`. -/
private lemma one_div_pow_le_one_div_sq {d : ℕ} (hd : 1 ≤ d) {k : ℕ} (hk : 2 ≤ k) :
    ((1 : ℝ) / (d : ℝ) ^ k) ≤ (1 : ℝ) / (d : ℝ) ^ 2 :=
  one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by exact_mod_cast hd) hk)

/-- Bound: `∑_{d=1}^{n} 1/dᵏ ≤ 2` for `k ≥ 2`. -/
private lemma sum_one_div_pow_Icc_le_two {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, ((1 : ℝ) / (d : ℝ) ^ k) ≤ 2 := by
  have h_split : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [h_split, Finset.sum_insert (by rw [Finset.mem_Icc]; omega),
    show (1 : ℝ) / (((1 : ℕ) : ℝ)) ^ k = 1 by push_cast; simp]
  have h_bound : ∀ d ∈ Finset.Icc 2 n,
      ((1 : ℝ) / (d : ℝ) ^ k) ≤ (1 : ℝ) / (d : ℝ) ^ 2 := fun d hd => by
    rw [Finset.mem_Icc] at hd
    exact one_div_pow_le_one_div_sq (by omega) hk
  linarith [Finset.sum_le_sum h_bound, sum_one_div_sq_le_one n]

/-- The bijection `d ↔ n/d` on divisors of `n`, cast to `ℝ`:
`σₖ(n) = nᵏ · ∑_{d ∣ n} 1/dᵏ`. -/
private lemma sigma_eq_pow_mul_sum_inv (k : ℕ) (n : ℕ) (hn : 1 ≤ n) :
    (σ k n : ℝ) = (n : ℝ) ^ k * ∑ d ∈ n.divisors, ((1 : ℝ) / (d : ℝ) ^ k) := by
  rw [show ((σ k n : ℕ) : ℝ) = (((∑ d ∈ n.divisors, (n / d) ^ k : ℕ) : ℕ) : ℝ) by
        congr 1; exact ArithmeticFunction.sigma_eq_sum_div k n]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hd_dvd, _⟩ := Nat.mem_divisors.mp hd
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd (by omega)
  rw [Nat.cast_div hd_dvd (by exact_mod_cast hd_pos.ne'), div_pow]
  field_simp

/-- **Sharp σ-bound**: for `k ≥ 2` and `n ≥ 1`, `σₖ(n) ≤ 2 nᵏ`.

This follows from `σₖ(n) = nᵏ · ∑_{d ∣ n} 1/dᵏ` and the bound
`∑_{d=1}^n 1/dᵏ ≤ 2`. -/
lemma sigma_le_two_mul_pow {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    (σ k n : ℝ) ≤ 2 * (n : ℝ) ^ k := by
  rw [sigma_eq_pow_mul_sum_inv k n hn]
  have h_subset : n.divisors ⊆ Finset.Icc 1 n := fun d hd => by
    rw [Nat.mem_divisors] at hd
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_dvd_of_pos hd.1 (by omega), Nat.le_of_dvd (by omega) hd.1⟩
  have h_sum_le : ∑ d ∈ n.divisors, ((1 : ℝ) / (d : ℝ) ^ k) ≤ 2 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun _ _ _ => by positivity))
      (sum_one_div_pow_Icc_le_two hk n hn)
  nlinarith [mul_le_mul_of_nonneg_left h_sum_le (by positivity : (0:ℝ) ≤ (n:ℝ)^k)]

/-! ## Deligne-style bounds on `|y_n|` and `|z_n|`

We bound `|τ(k)| < σ₀(k) k^(11/2) ≤ k · k^(11/2) = k^(13/2)` using
`σ₀(k) ≤ k`. Together with `σ₃(n - k) ≤ (n - k)^4 ≤ n^4` and
`σ₁(n - k) ≤ (n - k)^2 ≤ n^2`, this yields the bounds (∗).
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
    rw [show (((1 : ℕ) : ℝ)) = (1 : ℝ) from by norm_cast,
        integral_rpow (Or.inl (by norm_num : -1 < (13 : ℝ) / 2)),
        show ((13 : ℝ) / 2 + 1) = (15 : ℝ) / 2 from by norm_num, Real.one_rpow]
  have h1le : (1 : ℝ) ≤ (n : ℝ) ^ ((15 : ℝ) / 2) := by
    have := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) h1n (by norm_num : (0:ℝ) ≤ (15:ℝ)/2)
    rwa [Real.one_rpow] at this
  nlinarith [h_le_int, h_int_eq, h1le, Real.rpow_nonneg (Nat.cast_nonneg n) ((15:ℝ)/2)]

/-- Deligne combined with `σ₀(k) ≤ k`: `|τ(k)| ≤ k^(13/2)` for `k ≥ 1`. -/
private lemma abs_ramanujanTau_le_pow (k : ℕ) (hk : 1 ≤ k) :
    |(τ k : ℝ)| ≤ (k : ℝ) ^ ((13 : ℝ) / 2) := by
  have hτ := abs_ramanujanTau_lt k hk
  have hσ0 : (σ 0 k : ℝ) ≤ (k : ℝ) := by
    rw [ArithmeticFunction.sigma_zero_apply]
    exact_mod_cast Nat.card_divisors_le_self k
  have hkpos : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hpow_pos : (0 : ℝ) ≤ (k : ℝ) ^ ((11 : ℝ) / 2) := Real.rpow_nonneg hkpos _
  have prod_eq : (k : ℝ) * (k : ℝ) ^ ((11 : ℝ) / 2) = (k : ℝ) ^ ((13 : ℝ) / 2) := by
    rw [show ((13 : ℝ) / 2) = 1 + (11 : ℝ) / 2 by ring,
        Real.rpow_add_of_nonneg hkpos (by norm_num) (by norm_num), Real.rpow_one]
  nlinarith [hτ, mul_le_mul_of_nonneg_right hσ0 hpow_pos, prod_eq]

/-- `|y_n| ≤ (2/15) n^(23/2)`. -/
lemma abs_ySeq_le (n : ℕ) (hn : 1 ≤ n) :
    |ySeq n| ≤ (2 / 15) * (n : ℝ) ^ ((23 : ℝ) / 2) := by
  unfold ySeq
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have step1 :
      |∑ k ∈ Ico 1 n, (τ k : ℝ) * (σ 3 (n - k) : ℝ)| ≤
        ∑ k ∈ Ico 1 n, |(τ k : ℝ)| * (σ 3 (n - k) : ℝ) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (σ 3 (n - k) : ℕ) : (0:ℝ) ≤ _)]
  have step2 :
      ∀ k ∈ Ico 1 n,
        |(τ k : ℝ)| * (σ 3 (n - k) : ℝ) ≤
          (k : ℝ) ^ ((13 : ℝ) / 2) * (n : ℝ) ^ 4 := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hσ3_le : (σ 3 (n - k) : ℝ) ≤ (n : ℝ) ^ 4 := by
      exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ 3 (n - k)).trans
        (Nat.pow_le_pow_left (Nat.sub_le n k) 4)
    exact mul_le_mul (abs_ramanujanTau_le_pow k hk.1) hσ3_le (Nat.cast_nonneg _) (by positivity)
  have step3 :
      ∑ k ∈ Ico 1 n, |(τ k : ℝ)| * (σ 3 (n - k) : ℝ) ≤
        (n : ℝ) ^ 4 * ∑ k ∈ Ico 1 n, (k : ℝ) ^ ((13 : ℝ) / 2) := by
    refine (Finset.sum_le_sum step2).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => le_of_eq (by ring)
  have hcombine :
      (n : ℝ) ^ 4 * (n : ℝ) ^ ((15 : ℝ) / 2) = (n : ℝ) ^ ((23 : ℝ) / 2) := by
    rw [show ((n : ℝ) ^ 4) = (n : ℝ) ^ ((4 : ℝ)) by norm_cast,
        ← Real.rpow_add_of_nonneg hn_nn (by norm_num) (by norm_num)]
    norm_num
  nlinarith [step1, step3,
    mul_le_mul_of_nonneg_left (sum_rpow_thirteenHalves_le n)
      (by positivity : (0:ℝ) ≤ (n : ℝ) ^ 4), hcombine]

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
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (σ 1 (n - k) : ℕ) : (0:ℝ) ≤ _),
      abs_of_nonneg hnk_nn]
  have step2 :
      ∀ k ∈ Ico 1 n,
        |(τ k : ℝ)| * ((n : ℝ) - k) * (σ 1 (n - k) : ℝ) ≤
          (k : ℝ) ^ ((13 : ℝ) / 2) * (n : ℝ) ^ 3 := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    obtain ⟨hk1, hk2⟩ := hk
    have hk_le : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk2.le
    have hnk_nn : (0 : ℝ) ≤ (n : ℝ) - k := by linarith
    have hσ1' : (σ 1 (n - k) : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ 1 (n - k)).trans
        (Nat.pow_le_pow_left (Nat.sub_le n k) 2)
    have h_a : |(τ k : ℝ)| * ((n : ℝ) - k) ≤
        (k : ℝ) ^ ((13 : ℝ) / 2) * (n : ℝ) :=
      mul_le_mul (abs_ramanujanTau_le_pow k hk1) (by linarith) hnk_nn (by positivity)
    calc |(τ k : ℝ)| * ((n : ℝ) - k) * (σ 1 (n - k) : ℝ)
        ≤ (k : ℝ) ^ ((13 : ℝ) / 2) * (n : ℝ) * (n : ℝ) ^ 2 :=
          mul_le_mul h_a hσ1' (Nat.cast_nonneg _) (by positivity)
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

For `n ≥ 1`, every `σₖ(n)` lies between `nᵏ` and `nᵏ⁺¹`. The leading negative
contribution `- n σ₁₃(n) / 201801600` is at most `- n¹⁴ / 201801600`, and one
checks that the positive contributions cannot make up for it once `n` is
large enough.
-/

/-- Upper bound on `x_n`: replace each `σₖ(n)` by `n^k` (in negative terms,
using `σₖ(n) ≥ nᵏ`) or by `nᵏ⁺¹` (in positive terms, using `σₖ(n) ≤ nᵏ⁺¹`). -/
lemma xSeq_le (n : ℕ) (hn : 1 ≤ n) :
    xSeq n ≤
      - (n : ℝ) ^ 14 / 201801600
      + 4531 * (n : ℝ) ^ 14 / 47809681920
      - 149 * (n : ℝ) ^ 12 / 228096000
      + 49 * (n : ℝ) ^ 12 / 25660800
      - 49 * (n : ℝ) ^ 10 / 24883200 := by
  unfold xSeq
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have m13 : (n : ℝ) ^ 14 ≤ (n : ℝ) * (σ 13 n : ℝ) := by
    have := mul_le_mul_of_nonneg_left (pow_le_sigma 13 n hn) hn_nn; nlinarith
  have m11 : (n : ℝ) ^ 2 * (σ 11 n : ℝ) ≤ (n : ℝ) ^ 14 := by
    have h : (σ 11 n : ℝ) ≤ (n : ℝ) ^ 12 := sigma_le_pow_succ_real 11 n
    nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ((n:ℝ)))]
  have m9 : (n : ℝ) ^ 12 ≤ (n : ℝ) ^ 3 * (σ 9 n : ℝ) := by
    have := mul_le_mul_of_nonneg_left (pow_le_sigma 9 n hn) (pow_nonneg hn_nn 3); nlinarith
  have m7 : (n : ℝ) ^ 4 * (σ 7 n : ℝ) ≤ (n : ℝ) ^ 12 := by
    have h : (σ 7 n : ℝ) ≤ (n : ℝ) ^ 8 := sigma_le_pow_succ_real 7 n
    nlinarith [mul_le_mul_of_nonneg_left h (pow_nonneg hn_nn 4)]
  have m5 : (n : ℝ) ^ 10 ≤ (n : ℝ) ^ 5 * (σ 5 n : ℝ) := by
    have := mul_le_mul_of_nonneg_left (pow_le_sigma 5 n hn) (pow_nonneg hn_nn 5); nlinarith
  nlinarith [m13, m11, m9, m7, m5]

/-! ## Sharp upper bound on `xSeq` -/

/-- Sharp upper bound on `xSeq` using `σₖ(n) ≤ 2 nᵏ` for the positive
contributions. Compared with `xSeq_le`, the `+4531 n² σ₁₁` term contributes
`O(n¹³)` rather than `O(n¹⁴)`, so the leading `-n¹⁴ / c₁` is now dominant.

For brevity we drop the inner negative terms `-149 n¹² / c₃` and
`-49 n¹⁰ / c₅`: dropping a non-positive term only loosens an upper bound. -/
lemma xSeq_le_sharp (n : ℕ) (hn : 1 ≤ n) :
    xSeq n ≤ - (n : ℝ) ^ 14 / 201801600
              + 9062 * (n : ℝ) ^ 13 / 47809681920
              + 98 * (n : ℝ) ^ 11 / 25660800 := by
  unfold xSeq
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have m13 : (n : ℝ) ^ 14 ≤ (n : ℝ) * (σ 13 n : ℝ) := by
    have := mul_le_mul_of_nonneg_left (pow_le_sigma 13 n hn) hn_nn; nlinarith
  have m11 : (n : ℝ) ^ 2 * (σ 11 n : ℝ) ≤ 2 * (n : ℝ) ^ 13 := by
    have h : (σ 11 n : ℝ) ≤ 2 * (n : ℝ) ^ 11 := sigma_le_two_mul_pow (by norm_num) n hn
    nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ((n:ℝ)))]
  have m9 : (n : ℝ) ^ 12 ≤ (n : ℝ) ^ 3 * (σ 9 n : ℝ) := by
    have := mul_le_mul_of_nonneg_left (pow_le_sigma 9 n hn) (pow_nonneg hn_nn 3); nlinarith
  have m7 : (n : ℝ) ^ 4 * (σ 7 n : ℝ) ≤ 2 * (n : ℝ) ^ 11 := by
    have h : (σ 7 n : ℝ) ≤ 2 * (n : ℝ) ^ 7 := sigma_le_two_mul_pow (by norm_num) n hn
    nlinarith [mul_le_mul_of_nonneg_left h (pow_nonneg hn_nn 4)]
  have m5 : (n : ℝ) ^ 10 ≤ (n : ℝ) ^ 5 * (σ 5 n : ℝ) := by
    have := mul_le_mul_of_nonneg_left (pow_le_sigma 5 n hn) (pow_nonneg hn_nn 5); nlinarith
  nlinarith [m13, m11, m9, m7, m5, sq_nonneg ((n : ℝ)), pow_nonneg hn_nn 12,
             pow_nonneg hn_nn 10]

/-! ## Main theorem

`aSeq_neg_of_large` (`n ≥ 10000`) is proved using the sharp bound
`σₖ(n) ≤ 2 nᵏ` (k ≥ 2) — this is the elementary form of `σₖ(n) < ζ(k) nᵏ`,
following the user's hint. The proof reduces each correction term to a
multiple of `t¹⁴ / 1210809600` (one sixth of the dominant negative term),
showing the five corrections sum to at most `5 t¹⁴ / 1210809600 < t¹⁴ /
201801600`.

`aSeq_neg_of_small` remains open: with `ramanujanTau` treated as `opaque`
(per the sketch's "assume Deligne's bound without proof" directive), no
specific values such as `τ(1) = 1, τ(2) = -24, …` are accessible, so the
finitely-many small-`n` cases cannot be dispatched without either a
concrete definition or auxiliary axioms providing those values. Note that
Deligne alone permits `|τ(1)| < 2`, which is loose enough that `a_1 > 0`
is not contradicted by the bound (even though the actual `τ(1) = 1` makes
`a_1 < 0`).
-/

/-- For `t ≥ 1`: `t^((23:ℝ)/2) ≤ t^12`. -/
private lemma rpow_23_half_le_pow_12 (t : ℝ) (ht : 1 ≤ t) :
    t ^ ((23 : ℝ) / 2) ≤ t ^ 12 := by
  rw [← Real.rpow_natCast t 12]
  exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num)

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

/-- Effective bound: `aSeq n < 0` for `n ≥ 10000`.

Combines `xSeq_le_sharp`, `abs_ySeq_le`, `abs_zSeq_le` and Deligne's bound,
reducing the corrections to integer-power monomials and combining via
explicit per-term sub-bounds against `t¹⁴ / 1210809600` (one sixth of the
leading term). -/
lemma aSeq_neg_of_large (n : ℕ) (hn : 10000 ≤ n) : aSeq n < 0 := by
  have hn_pos : 1 ≤ n := by omega
  have ht_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have ht10000 : (10000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ht1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hc6_pos : 0 < c₆ := c₆_pos
  have hc7_abs : |c₇| = -c₇ := abs_of_neg c₇_neg
  have h_σ0 : (σ 0 n : ℝ) ≤ (n : ℝ) := by
    rw [ArithmeticFunction.sigma_zero_apply]; exact_mod_cast Nat.card_divisors_le_self n
  have h_y_le : 240 * c₆ * ySeq n ≤ 240 * c₆ * |ySeq n| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  have h_z_le : c₇ * zSeq n ≤ |c₇| * |zSeq n| := by
    rw [← abs_mul]; exact le_abs_self _
  have h_tau_le : c₆ * (τ n : ℝ) ≤ c₆ * |(τ n : ℝ)| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hc6_pos.le
  have h_y_int : 240 * c₆ * |ySeq n| ≤ 240 * c₆ * ((2 / 15) * (n : ℝ) ^ 12) := by
    have := (abs_ySeq_le n hn_pos).trans
      (by nlinarith [rpow_23_half_le_pow_12 (n:ℝ) ht1] :
        (2/15) * (n:ℝ)^((23:ℝ)/2) ≤ (2/15) * (n:ℝ)^12)
    gcongr
  have h_z_int : |c₇| * |zSeq n| ≤ |c₇| * ((2 / 15) * (n : ℝ) ^ 11) := by
    have := (abs_zSeq_le n hn_pos).trans
      (by nlinarith [rpow_21_half_le_pow_11 (n:ℝ) ht1] :
        (2/15) * (n:ℝ)^((21:ℝ)/2) ≤ (2/15) * (n:ℝ)^11)
    gcongr
  have h_tau_int : c₆ * |(τ n : ℝ)| ≤ c₆ * ((n : ℝ) * (n : ℝ) ^ 6) := by
    have hpow_pos : (0 : ℝ) ≤ (n : ℝ) ^ ((11 : ℝ) / 2) := Real.rpow_nonneg ht_pos.le _
    have h1 : |(τ n : ℝ)| ≤ (n : ℝ) * (n : ℝ) ^ 6 := by
      nlinarith [abs_ramanujanTau_lt n hn_pos, rpow_11_half_le_pow_6 (n : ℝ) ht1,
        ht_pos.le, mul_le_mul_of_nonneg_right h_σ0 hpow_pos]
    gcongr
  unfold aSeq
  have h_combined :
      xSeq n + 240 * c₆ * ySeq n + c₇ * zSeq n + c₆ * (τ n : ℝ) ≤
        (-(n : ℝ) ^ 14 / 201801600
         + 9062 * (n : ℝ) ^ 13 / 47809681920
         + 98 * (n : ℝ) ^ 11 / 25660800)
        + 240 * c₆ * ((2 / 15) * (n : ℝ) ^ 12)
        + |c₇| * ((2 / 15) * (n : ℝ) ^ 11)
        + c₆ * ((n : ℝ) * (n : ℝ) ^ 6) := by
    linarith [xSeq_le_sharp n hn_pos, h_y_le, h_y_int, h_z_le, h_z_int, h_tau_le, h_tau_int]
  refine lt_of_le_of_lt h_combined ?_
  have hc6_val : c₆ = 86619413 / 139015844352000 := rfl
  have hc7_abs_val : |c₇| = 118801 / 10746432000 := by rw [hc7_abs]; norm_num [c₇]
  rw [hc6_val, hc7_abs_val]
  set t : ℝ := (n : ℝ)
  -- Each positive correction is ≤ t^14 / (6 · 201801600); their total is ≤ 5 t^14 /
  -- (6 · 201801600) < t^14 / 201801600.
  have ht13_nn : (0 : ℝ) ≤ t ^ 13 := by positivity
  have ht12_nn : (0 : ℝ) ≤ t ^ 12 := by positivity
  have ht11_nn : (0 : ℝ) ≤ t ^ 11 := by positivity
  have ht7_nn : (0 : ℝ) ≤ t ^ 7 := by positivity
  have ht2 : (10000 : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by norm_num) ht10000 2
  have ht3 : (10000 : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht10000 3
  have ht7 : (10000 : ℝ) ^ 7 ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht10000 7
  have hb1 : 9062 * t ^ 13 / 47809681920 ≤ t ^ 14 / 1210809600 := by
    nlinarith [ht10000, ht13_nn, mul_le_mul_of_nonneg_right ht10000 ht13_nn]
  have hb2 : 240 * (86619413 / 139015844352000) * ((2 / 15) * t ^ 12) ≤
      t ^ 14 / 1210809600 :=
    by nlinarith [mul_le_mul_of_nonneg_right ht2 ht12_nn, ht12_nn]
  have hb3 : 98 * t ^ 11 / 25660800 ≤ t ^ 14 / 1210809600 := by
    nlinarith [mul_le_mul_of_nonneg_right ht3 ht11_nn, ht11_nn]
  have hb4 : 118801 / 10746432000 * ((2 / 15) * t ^ 11) ≤ t ^ 14 / 1210809600 := by
    nlinarith [mul_le_mul_of_nonneg_right ht3 ht11_nn, ht11_nn]
  have hb5 : 86619413 / 139015844352000 * (t * t ^ 6) ≤ t ^ 14 / 1210809600 := by
    nlinarith [mul_le_mul_of_nonneg_right ht7 ht7_nn, ht7_nn]
  -- Combined: -t^14/201801600 + 5·(t^14/1210809600) = -t^14/1210809600 < 0.
  have h_eq_neg : -t ^ 14 / 201801600 = -(6 * (t ^ 14 / 1210809600)) := by
    field_simp; ring
  have ht14_pos : 0 < t ^ 14 / 1210809600 := by positivity
  linarith [hb1, hb2, hb3, hb4, hb5, h_eq_neg, ht14_pos]

end
