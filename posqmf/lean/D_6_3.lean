import posqmf.lean.X_16_5_coeff

/-!
# Positivity of `(A_n + B_{n/2}) / 2688` for `n ≥ 5`

We define the integer-valued sequences

  `A_n = 10 n² σ₁(n) - 13 n σ₃(n) + 3 σ₅(n)`,
  `B_n = 120 n² σ₁(n) - 102 n σ₃(n) - 3 σ₅(n)`,

and the rational sequence

  `a_n = (A_n + B_{n/2}) / 2688`,

where `B_{n/2} = 0` if `n` is odd. We prove `a_n > 0` for every `n ≥ 5`.

The strategy follows the sketch in `D_6_3.tex`:

* Use the trivial bounds `nᵏ ≤ σₖ(n) ≤ 2 nᵏ` for `k ≥ 2` (and `n ≥ 1`).
* These yield, for `n ≥ 1`,
    - `A_n ≥ 3 n⁵ - 26 n⁴ + 10 n³`,
    - `B_n ≥ -6 n⁵ - 204 n⁴ + 120 n³`.
  When `n` is even with `n/2 = m`, the contribution of `B_m` to the leading
  power `n⁵` is `-3/16 · n⁵`, so the combined leading term is `(45/16) n⁵`,
  which dominates the negative `n⁴`-corrections for `n ≥ 14`.
* The remaining cases `5 ≤ n ≤ 13` are checked directly using the
  explicit values of `σ_k`.
-/

noncomputable section

open ArithmeticFunction Finset
open scoped sigma

namespace D63

/-! ## Sequences `A`, `B` and `a` -/

/-- `A_n = 10 n² σ₁(n) - 13 n σ₃(n) + 3 σ₅(n)`. -/
def A (n : ℕ) : ℝ :=
  10 * (n : ℝ) ^ 2 * (σ 1 n : ℝ) - 13 * (n : ℝ) * (σ 3 n : ℝ) + 3 * (σ 5 n : ℝ)

/-- `B_n = 120 n² σ₁(n) - 102 n σ₃(n) - 3 σ₅(n)`. -/
def B (n : ℕ) : ℝ :=
  120 * (n : ℝ) ^ 2 * (σ 1 n : ℝ) - 102 * (n : ℝ) * (σ 3 n : ℝ) - 3 * (σ 5 n : ℝ)

/-- `a_n = (A_n + B_{n/2}) / 2688`, with `B_{n/2} = 0` if `n` is odd. -/
def aSeq (n : ℕ) : ℝ :=
  (A n + (if Even n then B (n / 2) else 0)) / 2688

/-! ## Lower bounds on `A` and `B` -/

private lemma A_lower (n : ℕ) (hn : 1 ≤ n) :
    3 * (n : ℝ) ^ 5 - 26 * (n : ℝ) ^ 4 + 10 * (n : ℝ) ^ 3 ≤ A n := by
  unfold A
  have hσ1 : (n : ℝ) ≤ (σ 1 n : ℝ) := by simpa using pow_le_sigma 1 n hn
  have hσ3 : (σ 3 n : ℝ) ≤ 2 * (n : ℝ) ^ 3 := sigma_le_two_mul_pow (by norm_num) n hn
  have hσ5 : (n : ℝ) ^ 5 ≤ (σ 5 n : ℝ) := pow_le_sigma 5 n hn
  nlinarith [hσ1, hσ3, hσ5, sq_nonneg (n : ℝ), pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 2,
    mul_le_mul_of_nonneg_left hσ1 (by positivity : (0:ℝ) ≤ 10 * (n:ℝ)^2),
    mul_le_mul_of_nonneg_left hσ3 (by positivity : (0:ℝ) ≤ 13 * (n:ℝ))]

private lemma B_lower (m : ℕ) (hm : 1 ≤ m) :
    -6 * (m : ℝ) ^ 5 - 204 * (m : ℝ) ^ 4 + 120 * (m : ℝ) ^ 3 ≤ B m := by
  unfold B
  have hσ1 : (m : ℝ) ≤ (σ 1 m : ℝ) := by simpa using pow_le_sigma 1 m hm
  have hσ3 : (σ 3 m : ℝ) ≤ 2 * (m : ℝ) ^ 3 := sigma_le_two_mul_pow (by norm_num) m hm
  have hσ5 : (σ 5 m : ℝ) ≤ 2 * (m : ℝ) ^ 5 := sigma_le_two_mul_pow (by norm_num) m hm
  nlinarith [hσ1, hσ3, hσ5, pow_nonneg (Nat.cast_nonneg (α := ℝ) m) 2,
    mul_le_mul_of_nonneg_left hσ1 (by positivity : (0:ℝ) ≤ 120 * (m:ℝ)^2),
    mul_le_mul_of_nonneg_left hσ3 (by positivity : (0:ℝ) ≤ 102 * (m:ℝ))]

/-! ## Positivity for large `n` -/

private lemma A_pos_of_odd_large (n : ℕ) (hn : 9 ≤ n) : 0 < A n := by
  have ht : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ht_nn : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hdom : 27 * (n : ℝ) ^ 4 ≤ 3 * (n : ℝ) ^ 5 := by
    nlinarith [pow_nonneg ht_nn 4, ht]
  nlinarith [A_lower n (by omega), hdom, pow_nonneg ht_nn 3, pow_pos (by linarith : (0:ℝ) < n) 4]

private lemma A_add_B_pos_of_even_large (n : ℕ) (hn : 14 ≤ n) (he : Even n) :
    0 < A n + B (n / 2) := by
  obtain ⟨m, hm_eq⟩ := he
  have hcast : (n : ℝ) = 2 * (m : ℝ) := by exact_mod_cast (by omega : n = 2 * m)
  have ht : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 7 ≤ m)
  rw [show n / 2 = m by omega]
  have key : 90 * (m : ℝ) ^ 5 - 620 * (m : ℝ) ^ 4 + 200 * (m : ℝ) ^ 3 ≤ A n + B m := by
    have h := add_le_add (A_lower n (by omega)) (B_lower m (by omega))
    have e : 3 * (n : ℝ) ^ 5 - 26 * (n : ℝ) ^ 4 + 10 * (n : ℝ) ^ 3 +
        (-6 * (m : ℝ) ^ 5 - 204 * (m : ℝ) ^ 4 + 120 * (m : ℝ) ^ 3) =
        90 * (m : ℝ) ^ 5 - 620 * (m : ℝ) ^ 4 + 200 * (m : ℝ) ^ 3 := by rw [hcast]; ring
    linarith
  nlinarith [key, pow_nonneg (by linarith : (0:ℝ) ≤ m) 3, pow_pos (by linarith : (0:ℝ) < m) 4]

private lemma aSeq_pos_of_large (n : ℕ) (hn : 14 ≤ n) : 0 < aSeq n := by
  rw [aSeq, lt_div_iff₀ (by norm_num : (0:ℝ) < 2688), zero_mul]
  by_cases he : Even n
  · simpa [he] using A_add_B_pos_of_even_large n hn he
  · simpa [he] using A_pos_of_odd_large n (by omega)

/-! ## Positivity for small `n`: `5 ≤ n ≤ 13` (direct computation) -/

private lemma aSeq_pos_of_small (n : ℕ) (hn : 5 ≤ n) (hn' : n ≤ 13) : 0 < aSeq n := by
  interval_cases n <;> (unfold aSeq A B; norm_num [Nat.even_iff,
    show (σ 1 3 : ℕ) = 4 by decide, show (σ 3 3 : ℕ) = 28 by decide,
    show (σ 5 3 : ℕ) = 244 by decide, show (σ 1 4 : ℕ) = 7 by decide,
    show (σ 3 4 : ℕ) = 73 by decide, show (σ 5 4 : ℕ) = 1057 by decide,
    show (σ 1 5 : ℕ) = 6 by decide, show (σ 3 5 : ℕ) = 126 by decide,
    show (σ 5 5 : ℕ) = 3126 by decide, show (σ 1 6 : ℕ) = 12 by decide,
    show (σ 3 6 : ℕ) = 252 by decide, show (σ 5 6 : ℕ) = 8052 by decide,
    show (σ 1 7 : ℕ) = 8 by decide, show (σ 3 7 : ℕ) = 344 by decide,
    show (σ 5 7 : ℕ) = 16808 by decide, show (σ 1 8 : ℕ) = 15 by decide,
    show (σ 3 8 : ℕ) = 585 by decide, show (σ 5 8 : ℕ) = 33825 by decide,
    show (σ 1 9 : ℕ) = 13 by decide, show (σ 3 9 : ℕ) = 757 by decide,
    show (σ 5 9 : ℕ) = 59293 by decide, show (σ 1 10 : ℕ) = 18 by decide,
    show (σ 3 10 : ℕ) = 1134 by decide, show (σ 5 10 : ℕ) = 103158 by decide,
    show (σ 1 11 : ℕ) = 12 by decide, show (σ 3 11 : ℕ) = 1332 by decide,
    show (σ 5 11 : ℕ) = 161052 by decide, show (σ 1 12 : ℕ) = 28 by decide,
    show (σ 3 12 : ℕ) = 2044 by decide, show (σ 5 12 : ℕ) = 257908 by decide,
    show (σ 1 13 : ℕ) = 14 by decide, show (σ 3 13 : ℕ) = 2198 by decide,
    show (σ 5 13 : ℕ) = 371294 by decide])

/-! ## Main theorem -/

/-- Positivity of `a_n = (A_n + B_{n/2}) / 2688` for `n ≥ 5`. -/
theorem aSeq_pos (n : ℕ) (hn : 5 ≤ n) : 0 < aSeq n :=
  if h : 14 ≤ n then aSeq_pos_of_large n h else aSeq_pos_of_small n hn (by omega)

end D63

end
