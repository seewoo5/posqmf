import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

def aCoeffs : Fin 9 → ℤ
  | 0 => 1
  | 1 => 502
  | 2 => 14608
  | 3 => 88234
  | 4 => 156190
  | 5 => 88234
  | 6 => 14608
  | 7 => 502
  | 8 => 1

def bCoeffs : Fin 9 → ℤ
  | 0 => 8
  | 1 => 1968
  | 2 => 32368
  | 3 => 90608
  | 4 => 0
  | 5 => -90608
  | 6 => -32368
  | 7 => -1968
  | 8 => -8

noncomputable def f (t : ℝ) : ℝ :=
  ∑ k : Fin 9, (aCoeffs k : ℝ) * t * Real.exp (k * t) +
  ∑ k : Fin 9, (bCoeffs k : ℝ) * Real.exp (k * t)

private lemma coeff_nonneg_large_n (n : ℕ) (hn : 64 ≤ n) (k : Fin 9) :
    0 ≤ (k : ℕ) * (bCoeffs k : ℝ) + n * (aCoeffs k : ℝ) := by
  fin_cases k <;> simp only [aCoeffs, bCoeffs] <;> norm_num at hn ⊢ <;>
  first
  | (norm_cast at hn ⊢; nlinarith)
  | (cases n with | zero => contradiction | succ n =>
      push_cast at hn ⊢; nlinarith)

lemma term_nonneg_large_n (n : ℕ) (hn : 64 ≤ n) (k : Fin 9) :
    0 ≤ (k : ℕ)^n * (bCoeffs k : ℝ) + n * (k : ℕ)^(n-1) * (aCoeffs k : ℝ) := by
  rw [show (k : ℕ)^n * (bCoeffs k : ℝ) + n * (k : ℕ)^(n-1) * (aCoeffs k : ℝ) =
    (k : ℕ)^(n-1) * ((k : ℕ) * (bCoeffs k : ℝ) + n * (aCoeffs k : ℝ)) from by
    cases n with | zero => omega | succ n => simp [pow_succ]; ring]
  exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (coeff_nonneg_large_n n hn k)

lemma term_one_pos_large_n (n : ℕ) (hn : 64 ≤ n) :
    0 < (1 : ℕ)^n * (bCoeffs 1 : ℝ) + n * (1 : ℕ)^(n-1) * (aCoeffs 1 : ℝ) := by
  simp only [aCoeffs, bCoeffs]; positivity

noncomputable def derivSumAtZero (n : ℕ) : ℝ :=
  ∑ k : Fin 9, ((k : ℕ)^n * (bCoeffs k : ℝ) + n * (k : ℕ)^(n-1) * (aCoeffs k : ℝ))

def derivSumInt (n : ℕ) : ℤ :=
  ∑ k : Fin 9, ((k : ℕ)^n * bCoeffs k + n * (k : ℕ)^(n-1) * aCoeffs k)

lemma derivSum_eq_cast (n : ℕ) : derivSumAtZero n = (derivSumInt n : ℝ) := by
  simp [derivSumAtZero, derivSumInt]

lemma derivSumInt_pos_small (n : ℕ) (hn1 : 1 ≤ n) (hn2 : n < 64) :
    0 < derivSumInt n := by
  interval_cases n <;> decide

lemma factor_A_n_k (n : ℕ) (hn : 1 ≤ n) (k : Fin 9) :
    ((n : ℝ) * (k.val : ℝ)^(n-1) * (aCoeffs k : ℝ) + (k.val : ℝ)^n * (bCoeffs k : ℝ)) =
    (k.val : ℝ)^(n-1) * ((n : ℝ) * (aCoeffs k : ℝ) + (k.val : ℝ) * (bCoeffs k : ℝ)) := by
  rw [show (k.val : ℝ) ^ n = (k.val : ℝ) ^ (n - 1) * k.val by
    conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]]
  ring

lemma coeff_nonneg_high_deriv (n : ℕ) (hn : 64 ≤ n) (k : Fin 9) (hk : 0 < k.val)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ ((n : ℝ) * (k.val : ℝ)^(n-1) * (aCoeffs k) + (k.val : ℝ)^n * (bCoeffs k)) +
        (k.val : ℝ)^n * (aCoeffs k) * t := by
  rw [factor_A_n_k n (by omega) k]
  have h_coeff : 0 ≤ (n : ℝ) * (aCoeffs k : ℝ) + (k.val : ℝ) * (bCoeffs k : ℝ) := by
    convert coeff_nonneg_large_n n hn k using 1; ring
  have ha : (0 : ℝ) < aCoeffs k := by exact_mod_cast (by fin_cases k <;> simp_all [aCoeffs])
  exact add_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) h_coeff) (by positivity)

lemma f_smooth : ContDiff ℝ ⊤ f := by unfold f; fun_prop

lemma iteratedDeriv_t_mul_exp (n : ℕ) (c t : ℝ) :
    iteratedDeriv n (fun s => s * Real.exp (c * s)) t =
      ((n : ℝ) * c^(n-1) + c^n * t) * Real.exp (c * t) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    have h : HasDerivAt (fun s => (↑n * c ^ (n - 1) + c ^ n * s) * Real.exp (c * s)) _ t :=
      ((hasDerivAt_const t (↑n * c ^ (n - 1))).add
        ((hasDerivAt_id t).const_mul (c ^ n))).mul
        (((hasDerivAt_id t).const_mul c).exp)
    rw [h.deriv]; simp only [id, zero_add, mul_one, Pi.add_apply]
    cases n with
    | zero => simp; ring
    | succ m => simp only [Nat.succ_sub_one]; push_cast; ring

private lemma t_mul_exp_contDiff (c : ℝ) :
    ContDiff ℝ ⊤ (fun s => s * Real.exp (c * s)) := by fun_prop

lemma iteratedDeriv_a_term (n : ℕ) (_hn : 1 ≤ n) (k : Fin 9) (t : ℝ) :
    iteratedDeriv n (fun s => (aCoeffs k : ℝ) * s * Real.exp (k * s)) t =
      (aCoeffs k : ℝ) * ((n : ℝ) * (k.val : ℝ)^(n-1) + (k.val : ℝ)^n * t) *
        Real.exp (k.val * t) := by
  have heq : (fun s => (aCoeffs k : ℝ) * s * Real.exp (↑↑k * s)) =
             (fun s => (aCoeffs k : ℝ) * (s * Real.exp (↑↑k * s))) := by ext s; ring
  rw [heq, iteratedDeriv_const_mul ((t_mul_exp_contDiff ↑↑k).contDiffAt.of_le le_top),
      iteratedDeriv_t_mul_exp n ↑↑k t]; ring

private lemma exp_contDiff (c : ℝ) :
    ContDiff ℝ ⊤ (fun s => Real.exp (c * s)) := by fun_prop

lemma iteratedDeriv_b_term (n : ℕ) (k : Fin 9) (t : ℝ) :
    iteratedDeriv n (fun s => (bCoeffs k : ℝ) * Real.exp (k * s)) t =
      (bCoeffs k : ℝ) * (k.val : ℝ)^n * Real.exp (k.val * t) := by
  rw [iteratedDeriv_const_mul ((exp_contDiff ↑↑k).contDiffAt.of_le le_top)]
  simp [iteratedDeriv_exp_const_mul]; ring

private lemma a_term_contDiff (k : Fin 9) :
    ContDiff ℝ ⊤ (fun s => (aCoeffs k : ℝ) * s * Real.exp (k * s)) := by
  fun_prop

private lemma b_term_contDiff (k : Fin 9) :
    ContDiff ℝ ⊤ (fun s => (bCoeffs k : ℝ) * Real.exp (k * s)) := by fun_prop

lemma iteratedDeriv_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (n : ℕ) (t : ℝ) (hf : ∀ i ∈ s, ContDiff ℝ ⊤ (f i)) :
    iteratedDeriv n (fun x => ∑ i ∈ s, f i x) t =
    ∑ i ∈ s, iteratedDeriv n (f i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, iteratedDeriv_const]; split_ifs <;> rfl
  | @insert a s' ha ih =>
    have eq_fun : (fun x => ∑ i ∈ insert a s', f i x) = f a + (fun x => ∑ i ∈ s', f i x) := by
      ext x; simp only [Finset.sum_insert ha, Pi.add_apply]
    rw [eq_fun, iteratedDeriv_add
      ((hf a (Finset.mem_insert_self a s')).contDiffAt.of_le le_top)
      ((ContDiff.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)).contDiffAt.of_le le_top),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi), Finset.sum_insert ha]

lemma iteratedDeriv_sum_eq_sum (n : ℕ) (t : ℝ) :
    iteratedDeriv n f t =
      ∑ k : Fin 9, iteratedDeriv n (fun s => (aCoeffs k : ℝ) * s * Real.exp (k * s)) t +
      ∑ k : Fin 9, iteratedDeriv n (fun s => (bCoeffs k : ℝ) * Real.exp (k * s)) t := by
  have f_eq : f = (fun s => ∑ k : Fin 9, (aCoeffs k : ℝ) * s * Real.exp (k * s)) +
                  (fun s => ∑ k : Fin 9, (bCoeffs k : ℝ) * Real.exp (k * s)) := by
    ext s; simp only [Pi.add_apply, f]
  rw [f_eq, iteratedDeriv_add
    ((ContDiff.sum fun k _ => a_term_contDiff k).contDiffAt.of_le le_top)
    ((ContDiff.sum fun k _ => b_term_contDiff k).contDiffAt.of_le le_top),
    iteratedDeriv_finset_sum _ _ _ _ fun k _ => a_term_contDiff k,
    iteratedDeriv_finset_sum _ _ _ _ fun k _ => b_term_contDiff k]

lemma iteratedDeriv_f_formula (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    iteratedDeriv n f t =
      ∑ k : Fin 9, (((n : ℝ) * (k.val : ℝ)^(n-1) * (aCoeffs k) + (k.val : ℝ)^n * (bCoeffs k)) +
                    (k.val : ℝ)^n * (aCoeffs k) * t) * Real.exp (k.val * t) := by
  rw [iteratedDeriv_sum_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by
    rw [iteratedDeriv_a_term n hn k t, iteratedDeriv_b_term n k t]; ring

lemma term_k1_pos_high_deriv (n : ℕ) (t : ℝ) (ht : 0 < t) :
    let k : Fin 9 := ⟨1, by omega⟩
    0 < (((n : ℝ) * (k.val : ℝ)^(n-1) * (aCoeffs k) + (k.val : ℝ)^n * (bCoeffs k)) +
         (k.val : ℝ)^n * (aCoeffs k) * t) * Real.exp (k.val * t) := by
  simp only [aCoeffs, bCoeffs]; positivity

lemma iteratedDeriv_pos_high (n : ℕ) (hn : 64 ≤ n) (t : ℝ) (ht : 0 < t) :
    0 < iteratedDeriv n f t := by
  rw [iteratedDeriv_f_formula n (by omega) t]
  exact Finset.sum_pos' (fun k _ => by
    by_cases hk : k.val = 0
    · simp [show (k.val : ℝ) = 0 from by simp [hk], zero_pow (by omega : n - 1 ≠ 0),
        zero_pow (by omega : n ≠ 0)]
    · exact mul_nonneg (coeff_nonneg_high_deriv n hn k (Nat.pos_of_ne_zero hk) t (le_of_lt ht))
        (le_of_lt (Real.exp_pos _)))
    ⟨⟨1, by omega⟩, Finset.mem_univ _, term_k1_pos_high_deriv n t ht⟩

lemma iteratedDeriv_f_zero_eq (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv n f 0 = derivSumAtZero n := by
  rw [iteratedDeriv_f_formula n hn 0]
  simp only [mul_zero, add_zero, Real.exp_zero, mul_one, derivSumAtZero]
  congr 1; ext k; ring

lemma iteratedDeriv_f_zero_pos (n : ℕ) (hn : 1 ≤ n) : 0 < iteratedDeriv n f 0 := by
  rw [iteratedDeriv_f_zero_eq n hn]
  rcases le_or_gt 64 n with h64 | h64
  · exact Finset.sum_pos' (fun k _ => term_nonneg_large_n n h64 k)
      ⟨⟨1, by omega⟩, Finset.mem_univ _, term_one_pos_large_n n h64⟩
  · exact derivSum_eq_cast n ▸ Int.cast_pos.mpr (derivSumInt_pos_small n hn h64)

lemma integral_iteratedDeriv_pos (n : ℕ) (t : ℝ) (ht : 0 < t)
    (h_next : ∀ s : ℝ, 0 < s → 0 < iteratedDeriv (n+1) f s) :
    0 < ∫ s in (0)..t, iteratedDeriv (n+1) f s :=
  intervalIntegral.integral_pos ht
    (f_smooth.continuous_iteratedDeriv (n + 1) le_top).continuousOn
    (fun x hx => le_of_lt (h_next x hx.1))
    ⟨t / 2, ⟨by linarith, by linarith⟩, h_next (t / 2) (by linarith)⟩

lemma pos_of_next_deriv_pos (n : ℕ) (hn : 1 ≤ n)
    (h_next : ∀ s : ℝ, 0 < s → 0 < iteratedDeriv (n+1) f s) :
    ∀ t : ℝ, 0 < t → 0 < iteratedDeriv n f t := by
  intro t ht
  have hdiff := f_smooth.differentiable_iteratedDeriv n (by simp)
  have h_deriv : ∀ x ∈ Set.uIcc 0 t,
      HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f x) x := by
    intro x _; rw [iteratedDeriv_succ]; exact (hdiff x).hasDerivAt
  linarith [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv
    ((f_smooth.continuous_iteratedDeriv (n+1) (by simp)).intervalIntegrable 0 t),
    iteratedDeriv_f_zero_pos n hn, integral_iteratedDeriv_pos n t ht h_next]

lemma iteratedDeriv_pos_aux (n : ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) (hn : 64 ≤ n)
    (t : ℝ) (ht : 0 < t) : 0 < iteratedDeriv m f t := by
  obtain hm64 | hm64 := le_or_gt 64 m
  · exact iteratedDeriv_pos_high m hm64 t ht
  · exact pos_of_next_deriv_pos m hm1
      (fun s hs =>
        iteratedDeriv_pos_aux n (m + 1) (by omega) (by omega) hn s hs) t ht
termination_by n - m

lemma deriv_f_pos (t : ℝ) (ht : 0 < t) : 0 < deriv f t := by
  rw [← iteratedDeriv_one]
  exact iteratedDeriv_pos_aux 64 1 (by omega) (by omega) (by omega) t ht

lemma f_zero : f 0 = 0 := by
  simp only [f, mul_zero, Real.exp_zero, mul_one,
             Finset.sum_const_zero, zero_add]
  norm_cast

/- Positivity of $f(t)$ -/
theorem f_pos (t : ℝ) (ht : 0 < t) : 0 < f t := by
  have hftc := intervalIntegral.integral_deriv_eq_sub
    (fun x _ => f_smooth.differentiable le_top x)
    ((f_smooth.continuous_deriv le_top).intervalIntegrable 0 t)
  rw [f_zero, sub_zero] at hftc; rw [← hftc]
  exact intervalIntegral.integral_pos ht
    (f_smooth.continuous_deriv le_top).continuousOn
    (fun x hx => le_of_lt (deriv_f_pos x hx.1))
    ⟨t, by simp [le_of_lt ht], deriv_f_pos t ht⟩
