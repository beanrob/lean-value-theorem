import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import LeanValueTheorem.Sequences


-- Definition for l being the limit of the sequence a
def is_lim_seq (a : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, N > 0 ∧ (∀ n, n ≥ N → |a n - l| < ε)

-- Definition for l being the limit of the function f : D → ℝ at c

def is_lim_fun (D : Set ℝ) (f : ℝ → ℝ) (c : ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, |x - c| < δ → |f x - l| < ε

-- Algebra of limtis for sequences (for sums, products and quotients)
lemma seq_sum
  (f g : ℕ → ℝ)
  (a b : ℝ)
  (hf : is_sequence f)
  (hg : is_sequence g)
  (hfa : is_lim_seq f a)
  (hgb : is_lim_seq g b) :
  (is_sequence (fun n => f n + g n)) ∧
  (is_lim_seq (fun n => f n + g n) (a + b)) := by

  constructor
  · exact hf;
  · unfold is_lim_seq at hfa hgb
    intro (ε : ℝ) (hε : ε > 0)

    let ε' := ε / 3
    have hε' : ε' > 0 := div_pos hε (by norm_num)

    rcases hfa ε' hε' with ⟨N1, hN1, hfa_prop⟩
    rcases hgb ε' hε' with ⟨N2, hN2, hgb_prop⟩

    let N := max N1 N2
    use N

    have hn1 : N1 ≤ N := le_max_left N1 N2
    have hn2 : N2 ≤ N := le_max_right N1 N2
    have hN : 0 < N := le_trans hN1 hn1

    constructor
    · exact hN;
    · intro (n : ℕ) (hn : n ≥ N)
      have hn1' : n ≥ N1 := le_trans hn1 hn
      have hn2' : n ≥ N2 := le_trans hn2 hn
      simp

      have h1 : abs (f n - a) < ε' := hfa_prop n hn1'
      have h2 : abs (g n - b) < ε' := hgb_prop n hn2'

      have h : abs ((f n - a) + (g n - b)) ≤ abs (f n - a) + abs (g n - b) := by
        exact abs_add_le (f n - a) (g n - b)

      have h' : abs (f n - a) + abs (g n - b) ≤  ε' + ε' := le_of_lt (add_lt_add h1 h2)
      have last_step : |f n + g n - (a + b)| ≤ ε' + ε':=
        have r : (f n - a) + (g n - b) = f n + g n - (a + b) := by linarith
        calc
          |f n + g n - (a + b)|
          _ = |(f n - a) + (g n - b)| := by rw [r]
          _ ≤ abs (f n - a) + abs (g n - b) := h
          _ ≤ ε' + ε' := h'

      have last_last_step : ε' + ε' < ε := by
        calc
          ε' + ε'
          _ = (ε / 3) + (ε / 3) := by simp [ε']
          _ < ε := by linarith

      exact lt_of_lt_of_le' last_last_step last_step

lemma seq_scalar_prod
  (f : ℕ → ℝ)
  (a b : ℝ)
  (hf : is_sequence f)
  (hfa : is_lim_seq f a) :
  (is_sequence (fun n => b * f n)) ∧
  (is_lim_seq (fun n => b * f n) (b * a)) := by
  constructor
  · exact hf;
  · by_cases hb : b = 0
    · unfold is_lim_seq at hfa
      intro (ε : ℝ) (hε : ε > 0)
      use 1
      simp
      intro (n : ℕ) (hn : n ≥ 1)
      simp [hb]
      exact hε

    · intro (ε : ℝ) (hε : ε > 0)
      let ε' := ε /|b|
      have abs_b_nonzero : |b| ≠ 0 := by simp [hb]
      have abs_b_pos : |b| > 0 := lt_of_le_of_ne' (abs_nonneg b) abs_b_nonzero
      have hε' : ε' > 0 := div_pos hε abs_b_pos
      rcases hfa ε' hε' with ⟨N, hN, hfa_prop⟩
      use N

      constructor
      · exact hN;
      · intro (n : ℕ) (hn : n ≥ N)
        simp
        have h : |f n - a| < ε' := hfa_prop n hn

        have shuffle : b * f n - b * a = b * (f n - a) := by linarith
        calc
          |b * f n - b * a|
          _ = |b * (f n - a)| := by simp [shuffle]
          _ = |b| * |f n - a| := by apply abs_mul
          _ < |b| * ε' := mul_lt_mul_of_pos_left h abs_b_pos
          _ = |b| * (ε / |b|) := by simp [ε']
          _ = |b| * (ε * |b|⁻¹) := by simp [div_eq_mul_inv]
          _ = |b| * ε * |b|⁻¹ := by simp [mul_assoc]
          _ = ε * |b| * |b|⁻¹ := by simp [mul_comm]
          _ = ε * (1 : ℝ) := by simp [abs_b_nonzero]
          _ = ε := by simp

lemma seq_prod_special
  (f g : ℕ → ℝ)
  (hf : is_sequence f)
  (hg : is_sequence g)
  (hfa : is_lim_seq f 0)
  (hgb : is_lim_seq g 0) :
  (is_sequence (fun n => f n * g n)) ∧
  (is_lim_seq (fun n => f n * g n) (0)) := by

  constructor
  · exact hf;
  · unfold is_lim_seq at hfa hgb
    intro (ε : ℝ) (hε : ε > 0)

    let ε' := ε^(1/2)
    have hε' : ε' > 0 := sorry -- exponentiation properties

    rcases hfa ε' hε' with ⟨N1, hN1, hfa_prop⟩
    rcases hgb ε' hε' with ⟨N2, hN2, hgb_prop⟩

    let N := max N1 N2
    use N

    have hn1 : N1 ≤ N := le_max_left N1 N2
    have hn2 : N2 ≤ N := le_max_right N1 N2
    have hN : 0 < N := le_trans hN1 hn1

    constructor
    · exact hN;
    · intro (n : ℕ) (hn : n ≥ N)
      have hn1' : n ≥ N1 := le_trans hn1 hn
      have hn2' : n ≥ N2 := le_trans hn2 hn
      simp

      have shuffle_f : f n - 0 = f n := by simp
      have shuffle_g : g n - 0 = g n := by simp

      have h1 : |f n| < ε' := by simpa [shuffle_f] using hfa_prop n hn1'
      have h2 : |g n| < ε' := by simpa [shuffle_g] using hgb_prop n hn2'

      calc
        |f n| * |g n|
        _ < ε' * ε' := mul_lt_mul_of_nonneg h1 h2 (abs_nonneg (f n)) (abs_nonneg (g n))
        _ = ε^(1/2) * ε^(1/2) := by simp [ε']
        _ = ε := sorry -- exponentiation properties

lemma seq_prod
  (f g : ℕ → ℝ)
  (a b : ℝ)
  (hf : is_sequence f)
  (hg : is_sequence g)
  (hfa : is_lim_seq f a)
  (hgb : is_lim_seq g b) :
  (is_sequence (fun n => f n * g n)) ∧
  (is_lim_seq (fun n => f n * g n) (a * b)) := by
  constructor
  · exact hf;
  · unfold is_lim_seq at hfa hgb

    have reverse_trivial_limit
      (f : ℕ → ℝ) (a : ℝ)
      (hf : is_sequence (fun n => f n - a))
      (hfa : is_lim_seq (fun n => f n - a) 0) :
      (is_sequence f) ∧
      (is_lim_seq f a) := by sorry

    have trivial_limit
      (f : ℕ → ℝ) (a : ℝ)
      (hf : is_sequence f)
      (hfa : is_lim_seq f a) :
      (is_sequence (fun n => f n - a)) ∧
      (is_lim_seq (fun n => f n - a) 0) := by

      have hc : is_sequence (fun n => -a) := by trivial
      have hca : is_lim_seq (fun n => -a) (-a) := by sorry
      have h := (seq_sum f (fun n => -a) a (-a) hf hc hfa hca).2

      constructor
      · trivial
      · simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

    let seq1 := fun n => (f n - a)
    let seq2 := fun n => (g n - b)


    have shuffle : (fun n => f n * g n - a * b) =
     (fun n => seq1 n * seq2 n) +
     (fun n => a * seq2 n) +
     (fun n => b * seq1 n) := by sorry
      -- funext n
      -- simp [sub_mul, mul_sub, mul_comm, mul_left_comm, mul_assoc]

    have seq1_lim : is_lim_seq seq1 0 := by
      exact (trivial_limit f a hf hfa).2
    have seq2_lim : is_lim_seq seq2 0 := by
      exact (trivial_limit g b hg hgb).2

    have seq_mul_12 : is_lim_seq (fun n => (seq1 n  * seq2 n)) 0 := by
      exact (seq_prod_special seq1 seq2 (by trivial) (by trivial) seq1_lim seq2_lim).2

    have seq_mul_a2 : is_lim_seq (fun n => a * (seq2 n)) 0 := by
      simpa [mul_zero] using (seq_scalar_prod seq2 0 a (by trivial) seq2_lim).2


    have seq_mul_1b : is_lim_seq (fun n => b * (seq1 n)) 0 := by
      simpa [mul_zero] using (seq_scalar_prod seq1 0 b (by trivial) seq1_lim).2

    -- : is_lim_seq (fun n => (seq1 n * seq2 n) + (a * seq2 n) + (b * seq1 n)) 0
    have hshuffle_lim := by
      have h12 := by
        simpa using (
          seq_sum
            (fun n => seq1 n * seq2 n)
            (fun n => a * seq2 n)
            0 0 (by trivial) (by trivial)
            seq_mul_12 seq_mul_a2
        ).2

      simpa using (
        seq_sum
          (fun n => (seq1 n * seq2 n + a * seq2 n))
          (fun n => b * seq1 n)
          0 0 (by trivial) (by trivial)
          h12 seq_mul_1b
      ).2

    have limit_equality := congrArg (fun x => is_lim_seq x 0) shuffle
    have last_step : is_lim_seq (fun n => f n * g n - a * b) 0 := by
      simpa [limit_equality] using hshuffle_lim

    exact (reverse_trivial_limit (fun n => f n * g n) (a * b) (by trivial) last_step).2

lemma seq_recip
  (g : ℕ → ℝ) (b : ℝ)
  (hg : is_sequence g)
  (hgb : is_lim_seq g b)
  (hbz : b ≠ 0) :
  (is_sequence (fun n => 1 / g n)) ∧
  (is_lim_seq (fun n => 1 / g n) (1 / b)) := by
  constructor
  · trivial
  · unfold is_lim_seq at hgb
    intro (ε : ℝ) (hψ : ε > 0)

    let ε1 := (b ^ 2) / 2
    have constantpos : (b^2) / 2 > 0 := by sorry
    have recippos : 2 / (b^2) > 0 := by sorry
    have hε1 : ε1 > 0 := by sorry

    have bgn := (seq_scalar_prod g b b hg hgb).2
    rcases bgn ε1 hε1 with ⟨N1, hN1, hgb_prop1⟩

    have sub (n : ℕ)  (hnN1 : n ≥ N1) : b^2 / 2 < b * g n := by
      linarith [(abs_lt.mp (by simpa [ε1] using hgb_prop1 n hnN1)).1]

    have shuffle1 (n : ℕ) : |(1 / (g n)) - (1 / b)| = |b - g n| / |b * g n| := by
      have somehow (n : ℕ) : g n ≠ 0 := by sorry
      have hnbz : -b ≠ 0 := (neg_ne_zero.mpr) hbz
      have this := one_div_add_one_div (somehow n) hnbz
      calc
      |(1 / (g n)) - (1 / b)|
      _ = |(1 / (g n)) + (-(1 / b))| := by simp [sub_eq_add_neg]
      _ = |(1 / (g n)) + (1 / -b)| := by simp [div_neg]
      _ = |(g n + -b) / (g n * -b)| := by rw [this]
      _ = |(g n + -b)| / |(g n * -b)| := by rw [abs_div]
      _ = |-(b - g n)| / |(g n * -b)| := by rw [show (g n + -b) = -(b - g n) by linarith]
      _ = |-(b - g n)| / |-(g n * b)| := by rw [show (g n * -b) = -(g n * b) by linarith]
      _ = |b - g n| / |g n * b| := by rw [abs_neg, abs_neg]
      _ = |b - g n| / |b * g n| := by rw [mul_comm (g n) b]

    have shuffle2 (n : ℕ) (hnN1 : n ≥ N1) : |b - g n| / |b * g n| ≤ (2 / b ^ 2) * |g n - b| := by
      have shufflesub := sub n hnN1
      have ineq1 : (b^2) / 2 < |b * g n| := lt_of_lt_of_le shufflesub (le_abs_self (b * g n))
      have ineq2 : 1 / |b * g n| < 2 / b^2 := by
        simpa [one_div_div] using (one_div_lt_one_div_of_lt constantpos ineq1)

      calc
        |b - g n| / |b * g n|
        _ ≤ |b - g n| * (1 / |b * g n|) := by rw [div_eq_mul_one_div |b - g n| |b * g n|]
        _ ≤ |b - g n| * (2 / b^2) :=
          mul_le_mul_of_nonneg_left (le_of_lt ineq2) (abs_nonneg (b - g n))
        _ = |-(g n - b)| * (2 / b ^ 2) := by rw [show b - g n = -(g n - b) by linarith]
        _ = |g n - b| * (2 / b ^ 2) := by rw [abs_neg]
        _ = (2 / b ^ 2) * |g n - b| := by simp [mul_comm]

    let ε2 := ε * ((b ^ 2) / 4)
    have hε2 : ε2 > 0 := by sorry
    rcases hgb ε2 hε2 with ⟨N2, hN2, hgb_prop2⟩

    let N := max N1 N2
    have hN : N > 0 := lt_of_lt_of_le hN1 (le_max_left N1 N2)
    use N

    constructor
    · exact hN
    · intro (n : ℕ) (hn : n ≥ N)
      simp
      have hcz : 2/b^2 ≠ 0 := by linarith
      calc
        |(g n)⁻¹ - b⁻¹|
        _ = |(1 / g n) - (1 / b)| := by simp [one_div, one_div]
        _ = |b - g n| / |b * g n| := shuffle1 n
        _ ≤ (2 / b ^ 2) * |g n - b| := shuffle2 n (le_trans (le_max_left N1 N2) hn)
        _ ≤ (2 / b ^ 2) * ε2 := by
          have ineq1 := le_of_lt (hgb_prop2 n (le_trans (le_max_right N1 N2) hn))
          exact mul_le_mul_of_nonneg_left ineq1 (le_of_lt recippos)
        _ = (2 / b^2) * (ε * ((b ^ 2) / 4)) := by simp [ε2]
        _ = (2 / b^2) * (((b ^ 2) / 4) * ε) := by simp [mul_comm]
        _ = ((2 / b^2) * ((b ^ 2) / 4)) * ε := by simp [mul_assoc]
        _ = ((2 / b^2) * ((b ^ 2) / (2 * 2))) * ε := by linarith
        _ = ((2 / b^2) * ((b^2 / 2) * (1/2))) * ε := by
          simp [div_mul_eq_div_mul_one_div (b^2) 2 2]
        _ = (((2 / b^2) * (b^2 / 2)) * (1/2)) * ε := by linarith
        _ = (((2 / b^2) * (1 / (2 / b^2))) * (1/2)) * ε := by rw [(one_div_div 2 (b^2)).symm]
        _ = (((2 / b^2) * (2 / b^2)⁻¹) * (1/2)) * ε := by simp [div_eq_mul_inv]
        -- _ = (((2 / b^2)⁻¹ * (2 / b^2)) * (1/2)) * ε := by simp [mul_comm]
        _ = (1) * (1 / 2) * ε := by sorry
        _ < ε := by linarith


lemma seq_quot
  (f g : ℕ → ℝ)
  (a b : ℝ)
  (hf : is_sequence f)
  (hg : is_sequence g)
  (hfa : is_lim_seq f a)
  (hgb : is_lim_seq g b)
  (hbz : b ≠ 0) :
  (is_sequence (fun n => f n / g n)) ∧
  (is_lim_seq (fun n => f n / g n) (a / b)) := by sorry

-- Algebra of limits for functions (for sums, products and quotients)
lemma limit_sum
  (I : Set ℝ)
  (f g : ℝ → ℝ)
  (x L1 L2 : ℝ)
  (hfa : is_lim_fun I f x L1)
  (hgb : is_lim_fun I g x L2) :
  (is_lim_fun I (fun n => f n + g n) x (L1 + L2)) := by sorry
lemma limit_prod
  (I : Set ℝ)
  (f g : ℝ → ℝ)
  (x L1 L2 : ℝ)
  (hfa : is_lim_fun I f x L1)
  (hgb : is_lim_fun I g x L2) :
  (is_lim_fun I (fun n => f n * g n) x (L1 * L2)) := by sorry
lemma limit_quot
  (I : Set ℝ)
  (f g : ℝ → ℝ)
  (hg : ∀ x ∈ I, g x ≠ 0)
  (x L1 L2 : ℝ)
  (hfa : is_lim_fun I f x L1)
  (hgb : is_lim_fun I g x L2) :
  (is_lim_fun I (fun n => f n / g n) x (L1 / L2)) := by sorry

-- Proof that a non-negative sequence has non-negative limit
lemma limit_non_negative
  (f : ℕ → ℝ)
  (a : ℝ)
  (hf : is_sequence f)
  (hfa : is_lim_seq f a)
  (h_nonneg : ∀ n, f n ≥ 0) :
  a ≥ 0 := sorry
-- Proof that a non-positive sequence has non-positive limit
lemma limit_non_positive
  (f : ℕ → ℝ)
  (a : ℝ)
  (hf : is_sequence f)
  (hfa : is_lim_seq f a)
  (h_pos : ∀ n, f n > 0) : a > 0 := sorry
