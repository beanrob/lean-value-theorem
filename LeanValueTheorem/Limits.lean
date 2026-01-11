import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import LeanValueTheorem.Sequences

-- Definition for l being the limit of the sequence a
def is_lim_seq (a : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, n ≥ N → |a n - l| < ε

-- Definition for l being the limit of the function f : D → ℝ at c
def is_lim_fun (D : Set ℝ) (f : ℝ → ℝ) (c : ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, |x - c| < δ → |f x - l| < ε

-- Limit of a Constant Sequence
lemma const_seq_limit (a : ℝ) : (is_sequence (fun n => a)) ∧ (is_lim_seq (fun n => a) a) := by
  refine ⟨by trivial, fun ε hε => ⟨0, fun n => by simp [sub_self, abs_zero, hε]⟩⟩

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

  refine ⟨by trivial, ?_⟩
  intro ε hε
  let ε' := ε / 3
  have hε' : ε' > 0 := div_pos hε (by norm_num)

  rcases hfa ε' hε' with ⟨N1, hfa_prop⟩
  rcases hgb ε' hε' with ⟨N2, hgb_prop⟩

  refine ⟨max N1 N2, ?_⟩
  intro n hn
  have hn1 : n ≥ N1 := le_trans (le_max_left N1 N2) hn
  have hn2 : n ≥ N2 := le_trans (le_max_right N1 N2) hn
  have r : (f n - a) + (g n - b) = f n + g n - (a + b) := by ring1

  calc
  |f n + g n - (a + b)|
  _ = |(f n - a) + (g n - b)| := by rw [r]
  _ ≤ |f n - a| + |g n - b| := abs_add_le (f n - a) (g n - b)
  _ < ε' + ε' := add_lt_add (hfa_prop n hn1) (hgb_prop n hn2)
  _ = (ε / 3) + (ε / 3) := by rfl
  _ < ε := by linarith

-- given a sequence of the form sequence - constant with limit 0
-- the limit of the sequence is constant
lemma seq_lim_of_seq_sub_lim
  (f : ℕ → ℝ) (a : ℝ)
  (hf : is_sequence (fun n => f n - a))
  (hfa : is_lim_seq (fun n => f n - a) 0) :
  (is_sequence f) ∧
  (is_lim_seq f a) := by
  have ha := (const_seq_limit a)
  have h := seq_sum (fun n => f n - a) (fun n => a) 0 a hf ha.1 hfa ha.2
  simpa using h

-- given a sequence with some limit
-- the sequence (sequence - limit) has limit 0
lemma seq_sub_lim_of_seq_lim
  (f : ℕ → ℝ) (a : ℝ)
  (hf : is_sequence f)
  (hfa : is_lim_seq f a) :
  (is_sequence (fun n => f n - a)) ∧
  (is_lim_seq (fun n => f n - a) 0) := by
  have ha := const_seq_limit (-a)
  have h := (seq_sum f (fun n => -a) a (-a) hf ha.1 hfa ha.2)
  simpa using h

lemma seq_scalar_prod
  (f : ℕ → ℝ)
  (a b : ℝ)
  (hf : is_sequence f)
  (hfa : is_lim_seq f a) :
  (is_sequence (fun n => b * f n)) ∧
  (is_lim_seq (fun n => b * f n) (b * a)) := by


  refine ⟨by trivial, ?_⟩
  intro ε hε
  by_cases hb : b = 0
  · refine ⟨0, fun n _ => by simp [hb, hε]⟩

  · have abs_b_pos : |b| > 0 := (lt_of_le_of_ne' (abs_nonneg b) (by simp [hb]))
    let ε' := ε * (|b|)⁻¹
    have hε' : ε' > 0 := div_pos hε abs_b_pos

    rcases hfa ε' hε' with ⟨N, hfa_prop⟩
    refine ⟨N, ?_⟩
    intro n hn

    calc
      |b * f n - b * a|
      _ = |b| * |f n - a| := by rw [←mul_sub, abs_mul]
      _ < |b| * ε' := mul_lt_mul_of_pos_left (hfa_prop n hn) abs_b_pos
      _ = |b| * ε * |b|⁻¹ := by simp only [ε', mul_assoc]
      _ = ε := by simp [mul_comm, hb]

-- Proof that a non-negative sequence has non-negative limit
lemma seq_non_negative
  (f : ℕ → ℝ)
  (a : ℝ)
  (hf : is_sequence f)
  (hfa : is_lim_seq f a)
  (h_nonneg : ∀ n, f n ≥ 0) :
  a ≥ 0 := by

  by_contra! ha
  let ε := -a
  rcases hfa ε (neg_pos.mpr ha) with ⟨N, hf_prop⟩

  have h_neg (n : ℕ) (hn : n ≥ N) := by
    have ineq1 := (lt_of_le_of_lt (le_abs_self (f n - a)) (hf_prop n hn))
    calc
      f n = f n - a + a := by ring1
      _ < ε + a := add_lt_add_of_lt_of_le ineq1 (le_rfl)
      _ = 0 := by simp [ε]

  have side1 := h_neg N (by norm_num)
  have side2 := h_nonneg N
  exact not_lt_of_ge side2 side1

-- Proof that a non-positive sequence has non-positive limit
lemma seq_non_positive
  (f : ℕ → ℝ)
  (a : ℝ)
  (hf : is_sequence f)
  (hfa : is_lim_seq f a)
  (h_nonpos : ∀ n, f n ≤ 0) :
  a ≤ 0 := by

  have hnf := seq_scalar_prod f a (-1) hf hfa
  have h_nonneg := fun (n : ℕ) => by
    calc
      -1 * f n = -f n := (neg_eq_neg_one_mul (f n)).symm
      _ ≥ -0 := (neg_le_neg (h_nonpos n))
      _ = 0 := by simp

  have ha_neg :=  seq_non_negative (fun n => -1 * f n) (-1 * a) hnf.1 hnf.2 h_nonneg
  rw [←neg_eq_neg_one_mul] at ha_neg
  exact (neg_nonneg.mp ha_neg)

lemma seq_prod_special
  (f g : ℕ → ℝ)
  (hf : is_sequence f)
  (hg : is_sequence g)
  (hfa : is_lim_seq f 0)
  (hgb : is_lim_seq g 0) :
  (is_sequence (fun n => f n * g n)) ∧
  (is_lim_seq (fun n => f n * g n) (0)) := by

  refine ⟨by trivial, ?_⟩
  intro ε hε
  let ε' := ε / 3
  have hε' : ε' > 0 := div_pos hε (by norm_num)

  rcases hfa ε' hε' with ⟨N1, hfa_prop⟩
  rcases hgb 1 (by norm_num) with ⟨N2, hgb_prop⟩
  refine ⟨max N1 N2, ?_⟩

  intro n hn
  have h1 := by simpa [sub_zero] using hfa_prop n (le_trans (le_max_left N1 N2) hn)
  have h2 := by simpa [sub_zero] using hgb_prop n (le_trans (le_max_right N1 N2) hn)

  calc
    |(fun n ↦ f n * g n) n - 0| = |f n| * |g n| := by simp
    _ < ε' * 1 := mul_lt_mul_of_nonneg h1 h2 (abs_nonneg (f n)) (abs_nonneg (g n))
    _ = ε/3 := by simp [ε']
    _ < ε := by linarith

lemma seq_prod
  (f g : ℕ → ℝ)
  (a b : ℝ)
  (hf : is_sequence f)
  (hg : is_sequence g)
  (hfa : is_lim_seq f a)
  (hgb : is_lim_seq g b) :
  (is_sequence (fun n => f n * g n)) ∧
  (is_lim_seq (fun n => f n * g n) (a * b)) := by

  let s1 := fun n => (f n - a)
  let s2 := fun n => (g n - b)

  have shuffle : (fun n => f n * g n - a * b) =
    ((fun n => s1 n * s2 n) + (fun n => a * s2 n)) + (fun n => b * s1 n) := by
    funext n
    simp only [s1, s2, Pi.add_apply]
    ring1

  have seq1_lim := seq_sub_lim_of_seq_lim f a hf hfa
  have seq2_lim := seq_sub_lim_of_seq_lim g b hg hgb

  have seq_mul_12 := seq_prod_special s1 s2 seq1_lim.1 seq2_lim.1 seq1_lim.2 seq2_lim.2
  have seq_mul_a2 := by simpa [mul_zero] using (seq_scalar_prod s2 0 a seq2_lim.1 seq2_lim.2)
  have seq_mul_1b := by simpa [mul_zero] using (seq_scalar_prod s1 0 b seq1_lim.1 seq1_lim.2)

  -- : is_lim_seq (fun n => (seq1 n * seq2 n) + (a * seq2 n) + (b * seq1 n)) 0
  have seq_add_three := by
    have h12 := by simpa using
      (seq_sum (fun n => s1 n * s2 n) (fun n => a * s2 n)
      0 0 seq_mul_12.1 seq_mul_a2.1 seq_mul_12.2 seq_mul_a2.2)

    exact
      (seq_sum (fun n => (s1 n * s2 n + a * s2 n)) (fun n => b * s1 n)
      0 0 h12.1 seq_mul_1b.1 h12.2 seq_mul_1b.2)

  have hsub :
    is_sequence (fun n => f n * g n - a * b) ∧
    is_lim_seq (fun n => f n * g n - a * b) 0 := by
    simpa [shuffle] using seq_add_three

  exact seq_lim_of_seq_sub_lim (fun n => f n * g n) (a * b) hsub.1 hsub.2

-- sequence with limit not eq 0 is never equal to 0 at a large enough N
lemma seq_neq_zero_of_lim_neq_zero
  (g : ℕ → ℝ) (b : ℝ)
  (hg : is_sequence g)
  (hgb : is_lim_seq g b)
  (hbz : b ≠ 0) :
  ∃N : ℕ, ∀ n ≥ N, g n ≠ 0 := by
  sorry

lemma seq_recip
  (g : ℕ → ℝ) (b : ℝ)
  (hg : is_sequence g)
  (hgb : is_lim_seq g b)
  (hbz : b ≠ 0) :
  (is_sequence (fun n => 1 / g n)) ∧
  (is_lim_seq (fun n => 1 / g n) (1 / b)) := by

  refine ⟨by trivial, ?_⟩
  intro ε hε
  simp [one_div]

  let ε1 := (b ^ 2) / 2
  have hε1 : (b ^ 2) / 2 > 0 := div_pos (sq_pos_of_ne_zero hbz) (by norm_num)

  rcases (seq_scalar_prod g b b hg hgb).2 ε1 hε1 with ⟨N1, hgb_prop1⟩

  have sub (n : ℕ) (hnN1 : n ≥ N1) : b^2 / 2 < g n * b := by
    linarith [(abs_lt.1 (by simpa [ε1] using hgb_prop1 n hnN1)).1]

  rcases (seq_neq_zero_of_lim_neq_zero g b hg hgb hbz) with ⟨N', seq_prop⟩

  have shuffle1 (n : ℕ) (hnN' : n ≥ N') : |(g n)⁻¹ - b⁻¹| = |b - g n| / |g n * b| := by
    simpa [abs_div] using congrArg (fun x => |x|) (inv_sub_inv (seq_prop n hnN') hbz)

  have shuffle2
    (n : ℕ) (hnN1 : n ≥ N1) :
    |g n - b| / |g n * b| ≤ |g n - b| * (2 / b ^ 2) := by

    have ineq1 := lt_of_lt_of_le (sub n hnN1) (le_abs_self (g n * b))
    have ineq2 : (|g n * b|)⁻¹ < 2 / b^2 := by
      simpa [one_div_div] using (one_div_lt_one_div_of_lt hε1 ineq1)
    apply mul_le_mul_of_nonneg_left (le_of_lt ineq2) (abs_nonneg (g n - b))

  set ε2 := ε * (2 / b ^ 2)⁻¹ with hε2eq
  have h1ε1 : 2 / (b ^ 2) > 0 := div_pos (by norm_num) (sq_pos_of_ne_zero hbz)
  have hε2 : ε2 > 0 := mul_pos hε (inv_pos.mpr h1ε1)
  rcases hgb ε2 hε2 with ⟨N2, hgb_prop2⟩

  refine ⟨max (max N1 N2) N', ?_⟩
  intro n hn

  have hN1 := le_trans (le_max_left N1 N2) (le_max_left (max N1 N2) N')
  have hN2 := le_trans (le_max_right N1 N2) (le_max_left (max N1 N2) N')

  rw [shuffle1 n (le_trans (le_max_right (max N1 N2) N') hn)]

  have shuffle3 := GroupWithZero.mul_inv_cancel
    (2 / b^2)
    (div_ne_zero (by norm_num) (ne_of_gt (sq_pos_of_ne_zero hbz)))

  calc
    |b - g n| / |g n * b| = |g n - b| / |g n * b| := by simp [abs_sub_comm]
    _ ≤ |g n - b| * (2 / b ^ 2) := shuffle2 n (le_trans hN1 hn)
    _ < ε2 * (2 / b ^ 2) := mul_lt_mul_of_pos_right (hgb_prop2 n ((le_trans hN2 hn))) h1ε1
    _ = ε * (2 / b ^ 2)⁻¹ * (2 / b ^ 2) := by rw [hε2eq]
    _ = ε * ((2 / b ^ 2) * (2 / b ^ 2)⁻¹) := by linarith
    _ = ε * 1 := by rw [shuffle3]
    _ = ε := by simp

lemma seq_quot
  (f g : ℕ → ℝ)
  (a b : ℝ)
  (hf : is_sequence f)
  (hg : is_sequence g)
  (hfa : is_lim_seq f a)
  (hgb : is_lim_seq g b)
  (hbz : b ≠ 0) :
  (is_sequence (fun n => f n / g n)) ∧
  (is_lim_seq (fun n => f n / g n) (a / b)) := by

  have := seq_recip g b hg hgb hbz
  have := seq_prod f (fun n => 1 / g n) a (1 / b) hf this.1 hfa this.2
  have h := by simpa [mul_div_right_comm a 1 b] using this.2
  exact ⟨this.1, h⟩

-- Limit of a Constant Function
lemma const_fun_limit (I : Set ℝ) (a c : ℝ) : (is_lim_fun I (fun n => a) c a) := by
  exact fun ε hε => ⟨1, by norm_num, fun x hxI hxcδ => by simp [sub_self, abs_zero, hε]⟩

-- Algebra of limits for functions (for sums, products and quotients)
lemma fun_sum
  (I : Set ℝ)
  (f g : ℝ → ℝ)
  (c a b : ℝ)
  (hfa : is_lim_fun I f c a)
  (hgb : is_lim_fun I g c b) :
  (is_lim_fun I (fun n => f n + g n) c (a + b)) := by

  intro ε hε
  let ε' := ε/3
  have hε': ε' > 0 := div_pos (hε) (by norm_num)

  rcases hfa ε' hε' with ⟨δ1, hδ1, hfa_prop⟩
  rcases hgb ε' hε' with ⟨δ2, hδ2, hgb_prop⟩
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2 , ?_⟩

  intro x hxI hxcδ
  have h1 := (hfa_prop x hxI (lt_of_lt_of_le hxcδ (min_le_left δ1 δ2)))
  have h2 := (hgb_prop x hxI (lt_of_lt_of_le hxcδ (min_le_right δ1 δ2)))
  have r : (f x - a) + (g x - b) = f x + g x - (a + b) := by ring1

  calc
  |f x + g x - (a + b)|
  _ = |(f x - a) + (g x - b)| := by rw [r]
  _ ≤ |f x - a| + |g x - b| := abs_add_le (f x - a) (g x - b)
  _ < ε' + ε' := add_lt_add h1 h2
  _ = (ε / 3) + (ε / 3) := by rfl
  _ < ε := by linarith

lemma fun_lim_of_fun_sub_lim
  (I : Set ℝ)
  (f : ℝ → ℝ) (a c : ℝ)
  (hfa : is_lim_fun I (fun n => f n - a) c 0) :
  (is_lim_fun I f c a) := by
  have ha := (const_fun_limit I a c)
  have h := fun_sum I (fun n => f n - a) (fun n => a) c 0 a hfa ha
  simpa using h

lemma fun_sub_lim_of_fun_lim
  (I : Set ℝ)
  (f : ℝ → ℝ) (a c : ℝ)
  (hfa : is_lim_fun I f c a) :
  (is_lim_fun I (fun n => f n - a) c 0) := by
  have ha := const_fun_limit I (-a) c
  have h := (fun_sum I f (fun n => -a) c a (-a) hfa ha)
  simpa using h

lemma fun_scalar_prod
  (I : Set ℝ)
  (f : ℝ → ℝ)
  (m a c : ℝ)
  (hfa : is_lim_fun I f c a) :
  (is_lim_fun I (fun n => m * f n) c (m * a)) := by

  intro ε hε
  by_cases hm : m = 0
  · refine ⟨1, by norm_num, fun x hxI hxc1 => by simp [hm, hε]⟩
  · have abs_m_pos : |m| > 0 := (lt_of_le_of_ne' (abs_nonneg m) (by simp [hm]))
    let ε' := ε / |m|
    have hε' : ε' > 0 := div_pos hε abs_m_pos
    rcases hfa ε' hε' with ⟨δ1, hδ1, hfa_prop⟩
    refine ⟨δ1, hδ1, ?_⟩

    intro x hxI hxcδ
    simp
    calc
      |m * f x - m * a|
      _ = |m| * |f x - a| := by rw [←mul_sub, abs_mul]
      _ < |m| * ε' := mul_lt_mul_of_pos_left (hfa_prop x hxI hxcδ) abs_m_pos
      _ = |m| * ε * |m|⁻¹ := by simp only [ε', div_eq_mul_inv, mul_assoc]
      _ = ε := by simp [mul_comm, hm]

lemma fun_prod_special
  (I : Set ℝ)
  (f g : ℝ → ℝ)
  (c : ℝ)
  (hfa : is_lim_fun I f c 0)
  (hgb : is_lim_fun I g c 0) :
  (is_lim_fun I (fun n => f n * g n) c (0)) := by

  intro ε hε
  let ε' := ε/3
  have hε' : ε' > 0 := div_pos hε (by norm_num)

  rcases hfa ε' hε' with ⟨δ1, hδ1, hfa_prop⟩
  rcases hgb 1 (by norm_num) with ⟨δ2, hδ2, hgb_prop⟩
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2 , ?_⟩

  intro x hxI hxcδ
  have h1 := by simpa [sub_zero] using (hfa_prop x hxI (lt_of_lt_of_le hxcδ (min_le_left δ1 δ2)))
  have h2 := by simpa [sub_zero] using (hgb_prop x hxI (lt_of_lt_of_le hxcδ (min_le_right δ1 δ2)))

  calc
    |(fun n ↦ f n * g n) x - 0| = |f x| * |g x| := by simp
    _ < ε' * 1 := mul_lt_mul_of_nonneg h1 h2 (abs_nonneg (f x)) (abs_nonneg (g x))
    _ = ε/3 := by simp [ε']
    _ < ε := by linarith

lemma fun_prod
  (I : Set ℝ)
  (f g : ℝ → ℝ)
  (c a b : ℝ)
  (hfa : is_lim_fun I f c a)
  (hgb : is_lim_fun I g c b) :
  (is_lim_fun I (fun n => f n * g n) c (a * b)) := by

  let s1 := fun n => (f n - a)
  let s2 := fun n => (g n - b)

  have shuffle : (fun n => f n * g n - a * b) =
    ((fun n => s1 n * s2 n) + (fun n => a * s2 n)) + (fun n => b * s1 n) := by
    funext n
    simp only [s1, s2, Pi.add_apply]
    ring1


  have seq1_lim := fun_sub_lim_of_fun_lim I f a c hfa
  have seq2_lim := fun_sub_lim_of_fun_lim I g b c hgb

  have seq_mul_12 := fun_prod_special I s1 s2 c seq1_lim seq2_lim
  have seq_mul_a2 := by simpa [mul_zero] using (fun_scalar_prod I s2 a 0 c seq2_lim)
  have seq_mul_1b := by simpa [mul_zero] using (fun_scalar_prod I s1 b 0 c seq1_lim)

  -- : is_lim_seq (fun n => (seq1 n * seq2 n) + (a * seq2 n) + (b * seq1 n)) 0
  have seq_add_three := by
    have h12 := by simpa using
      (fun_sum I (fun n => s1 n * s2 n) (fun n => a * s2 n)
      c 0 0 seq_mul_12 seq_mul_a2)

    exact
      (fun_sum I (fun n => (s1 n * s2 n + a * s2 n)) (fun n => b * s1 n)
      c 0 0 h12 seq_mul_1b)

  have hsub :
    is_lim_fun I (fun n => f n * g n - a * b) c 0 := by
    simpa [shuffle] using seq_add_three

  exact fun_lim_of_fun_sub_lim I (fun n => f n * g n) (a * b) c hsub

-- function with limit not eq 0 is never equal to 0 at a small enough delta
lemma fun_neq_zero_of_lim_neq_zero
  (I : Set ℝ)
  (g : ℝ → ℝ) (c b : ℝ)
  (hgb : is_lim_fun I g c b)
  (hbz : b ≠ 0) :
  ∃δ > 0, ∀ x ∈ I, |x - c| < δ → g x ≠ 0 := by
  sorry

lemma fun_recip
  (I : Set ℝ)
  (g : ℝ → ℝ) (c b : ℝ)
  (hgb : is_lim_fun I g c b)
  (hbz : b ≠ 0) :
  (is_lim_fun I (fun n => 1 / g n) c (1 / b)) := by

  intro ε hε
  simp [one_div]

  let ε1 := (b ^ 2) / 2
  have hε1 : (b ^ 2) / 2 > 0 := div_pos (sq_pos_of_ne_zero hbz) (by norm_num)
  rcases (fun_scalar_prod I g b b c hgb) ε1 hε1 with ⟨δ1, hδ1, hgb_prop1⟩

  have sub (x : ℝ) (hxI : x ∈ I) (hxcδ : |x - c| < δ1) : b^2 / 2 < g x * b := by
    linarith [(abs_lt.1 (by simpa [ε1] using hgb_prop1 x hxI hxcδ)).1]

  rcases (fun_neq_zero_of_lim_neq_zero I g c b hgb hbz) with ⟨δ', hδ', fun_prop⟩

  have shuffle1
    (x : ℝ) (hxI : x ∈ I) (hxcδ' : |x - c| < δ') :
    |(g x)⁻¹ - b⁻¹| = |b - g x| / |g x * b| := by
    simpa [abs_div] using congrArg (fun x => |x|) (inv_sub_inv (fun_prop x hxI hxcδ') hbz)

  have shuffle2
    (x : ℝ) (hxI : x ∈ I) (hxcδ : |x - c| < δ1) :
    |g x - b| / |g x * b| ≤ |g x - b| * (2 / b ^ 2) := by

    have ineq1 := lt_of_lt_of_le (sub x hxI hxcδ) (le_abs_self (g x * b))
    have ineq2 : (|g x * b|)⁻¹ < 2 / b^2 := by
      simpa [one_div_div] using (one_div_lt_one_div_of_lt hε1 ineq1)
    apply mul_le_mul_of_nonneg_left (le_of_lt ineq2) (abs_nonneg (g x - b))

  set ε2 := ε * (2 / b ^ 2)⁻¹ with hε2eq
  have h1ε1 : 2 / (b ^ 2) > 0 := div_pos (by norm_num) (sq_pos_of_ne_zero hbz)
  have hε2 : ε2 > 0 := mul_pos hε (inv_pos.mpr h1ε1)
  rcases hgb ε2 hε2 with ⟨δ2, hδ2, hgb_prop2⟩

  refine ⟨min (min δ1 δ2) δ', lt_min (lt_min hδ1 hδ2) hδ', ?_⟩

  intro x hxI hxcδ

  have hδ1 := le_trans (min_le_left (min δ1 δ2) δ') (min_le_left δ1 δ2)
  have hδ2 := le_trans (min_le_left (min δ1 δ2) δ') (min_le_right δ1 δ2)

  rw [shuffle1 x hxI (lt_of_lt_of_le hxcδ ((min_le_right (min δ1 δ2) δ')))]

  have shuffle3 := GroupWithZero.mul_inv_cancel
    (2 / b^2) (div_ne_zero (by norm_num) (ne_of_gt (sq_pos_of_ne_zero hbz)))

  calc
    |b - g x| / |g x * b| = |g x - b| / |g x * b| := by simp [abs_sub_comm]
    _ ≤ |g x - b| * (2 / b ^ 2) := shuffle2 x hxI (lt_of_lt_of_le hxcδ hδ1)
    _ < ε2 * (2 / b ^ 2) := mul_lt_mul_of_pos_right (hgb_prop2 x hxI (lt_of_lt_of_le hxcδ hδ2)) h1ε1
    _ = ε * (2 / b ^ 2)⁻¹ * (2 / b ^ 2) := by rw [hε2eq]
    _ = ε * ((2 / b ^ 2) * (2 / b ^ 2)⁻¹) := by linarith
    _ = ε * 1 := by rw [shuffle3]
    _ = ε := by simp

lemma fun_quot
  (I : Set ℝ)
  (f g : ℝ → ℝ)
  (c a b : ℝ)
  (hbz : b ≠ 0)
  (hfa : is_lim_fun I f c a)
  (hgb : is_lim_fun I g c b) :
  (is_lim_fun I (fun n => f n / g n) c (a / b)) := by

  have := fun_recip I g c b hgb hbz
  have := fun_prod I f (fun n => 1 / g n) c a (1 / b) hfa this
  simpa [mul_div_right_comm a 1 b] using this

-- Proof that a non-negative function has non-negative limit
lemma fun_non_negative
  (I : Set ℝ)
  (f : ℝ → ℝ)
  (c a : ℝ)
  (hfa : is_lim_fun I f c a)
  (h_nonneg : ∀ x ∈ I, f x ≥ 0) :
  a ≥ 0 := by

  by_contra! ha
  let ε := -a
  rcases hfa ε (neg_pos.mpr ha) with ⟨δ, hδ, hf_prop⟩

  have proof (x : ℝ) (hxI : x ∈ I) (hxcδ : |x - c| < δ) := by
    have ineq1 := (lt_of_le_of_lt (le_abs_self (f x - a)) (hf_prop x hxI hxcδ))
    have side1 := by
      calc
        f x = f x - a + a := by linarith
        _ < ε + a := add_lt_add_of_lt_of_le ineq1 (le_rfl)
        _ = 0 := by simp [ε]

    have side2 := h_nonneg x hxI
    exact not_lt_of_ge side2 side1

  exact proof (sorry) (sorry) (sorry)

-- Proof that a non-positive function has non-positive limit
lemma fun_non_positive
  (I : Set ℝ)
  (f : ℝ → ℝ)
  (c a : ℝ)
  (hfa : is_lim_fun I f c a)
  (h_nonpos : ∀ n, f n ≤ 0) :
  a ≤ 0 := by

  have hnf := fun_scalar_prod I f (-1) a c hfa
  have h_nonneg := fun (x : ℝ) (hxI : x ∈ I) => by
    calc
      -1 * f x = -f x := (neg_eq_neg_one_mul (f x)).symm
      _ ≥ -0 := (neg_le_neg (h_nonpos x))
      _ = 0 := by simp

  have ha_neg := fun_non_negative I (fun n => -1 * f n) c (-1 * a) hnf h_nonneg
  rw [←neg_eq_neg_one_mul] at ha_neg
  exact (neg_nonneg.mp ha_neg)
