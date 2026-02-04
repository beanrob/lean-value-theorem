import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import LeanValueTheorem.Misc

def is_sequence (f : ℕ → ℝ) : Prop :=
  true

def is_sequence_non_positive (f : ℕ → ℝ) : Prop :=
  ∀ a : ℕ, f a < 0

def is_sequence_non_negative (f : ℕ → ℝ) : Prop :=
  ∀ a : ℕ, f a > 0

-- Definition for l being the limit of the sequence a
def is_lim_seq (a : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, n ≥ N → |a n - l| < ε

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
  have r : (f n - a) + (g n - b) = f n + g n - (a + b) := sub_add_sub_comm (f n) a (g n) b

  have number : ((2/3) : ℝ) < 1 := (div_lt_one₀ (by norm_num)).mpr (by exact_mod_cast (by decide))

  calc
  |f n + g n - (a + b)|
  _ = |(f n - a) + (g n - b)| := by rw [r]
  _ ≤ |f n - a| + |g n - b| := abs_add_le (f n - a) (g n - b)
  _ < ε' + ε' := add_lt_add (hfa_prop n hn1) (hgb_prop n hn2)
  _ = (ε / 3) + (ε / 3) := by rfl
  _ = ((2 / 3) : ℝ) * ε := by ring1
  _ < (1 : ℝ) * ε := mul_lt_mul_of_pos_right number hε
  _ = ε := by simp

-- given a sequence of the form sequence - constant with limit 0
-- the limit of the sequence is the constant
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
      f n = f n - a + a := Eq.symm (sub_add_cancel (f n) a)
      _ < ε + a := add_lt_add_of_lt_of_le ineq1 (le_rfl)
      _ = 0 := by simp [ε]

  have side1 := h_neg N (by norm_num)
  have side2 := h_nonneg N
  have := not_lt_of_ge side2
  have :=  this side1
  exact this

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

  have ha_neg := seq_non_negative (fun n => -1 * f n) (-1 * a) hnf.1 hnf.2 h_nonneg
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
  have number : ((1/3) : ℝ) < 1 := (div_lt_one₀ (by norm_num)).mpr (by norm_num)

  calc
    |(fun n ↦ f n * g n) n - 0| = |f n| * |g n| := by simp
    _ < ε' * 1 := mul_lt_mul_of_nonneg h1 h2 (abs_nonneg (f n)) (abs_nonneg (g n))
    _ = ε/3 := by simp [ε']
    _ = (1/3) * ε := by ring1
    _ < (1 : ℝ) * ε := mul_lt_mul_of_pos_right number hε
    _ = ε := by simp

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

  have hbp: |b| > 0 := abs_pos.mpr hbz
  rcases hgb (|b|/2) (div_pos hbp (by norm_num)) with ⟨N, h_prop⟩
  refine ⟨N, ?_⟩
  intro n hn

  by_contra! h
  have : |g n - b| = |b| := by simp [h]
  have side1 : |b| < |b| / 2 := by simpa [this] using (h_prop n hn)
  have side2 : |b| / 2 < |b| := by exact div_two_lt_of_pos hbp
  exact (not_lt_of_gt side1) side2

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
    have ineq1 := add_lt_of_lt_sub_right (abs_lt.1 (by simpa [ε1] using hgb_prop1 n hnN1)).1
    have rearrange : -(b ^ 2 / 2) + b * b = b^2 / 2 := by ring1
    rw [rearrange] at ineq1
    simpa only [mul_comm, gt_iff_lt] using ineq1

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
    _ = ε * ((2 / b ^ 2) * (2 / b ^ 2)⁻¹) := by ring1
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

lemma sandwich
  (f g k : ℕ → ℝ)
  (a b : ℝ)
  (hf : is_sequence f)
  (hg : is_sequence g)
  (hk : is_sequence k)
  (hfa : is_lim_seq f a)
  (hkb : is_lim_seq k b)
  (hfgk : ∀ n : ℕ, f n ≤ g n ∧ g n ≤ k n)
  (hab : a = b) :
  (is_lim_seq g a) := by

  intro ε hε
  rcases hfa ε hε with ⟨N1, hf_prop⟩
  rcases hkb ε hε with ⟨N2, hk_prop⟩

  use max N1 N2
  intro n hnN

  -- have (ha : |a| < b) : -b < a ∧ a < b := by exact

  have step1 := hf_prop n (le_trans (le_max_left N1 N2) hnN)
  have left1 : a - ε < f n := sub_lt_of_abs_sub_lt_left step1

  have step2 := (hk_prop n (le_trans (le_max_right N1 N2) hnN))
  have right1 : k n < b + ε := lt_add_of_tsub_lt_left (abs_lt.mp step2).2
  rw [←hab] at right1

  have left2 := lt_of_lt_of_le left1 (hfgk n).1
  have right2 := lt_of_le_of_lt (hfgk n).2 right1

  have left3 : -ε < g n - a := by exact lt_tsub_iff_left.mpr left2
  have right3 : g n - a < ε := by exact sub_left_lt_of_lt_add right2

  exact abs_lt.mpr ⟨left3, right3⟩
