import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import LeanValueTheorem.Intervals


-- Definition for l being the limit of the function f : D → ℝ at c
def is_lim_fun (D : Set ℝ) (f : ℝ → ℝ) (c : ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, |x - c| < δ → |f x - l| < ε

-- Limit of a Constant Function
lemma const_fun_limit (I : Set ℝ) (a c : ℝ) : (is_lim_fun I (fun n => a) c a) := by
  exact fun ε hε => ⟨1, by norm_num, fun x hxI hxcδ => by simp [sub_self, abs_zero, hε]⟩

lemma const_fun_limit_unique
  (I : Set ℝ) (a l c : ℝ) (hcI : c ∈ I) (hcla : is_lim_fun I (fun n => a) c l) :
  a = l := by

  by_contra! h
  have hpos : |l - a| > 0 := abs_pos.mpr (sub_ne_zero.mpr (ne_comm.mp h))
  rcases hcla (|l - a| / 2) (div_pos hpos (by norm_num)) with ⟨δ, hδ, h_prop⟩
  have hcc : |c - c| < δ := by simpa using hδ

  have side1 : |l - a| < |l - a| / 2 := by simpa [abs_sub_comm] using h_prop c hcI hcc
  have side2 : |l - a| / 2 < |l - a| := by exact div_two_lt_of_pos hpos
  exact (not_lt_of_gt side1) side2


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
  have r : (f x - a) + (g x - b) = f x + g x - (a + b) := sub_add_sub_comm (f x) a (g x) b
  have number : ((2/3) : ℝ) < 1 := (div_lt_one₀ (by norm_num)).mpr (by exact_mod_cast (by decide))

  calc
  |f x + g x - (a + b)|
  _ = |(f x - a) + (g x - b)| := by rw [r]
  _ ≤ |f x - a| + |g x - b| := abs_add_le (f x - a) (g x - b)
  _ < ε' + ε' := add_lt_add h1 h2
  _ = (ε / 3) + (ε / 3) := by rfl
  _ = (2/3 :ℝ) * ε := by ring1
  _ < (1 : ℝ) * ε := mul_lt_mul_of_pos_right number hε
  _ = ε := by simp

-- given a function of the form function - constant with limit 0
-- the limit of the function is the constant
lemma fun_lim_of_fun_sub_lim
  (I : Set ℝ)
  (f : ℝ → ℝ) (a c : ℝ)
  (hfa : is_lim_fun I (fun n => f n - a) c 0) :
  (is_lim_fun I f c a) := by
  have ha := (const_fun_limit I a c)
  have h := fun_sum I (fun n => f n - a) (fun n => a) c 0 a hfa ha
  simpa using h

-- given a function with some limit
-- the function (function - limit) has limit 0
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
  have number : ((1/3) : ℝ) < 1 := (div_lt_one₀ (by norm_num)).mpr (by norm_num)

  calc
    |(fun n ↦ f n * g n) x - 0| = |f x| * |g x| := by simp
    _ < ε' * 1 := mul_lt_mul_of_nonneg h1 h2 (abs_nonneg (f x)) (abs_nonneg (g x))
    _ = ε/3 := by simp [ε']
    _ = (1/3) * ε := by ring1
    _ < (1 : ℝ) * ε := mul_lt_mul_of_pos_right number hε
    _ = ε := by simp

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

  have hbp: |b| > 0 := abs_pos.mpr hbz
  rcases hgb (|b|/2) (div_pos hbp (by norm_num)) with ⟨δ, hδ, h_prop⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hxI hxcδ
  have number : (1/2 : ℝ) < 1 := (div_lt_one₀ (by norm_num)).mpr (by norm_num)

  by_contra! h
  have : |g x - b| = |b| := by simp only [h, zero_sub, abs_neg]
  have side1 : |b| < |b| / 2 := by simpa [this] using (h_prop x hxI hxcδ)
  have side2 : |b| / 2 < |b| := by exact div_two_lt_of_pos hbp
  exact (not_lt_of_gt side1) side2

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

  have sub (x : ℝ) (hxI : x ∈ I) (hxcδ : |x - c| < δ1)  : b^2 / 2 < g x * b := by
    have ineq1 := add_lt_of_lt_sub_right (abs_lt.1 (by simpa [ε1] using hgb_prop1 x hxI hxcδ)).1
    have rearrange : -(b ^ 2 / 2) + b * b = b^2 / 2 := by ring1
    rw [rearrange] at ineq1
    simpa only [mul_comm, gt_iff_lt] using ineq1

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
    |b - g x| / |g x * b| = |g x - b| / |g x * b| := by simp only [abs_sub_comm]
    _ ≤ |g x - b| * (2 / b ^ 2) := shuffle2 x hxI (lt_of_lt_of_le hxcδ hδ1)
    _ < ε2 * (2 / b ^ 2) := mul_lt_mul_of_pos_right (hgb_prop2 x hxI (lt_of_lt_of_le hxcδ hδ2)) h1ε1
    _ = ε * (2 / b ^ 2)⁻¹ * (2 / b ^ 2) := by rw [hε2eq]
    _ = ε * ((2 / b ^ 2) * (2 / b ^ 2)⁻¹) := by ring1
    _ = ε * 1 := by rw [shuffle3]
    _ = ε := by simp only [mul_one]

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
  simpa only [one_div] using this

-- Proof that a non-negative function has non-negative limit
lemma fun_non_negative
  (c a l r : ℝ)
  (f : ℝ → ℝ)
  (hlr : ¬(l = r))
  (hccI : c ∈ cci l r)
  (hfa : is_lim_fun (ooi l r) f c a)
  (h_nonneg : ∀ x ∈ ooi l r, f x ≥ 0) :
  a ≥ 0 := by

  by_contra! ha
  rcases hfa (-a) (neg_pos.mpr ha) with ⟨δ, hδ, hf_prop⟩

  have proof (x : ℝ) (hxI : x ∈ ooi l r) (hxcδ : |x - c| < δ) := by
    have ineq1 := (lt_of_le_of_lt (le_abs_self (f x - a)) (hf_prop x hxI hxcδ))
    have side1 := by
      calc
        f x = f x - a + a := Eq.symm (sub_add_cancel (f x) a)
        _ < -a + a := add_lt_add_of_lt_of_le ineq1 (le_rfl)
        _ = 0 := by simp only [neg_add_cancel]

    have side2 := h_nonneg x hxI
    exact (not_lt_of_ge side2) side1

  have hc : (min l r ≤ c) ∧ (c ≤ max l r) := hccI
  rcases hc with ⟨hcmin, hcmax⟩
  by_cases hc_min : c = min l r
  · by_cases hc_max : c = max l r
    · have min_eq_max := hc_max.symm.trans hc_min
      have eq1 := le_antisymm (le_of_le_of_eq (le_max_right l r) min_eq_max) (min_le_right l r)
      have eq2 := le_antisymm (le_of_le_of_eq (le_max_left l r) min_eq_max) (min_le_left l r)
      exact hlr (eq1.trans eq2.symm).symm
    · set x := c + min (δ/2) ((max l r -c)/2) with hxc

      have hδ2 : δ/2 > 0 := div_pos hδ (by norm_num)
      have in1 : max l r ≠ min l r := by rw [hc_min] at hc_max; exact (ne_comm.mpr hc_max)
      have in2 : min l r ≤ max l r := le_trans (min_le_left l r) (le_max_left l r)
      have in3 : min l r < max l r := lt_of_le_of_ne in2 (ne_comm.mpr in1)
      have in4 : max l r - c > 0 :=  by rw [hc_min]; exact sub_pos.mpr in3
      have in5 : ((max l r -c)/2) > 0:= div_pos in4 (by norm_num)
      have in6 : min (δ/2) ((max l r -c)/2) > 0 := lt_min hδ2 in5
      have in7 := lt_add_of_pos_right c in6
      have in8 := min_le_right (δ/2) ((max l r -c)/2)
      have in9 : ((max l r - c) / 2) < (max l r - c) := half_lt_self in4
      have in10 : min (δ/2) ((max l r -c)/2) < (max l r - c) := lt_of_le_of_lt in8 in9
      have in11 : min (δ/2) ((max l r -c)/2) ≤ (δ/2) := min_le_left (δ/2) ((max l r -c)/2)
      have in12 : δ/2 < δ := half_lt_self hδ

      have final_less : min l r < x := by simpa [hc_min, hxc] using in7
      have final_more : x < max l r := by simpa [←hxc] using (add_lt_add_left in10 c)

      apply proof x ⟨final_less, final_more⟩
      rw [hxc]
      simp only [add_sub_cancel_left]
      rw [abs_of_pos in6]
      exact lt_of_le_of_lt in11 in12

  · by_cases hc_max : c = max l r
    · set x := c - min (δ/2) ((c - min l r)/2) with hxc

      have hδ2 : δ/2 > 0 := div_pos hδ (by norm_num)
      have in1 : max l r ≠ min l r := by rw [hc_max] at hc_min; exact hc_min
      have in2 : min l r ≤ max l r := le_trans (min_le_left l r) (le_max_left l r)
      have in3 : min l r < max l r := lt_of_le_of_ne in2 (ne_comm.mpr in1)
      have in4 : c - min l r > 0 :=  by rw [hc_max]; exact sub_pos.mpr in3
      have in5 : ((c - min l r)/2) > 0:= div_pos in4 (by norm_num)
      have in6 : min (δ/2)  ((c - min l r)/2) > 0 := lt_min hδ2 in5
      have in7 := sub_lt_self c in6
      have in8 := min_le_right (δ/2) ((c - min l r)/2)
      have in9 : ((c - min l r) / 2) < (c - min l r) := half_lt_self in4
      have in10 : min (δ/2) ((c - min l r) / 2) < (c - min l r) := lt_of_le_of_lt in8 in9
      have in11 : min (δ/2) ((c - min l r) / 2) ≤ (δ/2) := min_le_left (δ/2) ((c - min l r) / 2)
      have in12 : δ/2 < δ := half_lt_self hδ

      have final_less : min l r < x := by simpa [←hxc] using (sub_lt_sub_left in10 c)
      have final_more : x < max l r := by simpa [hc_max, hxc] using in7

      apply proof x ⟨final_less, final_more⟩
      rw [hxc]
      simp only [sub_sub_cancel_left, abs_neg]
      rw [abs_of_pos in6]
      exact lt_of_le_of_lt in11 in12

    · have final_less := lt_of_le_of_ne hcmin (ne_comm.mpr hc_min)
      have final_more := lt_of_le_of_ne hcmax hc_max
      exact proof c ⟨final_less, final_more⟩ (by simpa using hδ)


-- Proof that a non-positive function has non-positive limit
lemma fun_non_positive
  (c a l r : ℝ)
  (f : ℝ → ℝ)
  (hlr : ¬(l = r))
  (hccI : c ∈ cci l r)
  (hfa : is_lim_fun (ooi l r) f c a)
  (h_nonpos : ∀ x ∈ ooi l r, f x ≤ 0) :
  a ≤ 0 := by

  have hnf := fun_scalar_prod (ooi l r) f (-1) a c hfa
  have h_nonneg := fun (x : ℝ) (hxI : x ∈ ooi l r) => by
    calc
      -1 * f x = -f x := (neg_eq_neg_one_mul (f x)).symm
      _ ≥ -0 := (neg_le_neg (h_nonpos x hxI))
      _ = 0 := by simp

  have ha_neg := fun_non_negative c (-1 * a) l r (fun n => -1 * f n) hlr hccI hnf h_nonneg
  rw [←neg_eq_neg_one_mul] at ha_neg
  exact (neg_nonneg.mp ha_neg)

lemma lim_fun_unique
  (D : Set ℝ) (f : ℝ → ℝ) (c m n : ℝ)
  (hfm : is_lim_fun D f c m)
  (hfn : is_lim_fun D f c n) :
  m = n := by

  have lim1 := fun_scalar_prod D f (-1) n c hfn
  have lim2 := fun_sum D f (fun n => -1 * f n) c m (-1 * n) hfm lim1
  simp only [neg_mul, one_mul, add_neg_cancel] at lim2
  have hcD : c ∈ D := by sorry
  have eq := const_fun_limit_unique D 0 (m + -n) c hcD lim2
  rw [eq_add_neg_iff_add_eq, zero_add] at eq
  exact Eq.symm eq


lemma lim_exists_on_subset (D E : Set ℝ) (f : ℝ → ℝ) (c : ℝ) (hDE : E ⊆ D) :
 (∃ l, is_lim_fun D f c l) → (∃ l, is_lim_fun E f c l) := by
 refine fun a ↦ ?_
 obtain ⟨l, hl⟩ := a
 unfold is_lim_fun
 unfold is_lim_fun at hl
 use l
 refine fun ε a ↦ ?_
 apply hl at a
 obtain ⟨δ, hδ⟩ := a
 cases hδ; expose_names
 use δ
 exact ⟨left, fun x a a_1 ↦ right x (hDE a) a_1⟩

lemma lim_union (D E : Set ℝ) (f : ℝ → ℝ) (c l m n : ℝ)
 (hD : is_lim_fun D f c m) (hE : is_lim_fun E f c n) (hDE : is_lim_fun (D ∪ E) f c l) :
 l = m ∧ l = n := by
 have hxD (x : ℝ) : x ∈ D → x ∈ D ∪ E := by exact fun a ↦ Set.mem_union_left E a
 have hxE (x : ℝ) : x ∈ E → x ∈ D ∪ E := by exact fun a ↦ Set.mem_union_right D a
 unfold is_lim_fun at hDE
 have h : (∀ ε > 0, ∃ δ > 0, ∀ x ∈ D ∪ E, |x - c| < δ → |f x - l| < ε) ↔
          ((∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, |x - c| < δ → |f x - l| < ε) ∧
           (∀ ε > 0, ∃ δ > 0, ∀ x ∈ E, |x - c| < δ → |f x - l| < ε)) := by
  rw [iff_def]
  and_intros
  · refine fun a ↦ ?_
    and_intros
    · refine fun ε b ↦ ?_
      apply a at b
      obtain ⟨δ,hδ⟩ := b
      cases hδ; expose_names
      use δ
      and_intros
      · exact left
      · exact fun x a a_1 ↦ right x (hxD x a) a_1
    · refine fun ε b ↦ ?_
      apply a at b
      obtain ⟨δ,hδ⟩ := b
      cases hδ; expose_names
      use δ
      and_intros
      · exact left
      · exact fun x a a_1 ↦ right x (hxE x a) a_1
  · exact fun a ε a_1 ↦ hDE ε a_1
 rw [h] at hDE
 have h1 := hDE.left
 have h2 := hDE.right
 have hleft  := lim_fun_unique D f c l m h1 hD
 have hright := lim_fun_unique E f c l n h2 hE
 exact ⟨hleft, hright⟩
