import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import LeanValueTheorem.Sequences


-- Definition for l being the limit of the sequence a
def is_lim_seq (a : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, N > 0 ∧ (∀ n, n ≥ N → abs (a n - l) < ε)

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
  (is_lim_seq (fun n => b * f n) (b * a)) := by sorry


lemma seq_prod
  (f g : ℕ → ℝ)
  (a b : ℝ)
  (hf : is_sequence f)
  (hg : is_sequence g)
  (hfa : is_lim_seq f a)
  (hgb : is_lim_seq g b) :
  (is_sequence (fun n => f n * g n)) ∧
  (is_lim_seq (fun n => f n * g n) (a * b)) := by sorry



lemma seq_quot
  (f g : ℕ → ℝ)
  (a b : ℝ)
  (hf : is_sequence f)
  (hg : is_sequence g)
  (hfa : is_lim_seq f a)
  (hgb : is_lim_seq g b) :
  (is_sequence (fun n => f n / g n)) ∧
  (is_lim_seq (fun n => f n / g n) (a / b)) := sorry

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
