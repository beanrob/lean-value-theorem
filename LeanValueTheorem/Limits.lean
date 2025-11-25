import Mathlib.Data.Real.Basic
import LeanValueTheorem.Sequences


-- Definition for l being the limit of the sequence a
def is_lim_seq (a : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, N > 0 ∧ (∀ n, n ≥ N → abs (a n - l) < ε)

-- Definition for l being the limit of the function f at point c
def is_lim_fun (f : ℝ → ℝ) (c : ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - c) < δ → abs (f x - l) < ε

-- Definition for l being the limit of the function f at point c *from above*
def is_lim_fun_abv (f : ℝ → ℝ) (c : ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x > c, x - c < δ → abs (f x - l) < ε

-- Algebra of limtis for sequences (for sums, products and quotients)
lemma seq_sum
  (f g : ℕ → ℝ)
  (a b : ℝ)
  (hf : is_sequence f)
  (hg : is_sequence g)
  (hfa : is_lim_seq f a)
  (hgb : is_lim_seq g b) :
  (is_sequence (fun n => f n + g n)) ∧
  (is_lim_seq (fun n => f n + g n) (a + b)) := by sorry
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
  (f g : ℝ → ℝ)
  (x0 L1 L2 : ℝ)
  (hfa : is_lim_fun f x0 L1)
  (hgb : is_lim_fun g x0 L2) :
  (is_lim_fun (fun x => f x + g x) x0 (L1 + L2)) := by sorry
lemma limit_prod
  (f g : ℝ → ℝ)
  (x0 L1 L2 : ℝ)
  (hfa : is_lim_fun f x0 L1)
  (hgb : is_lim_fun g x0 L2) :
  (is_lim_fun (fun x => f x * g x) x0 (L1 * L2)) := by sorry
lemma limit_quot
  (f g : ℝ → ℝ)
  (x0 L1 L2 : ℝ)
  (hfa : is_lim_fun f x0 L1)
  (hgb : is_lim_fun g x0 L2) :
  (is_lim_fun (fun x => f x / g x) x0 (L1 / L2)) := by sorry

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
