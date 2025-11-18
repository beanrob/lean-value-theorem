import Mathlib.Data.Real.Basic
import LeanValueTheorem.Sequences

namespace Limits


def limit_sequence (s : ℕ → ℝ) (a : ℝ) : Prop := sorry

def limit_function (f : ℝ → ℝ) (x0 : ℝ) (L : ℝ) : Prop := sorry

lemma algebra_of_sequences -- maybe splot it up into 3 results
  (f g : ℕ → ℝ)
  (a b : ℝ)
  (hf : is_sequence f)
  (hg : is_sequence g)
  (hfa : limit_sequence f a)
  (hgb : limit_sequence g b) :

  (is_sequence (fun n => f n + g n)) ∧
  (limit_sequence (fun n => f n + g n) (a + b)) ∧

  (is_sequence (fun n => f n * g n)) ∧
  (limit_sequence (fun n => f n * g n) (a * b)) ∧

  (is_sequence (fun n => f n / g n)) ∧
  (limit_sequence (fun n => f n / g n) (a + b)):= sorry

lemma algebra_of_functions -- maybe splot it up into 3 results
  (f g : ℝ → ℝ)
  (x0 L1 L2 : ℝ)
  (hfa : limit_function f x0 L1)
  (hgb : limit_function g x0 L2) :

  (limit_function (fun x => f x + g x) x0 (L1 + L2)) ∧

  (limit_function (fun x => f x * g x) x0 (L1 * L2)) ∧

  (limit_function (fun x => f x / g x) x0 (L1 / L2)):= sorry

lemma limit_non_negative
  (f : ℕ → ℝ)
  (a : ℝ)
  (hf : is_sequence f)
  (hfa : limit_sequence f a)
  (h_nonneg : ∀ n, f n ≥ 0) :
  a ≥ 0 := sorry

lemma limit_non_positive
  (f : ℕ → ℝ)
  (a : ℝ)
  (hf : is_sequence f)
  (hfa : limit_sequence f a)
  (h_pos : ∀ n, f n > 0) :
  a > 0 := sorry


end Limits
