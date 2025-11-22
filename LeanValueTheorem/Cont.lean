import Mathlib.Data.Real.Basic
import LeanValueTheorem.Intervals
import LeanValueTheorem.Sequences
import LeanValueTheorem.Limits
import LeanValueTheorem.Misc

-- Definition for a function being continuous at one point, using ε-δ
def is_cont_at_ε_δ {I : Set ℝ} (f : I → ℝ) (a : I) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 → ∀ x : I, abs (x.val - a.val) < δ → abs (f x - f a) < ε

-- Definition for a function being continuous at one point, using sequences
def is_cont_at_seq {I : Set ℝ} (f : I → ℝ) (a : I) : Prop :=
  ∀ seq : ℕ → ℝ, is_lim_seq seq a → is_lim_seq (f ∘ seq) (f a)

-- Definition for a function being continuous at a point, using interchangability
-- of the sequential and ε-δ definitions
def is_cont_at {I : Set ℝ} (f : I → ℝ) (a : I) : Prop :=
  (is_cont_at_ε_δ f a) ∧ (is_cont_at_seq f a)

-- Definition for a function being continuous on its whole domain
def is_cont (I : Set ℝ) (hI : is_interval I) (f : I → ℝ) : Prop :=
  ∀ a : I, is_cont_at f a

-- Algebra of continuous functions (for sums, products, and quotients)
lemma cont_sum
  (I : Set ℝ) (hI : is_interval I)
  (f g : I → ℝ) (a : I)
  {hfIa : is_cont_at f a}
  {hgIa : is_cont_at g a} :
  (is_cont_at (fun x => f x + g x) a) := sorry
lemma cont_prod
  (I : Set ℝ) (hI : is_interval I)
  (f g : I → ℝ) (a : I)
  {hfIa : is_cont_at f a}
  {hgIa : is_cont_at g a} :
  (is_cont_at (fun x => f x * g x) a) := sorry
lemma cont_quot
  (I : Set ℝ) (hI : is_interval I)
  (f g : I → ℝ) (a : I)
  {hfIa : is_cont_at f a}
  {hgIa : is_cont_at g a} :
  (is_cont_at (fun x => f x / g x) a) := sorry

-- Interchangability of ε-δ definition and sequential
-- Forwards direction
lemma cont_ε_δ_imp_cont_seq
  (I : Set ℝ) (hI : is_interval I)
  (f : I → ℝ) (a : I)
  {hfIa : is_cont_at_ε_δ f a} :
  is_cont_at_seq f a := sorry
-- Backwards direction
lemma cont_seq_imp_cont_ε_δ
  (I : Set ℝ) (hI : is_interval I)
  (f : I → ℝ) (a : I)
  {hfIa : is_cont_at_seq f a} :
  is_cont_at_ε_δ f a := sorry

-- Proof that continuous functions attain their bounds
lemma cont_attains_bounds
  (I : Set ℝ) (hI : is_interval I)
  (f : I → ℝ)
  {hfI : is_cont I hI f} :
  (∃ a : I, is_fun_min I hI f a) ∧
  (∃ b : I, is_fun_max I hI f b) := sorry
