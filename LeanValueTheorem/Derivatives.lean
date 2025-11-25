import Mathlib.Data.Real.Basic
import LeanValueTheorem.Misc
import LeanValueTheorem.Limits
import LeanValueTheorem.Intervals


-- Defintion for f' being the derivative of f : D → ℝ at a
def is_deriv_at (D : Set ℝ) (f : ℝ → ℝ) (m : ℝ) (a : ℝ) : Prop :=
  a ∈ D →
  is_lim_fun_abv {h : ℝ | a + h ∈ D} (fun h => (f (a + h) - f (a)) / h ) m 0

-- Defintion for f' being the derivative of f : D → ℝ on a set A
def is_deriv (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (A : Set ℝ) : Prop :=
  ∀ a ∈ A, is_deriv_at D f (f' a) a

-- Proof that f : D → ℝ has zero derivative if and only if it is constant
lemma fun_with_zero_deriv
  (D : Set ℝ) (f : ℝ → ℝ) :
  is_deriv D f 0 D ↔ is_const_fun D f := by
    constructor
    · intro hder x y hD
      obtain ⟨hx, hy⟩ := hD
      sorry --I belive this direction requires the Mean Value Theorem
    · intro hcon a ha _ ε hε
      use 1
      constructor
      · simp
      · intro h hh1 hh2
        simp only [sub_zero]
        have hah : a + h ∈ D ∧ a ∈ D := by
          constructor
          · exact hh1
          · exact ha
        specialize hcon (a + h) a hah
        rw [hcon]
        simp only [sub_self, zero_div, abs_zero, gt_iff_lt]
        exact hε

lemma sum_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ -> ℝ) (hf : is_deriv D f f' D)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ -> ℝ) (hg : is_deriv E g g' E) :
  ∀ a b, is_deriv (D ∩ E) (fun x => a * (f x) + b * (g x))
  (fun x => a * (f' x) + b * (g' x)) (D ∩ E) := by
    sorry

lemma product_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ -> ℝ) (hf : is_deriv D f f' D)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ -> ℝ) (hg : is_deriv E g g' E) :
  is_deriv (D ∩ E) (fun x => (f x) * (g x))
  (fun x => (f' x) * (g x) + (f x) * (g' x)) (D ∩ E) := by
    sorry

lemma chain_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ -> ℝ) (hf : is_deriv D f f' D)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ -> ℝ) (hg : is_deriv E g g' E)
  (hdom : ∀ x ∈ D, (f x) ∈ E) :
  is_deriv D (fun x => g (f x))
  (fun x => (g' (f x)) * (f' x)) D := by
    sorry
