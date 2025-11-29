import Mathlib.Data.Real.Basic
import LeanValueTheorem.Misc
import LeanValueTheorem.Limits
import LeanValueTheorem.Intervals


-- Defintion for m being the value of the derivative of f : D → ℝ at a
def is_deriv_at (D : Set ℝ) (f : ℝ → ℝ) (m : ℝ) (a : ℝ) : Prop :=
  a ∈ D →
  is_lim_fun {h : ℝ | a + h ∈ D ∧ h ≠ 0} (fun h => (f (a + h) - f (a)) / h ) 0 m

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
      sorry --requires MVT
    · intro hcon a ha _ ε hε
      use 1
      constructor
      · simp
      · intro h hh hh3
        obtain ⟨hh1, hh2⟩ := hh
        simp only [Pi.zero_apply, sub_zero]
        have hah : a + h ∈ D ∧ a ∈ D := by
          constructor
          · exact hh1
          · exact ha
        specialize hcon (a + h) a hah
        rw [hcon]
        simp only [sub_self, zero_div, abs_zero, gt_iff_lt]
        exact hε

-- Proof that the derivative of af + bg is af' + bg'
lemma sum_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ -> ℝ) (hf : is_deriv D f f' D)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ -> ℝ) (hg : is_deriv E g g' E) :
  ∀ a b, is_deriv (D ∩ E) (fun x => a * (f x) + b * (g x))
  (fun x => a * (f' x) + b * (g' x)) (D ∩ E) := by
    sorry

-- Proof that the derivative of f * g is f' * g + f * g'
lemma product_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ -> ℝ) (hf : is_deriv D f f' D)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ -> ℝ) (hg : is_deriv E g g' E) :
  is_deriv (D ∩ E) (fun x => (f x) * (g x))
  (fun x => (f' x) * (g x) + (f x) * (g' x)) (D ∩ E) := by
    sorry

-- Proof that the derivative of g(f) is f' * g'(f)
lemma chain_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ -> ℝ) (hf : is_deriv D f f' D)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ -> ℝ) (hg : is_deriv E g g' E)
  (hdom : ∀ x ∈ D, (f x) ∈ E) :
  is_deriv D (fun x => g (f x))
  (fun x => (g' (f x)) * (f' x)) D := by
    sorry

-- Proof that the derivative of f/g is f'g - fg' / g^2
lemma quotient_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ -> ℝ) (hf : is_deriv D f f' D)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ -> ℝ) (hg : is_deriv E g g' E)
  (hnz : ∀ x ∈ E, (g x) ≠ 0) :
  is_deriv (D ∩ E) (fun x => (f x) / (g x))
  (fun x => ((f' x) * (g x) - (f x) * (g' x)) / (g x) ^ 2) (D ∩ E) := by
    have hch : is_deriv E (fun x => 1 / (g x)) (fun x => (-1 / (g x) ^ 2) * (g' x)) E := by
      apply chain_rule E g g' hg {x : ℝ | x ≠ 0} (fun x => 1 / x) (fun x => -1 / x^2) _ _
      · intro a ha _
        sorry --algebra of limits goes here
      · exact hnz
    have hpr : is_deriv (D ∩ E) (fun x ↦ f x * (1 / g x)) (fun x ↦ f' x * (1 / g x) + f x * (-1 / g x ^ 2 * g' x)) (D ∩ E) := by
      apply product_rule D f f' hf E (fun x => 1 / (g x)) (fun x => (-1 / (g x) ^ 2) * (g' x)) _
      exact hch
    sorry --this is just rearranging
