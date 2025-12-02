import Mathlib.Data.Real.Basic
import LeanValueTheorem.Misc
import LeanValueTheorem.Limits
import LeanValueTheorem.Intervals

import Mathlib.Tactic.Linarith

-- Defintion for m being the value of the derivative of f : D → ℝ at a
def is_deriv_at (D : Set ℝ) (f : ℝ → ℝ) (m : ℝ) (a : ℝ) : Prop :=
  a ∈ D →
  is_lim_fun {h : ℝ | a + h ∈ D ∧ h ≠ 0} (fun h => (f (a + h) - f (a)) / h ) 0 m

-- Defintion for f' being the derivative of f : D → ℝ on a set A
def is_deriv (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (A : Set ℝ) : Prop :=
  ∀ a ∈ A, is_deriv_at D f (f' a) a

-- Proof that f : D → ℝ has zero derivative if it is constant
lemma const_zero_deriv
  (D : Set ℝ) (f : ℝ → ℝ) :
  is_const_fun D f → is_deriv D f 0 D := by
  intro hcon a ha _ ε hε
  use 1
  constructor
  · simp
  · intro h hh12 hh3
    obtain ⟨hh1, hh2⟩ := hh12
    simp only [Pi.zero_apply, sub_zero]
    have hah : a + h ∈ D ∧ a ∈ D := by
      constructor
      · exact hh1
      · exact ha
    specialize hcon (a + h) a hah
    rw [hcon]
    simp only [sub_self, zero_div, abs_zero, gt_iff_lt]
    exact hε

-- Proof that f(x) = x has derivative 1
lemma x_one_deriv
  (D : Set ℝ) :
  is_deriv D (fun x => x) 1 D := by
    intro a ha _ ε hε
    use 1
    constructor
    · simp
    · intro h hh12 hh3
      obtain ⟨hh1, hh2⟩ := hh12
      simp only [add_sub_cancel_left, Pi.one_apply]
      have hdiv : h / h = 1 := by
        exact (div_eq_one_iff_eq hh2).mpr rfl
      rw [hdiv]
      simp only [sub_self, abs_zero, gt_iff_lt]
      exact hε

-- Proof that 1/x has derivative -1/x^2
lemma recip_deriv
  (D : Set ℝ) (hD : ∀ x ∈ D, x ≠ 0) :
  is_deriv D (fun x => 1 / x) (fun x => -1 / x ^ 2) D := by
    intro a ha _
    sorry --algebra of limits goes here (I think)

-- Proof that the derivative of af + bg is af' + bg'
lemma sum_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ -> ℝ) (A : Set ℝ) (hf : is_deriv D f f' A)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ -> ℝ) (B : Set ℝ) (hg : is_deriv E g g' B) :
  ∀ a b, is_deriv (D ∩ E) (fun x => a * (f x) + b * (g x))
  (fun x => a * (f' x) + b * (g' x)) (A ∩ B) := by
    intro a b c hc _
    sorry --algebra of limits goes here

-- Proof that the derivative of f * g is f' * g + f * g'
lemma product_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ -> ℝ) (A : Set ℝ) (hf : is_deriv D f f' A)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ -> ℝ) (B : Set ℝ) (hg : is_deriv E g g' B) :
  is_deriv (D ∩ E) (fun x => (f x) * (g x))
  (fun x => (f' x) * (g x) + (f x) * (g' x)) (A ∩ B) := by
    intro a ha _
    sorry --algebra of limits goes here

--Proof that the derivative of x ^ n is n * x ^ (n + 1) for n ∈ ℕ
lemma power_rule
  (D : Set ℝ) (n : ℕ) :
  is_deriv D (fun x => x ^ n) (fun x => n * x ^ (n - 1)) D := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_tsub, mul_one]
    apply const_zero_deriv
    intro x y hxy
    simp
  | succ n hn =>
    simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
    have hmul : is_deriv (D ∩ D) (fun x ↦ x ^ n * x)
     (fun x ↦ n * x ^ (n - 1) * x + x ^ n * 1) (D ∩ D) := by
      apply product_rule D (fun x ↦ x ^ n) (fun x ↦ ↑n * x ^ (n - 1)) D hn
       D (fun x => x) (fun x => 1) D _
      exact x_one_deriv D
    simp only [Set.inter_self, mul_one] at hmul
    have hf1 : (fun (x : ℝ) ↦ x ^ (n + 1)) = (fun (x : ℝ) ↦ x ^ n * x) := by
      refine funext ?_
      intro y
      exact rfl
    have hf2 : (fun (x : ℝ) ↦ (↑n + 1) * x ^ n) = (fun (x : ℝ) ↦ ↑n * x ^ (n - 1) * x + x ^ n) := by
      refine funext ?_
      intro y
      calc
        (n + 1) * y ^ n = n * y ^ n + y ^ n := by exact add_one_mul (↑n) (y ^ n)
                     _  = n * y ^ (n - 1) * y + y ^ n := by
                      refine (add_left_inj (y ^ n)).mpr ?_
                      sorry --"failed to synthesize IsLeftCancelMul ℝ"
    rw [hf1, hf2]
    exact hmul

-- Proof that the derivative of g(f) is f' * g'(f)
lemma chain_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ -> ℝ) (A : Set ℝ) (hf : is_deriv D f f' A)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ -> ℝ) (B : Set ℝ) (hg : is_deriv E g g' B)
  (hdom : ∀ x ∈ D, (f x) ∈ B) :
  is_deriv D (fun x => g (f x))
  (fun x => (g' (f x)) * (f' x)) A := by
    intro a ha _
    sorry --algebra of limits goes here

lemma power_rule_neg
  (D : Set ℝ) (hD : ∀ x ∈ D, x ≠ 0) (n : ℕ):
  is_deriv D (fun x => x ^ (-(n : ℤ))) (fun x => -n * x ^ (-(n : ℤ) - 1)) D := by
    have hrecip : is_deriv D (fun x ↦ 1 / x ^ n)
     (fun x ↦ -1 / (x ^ n) ^ 2 * (n * x ^ (n - 1))) D :=  by
     apply chain_rule D (fun x => x ^ n) (fun x => n * x ^ (n - 1)) D _
      {x | x ≠ 0} (fun x => 1 / x) (fun x => -1 / x ^ 2) {x | x ≠ 0} _
     · intro y hy
       refine Set.mem_setOf.mpr ?_
       apply hD at hy
       exact pow_ne_zero n hy
     · exact power_rule D n
     · apply recip_deriv
       simp
    have hf1 : (fun (x : ℝ) ↦ x ^ (-(n : ℤ))) = (fun (x : ℝ) ↦ 1 / x ^ n) := by
      refine funext ?_
      intro y
      simp
    rw [hf1]
    simp only [one_div, neg_mul]
    have hf2 : (fun (x : ℝ) ↦ -(n : ℤ) * x ^ (-(n : ℤ) - 1))
     = (fun (x : ℝ) ↦ -1 / (x ^ n) ^ 2 * (↑n * x ^ (n - 1))) := by
      refine funext ?_
      intro y
      simp only [Int.cast_natCast, neg_mul]
      sorry --I think dividing by n is the issue here again
    simp only [Int.cast_natCast, neg_mul] at hf2
    rw [hf2]
    simp only [one_div] at hrecip
    exact hrecip

-- Proof that the derivative of f/g is f'g - fg' / g^2
lemma quotient_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ -> ℝ) (hf : is_deriv D f f' D)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ -> ℝ) (hg : is_deriv E g g' E)
  (hnz : ∀ x ∈ E, (g x) ≠ 0) :
  is_deriv (D ∩ E) (fun x => (f x) / (g x))
  (fun x => ((f' x) * (g x) - (f x) * (g' x)) / (g x) ^ 2) (D ∩ E) := by
    have hch : is_deriv E (fun x => 1 / (g x)) (fun x => (-1 / (g x) ^ 2) * (g' x)) E := by
      apply chain_rule E g g' E hg
       {x : ℝ | x ≠ 0} (fun x => 1 / x) (fun x => -1 / x^2) {x : ℝ | x ≠ 0} _ _
      · apply recip_deriv
        simp
      · exact hnz
    have hpr : is_deriv (D ∩ E) (fun x ↦ f x * (1 / g x))
     (fun x ↦ f' x * (1 / g x) + f x * (-1 / g x ^ 2 * g' x)) (D ∩ E) := by
      apply product_rule D f f' D hf E (fun x => 1 / (g x)) (fun x => (-1 / (g x) ^ 2) * (g' x)) E _
      exact hch
    have hf1 : (fun x ↦ f x / g x) = (fun x ↦ f x * (1 / g x)) := by
      refine funext ?_
      intro y
      exact div_eq_mul_one_div (f y) (g y)
    have hf2 : (fun x ↦ (f' x * g x - f x * g' x) / g x ^ 2)
     = (fun x ↦ f' x * (1 / g x) + f x * (-1 / g x ^ 2 * g' x)) := by
      refine funext ?_
      intro y
      sorry --pain and suffering
    rw [hf1, hf2]
    exact hpr
