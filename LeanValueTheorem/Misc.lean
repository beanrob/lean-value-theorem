import LeanValueTheorem.Intervals

-- Temp import for triangle inequality!!!
import Mathlib.Algebra.Order.Group.Unbundled.Abs


-- Definition for f : D → ℝ being a constant function
def is_const_fun (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, x ∈ D ∧ y ∈ D → f x = f y

-- If f is constant on [a,b] then it is constant on (a,b)
lemma const_closed_imp_const_open (a b : ℝ) (f : ℝ → ℝ) :
 is_const_fun (cci a b) f → is_const_fun (ooi a b) f := by
 intro h
 unfold is_const_fun at h
 unfold is_const_fun
 refine fun x y a ↦ ?_
 apply h
 cases a; expose_names
 apply open_in_closed at left
 apply open_in_closed at right
 exact ⟨left, right⟩

-- f is constant on the closed interval [a,b] if and only if f(x) = f(a) for all x in [a,b]
lemma closed_const (a b : ℝ) (f : ℝ → ℝ) {hab : a < b} :
 is_const_fun (cci a b) f ↔ ∀ x ∈ (cci a b), f x = f a := by
 rw [iff_def]
 and_intros
 · intro h
   unfold is_const_fun at h
   have ha : a ∈ (cci a b) := by
    have hz : a ≤ a := by exact Std.IsPreorder.le_refl a
    have hb : a ≤ b := by exact Std.le_of_lt hab
    exact Set.mem_sep hz hb
   refine fun x a ↦ ?_
   apply h
   exact ⟨a, ha⟩
 · intro h
   unfold is_const_fun
   refine fun x y a ↦ ?_
   cases a; expose_names
   apply h at left
   apply h at right
   apply Eq.trans left
   exact Eq.symm right

-- If f is NOT constant on [a,b] then f(x) differs from f(a) for some x in [a,b]
lemma not_const_imp_diff (a b : ℝ) (f : ℝ → ℝ) (hab : a < b) :
 ¬is_const_fun (cci a b) f → ∃ x : ℝ, x ∈ (cci a b) ∧ f x ≠ f a := by
 contrapose
 intro h
 rw [not_not]
 rw [closed_const]
 · rw [not_exists] at h
   refine fun x a ↦ ?_
   apply h at x
   rw [not_and_not_right] at x
   exact x a
 · exact hab
