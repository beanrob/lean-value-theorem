import Mathlib.Data.Real.Basic
import LeanValueTheorem.Misc
import LeanValueTheorem.Limits
import LeanValueTheorem.Intervals
import LeanValueTheorem.Bounds

import Mathlib.Tactic.Linarith

-- Defintion for m being the value of the derivative of f : D → ℝ at a
def is_deriv_at (D : Set ℝ) (f : ℝ → ℝ) (m : ℝ) (a : ℝ) : Prop :=
  a ∈ D →
  is_lim_fun {h : ℝ | a + h ∈ D ∧ h ≠ 0} (fun h ↦ (f (a + h) - f (a)) / h ) 0 m

-- Defintion for f' being the derivative of f : D → ℝ on a set A
def is_deriv (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (A : Set ℝ) : Prop :=
  ∀ a ∈ A, is_deriv_at D f (f' a) a

lemma deriv_at_unique (D : Set ℝ) (f : ℝ → ℝ) (m n: ℝ) (a : ℝ) (ha : a ∈ D) :
 (is_deriv_at D f m a ∧ is_deriv_at D f n a) → m = n := by
 let ha_1 := ha
 refine fun b ↦ ?_
 unfold is_deriv_at at b
 apply b.left at ha
 apply b.right at ha_1
 sorry

lemma deriv_at_deriv (D : Set ℝ) (m a : ℝ) (f f': ℝ → ℝ) (ha : a ∈ D)
 (hf' : is_deriv D f f' D) (hf : is_deriv_at D f m a) : f' a = m := by
 unfold is_deriv at hf'
 have hderiv : is_deriv_at D f (f' a) a := by exact hf' a ha
 have hand : is_deriv_at D f m a ∧ is_deriv_at D f (f' a) a := by exact ⟨hf, hf' a ha⟩
 exact deriv_at_unique D f (f' a) m a ha (id (And.symm hand))

-- Proof that f : D → ℝ has zero derivative if it is constant
lemma const_zero_deriv
  (D : Set ℝ) (f : ℝ → ℝ) (A : Set ℝ) :
  is_const_fun D f → is_deriv D f 0 A := by
  intro hcon a haA haD ε hε
  use 1
  constructor
  · simp
  · intro h hh12 hh3
    obtain ⟨hh1, hh2⟩ := hh12
    simp only [Pi.zero_apply, sub_zero]
    have hah : a + h ∈ D ∧ a ∈ D := by
      constructor
      · exact hh1
      · exact haD
    specialize hcon (a + h) a hah
    rw [hcon]
    simp only [sub_self, zero_div, abs_zero, gt_iff_lt]
    exact hε

-- Proof that f(x) = x has derivative 1
lemma x_one_deriv
  (D : Set ℝ) :
  is_deriv D (fun x ↦ x) 1 D := by
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
  is_deriv D (fun x ↦ 1 / x) (fun x ↦ -1 / x ^ 2) D := by
    intro a ha _
    have hsimp : (fun h ↦ ((fun x ↦ 1 / x) (a + h) - (fun x ↦ 1 / x) a) / h)
     = (fun h ↦ -1 / (a * (a + h))) := by
      refine funext ?_
      intro h
      sorry
    sorry

-- Proof that the derivative of f + g is f' + g'
lemma sum_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (A : Set ℝ) (hf : is_deriv D f f' A)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ) (B : Set ℝ) (hg : is_deriv E g g' B) :
  is_deriv (D ∩ E) (fun x ↦ (f x) + (g x))
  (fun x ↦ (f' x) + (g' x)) (A ∩ B) := by
    intro a ha1 ha2
    obtain ⟨haA, haB⟩ := ha1
    obtain ⟨haD, haE⟩ := ha2
    unfold is_deriv at hf hg
    unfold is_deriv_at at hf hg
    specialize hf a haA haD
    specialize hg a haB haE
    sorry --algebra of limits goes here

-- Proof that the derivative of f * g is f' * g + f * g'
lemma product_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (A : Set ℝ) (hf : is_deriv D f f' A)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ) (B : Set ℝ) (hg : is_deriv E g g' B) :
  is_deriv (D ∩ E) (fun x ↦ (f x) * (g x))
  (fun x ↦ (f' x) * (g x) + (f x) * (g' x)) (A ∩ B) := by
    intro a ha _
    sorry --algebra of limits goes here

-- Proof that the derivative of rf is rf'
lemma scale_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (A : Set ℝ) (hf : is_deriv D f f' A)
  (r : ℝ) : is_deriv D (fun x ↦ r * (f x)) (fun x ↦ r * (f' x)) A := by
    have hconst : is_deriv D (fun y ↦ r) 0 A := by
      apply const_zero_deriv
      intro x y hxy
      simp
    have hprod : is_deriv (D ∩ D) (fun x ↦ r * f x) (fun x ↦ 0 * f x + r * f' x) (A ∩ A) := by
      exact product_rule D (fun y ↦ r) 0 A hconst D f f' A hf
    simp only [Set.inter_self, zero_mul, zero_add] at hprod
    exact hprod

--Proof that the derivative of x ^ n is n * x ^ (n + 1) for n ∈ ℕ
lemma power_rule
  (D : Set ℝ) (n : ℕ) :
  is_deriv D (fun x ↦ x ^ n) (fun x ↦ n * x ^ (n - 1)) D := by
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
       D (fun x ↦ x) (fun x ↦ 1) D _
      exact x_one_deriv D
    simp only [Set.inter_self, mul_one] at hmul
    have hf1 : (fun (x : ℝ) ↦ x ^ (n + 1)) = (fun (x : ℝ) ↦ x ^ n * x) := by
      refine funext ?_
      intro y
      exact rfl
    have hf2 : (fun (x : ℝ) ↦ (↑n + 1) * x ^ n) = (fun (x : ℝ) ↦ ↑n * x ^ (n - 1) * x + x ^ n) := by
      refine funext ?_
      intro y
      rcases Or.symm (ne_or_eq n 0) with hz | hnz
      · rw [hz]
        simp
      · rw [mul_assoc (↑n) (y ^ (n - 1)) y, pow_sub_one_mul hnz y, ← add_one_mul (↑n) (y ^ n)]
    rw [hf1, hf2]
    exact hmul

-- Proof that the derivative of g(f) is f' * g'(f)
lemma chain_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (A : Set ℝ) (hf : is_deriv D f f' A)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ) (B : Set ℝ) (hg : is_deriv E g g' B)
  (hdom : ∀ x ∈ D, (f x) ∈ B) :
  is_deriv D (fun x ↦ g (f x))
  (fun x ↦ (g' (f x)) * (f' x)) A := by
    intro a ha _
    sorry --algebra of limits goes here

-- Proof that the derivative of x ^ -n is -n * x ^ (-n - 1) for n ∈ ℤ
lemma power_rule_neg
  (D : Set ℝ) (hD : ∀ x ∈ D, x ≠ 0) (n : ℤ) (hn : n > 0) :
  is_deriv D (fun x ↦ x ^ (-n)) (fun x ↦ -n * x ^ (-n - 1)) D := by
    have hrecip : is_deriv D (fun x ↦ 1 / x ^ n)
     (fun x ↦ -1 / (x ^ n) ^ 2 * (n * x ^ (n - 1))) D :=  by
     apply chain_rule D (fun x ↦ x ^ n) (fun x ↦ n * x ^ (n - 1)) D _
      {x | x ≠ 0} (fun x ↦ 1 / x) (fun x ↦ -1 / x ^ 2) {x | x ≠ 0} _
     · intro y hy
       refine Set.mem_setOf.mpr ?_
       apply hD at hy
       exact zpow_ne_zero n hy
     · have hpos : n = n.toNat := by
        refine Eq.symm (Int.toNat_of_nonneg ?_)
        exact Int.le_of_lt hn
       rw [hpos]
       have hder : is_deriv D (fun x ↦ x ^ n.toNat) (fun x ↦ ↑n.toNat * x ^ (n.toNat - 1)) D := by
        exact power_rule D n.toNat
       convert hder
       rename ℝ => z
       rw [← Int.natCast_pred_of_pos ?_]
       · simp
       · simp only [Int.lt_toNat, Nat.cast_zero]
         exact hn
     · apply recip_deriv
       simp
    have hf1 : (fun (x : ℝ) ↦ x ^ (-n)) = (fun (x : ℝ) ↦ 1 / x ^ n) := by
      refine funext ?_
      intro y
      simp
    rw [hf1]
    simp only [one_div, neg_mul]
    have hf2 : (fun (x : ℝ) ↦ -n * x ^ (-n - 1))
     = (fun (x : ℝ) ↦ -1 / (x ^ n) ^ 2 * (↑n * x ^ (n - 1))) := by
      refine funext ?_
      intro y
      simp only [neg_mul]
      rw [show -1 / (y ^ n) ^ 2 = -1 * ((y ^ n) ^ 2)⁻¹ from rfl]
      simp only [neg_mul, one_mul, neg_inj]
      rw [mul_rotate' ((y ^ n) ^ 2)⁻¹ (↑n) (y ^ (n - 1)), mul_right_inj' ?_]
      · rw [← zpow_neg_coe_of_pos (y ^ n) Nat.zero_lt_two, ← zpow_mul', ← zpow_add' ?_]
        · rw [Int.ofNat_two, sub_add_eq_add_sub, ← one_add_mul]
          simp only [Int.reduceNeg, Int.reduceAdd, neg_mul, one_mul]
        · right
          left
          rw [sub_add_eq_add_sub, ← one_add_mul]
          simp
          rw [Int.sub_eq_zero, @neg_eq_iff_eq_neg, ← ne_eq n (-1)]
          refine Ne.symm (Int.ne_of_lt ?_)
          have hneg : -1 < 0 := by
            exact neg_one_lt_zero
          exact Int.lt_trans hneg hn
      · simp only [ne_eq, Int.cast_eq_zero]
        exact Int.ne_of_gt hn
    simp only [neg_mul] at hf2
    rw [hf2]
    simp only [one_div] at hrecip
    exact hrecip

-- Proof that the derivative of f/g is f'g - fg' / g^2
lemma quotient_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (hf : is_deriv D f f' D)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ) (hg : is_deriv E g g' E)
  (hnz : ∀ x, (g x) ≠ 0) :
  is_deriv (D ∩ E) (fun x ↦ (f x) / (g x))
  (fun x ↦ ((f' x) * (g x) - (f x) * (g' x)) / (g x) ^ 2) (D ∩ E) := by
    have hch : is_deriv E (fun x ↦ 1 / (g x)) (fun x ↦ (-1 / (g x) ^ 2) * (g' x)) E := by
      apply chain_rule E g g' E hg
       {x : ℝ | x ≠ 0} (fun x ↦ 1 / x) (fun x ↦ -1 / x^2) {x : ℝ | x ≠ 0} _ _
      · apply recip_deriv
        simp
      · intro y hy
        apply hnz
    have hpr : is_deriv (D ∩ E) (fun x ↦ f x * (1 / g x))
     (fun x ↦ f' x * (1 / g x) + f x * (-1 / g x ^ 2 * g' x)) (D ∩ E) := by
      apply product_rule D f f' D hf E (fun x ↦ 1 / (g x)) (fun x ↦ (-1 / (g x) ^ 2) * (g' x)) E _
      exact hch
    have hf1 : (fun x ↦ f x / g x) = (fun x ↦ f x * (1 / g x)) := by
      refine funext ?_
      intro y
      exact div_eq_mul_one_div (f y) (g y)
    have hf2 : (fun x ↦ (f' x * g x - f x * g' x) / g x ^ 2)
     = (fun x ↦ f' x * (1 / g x) + f x * (-1 / g x ^ 2 * g' x)) := by
      refine funext ?_
      intro y
      rw [sub_div, sub_eq_add_neg]
      congr
      · rw [mul_div_assoc, ← zpow_one_sub_natCast₀ ?_]
        · simp only [Nat.cast_ofNat, Int.reduceSub, zpow_neg, zpow_one, one_div]
        · apply hnz
      · rw [← div_neg, mul_div_assoc, ← one_div_mul_eq_div, div_neg_eq_neg_div']
    rw [hf1, hf2]
    exact hpr

-- Proof that the derivative of a function on an interval is unique
lemma deriv_unique (D : Set ℝ) (f f' g' : ℝ → ℝ) (A : Set ℝ) :
 is_deriv D f f' A ∧ is_deriv D f g' A → ∀ x ∈ A, f' x = g' x := by
 intro h
 unfold is_deriv at h
 unfold is_deriv_at at h
 cases h; expose_names
 --pain
 sorry

--some specific derivative computations to simplify the proof in LeanValueTheorem
lemma const_x_const_deriv (D : Set ℝ) (c : ℝ) : is_deriv D (fun x => c*x) (fun x => c) D := by
 let fc : ℝ → ℝ := (fun x => c)
 let f0 : ℝ → ℝ := (fun x => 0)
 let fx : ℝ → ℝ := (fun x => x)
 let f1 : ℝ → ℝ := (fun x => 1)
 have hc : is_deriv D fc f0 D := by
  exact const_zero_deriv D (fun x ↦ c) D fun x y ↦ congrFun rfl
 have hx : is_deriv D fx f1 D := by
  exact x_one_deriv D
 have hf1 : (fun x => fc x * fx x) = (fun x => c * x) := by exact rfl
 have hf2 : (fun x => f0 x * fx x + fc x * f1 x) = (fun x => c) := by
  funext
  expose_names
  unfold f0
  unfold f1
  rw [zero_mul (fx x)]
  rw [mul_one (fc x)]
  exact AddZeroClass.zero_add (fc x)
 rw [← Set.inter_self D]
 rw [← hf1]
 rw [← hf2]
 refine product_rule D fc f0 D hc D fx f1 D hx

lemma g_deriv (D : Set ℝ) (c : ℝ) (f f' : ℝ → ℝ) (hff' : is_deriv D f f' D) :
 is_deriv D (fun x => f x - c * x) (fun x => f' x - c) D := by
 let fc : ℝ → ℝ := fun x => -c * x
 let fc' : ℝ → ℝ := fun x => -c
 have hc : is_deriv D fc fc' D := by exact const_x_const_deriv D (-c)
 have hf1 : (fun x ↦ f x + fc x) = (fun x => f x - c * x) := by
  funext; expose_names
  unfold fc
  rw [← sub_neg_eq_add (f x) (-c * x)]
  rw [neg_mul_eq_neg_mul (-c) x]
  rw [neg_neg c]
 have hf2 : (fun x ↦ f' x + fc' x) = (fun x => f' x - c) := by
  funext; expose_names
  unfold fc'
  exact rfl
 rw [← hf1]; rw [← hf2]
 have hf3 : is_deriv (D ∩ D) (fun x ↦ f x + fc x) (fun x ↦ f' x + fc' x) (D ∩ D) := by
  apply sum_rule D f f' D hff' D fc fc' D hc
 simp only [Set.inter_self] at hf3
 exact hf3
