import Mathlib.Data.Real.Basic
import LeanValueTheorem.Misc
import LeanValueTheorem.Limits
import LeanValueTheorem.Intervals
import LeanValueTheorem.Bounds

-- Defintion for m being the value of the derivative of f : D → ℝ at a
def is_deriv_at (D : Set ℝ) (f : ℝ → ℝ) (m : ℝ) (a : ℝ) : Prop :=
  a ∈ D →
  is_lim_fun {h : ℝ | a + h ∈ D ∧ h ≠ 0} (fun h ↦ (f (a + h) - f (a)) / h ) 0 m

-- Defintion for f' being the derivative of f : D → ℝ on a set A
def is_deriv (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (A : Set ℝ) : Prop :=
  ∀ a ∈ A, is_deriv_at D f (f' a) a

-- Proof that the value of the derivative of f : D → ℝ at a is unique
lemma deriv_at_unique (D : Set ℝ) (f : ℝ → ℝ) (m n : ℝ) (a : ℝ) (ha : a ∈ D) :
 (is_deriv_at D f m a ∧ is_deriv_at D f n a) → m = n := by
 let ha_1 := ha
 refine fun b ↦ ?_
 unfold is_deriv_at at b
 apply b.left at ha
 apply b.right at ha_1
 rw [← hunionrw] at ha
 rw [← hunionrw] at ha_1
 have : {h | a + h ∈ D ∧ h < 0} ⊆ ({h | a + h ∈ D ∧ h < 0} ∪ {h | a + h ∈ D ∧ h > 0}) := by
  exact Set.subset_union_left
 have :
  is_lim_fun {h | a + h ∈ D ∧ h < 0} (fun h ↦ (f (a + h) - f a) / h) 0 m := by
  sorry
 sorry


-- Proof that the derivative of a function on an interval is unique
lemma deriv_unique (D : Set ℝ) (f f' g' : ℝ → ℝ) (A : Set ℝ) :
 (is_deriv D f f' A ∧ is_deriv D f g' A) → ∀ x ∈ A ∩ D, f' x = g' x := by
 refine fun a x a_1 ↦ ?_
 have hA : x ∈ A := by exact Set.mem_of_mem_inter_left a_1
 let hA' := hA
 have hD : x ∈ D := by exact Set.mem_of_mem_inter_right a_1
 apply deriv_at_unique D f (f' x) (g' x) x hD
 unfold is_deriv at a
 apply a.left at hA
 apply a.right at hA'
 exact ⟨hA, hA'⟩

-- Proof that f'(a) is the value derivative of f : D → ℝ at a
lemma deriv_at_deriv (D : Set ℝ) (m a : ℝ) (f f' : ℝ → ℝ) (ha : a ∈ D)
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

-- Lemma used to work with limits of functions on different domains
lemma h_subset (a x : ℝ) (D E : Set ℝ) (f : ℝ → ℝ)
 (hf : is_lim_fun {h | a + h ∈ D ∧ h ≠ 0} (fun h ↦ (f (a + h) - f a) / h) 0 x) :
 is_lim_fun {h | a + h ∈ D ∩ E ∧ h ≠ 0} (fun h ↦ (f (a + h) - f a) / h) 0 x := by
      unfold is_lim_fun
      unfold is_lim_fun at hf
      intro ε hε
      specialize hf ε hε
      obtain ⟨δ, hδ⟩ := hf
      use δ
      obtain ⟨hδ1, hδ2⟩ := hδ
      constructor
      · exact hδ1
      · intro x
        specialize hδ2 x
        intro hx
        have hx1 : x ∈ {h | a + h ∈ D ∧ h ≠ 0} := by
          simp only [ne_eq, Set.mem_setOf_eq]
          simp only [Set.mem_inter_iff, ne_eq, Set.mem_setOf_eq] at hx
          obtain ⟨hx2, hx3⟩ := hx
          constructor
          · obtain ⟨hx4, hx5⟩ := hx2
            exact hx4
          · exact hx3
        exact hδ2 hx1

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
    have hf1 : is_lim_fun {h | a + h ∈ D ∩ E ∧ h ≠ 0} (fun h ↦ (f (a + h) - f a) / h) 0 (f' a) := by
      exact h_subset a (f' a) D E f hf
    have hg1 : is_lim_fun {h | a + h ∈ E ∩ D ∧ h ≠ 0} (fun h ↦ (g (a + h) - g a) / h) 0 (g' a) := by
      apply h_subset a (g' a) E D g hg
    have hset : {h | a + h ∈ E ∩ D ∧ h ≠ 0} = {h | a + h ∈ D ∩ E ∧ h ≠ 0} := by
      refine Set.ext ?_
      intro x
      simp only [Set.mem_inter_iff, ne_eq, Set.mem_setOf_eq, and_congr_left_iff]
      intro hx
      exact And.comm
    rw[hset] at hg1
    have heq : (fun h ↦ ((fun x ↦ f x + g x) (a + h) - (fun x ↦ f x + g x) a) / h)
     = (fun n ↦ (f (a + n) - f a) / n + (g (a + n) - g a) / n) := by
      funext
      rename ℝ => y
      simp only
      rw [add_sub_add_comm, add_div]
    rw[heq]
    exact fun_sum {h | a + h ∈ D ∩ E ∧ h ≠ 0}
     (fun h ↦ (f (a + h) - f a) / h) (fun h ↦ (g (a + h) - g a) / h) 0 (f' a) (g' a) hf1 hg1

-- Proof that the derivative of f * g is f' * g + f * g'
lemma product_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (A : Set ℝ) (hf : is_deriv D f f' A)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ) (B : Set ℝ) (hg : is_deriv E g g' B) :
  is_deriv (D ∩ E) (fun x ↦ (f x) * (g x))
  (fun x ↦ (f' x) * (g x) + (f x) * (g' x)) (A ∩ B) := by
    intro a ha1 ha2
    obtain ⟨haA, haB⟩ := ha1
    obtain ⟨haD, haE⟩ := ha2
    unfold is_deriv at hf hg
    unfold is_deriv_at at hf hg
    specialize hf a haA haD
    specialize hg a haB haE
    have hf1 : is_lim_fun {h | a + h ∈ D ∩ E ∧ h ≠ 0} (fun h ↦ (f (a + h) - f a) / h) 0 (f' a) := by
      exact h_subset a (f' a) D E f hf
    have hg1 : is_lim_fun {h | a + h ∈ E ∩ D ∧ h ≠ 0} (fun h ↦ (g (a + h) - g a) / h) 0 (g' a) := by
      apply h_subset a (g' a) E D g hg
    have hset : {h | a + h ∈ E ∩ D ∧ h ≠ 0} = {h | a + h ∈ D ∩ E ∧ h ≠ 0} := by
      refine Set.ext ?_
      intro x
      simp only [Set.mem_inter_iff, ne_eq, Set.mem_setOf_eq, and_congr_left_iff]
      intro hx
      exact And.comm
    rw[hset] at hg1
    sorry --hmmm

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
          simp only [Nat.cast_ofNat, Int.reduceNeg, Int.reduceAdd, neg_mul, one_mul, ne_eq]
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
        · simp
        · apply hnz
      · rw [← div_neg, mul_div_assoc, ← one_div_mul_eq_div, div_neg_eq_neg_div']
    rw [hf1, hf2]
    exact hpr

--simpler version of sum rule
lemma simple_sum_rule (D : Set ℝ) (f f' g g' : ℝ → ℝ)
                      (hf : is_deriv D f f' D) (hg : is_deriv D g g' D) :
 is_deriv D (fun x => f x + g x) (fun x => f' x + g' x) D := by
 have hx := sum_rule D f f' D hf D g g' D hg
 rw [Set.inter_self D] at hx
 exact hx


--some specific derivative computations to simplify the proof in LeanValueTheorem

-- Proof that cx has derivative c
lemma const_x_const_deriv (D : Set ℝ) (c : ℝ) : is_deriv D (fun x => c*x) (fun x => c) D := by
 let fc : ℝ → ℝ := (fun x => c)
 let f0 : ℝ → ℝ := (fun x => 0)
 let fx : ℝ → ℝ := (fun x => x)
 let f1 : ℝ → ℝ := (fun x => 1)
 have hc := const_zero_deriv D (fun x ↦ c) D
 have hx := x_one_deriv D
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
 exact product_rule D fc f0 D (hc fun x y ↦ congrFun rfl) D fx f1 D hx

-- Proof that g(x) = f(x) - cx has derivative f'(x) - c
lemma g_deriv (D : Set ℝ) (c : ℝ) (f f' : ℝ → ℝ) (hff' : is_deriv D f f' D) :
 is_deriv D (fun x => f x - c * x) (fun x => f' x - c) D := by
 let fc : ℝ → ℝ := fun x => -c * x
 let fc' : ℝ → ℝ := fun x => -c
 have hc := const_x_const_deriv D (-c)
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
 exact simple_sum_rule D f f' fc fc' hff' hc
