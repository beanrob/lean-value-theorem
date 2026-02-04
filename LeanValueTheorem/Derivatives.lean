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


-- The next 3 lemmas are only proven for functions on open intervals

-- Proof that the value of the derivative of f : (ooi l r) → ℝ at a is unique
lemma deriv_at_unique (l r : ℝ) (f : ℝ → ℝ) (m n : ℝ) (a : ℝ) (hlr : l < r) (ha : a ∈ (ooi l r)) :
 (is_deriv_at (ooi l r) f m a ∧ is_deriv_at (ooi l r) f n a) → m = n := by
 let ha_1 := ha
 let ha_2 := ha
 refine fun z ↦ ?_
 unfold is_deriv_at at z
 apply z.left at ha_1
 apply z.right at ha_2
 rw [openrw4 l r a hlr ha] at ha_1
 rw [openrw4 l r a hlr ha] at ha_2
 refine special_lim_fun_unique 0 m n (l-a) (r-a) (fun h ↦ (f (a + h) - f a) / h) ?_ ?_ ha_1 ha_2
 · unfold ooi
   unfold ooi at ha
   rw [min_sub_sub_right]
   rw [max_sub_sub_right]
   rw [min_eq_left_of_lt hlr]
   rw [max_eq_right_of_lt hlr]
   rw [min_eq_left_of_lt hlr] at ha
   rw [max_eq_right_of_lt hlr] at ha
   rw [show (a ∈ {x | l < x ∧ x < r}) = (l < a ∧ a < r) from rfl] at ha
   exact Set.mem_sep (sub_neg.mpr ha.left) (sub_pos.mpr ha.right)
 · exact sub_lt_sub_right hlr a

-- Proof that the derivative of a function on an interval is unique
lemma deriv_unique (l r : ℝ) (f f' g' : ℝ → ℝ) (hlr : l < r) :
 (is_deriv (ooi l r) f f' (ooi l r) ∧ is_deriv (ooi l r) f g' (ooi l r)) →
  ∀ x ∈ (ooi l r), f' x = g' x := by
 refine fun a x a_1 ↦ ?_
 let a_2 := a_1
 apply deriv_at_unique l r f (f' x) (g' x) x hlr a_1
 unfold is_deriv at a
 apply a.left at a_1
 apply a.right at a_2
 exact ⟨a_1, a_2⟩

-- Proof that f'(a) is the value derivative of f : D → ℝ at a
lemma deriv_at_deriv (l r m a : ℝ) (f f' : ℝ → ℝ) (hlr : l < r) (ha : a ∈ (ooi l r))
 (hf' : is_deriv (ooi l r) f f' (ooi l r)) (hf : is_deriv_at (ooi l r) f m a) : f' a = m := by
 unfold is_deriv at hf'
 have hderiv : is_deriv_at (ooi l r) f (f' a) a := by exact hf' a ha
 have hand : is_deriv_at (ooi l r) f m a ∧ is_deriv_at (ooi l r) f (f' a) a := by
  exact ⟨hf, hf' a ha⟩
 exact deriv_at_unique l r f (f' a) m a hlr ha (id (And.symm hand))



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
    simp only
    have hrecip : is_lim_fun {h | a + h ∈ D ∧ h ≠ 0}
     (fun h ↦ 1 / -((a + h) * a)) 0 (1 / -a ^ 2) := by
      apply fun_recip {h | a + h ∈ D ∧ h ≠ 0}
      · have hshift : (fun h ↦ -((a + h) * a)) = (fun h ↦ -a * (a + h)) := by
          funext h
          simp only [neg_mul, neg_inj]
          rw [mul_comm]
        rw[hshift]
        rw [sq, neg_mul_eq_neg_mul]
        apply fun_scalar_prod {h | a + h ∈ D ∧ h ≠ 0} (fun h ↦ a + h) (-a) a 0
        nth_rewrite 3 [← add_zero a]
        apply fun_sum {h | a + h ∈ D ∧ h ≠ 0} (fun h ↦ a) (fun h ↦ h) 0 a 0
        · apply const_fun_limit
        · intro ε hε
          use ε
          constructor
          · exact hε
          · intro x hx1 hx2
            simp only [sub_zero]
            simp only [sub_zero] at hx2
            exact hx2
      · specialize hD a ha
        simp only [ne_eq, neg_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
        exact hD
    unfold is_lim_fun
    unfold is_lim_fun at hrecip
    intro ε hε
    specialize hrecip ε hε
    obtain ⟨δ, hδ, hrecip⟩ := hrecip
    use δ
    constructor
    · exact hδ
    · intro x hx1 hx2
      specialize hrecip x hx1 hx2
      simp only
      simp only at hrecip
      have heq : 1 / -((a + x) * a) - 1 / -a ^ 2 = (1 / (a + x) - 1 / a) / x - -1 / a ^ 2 := by
        obtain ⟨hxa, hx0⟩ := hx1
        rw [← div_neg_eq_neg_div', sub_left_inj, div_sub_div 1 1 ?_ ?_]
        · rw [one_mul, mul_one, sub_add_cancel_left, div_right_comm, neg_div_self ?_]
          · rw [← div_neg_eq_neg_div']
          · exact hx0
        · exact hD (a + x) hxa
        · exact hD a ha
      exact lt_of_eq_of_lt (congrArg abs (id (Eq.symm heq))) hrecip

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
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ) (B : Set ℝ) (hg : is_deriv E g g' B)
  (hcont : is_cont_on g E B) :
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
    have hh1 : (fun x ↦ f' x * g x + f x * g' x) a = (f' a) * (g a) + (f a) * (g' a) := by
      simp
    rw [hh1]
    have hh2 : (fun h ↦ ((fun x ↦ f x * g x) (a + h) - (fun x ↦ f x * g x) a) / h)
     = (fun h ↦ ((f (a + h) - f (a)) / h) * (g (a + h)) + (f a) * ((g (a + h) - g (a)) / h)) := by
      funext h
      simp only
      rw [div_mul_eq_mul_div, mul_div, ← add_div, sub_mul, mul_sub]
      simp
    rw [hh2]
    apply fun_sum {h | a + h ∈ D ∩ E ∧ h ≠ 0}
     (fun h => (f (a + h) - f a) / h * g (a + h)) (fun h => f a * ((g (a + h) - g a) / h))
     0 (f' a * g a) (f a * g' a) ?_ ?_
    · apply fun_prod {h | a + h ∈ D ∩ E ∧ h ≠ 0}
       (fun h => (f (a + h) - f a) / h) (fun h => g (a + h)) 0 (f' a) (g a) ?_ ?_
      · exact hf1
      · specialize hcont a haB
        unfold is_cont_at at hcont
        obtain ⟨hed, _ ⟩ := hcont
        specialize hed haE
        unfold is_lim_fun
        intro ε hε
        specialize hed ε hε
        obtain ⟨δ, hδ⟩ := hed
        use δ
        obtain ⟨hδ0, hδ1⟩ := hδ
        constructor
        · exact hδ0
        · intro h h1 h2
          simp only
          specialize hδ1 (a + h)
          have hE : (a + h) ∈ E := by
            simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at h1
            obtain ⟨h11, _⟩ := h1
            obtain ⟨_, h112⟩ := h11
            exact h112
          specialize hδ1 hE
          simp only [add_sub_cancel_left] at hδ1
          simp only [sub_zero] at h2
          specialize hδ1 h2
          exact hδ1
    · apply fun_prod {h | a + h ∈ D ∩ E ∧ h ≠ 0}
       (fun h => f a) (fun h => (g (a + h) - g a) / h) 0 (f a) (g' a) ?_ ?_
      · apply const_fun_limit
      · exact hg1

-- Proof that the derivative of rf is rf'
lemma scale_rule
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (A : Set ℝ) (hf : is_deriv D f f' A)
  (r : ℝ) : is_deriv D (fun x ↦ r * (f x)) (fun x ↦ r * (f' x)) A := by
    have hconst : is_deriv D (fun y ↦ r) 0 A := by
      apply const_zero_deriv
      intro x y hxy
      simp
    have hprod : is_deriv (D ∩ D) (fun x ↦ f x * r) (fun x ↦ f' x * r + f x * 0) (A ∩ A) := by
      apply product_rule D f f' A hf D (fun y ↦ r) 0 A hconst ?_
      unfold is_cont_on
      intro a ha
      unfold is_cont_at
      have hcont : is_cont_at_ε_δ (fun y ↦ r) D a := by
        unfold is_cont_at_ε_δ
        intro haD ε hε
        simp only [gt_iff_lt, sub_self, abs_zero]
        use 1
        constructor
        · simp
        · intro x hx hax
          exact hε
      constructor
      · exact hcont
      · apply cont_ε_δ_imp_cont_seq (fun y ↦ r) D a
        exact hcont
    simp at hprod
    have h1 : (fun x ↦ r * f x) = (fun x ↦ f x * r) := by
      funext x
      rw [mul_comm]
    have h2 : (fun x ↦ r * f' x) = (fun x ↦ f' x * r) := by
      funext x
      rw [mul_comm]
    rw [h1, h2]
    exact hprod

-- Proof that the derivative of x ^ n is n * x ^ (n + 1) for n ∈ ℕ
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
      apply product_rule D (fun x ↦ x ^ n) (fun x ↦ ↑n * x ^ (n - 1))
       D hn D (fun x ↦ x) (fun x ↦ 1) D _ ?_
      · exact x_one_deriv D
      · have hid : is_cont (fun x => x) D := by
          exact id_cont D
        unfold is_cont_on
        unfold is_cont at hid
        intro a ha
        specialize hid a ha
        exact hid
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

-- Proof of local linearisation property (used for chain rule)
lemma local_lin
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (A : Set ℝ) (hf : is_deriv D f f' A) :
  ∀ c ∈ A, ∃ ε : ℝ → ℝ,  (∀ x ∈ A,
  (f x) - (f c) = (f' c) * (x - c) + (ε x) * (x - c)) ∧ ε c = 0 ∧ is_cont_at ε D c := by
    intro c hc
    use fun x ↦
      if x = c then 0
      else ((f x) - (f c)) / (x - c) - (f' c)
    constructor
    · intro y hy
      simp only [ite_mul, zero_mul]
      by_cases heq : y = c
      · rw [heq]
        simp
      · rw [if_neg heq, ← add_mul]
        rw [show (f y - f c) / (y - c) - f' c = (f y - f c) / (y - c) + -f' c from rfl]
        rw [add_add_neg_cancel'_right, div_mul_cancel₀ (f y - f c) ?_]
        rw [sub_ne_zero]
        exact heq
    · constructor
      · simp
      · unfold is_cont_at
        have hcont : is_cont_at_ε_δ
         (fun x ↦ if x = c then 0 else (f x - f c) / (x - c) - f' c) D c := by
          unfold is_cont_at_ε_δ
          intro hc1
          intro η hη
          unfold is_deriv at hf
          specialize hf c hc
          unfold is_deriv_at at hf
          specialize hf hc1
          unfold is_lim_fun at hf
          specialize hf η hη
          obtain ⟨δ, hδ, hf⟩ := hf
          use δ
          constructor
          · exact hδ
          · intro x hx1 hx2
            by_cases heq : x = c
            · rw [heq]
              simp only [↓reduceIte, sub_self, abs_zero]
              exact hη
            · simp only [↓reduceIte, sub_zero]
              rw [if_neg heq]
              specialize hf (x - c)
              simp only [ne_eq, Set.mem_setOf_eq, add_sub_cancel, sub_zero, and_imp] at hf
              specialize hf hx1 ?_
              · rw [← ne_eq, sub_ne_zero]
                exact heq
              · specialize hf hx2
                exact hf
        constructor
        · exact hcont
        · apply cont_ε_δ_imp_cont_seq
           (fun x ↦ if x = c then 0 else (f x - f c) / (x - c) - f' c) D c
          exact hcont

-- Proof that the derivative of g(f) is f' * g'(f)
lemma chain_rule
--I ran out of time to complete this as it ended up being much harder to prove than I expected
--a lot of the proof is here but the final steps are missing
  (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (A : Set ℝ) (hf : is_deriv D f f' A)
  (E : Set ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ) (B : Set ℝ) (hg : is_deriv E g g' B)
  (hdom : ∀ x ∈ D, (f x) ∈ B) (hdom' : ∀ x ∈ D, (f x) ∈ E) (hfcont : is_cont_on f D A) :
  is_deriv D (fun x ↦ g (f x))
  (fun x ↦ (g' (f x)) * (f' x)) A := by
    intro a ha1 ha2
    simp only
    have hlin :
     ∀ c ∈ B, ∃ ε : ℝ → ℝ,  (∀ x ∈ B,
     (g x) - (g c) = (g' c) * (x - c) + (ε x) * (x - c)) ∧ ε c = 0 ∧ is_cont_at ε E c := by
      exact local_lin E g g' B hg
    specialize hlin (f a) ?_
    · specialize hdom a ha2
      exact hdom
    · obtain ⟨ε, hlin⟩ := hlin
      unfold is_lim_fun
      intro η hη
      unfold is_deriv at hf
      specialize hf a ha1
      unfold is_deriv_at at hf
      specialize hf ha2
      unfold is_lim_fun at hf
      specialize hf (η / |2 * (g' (f a))|) ?_
      --from here on there actually need to be two cases, to account for if (g' (f a)) = 0
      --both work but they need different choices in hf and hcont
      · refine (div_pos_iff_of_pos_left hη).mpr ?_
        simp only [abs_mul, Nat.abs_ofNat, Nat.ofNat_pos, mul_pos_iff_of_pos_left, abs_pos, ne_eq]
        sorry --this is true in case 1
      · obtain ⟨δ1, hδ1, hf⟩ := hf
        obtain ⟨hlin, hε, hcont⟩ := hlin
        obtain ⟨hcont, _⟩ := hcont
        unfold is_cont_at_ε_δ at hcont
        specialize hcont ?_
        · exact hdom' a ha2
        · specialize hcont (η / ((η / |(g' (f a))|) + 2 * |f' a|)) ?_
          · refine div_pos_iff.mpr ?_
            left
            constructor
            · exact hη
            · refine Right.add_pos_of_pos_of_nonneg ?_ ?_
              · refine div_pos hη ?_
                simp
                sorry --this is true in case 1
              · simp
          · obtain ⟨δ2, hδ2, hcont⟩ := hcont
            unfold is_cont_on at hfcont
            specialize hfcont a ha1
            unfold is_cont_at at hfcont
            obtain ⟨hfcont, _⟩ := hfcont
            unfold is_cont_at_ε_δ at hfcont
            specialize hfcont ha2 δ2 ?_
            · exact hδ2
            obtain ⟨δ3, hδ3, hfcont⟩ := hfcont
            use min δ1 δ2
            constructor
            · sorry --very provable
            · intro h hh hδ
              simp only [sub_zero] at hδ
              specialize hlin (f (a + h)) ?_
              · apply hdom (a + h) ?_
                · obtain ⟨h1, h0⟩ := hh
                  exact h1
              · simp only
                rw [hlin]
                rw [← add_mul, mul_div_assoc]
                specialize hcont (f (a + h)) ?_
                · sorry --very provable
                · specialize hdom' (a + h) ?_
                  · obtain ⟨h1, h0⟩ := hh
                    exact h1
                  · specialize hf h hh
                    simp only [sub_zero] at hf
                    specialize hf ?_
                    · sorry --very provable
                    · rw [hε] at hcont
                      simp only [sub_zero] at hcont
                      specialize hfcont (a + h) ?_
                      · obtain ⟨h1, h0⟩ := hh
                        exact h1
                      · simp at hfcont
                        specialize hfcont ?_
                        · sorry --very provable
                        · specialize hcont hfcont
                          rw [add_mul]
                          rw [add_comm]
                          rw [add_sub_assoc]
                          rw [← mul_sub]
                          have htri : |ε (f (a + h)) * ((f (a + h) - f a) / h) +
                           g' (f a) * ((f (a + h) - f a) / h - f' a)| ≤
                           |ε (f (a + h)) * ((f (a + h) - f a) / h)|
                            + |g' (f a) * ((f (a + h) - f a) / h - f' a)| := by
                            apply abs_add_le
                          have hans : |ε (f (a + h)) * ((f (a + h) - f a) / h)| +
                           |g' (f a) * ((f (a + h) - f a) / h - f' a)| < η := by
                            simp only [abs_mul]
                            have hright : |g' (f a)| * |(f (a + h) - f a) / h - f' a| < η / 2 := by
                              rw [← lt_div_iff₀' ?_]
                              · rw [div_div η 2 |g' (f a)|]
                                simp only [abs_mul, Nat.abs_ofNat] at hf
                                exact hf
                              · sorry --this is true in case 1
                            have hleft : |ε (f (a + h)) * ((f (a + h) - f a) / h)| < η / 2 := by
                              simp only [abs_mul]
                              sorry --this is true but needs a lot of rearranging still
                            have halm : |ε (f (a + h))| * |(f (a + h) - f a) / h| +
                             |g' (f a)| * |(f (a + h) - f a) / h - f' a| < (η / 2) + (η / 2) := by
                              refine Left.add_lt_add ?_ hright
                              simp only [abs_mul] at hleft
                              exact hleft
                            simp at halm
                            exact halm
                          exact Std.lt_of_le_of_lt htri hans

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
     · simp only [Set.mem_setOf_eq]
       exact fun x a ↦ zpow_ne_zero n (hD x a)
     · sorry --x^n cts
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
  (hnz : ∀ x, (g x) ≠ 0) (hcont : is_cont g E) :
  is_deriv (D ∩ E) (fun x ↦ (f x) / (g x))
  (fun x ↦ ((f' x) * (g x) - (f x) * (g' x)) / (g x) ^ 2) (D ∩ E) := by
    have hch : is_deriv E (fun x ↦ 1 / (g x)) (fun x ↦ (-1 / (g x) ^ 2) * (g' x)) E := by
      apply chain_rule E g g' E hg
       {x : ℝ | x ≠ 0} (fun x ↦ 1 / x) (fun x ↦ -1 / x^2) {x : ℝ | x ≠ 0} _ _
      · simp only [Set.mem_setOf_eq]
        exact fun x a ↦ hnz x
      · unfold is_cont_on
        unfold is_cont at hcont
        exact hcont
      · apply recip_deriv
        simp
      · intro y hy
        apply hnz
    have hpr : is_deriv (D ∩ E) (fun x ↦ f x * (1 / g x))
     (fun x ↦ f' x * (1 / g x) + f x * (-1 / g x ^ 2 * g' x)) (D ∩ E) := by
      apply product_rule D f f' D hf E (fun x ↦ 1 / (g x))
       (fun x ↦ (-1 / (g x) ^ 2) * (g' x)) E _ ?_
      · exact hch
      · apply reciprocal_cont g E
        · exact hcont
        · intro x _
          specialize hnz x
          exact hnz
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
 apply product_rule D fc f0 D (hc fun x y ↦ congrFun rfl) D fx f1 D hx ?_
 exact id_cont D

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
