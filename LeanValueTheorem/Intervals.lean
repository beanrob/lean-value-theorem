import Mathlib.Data.Real.Basic


-- Definitions for intervals from a to b
  -- ooi = open-open interval
  -- cci = closed-closed interval
  -- oci = open-closed interval
  -- coi = closed-open interval
def ooi : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | min a b < x ∧ x < max a b })
def cci : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | min a b ≤ x ∧ x ≤ max a b })
def oci : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | min a b < x ∧ x ≤ max a b })
def coi : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | min a b ≤ x ∧ x < max a b })

-- Definition for whether a set is an interval
def is_interval (I : Set ℝ) : Prop :=
  ∃ a b : ℝ,
  I = ooi a b ∨
  I = cci a b ∨
  I = oci a b ∨
  I = coi a b

-- Defintion for whether a set is an open interval
def is_open (I : Set ℝ) : Prop :=
  ∃ a b : ℝ,
  I = ooi a b

-- Defintion for whether a set is a closed interval
def is_closed (I : Set ℝ) : Prop :=
  ∃ a b : ℝ,
  I = cci a b

-- Proof that open intervals are open
lemma open_interval (I : Set ℝ) : is_open I → is_interval I := by
  unfold is_open
  intro h
  let ⟨a, b, h'⟩ := h
  unfold is_interval
  use a
  use b
  aesop

-- Proof that closed intervals are closed
lemma closed_interval (I : Set ℝ) : is_closed I → is_interval I := by
  unfold is_closed
  intro h
  let ⟨a, b, h'⟩ := h
  unfold is_interval
  use a
  use b
  aesop

-- Proof that if x is in an open interval then it is in the corresponding closed interval
lemma open_in_closed (a b x : ℝ) (hxab : x ∈ (ooi a b)) : x ∈ (cci a b) := by
 exact ⟨le_of_lt hxab.left, le_of_lt hxab.right⟩


-- Proof that an open interval (a,b) with a < b is non-empty
lemma non_empty (a b : ℝ) (hab : a ≠ b) : ∃ c : ℝ, c ∈ (ooi a b) :=
 have h := min_lt_max.mpr hab
 have ha := left_lt_add_div_two.mpr h
 have hb := add_div_two_lt_right.mpr h
 Exists.intro ((min a b + max a b) / 2) (Set.mem_sep ha hb)

lemma closed_not_bounds_open
 (a b c : ℝ) (ha : c ≠ a) (hb : c ≠ b) (hab : c ∈ cci a b) :
 c ∈ ooi a b := by

 unfold ooi
 unfold cci at hab
 refine Set.mem_setOf.mpr ?_
 rw [Set.mem_setOf] at hab
 cases hab; expose_names

 have hmin : c ≠ min a b := by
  by_cases h : a ≤ b
  · simp [h, ha]
  · simp only [not_le] at h
    simp [le_of_lt h, hb]

 have hmax : c ≠ max a b := by
  by_cases h : a ≤ b
  · simp [h, hb]
  · simp only [not_le] at h
    simp [le_of_lt h, ha]

 and_intros
 · exact Std.lt_of_le_of_ne left (ne_comm.mp hmin)
 · exact Std.lt_of_le_of_ne right hmax
