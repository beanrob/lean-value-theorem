# Documentation

This file contains brief documentation of what is formalised where, and the
purposes of each file in the project.

## `LeanValueTheorem.lean`

This file is in the root of the project. It contains the main results of the
project, including the mean value theorem itself. We were able to extend the
project beyond the initial specification to include Cauchy's mean value theorem
as well as Lagrange's.

### Formalised

- `theorem rolle` - Rolle's Theorem
- `theorem mvt` - Lagrange's Mean Value Theorem
- `theorem cauchy_mvt` - Cauchy's Mean Value Theorem

## `LeanValueTheorem` Folder

Most of the project code is contained in the `LeanValueTheorem` older, split up
into separate files for improved organisation.

### `Bolzano_Weierstrass.lean`

This file contains the pieces needed to prove Bolzano-Weierstrass theorem, which
is needed to prove that continuous functions are bounded.

#### Formalised

- `lemma rw1` - Rewrite for (a, b).1 = a
- `lemma rw2` - Rewrite for (a, b).2 = b
- `def in_left_prop` - Decider for x being in the left half of an interval
- `def in_right_prop` - Decider for x being in the right half of an interval
- `lemma split_prop` - Every x in an interval is in either the left or right half
- `def left_int` - Left half of an interval
- `def right_int` - Right half of an interval
- `def ab_pair` - Constructs the recursive sequence of intervals needed for deciding
  the nested intervals that contain an infinite number of points
- `def a` - Sequence of lower bounds of the nested intervals
- `def b` - Sequence of upper bounds of the nested intervals
- `lemma ab_pair_0` - The first interval is the lower and upper bounds of the sequence
- `lemma ha_val_0` - The first lower bound is the lower bound of the sequence
- `lemma hb_val_0` - The first upper bound is the upper bound of the sequence
- `lemma ha_vals` - The n+1 lower bound is either the nth lower bound or the midpoint
  of the nth interval
- `lemma hb_vals` - The n+1 upper bound is either the nth upper bound or the midpoint
  of the nth interval
- `lemma h_aseq_le_bseq` - The lower bounds are always less than or equal to the
  upper bounds
- `lemma a_inc1` - a n <= a (n + 1)
- `lemma b_dec1` - b (n + 1) <= b n
- `lemma a_inc2` - a is an increasing sequence
- `lemma b_dec2` - b is a decreasing sequence
- `lemma a_bounded_abv` - a is bounded above
- `lemma b_bounded_below` - b is bounded below
- `lemma inf_seq_points_ab` - The nth intervals contain infinitely many points of the
  original sequence
- `lemma diff_a_b` - The interval width halfs at each recursion
- `lemma diff2_a_b` - The Closed form of interval width at each recursion
- `lemma zero_lim_of_one_div_two_k` - The limit of 1/2^k is 0
- `lemma lim_b_sub_a` - The width of the intervals tends to 0
- `theorem bolzano_weierstrass` - Bolzano-Weierstrass Theorem

### `Bounded_Sequences.lean`

This file deals with various necessary pieces needed to prove
Bolzano-Weierstrass theorem, including formalising the Weierstrass criterion.

#### Formalised

- `lemma sequence_in_closed` - A sequence within a closed interval has its limit
  in that same interval
- `lemma supremum_nearly_attained` - The supremum of a bounded sequence is always 
  nearly attained
- `lemma infemum_nearly_attained` - The infemum of a bounded sequence is always nearly
  attained
- `lemma weierstrass_criterion_inc` - Weierstrass's Criterion for increasing
  sequences
- `lemma weierstrass_criterion_dec` - Weierstrass's Criterion for decreasing
  sequences

### `Bounds.lean`

This file deals specifically with bounded _functions_ instead of sequences.
Knowing that continuous functions are bounded is a key part of proving Rolle's
Theorem, so it is necessary to formalise notions of functions being bounded.

#### Formalised

- `theorem cont_closed_imp_bounded` - Continuous functions defined on a closed
  set are bounded
- `lemma bounded_has_GLB_and_LUB` - Bounded functions have a definitive greatest
  lower bound and least upper bound
- `theorem cont_closed_attained_bounds` - Continuous functions defined on a
  closed set attain their bounds

### `Cont.lean`

This file deals with continuity of functions, defining it in both the
epsilon-delta sense and the sequential sense. Then, the continuity of various
form factors of functions were proven, such as sums and reciprocals.

#### Formalised

- `def is_cont_at_ε_δ` - Continuity at one point in the epsilon-delta sense
- `def is_cont_at_seq` - Continuity at one point in the sequential sense
- `def is_cont_at` - Overall continuity at one point, requiring both of the
  above
- `def is_cont_on` - Continuity of a function on a set
- `def is_cont` - Continuity of a function on the whole of its domain
- `lemma cont_ε_δ_imp_cont_seq` - Epsilon-delta continuity implies sequential
  continuity
- `cont_seq_imp_cont_ε_δ` - Sequential continuity implies epsilon-delta
  continuity
- `lemma cont_sum` - The sum of functions that are continuous at a point is
  continuous at that same point
- `lemma cont_on_sum` The sum of functions that are continuous on a set is
  continuous on that same set
- `lemma cont_scalar_prod` - The function multiplied by a scalar that is
  continuous at a point is continuous at that same point
- `lemma cont_prod` - The product of functions that are continuous at a point is
  continuous at that same point
- `lemma cont_prod` - The product of functions that are continuous on a set is
  continuous on that same set
- `lemma cont_quot` - The quotient of functions that are continuous at a point
  is continuous at that same point, provided the divisor is non-zero there
- `lemma cont_quot` - The quotient of functions that are continuous on a set
  is continuous on that same set, provided the divisor is non-zero on it
- `lemma reciprocal_cont` - The reciprocal of a function that is continuous at a
  point is continuous at that same point, provided it is non-zero there
- `lemma id_cont` - The identity function is continuous
- `lemma const_cont` - The constant function is continuous


### `Derivatives.lean`

This file deals with the formalisation of derivatives and various rule
surrounding them. Rules for differentiation such as the product and chain rules
are proven here.

#### Formalised

- `def is_deriv_at` - Derivative of a function at a point
- `def_is_deriv` - Derivative of a function on its domain
- `lemma deriv_at_unique` - The value of a derivative at a point is unique
- `lemma deriv_unique` - The derivative of a function is unique
- `lemma const_zero_deriv` - The constant function has zero derivative
- `lemma x_one_deriv` - The derivative of the identity function is 1
- `lemma recip_deriv` - The derivative of the reciprocal function
- `lemma h_subset` - (This is not a "real" result, just needed to simplify working with limits of functions with different domains)
- `lemma sum_rule` - The sum rule for differentiation
- `lemma product_rule` - The product rule for differentiation
- `lemma scale_rule` - The derivative of a function multiplied by a scalar
- `lemma power_rule` - The derivative of the n-th power function
- `lemma local_lin` - The derivative yields a local linearisation of the function
- `lemma quotient_rule` - The quotient rule for differentiation
- `lemma simple_sum_rule` - Special case of the sum rule
- `lemma const_x_const_deriv` - The derivative of the identity multiplied by a
  constant
- `lemma g_deriv` - The derivative of of a given function with the identity
  multiplied by a constant being subtracted

### Unformalised

- `lemma chain_rule` - The chain rule for differentiation
  - The proof requires chosing several different epsilons and deltas that emerge from the properties of the functions involved. There are also two cases depending on if a certain value is zero or not. Proof of the chain rule was left until late in the project and there was not enough time to complete it.
- `lemma power_rule_neg` - An analogue of `lemma power_rule` for negative
  exponents
  - Almost complete, but the use of the chain rule requires showing that x^n is continuous, a result which was not proved in Cont.lean.

### `Intervals.lean`

The intervals file provides some small definitions for interval sets that can be
utilised by the other files. Notions of boundedness and openness/closedness of
sets are also included.

#### Formalised

- `def ooi` - Interval that is open on both ends
- `def cci` - Interval that is closed on both ends
- `def oci` - Interval that is closed only on the right
- `def coi` - Interval that is closed only on the left
- `def is_interval` - Whether a given set is an interval
- `def is_open` - Whether an interval is open
- `def is_closed` - Whether an interval is closed
- `lemma open_interval` - Open intervals are open
- `lemma closed_interval` - Closed intervals are closed
- `lemma open_in_closed` - A open interval is a subset of the closed interval
  with the same boundaries
- `lemma bounds_in_closed` - A closed interval contains its bounds
- `lemma bounds_no_in_open` - An open interval does not contain its bounds
- `lemma non-empty` - An open interval with non-equal boundaries is non-empty
- `lemma non_empty_closed` - The above for closed intervals
- `lemma closed_not_bounds_open` - A point in a closed interval that is not a
  boundary point is in the corresponding open interval too
- `lemma huniorw` - ???
- `lemma openrwl` - ???
- `lemma openrw2` - ???
- `lemma openrw3` - ???
- `lemma openrw4` - ???
- `lemma openrw5` - ???

### `Limits.lean`

This file deals with the notion of limits of functions, which is necessary
groundwork for the derivatives file.

#### Formalised

- `def is_lim_fun` - The limit of a function
- `lemma const_fun_limit` - The constant function's limit is its value
- `lemma const_fun_limit_unique` - The constant function's limit is unique
- `lemma fun_sum` - Algebra of limits for function sums
- `lemma fun_lim_of_fun_sub_lim` - Reverse of the below
- `lemma fun_sub_lim_of_fun_lim` - A function minus its limit has limit 0
- `lemma fun_scalar_prod` - A function multiplied by a scalar has its limit
  multiplied by that scalar too
- `lemma fun_prod_special` - The limit of two functions tending to zero is zero
- `lemma fun_prod` - Algebra of limits for function products
- `lemma fun_neq_zero_of_lim_neq_zero` - Function with non-zero limit is
  non-zero past a certain point
- `lemma fun_recip` - Algebra of limits for the reciprocal of a function
- `lemma fun_quot` - Algebra of limits for function quotients
- `lemma fun_non_negative` - Non-negative functions have non-negative limits
- `lemma fun_non_positive` - Non-positive functions have non-positive limits
- `lemma lim_fun_unique` - The limit of a function is unique
- `lemma lim_exists_on_subset` - ???
- `lemma lim_union` - ???
- `lemma special_lim_fun_unique` - ???

### `Misc.lean`

This file is for miscellaneous results with no other obvious home. Most results
are related to the constant function and are utilised by the sequences file.

#### Formalised

- `def is_const_fun` - If a function is constant
- `lemma const_closed_imp_const_open` - A function being constant on a closed
  interval implies it is constant on the corresponding open interval too
- `lemma closed_const` - If a function is constant on the closed interval, all
  its values must be the same as that of the value at the lower boundary
- `lemma not_const_imp_diff` - Negation of the above
- `lemma left_le_add_div_two` - Given a <= b, a <= (a + b) / 2
- `lemma add_div_two_le_right` - Given a <= b, (a + b) / 2 <= b

### `Sequences.lean`

This file is concerned with formalising sequences. The project defines sequences
as functions from the natural numbers to the real numbers, with the input value
being the index.

#### Formalised

- `def is_sequence` - Defintion of a sequence - in end any function from ℕ to ℝ was decided to be a sequence
- `def is_sequence_non_positive` - Non-positive sequences
- `def is_sequence_non_negative` - Non-negative sequences
- `def is_lim_seq` - The limit of a sequence
- `lemma const_seq_limit` - The limit of a constant sequence is its value
- `lemma seq_sum` - Algebra of limits for sequence sums
- `lemma seq_lim_of_seq_sub_lim` - Given a sequence of the form (sequence - constant) with limit 0 the limit of the sequence is the constant
- `lemma seq_sub_lim_of_seq_lim` - Given a sequence with some limit, the new sequence formed by (old sequence - limit) has limit 0
- `lemma seq_scalar_product` - A sequence multiplied by a scalar has its limit
  multiplied by that scalar too
- `lemma seq_non_negative` - Non-negative sequences have non-negative limits
- `lemma seq_non_positive` - Non-positive sequences have non-positive limits
- `lemma seq_prod_special` - The limit of two sequences tending to zero is zero
- `lemma seq_prod` - Algebra of limits for sequence products
- `lemma seq_neg_zer_of_lim_neq_zero` - Sequence with non-zero limit is non-zero
  past a certain point
- `lemma seq_recip` - Algebra of limits for the reciprocal of a function
- `lemma seq_quot` - Algebra of limits for sequence quotients
- `lemma sandwich` - Given a sequence bounded above and below by two sequences with the same limit, the sequence has that same limit too
