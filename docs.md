# Documentation

This file contains brief documentation of what is formalised where, and the
purposes of each file in the project.

## `LeanValueTheorem.lean`

This file is in the root of the project. It contains the main results of the
project, including the mean value theorem itself. We were able to extend the
project beyond the initial specification to include Cauchy's mean value theorem
as well as Lagrange's.

### Formalised:
- `theorem rolle` - Rolle's Theorem
- `theorem mvt` - Lagrange's Mean Value Theorem
- `theorem cauchy_mvt` - Cauchy's Mean Value Theorem

## `LeanValueTheorem` Folder

Most of the project code is contained in the `LeanValueTheorem` older, split up
into separate files for improved organisation.

### `Bolzano_Weierstrass.lean`

This file contains the pieces needed to prove Bolzano-Weierstrass theorem, which
is needed to prove that continuous functions are bounded. 

#### Formalised:
- `theorem bolzano_weierstrass` - Bolzano-Weierstrass Theorem

### `Bounded_Sequences.lean`

This file deals with various necessary pieces needed to prove
Bolzano-Weierstrass theorem, including formalising the Weierstrass criterion.

#### Formalised:
- `lemma sequence_in_closed` - A sequence within a closed interval has its limit
  in that same interval
- `lemma supremum_nearly_attained` - ???
- `lemma infemum_nearly_attained` - ???
- `lemma weierstrass_criterion_inc` - Weierstrass's Criterion for increasing
  sequences
- `lemma weierstrass_criterion_dec` - Weierstrass's Criterion for decreasing
  sequences

### `Bounds.lean`

This file deals specifically with bounded _functions_ instead of sequences.
Knowing that continuous functions are bounded is a key part of proving Rolle's
Theorem, so it is necessary to formalise notions of functions being bounded.

#### Formalised:
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

#### Formalised:
- `def is_cont_at_ε_δ` - Continuity at one point in the epsilon-delta sense
- `def is_cont_at_seq` - Continuity at one point in the sequential sense
- `def is_cont_at` - Overall continuity at one point, requiring both of the
  above
- `def is_cont_on` - Continuity of a function on a set
- `def is_cont` - Continuity of a function on the whole of its domain
- `lemma cont_ε_δ_imp_cont_seq` - Epsilon-delta continuity implies sequential
  continuity
- `lemma cont_sum` - The sum of functions that are continuous at a point is
  continuous at that same point
- `lemma cont_on_sum` The sum of functions that are continuous on a set is
  continuous on that same set
- `lemma cont_scalar_prod` - ???
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

#### Unformalised:
- `cont_seq_imp_cont_ε_δ` - Sequential continuity implies epsilon-delta
  continuity
  - The way that continuity is currently formalised, there were roadblocks in
    proving this notion
  - The generally accepted method of proof for this is proof by contradiction,
    which is what was attempted, but constructing the sequence needed to do so
    was not possible due to its vague definition
  - The sequence is built as follows:
    > For each $n$ choose a point $x_n$ with $|x_n − a| < \frac{1}{n}$ but $|f(x_n) − f(a)| \geq \epsilon$.
  - Although such a sequence of points exists, sequences in this project are
    formalised as functions from naturals to reals, and we could not figure out
    how to deifne a function that maps the natural numbers onto such a series of
    points
  - When seeking an alternative method of proof, a solution was nearly found,
    but a final roadblock was found, in that the sequence used for the proof
    would need to have limit $a$ but be equal to a certain point $x$ for some
    arbitrarily large $n$
  - The incomplete proof is included in the file

### `Derivatives.lean`
This file deals with the formalisation of derivatives and various rule
surrounding them. Rules for differentiation such as the product and chain rules
are proven here.

#### Formalised:
- `def is_deriv_at` - Derivative of a function at a point
- `def_is_deriv` - Derivative of a function on its domain
- `lemma deriv_at_unique` - The value of a derivative at a point is unique
- `lemma deriv_unique` - The derivative of a function is unique
- `lemma const_zero_deriv` - The constant function has zero derivative
- `lemma x_one_deriv` - The derivative of the identity function is 1
- `lemma recip_deriv` - The derivative of the reciprocal function
- `lemma h_subset` - ???
- `lemma sum_rule` - The sum rule for differentiation
- `lemma product_rule` - The product rule for differentiation
- `lemma scale_rule` - The derivative of a function multiplied by a scalar
- `lemma power_rule` - The derivative of the n-th power function
- `lemma chain_rule` - The chain rule for differentiation
- `lemma power_rule_neg` - An analogue of `lemma power_rule` for negative
  exponents
- `lemma quotient_rule` - The quotient rule for differentiation
- `lemma simple_sum_rule` - Special case of the sum rule
- `lemma const_x_const_deriv` - The derivative of the identity multiplied by a
  constant
- `lemma g_deriv` - The derivative of of a given function with the identity
  multiplied by a constant being subtracted

### `Intervals.lean`

The intervals file provides some small definitions for interval sets that can be
utilised by the other files. Notions of boundedness and openness/closedness of
sets are also included.

#### Formalised:
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
### `Misc.lean`
### `Sequences.lean`
