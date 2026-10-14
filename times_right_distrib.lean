import natural_numbers
import plus_assoc

theorem times_right_distrib ( m n p : ℕ )
: (m + n ) * p = m*p + n*p := by
  induction m using ℕ.rec
  case zero =>
    rewrite [plus]
    rewrite [times]
    rewrite [plus]
    rfl
  case succ m ih =>
    rewrite [plus]
    rewrite [times]
    rewrite [ih]
    rewrite [times]
    rewrite [plus_assoc]
    rfl
