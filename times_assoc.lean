import natural_numbers
import succ_times
import times_right_distrib

theorem times_assoc ( m n p : ℕ )
: m * ( n * p ) = ( m * n ) * p := by
  induction m using ℕ.rec
  case zero =>
    rewrite [times]
    rewrite [times]
    rewrite [times]
    rfl
  case succ m ih =>
    rw [succ_times]
    rw [succ_times]
    rw [ih]
    rewrite [← times_right_distrib]
    rfl
