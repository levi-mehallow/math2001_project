import natural_numbers
import times_zero
import times_succ

theorem times_comm ( m n : ℕ )
: m * n = n * m := by
  induction m using ℕ.rec
  case zero =>
    rewrite [times]
    rewrite [times_zero]
    rfl
  case succ m ih =>
    rewrite [times]
    rewrite [times_succ]
    rewrite [ih]
    rfl
