import natural_numbers
import plus_zero
import plus_succ

theorem plus_comm ( m n : ℕ )
: m + n = n + m := by
  induction m using ℕ.rec
  case zero =>
    rewrite [plus]
    rewrite [plus_zero]
    rfl
  case succ m ih =>
    rewrite [plus]
    rewrite [plus_succ]
    rewrite [ih]
    rfl
