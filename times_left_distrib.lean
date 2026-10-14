import natural_numbers
import plus_assoc
import plus_comm

theorem times_left_distrib ( m n p : ℕ )
: m * ( n + p ) = m*n + m*p := by
  induction m using ℕ.rec
  case zero =>
    unfold times
    rewrite [plus]
    rfl
  case succ m ih =>
    unfold times
    rewrite [ih]
    rewrite [plus_assoc]
    rewrite [plus_assoc]
    rewrite [← plus_assoc]
    rewrite [← plus_assoc n p (m*n + m*p)]
    rewrite [plus_assoc p (m*n)]
    rewrite [plus_comm p (m*n)]
    rewrite [← plus_assoc]
    conv => rhs ; rewrite [← plus_assoc]
    conv => rhs ; rewrite [← plus_assoc]
    -- Wow, it hurt trying to do that.
