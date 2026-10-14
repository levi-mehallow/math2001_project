import natural_numbers
import plus_assoc
import plus_comm

theorem times_succ ( m n : ℕ )
: m * n.succ = m + m * n := by
  induction m using ℕ.rec
  case zero =>
    unfold plus times
    rfl
  case succ m ih =>
    unfold plus
    unfold times
    rewrite [plus]
    rewrite [ih]
    -- apply congrArg
    -- rewrite [plus_assoc n m (m*n)]
    -- rewrite [plus_assoc m n (m*n)]
    -- rewrite [plus_comm m n]
    -- rfl
    rewrite [plus_assoc]
    apply congrArg
    rewrite [plus_comm n m]
    conv => lhs ; rewrite [← plus_assoc]
    -- Although, this ending is a little lack luster as there is no rfl.
    
