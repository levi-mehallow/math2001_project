import natural_numbers
import zero_plus

theorem plus_assoc ( m n p : ℕ )
: m + ( n + p ) = ( m + n ) + p := by
  induction m using ℕ.rec
  case zero =>
    rewrite [zero_plus]
    rewrite [zero_plus]
    rfl
  case succ m ih =>
    rewrite [plus]
    rewrite [plus]
    rewrite [ih]
    rewrite [← plus]
    rfl
