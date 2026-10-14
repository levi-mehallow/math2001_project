import natural_numbers
import plus_zero

theorem succ_plus ( m n : ℕ )
: m.succ + n = (plus m n).succ := by
  induction m using ℕ.rec
  case zero =>
    unfold plus plus
    rfl
  case succ m ih =>
    unfold plus
    rewrite [ih]
    rfl
