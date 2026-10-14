import natural_numbers

theorem plus_succ ( m n : ℕ )
: m + n.succ = (m + n).succ := by
  induction m using ℕ.rec
  case zero =>
    unfold plus
    rfl
  case succ m ih =>
    unfold plus
    rewrite [ih]
    rfl
