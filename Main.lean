import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

def modAdd (a b n : Nat) : Nat := (a + b) % n
#eval modAdd 7 9 5

theorem modAdd_comm (a b n : Nat) : modAdd a b n = modAdd b a n := by
  unfold modAdd
  rw [Nat.add_comm]
