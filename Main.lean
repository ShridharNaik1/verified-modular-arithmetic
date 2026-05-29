import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

def modAdd (a b n : Nat) : Nat := (a + b) % n
#eval modAdd 7 9 5

theorem modAdd_comm (a b n : Nat) : modAdd a b n = modAdd b a n := by
  unfold modAdd
  rw [Nat.add_comm]

theorem modAdd_zero (a n : Nat) : modAdd a 0 n = a % n := by
  unfold modAdd
  rw [Nat.add_zero]

theorem modAdd_assoc (a b c n : Nat) : modAdd (modAdd a b n) c n = modAdd a (modAdd b c n) n := by
  unfold modAdd
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
