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

def congruentMod (a b n : Nat) : Prop := (a % n) = (b % n)
#eval congruentMod (17 % 5) (2 % 5)

theorem congruentMod_refl (a n : Nat) : congruentMod a a n := by
  unfold congruentMod
  rfl

theorem congruentMod_symm (a b n : Nat) : congruentMod a b n → congruentMod b a n := by
  intro h
  unfold congruentMod at h ⊢
  rw [h]
