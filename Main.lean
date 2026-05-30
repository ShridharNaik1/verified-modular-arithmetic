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

theorem congruentMod_refl (a n : Nat) : congruentMod a a n := by
  unfold congruentMod
  rfl

theorem congruentMod_symm (a b n : Nat) : congruentMod a b n → congruentMod b a n := by
  intro h
  unfold congruentMod at h ⊢
  rw [h]

theorem congruentMod_trans (a b c n : Nat) : congruentMod a b n → congruentMod b c n → congruentMod a c n := by
  intro hab hbc
  unfold congruentMod at hab hbc ⊢
  rw [hab, hbc]

theorem congruentMod_add (a b c d n : Nat) : congruentMod a c n → congruentMod b d n → congruentMod (modAdd a b n) (modAdd c d n) n := by
  intro hac hbd
  unfold congruentMod at hac hbd ⊢
  unfold modAdd
  simp [Nat.add_mod, Nat.add_mod, hac, hbd]

theorem congruentMod_mul (a b c d n : Nat) : congruentMod a c n → congruentMod b d n → congruentMod (a * b) (c * d) n := by
  intro hac hbd
  unfold congruentMod at hac hbd ⊢
  simp [Nat.mul_mod, Nat.mul_mod, hac, hbd]

theorem congruentMod_of_eq_mod (a b n : Nat) : a % n = b % n → congruentMod a b n := by
  intro h
  unfold congruentMod
  rw [h]

theorem congruentMod_add_same (a b n : Nat) : congruentMod a b n → congruentMod (modAdd a a n) (modAdd b b n) n := by
  intro hab
  unfold congruentMod at hab ⊢
  unfold modAdd
  simp [Nat.add_mod, hab]

theorem congruentMod_mul_same (a b n : Nat) : congruentMod a b n → congruentMod (a * a) (b * b) n := by
  intro hab
  unfold congruentMod at hab ⊢
  simp [Nat.mul_mod, hab]

theorem mod_add_mod (a b n : Nat) : (a + b) % n = ((a % n) + (b % n)) % n := by
  rw [Nat.add_mod]

theorem mod_mul_mod (a b n : Nat) : (a * b) % n = ((a % n) * (b % n)) % n := by
  rw [Nat.mul_mod]

theorem congruentMod_zero (a n : Nat) : congruentMod a 0 n → a % n = 0 := by
  intro h
  unfold congruentMod at h
  rw [h]
  exact Nat.zero_mod n

theorem congruentMod_suc (a b n : Nat) : congruentMod a b n → congruentMod (a + 1) (b + 1) n := by
  intro hab
  unfold congruentMod at hab ⊢
  simp [Nat.add_mod, Nat.add_mod, hab]

theorem congruentMod_add_const (a b c n : Nat) : congruentMod a b n → congruentMod (a + c) (b + c) n := by
  intro hab
  unfold congruentMod at hab ⊢
  simp [Nat.add_mod, Nat.add_mod, hab]
