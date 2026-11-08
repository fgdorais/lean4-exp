/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Extra.Basic

namespace Nat

/-- `n.isEven` is `true` when `n` is even. -/
@[expose] public protected def isEven (n : Nat) : Bool := n % 2 == 0

/-- `n.isOdd` is `true` when `n` is odd. -/
@[expose] public protected def isOdd (n : Nat) : Bool := n % 2 != 0

public theorem not_isOdd_eq_isEven (n : Nat) : (!n.isOdd) = n.isEven := Bool.not_not ..

public theorem not_isEven_eq_isOdd (n : Nat) : (!n.isEven) = n.isOdd := rfl

public theorem mod_two_eq_zero_of_isEven (h : n.isEven) : n % 2 = 0  := eq_of_beq h

public theorem mod_two_eq_one_of_isOdd (h : n.isOdd) : n % 2 = 1  :=
  Or.resolve_left (mod_two_eq_zero_or_one n) (bne_iff_ne.mp h)

public theorem isEven_iff_mod_two_eq_zero (n : Nat) : n.isEven ↔ n % 2 = 0 := beq_iff_eq ..

public theorem isOdd_iff_mod_two_eq_one (n : Nat) : n.isOdd ↔ n % 2 = 1 :=
  ⟨mod_two_eq_one_of_isOdd, fun h => by simp [Nat.isOdd, h]⟩

public theorem isEven_dest (h : n.isEven) : ∃ m, n = 2 * m := by
  exists n / 2
  conv => lhs; rw [← div_add_mod n 2]
  rw [mod_two_eq_zero_of_isEven h, Nat.add_zero]

public theorem isOdd_dest (h : n.isOdd) : ∃ m, n = 2 * m + 1 := by
  exists n / 2
  conv => lhs; rw [← div_add_mod n 2]
  rw [mod_two_eq_one_of_isOdd h]

public theorem isEven_bit0 (n : Nat) : (2 * n).isEven := by simp [Nat.isEven]

public theorem isOdd_bit0 (n : Nat) : (2 * n).isOdd = false := by simp [Nat.isOdd]

public theorem isEven_bit1 (n : Nat) : (2 * n + 1).isEven = false := by simp [Nat.isEven]

public theorem isOdd_bit1 (n : Nat) : (2 * n + 1).isOdd = true := by simp [Nat.isOdd]

public theorem isEven_succ (n : Nat) : (n+1).isEven = n.isOdd := by
  rw [Bool.eq_iff_iff]
  rw [isOdd_iff_mod_two_eq_one]
  rw [isEven_iff_mod_two_eq_zero]
  rw [add_mod, mod_eq_of_lt Nat.one_lt_two]
  constructor
  · intro h
    apply Or.resolve_left (mod_two_eq_zero_or_one n)
    intro h1
    rw [h1] at h
    contradiction
  · intro h; rw [h]

public theorem isOdd_succ (n : Nat) : (n+1).isOdd = n.isEven := by
  rw [Bool.eq_iff_iff]
  rw [isOdd_iff_mod_two_eq_one]
  rw [isEven_iff_mod_two_eq_zero]
  rw [add_mod, mod_eq_of_lt Nat.one_lt_two]
  constructor
  · intro h
    apply Or.resolve_right (mod_two_eq_zero_or_one n)
    intro h1
    rw [h1] at h
    contradiction
  · intro h; rw [h]

public theorem succ_isEven_iff_isOdd {n : Nat} : (n+1).isEven ↔ n.isOdd := by rw [isEven_succ]

public theorem succ_isOdd_iff_isEven {n : Nat} : (n+1).isOdd ↔ n.isEven := by rw [isOdd_succ]

end Nat
