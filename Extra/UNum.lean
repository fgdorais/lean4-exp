/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-- `UNum d`: unsigned binary numeral with `2 ^ d` bits precision. -/
inductive UNum : Nat → Type
| /-- Constructor for `UNum 0`. -/
  bit (b : Bool) : UNum 0
| /-- Constructor for `UNum (d + 1)`. -/
  mk (lo hi : UNum d) : UNum (d + 1)
deriving DecidableEq

namespace UNum

/-- Lower half of a `UNum (d + 1)` numeral. -/
protected abbrev lo : UNum (d+1) → UNum d
  | mk lo _ => lo

/-- Upper half of a `UNum (d + 1)` numeral. -/
protected abbrev hi : UNum (d+1) → UNum d
  | mk _ hi => hi

/-- Construct a `UNum d` numeral from a `Nat`. -/
protected def ofNat : {d : Nat} → (x : Nat) → UNum d
  | 0, x => bit (x.testBit 0)
  | d+1, x => mk (UNum.ofNat x) (UNum.ofNat (x >>> (1 <<< d)))

instance : OfNat (UNum n) x where
  ofNat := UNum.ofNat x

protected def toBitVec (a : UNum d) : BitVec (2 ^ d) :=
  match d, a with
  | 0, bit a => .ofBool a
  | d+1, mk a₀ a₁ => Nat.two_pow_succ d ▸ BitVec.append a₁.toBitVec a₀.toBitVec

protected def toNat (a : UNum d) : Nat := a.toBitVec.toNat

protected def toStringRaw : {d : Nat} → UNum d → String
  | 0, bit a => toString a.toNat
  | _+1, mk lo hi => UNum.toStringRaw hi ++ UNum.toStringRaw lo

instance : ToString (UNum d) where
  toString a := "0b" ++ a.toStringRaw

/-- `UNum d` numeral zero. -/
protected def zero : {d : Nat} → UNum d
  | 0 => bit false
  | _+1 => mk UNum.zero UNum.zero

instance : Zero (UNum d) where
  zero := UNum.zero

/-- `UNum d` numeral one. -/
protected def one : {d : Nat} → UNum d
  | 0 => bit true
  | _+1 => mk UNum.one UNum.zero

instance : One (UNum d) where
  one := UNum.one

/-- Maximum `UNum d` value. -/
protected def max : {d : Nat} → UNum d
  | 0 => bit true
  | _+1 => mk UNum.max UNum.max

/-- Addition with carry. -/
def addc : {d : Nat} → (a b : UNum d) → Bool → UNum d × Bool
  | 0, bit a, bit b, c => (bit <| a ^^ b ^^ c, c && (a ^^ b) ^^ (a && b))
  | _+1, mk a₀ a₁, mk b₀ b₁, c =>
    let (s₀, c) := addc a₀ b₀ c
    let (s₁, c) := addc a₁ b₁ c
    (mk s₀ s₁, c)

instance : Add (UNum n) where
  add x y := addc x y false |>.fst

theorem addc_comm (a b : UNum d) : UNum.addc a b c = UNum.addc b a c := by
  induction d generalizing c with
  | zero =>
    match a, b with
    | bit false, bit false => simp [addc]
    | bit false, bit true => simp [addc]
    | bit true, bit false => simp [addc]
    | bit true, bit true => simp [addc]
  | succ d ih =>
    match a, b with
    | mk a₀ a₁, mk b₀ b₁ => simp [addc, ih]

theorem add_zero (a : UNum d) : a + 0 = a := by
  induction d with
  | zero =>
    match a with
    | bit false => simp [(· + ·), Add.add]
    | bit true => simp
  | succ d ih =>
    done

theorem add_assoc (a b c : UNum d) : (a + b) + c = a + (b + c) := by


/-- Subtraction with borrow. -/
def subb : {d : Nat} → (a b : UNum d) → Bool → UNum d × Bool
  | 0, bit a, bit b, c => (bit <| a ^^ b ^^ c, !a && (b ^^ c) ^^ (b && c))
  | _+1, mk a₀ a₁, mk b₀ b₁, c =>
    let (s₀, c) := subb a₀ b₀ c
    let (s₁, c) := subb a₁ b₁ c
    (mk s₀ s₁, c)

instance : Sub (UNum n) where
  sub x y := subb x y false |>.fst

/-- Double precision multiplication with double carry. -/
def mulAddAdd : {d : Nat} → (a b c₁ c₂ : UNum d) → UNum (d + 1)
  | 0, bit a, bit b, bit c₁, bit c₂ =>
    mk (bit <| (a && b) ^^ (c₁ ^^ c₂)) (bit <| ((a && b) && (c₁ ^^ c₂)) ^^ (c₁ && c₂))
  | _+1, mk a₀ a₁, mk b₀ b₁, mk c₁₀ c₁₁, mk c₂₀ c₂₁ =>
    match mulAddAdd a₀ b₀ c₁₀ c₂₀ with
    | mk p₀ p₁ =>
    match mulAddAdd a₀ b₁ c₁₁ p₁ with
    | mk p₁ m₀ =>
    match mulAddAdd a₁ b₀ c₂₁ p₁ with
    | mk p₁ m₁ =>
      mk (mk p₀ p₁) (mulAddAdd a₁ b₁ m₀ m₁)

/-- Double precision multiplication. -/
def muld (a b : UNum d) : UNum (d + 1) := mulAddAdd a b UNum.zero UNum.zero

instance : Mul (UNum d) where
  mul a b := muld a b |>.lo
