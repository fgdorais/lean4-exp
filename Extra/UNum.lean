/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Fixed-width unsigned binary numerals

`UNum d` is an unsigned binary numeral with `2 ^ d` bits, held as a balanced
binary tree: a `UNum (d + 1)` is a low and a high `UNum d` half. Arithmetic is
structural recursion on `d`, with a carry threaded through the two halves.
-/

@[expose] public section

/-- `UNum d`: unsigned binary numeral with `2 ^ d` bits precision. -/
inductive UNum : Nat → Type
| /-- A `UNum 0` numeral is a single bit. -/
  bit (b : Bool) : UNum 0
| /-- A `UNum (d + 1)` numeral is a low and a high `UNum d` half. -/
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

/-- Bits of a `UNum d` numeral, as a `BitVec (2 ^ d)`. -/
protected def toBitVec (a : UNum d) : BitVec (2 ^ d) :=
  match d, a with
  | 0, bit a => .ofBool a
  | d+1, mk a₀ a₁ => Nat.two_pow_succ d ▸ BitVec.append a₁.toBitVec a₀.toBitVec

/-- Value of a `UNum d` numeral as a `Nat`. -/
protected def toNat (a : UNum d) : Nat := a.toBitVec.toNat

/-- Binary digits of a `UNum d` numeral, high bit first and with no prefix. -/
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

theorem add_def (a b : UNum d) : a + b = (addc a b false).fst := rfl

theorem addc_mk (a₀ a₁ b₀ b₁ : UNum d) (c : Bool) :
    addc (mk a₀ a₁) (mk b₀ b₁) c
      = (mk (addc a₀ b₀ c).1 (addc a₁ b₁ (addc a₀ b₀ c).2).1,
         (addc a₁ b₁ (addc a₀ b₀ c).2).2) := by
  cases h : addc a₀ b₀ c with
  | mk s m =>
    cases h' : addc a₁ b₁ m with
    | mk t M => simp [addc, h, h']

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

theorem add_comm (a b : UNum d) : a + b = b + a := by
  rw [add_def, add_def, addc_comm]

theorem zero_eq : {d : Nat} → (0 : UNum d) = UNum.zero
  | 0 => by decide
  | _+1 => by
    show mk (UNum.ofNat 0) (UNum.ofNat (0 >>> _)) = mk UNum.zero UNum.zero
    rw [Nat.zero_shiftRight, show (UNum.ofNat 0 : UNum _) = UNum.zero from zero_eq]

theorem addc_zero : {d : Nat} → (a : UNum d) → addc a UNum.zero false = (a, false)
  | 0, bit a => by cases a <;> rfl
  | _+1, mk a₀ a₁ => by
    show addc (mk a₀ a₁) (mk UNum.zero UNum.zero) false = _
    rw [addc, addc_zero a₀]
    dsimp only
    rw [addc_zero a₁]

theorem add_zero (a : UNum d) : a + 0 = a := by
  rw [add_def, zero_eq, addc_zero]

-- Associativity with the carries made explicit. The two carry bits going in
-- have to agree up to order, and then the two coming out agree up to order
-- again -- which is what makes the induction step go through, since the hi
-- half is fed the carries out of the lo half. `add_assoc` is the case where
-- all four are `false`.
theorem addc_assoc : {d : Nat} → (a b c : UNum d) → (p q p' q' : Bool) →
    (p ^^ q) = (p' ^^ q') → (p && q) = (p' && q') →
    (addc (addc a b p).1 c q).1 = (addc a (addc b c p').1 q').1
    ∧ ((addc a b p).2 ^^ (addc (addc a b p).1 c q).2)
        = ((addc b c p').2 ^^ (addc a (addc b c p').1 q').2)
    ∧ ((addc a b p).2 && (addc (addc a b p).1 c q).2)
        = ((addc b c p').2 && (addc a (addc b c p').1 q').2)
  | 0, bit x, bit y, bit z, p, q, p', q', h₁, h₂ => by
    cases x <;> cases y <;> cases z <;> cases p <;> cases q <;> cases p' <;> cases q' <;>
      simp_all [addc]
  | _+1, mk a₀ a₁, mk b₀ b₁, mk c₀ c₁, p, q, p', q', h₁, h₂ => by
    have ih₀ := addc_assoc a₀ b₀ c₀ p q p' q' h₁ h₂
    have ih₁ := addc_assoc a₁ b₁ c₁ _ _ _ _ ih₀.2.1 ih₀.2.2
    simp only [addc_mk]
    exact ⟨by rw [ih₀.1, ih₁.1], ih₁.2.1, ih₁.2.2⟩

theorem add_assoc (a b c : UNum d) : (a + b) + c = a + (b + c) :=
  (addc_assoc a b c false false false false rfl rfl).1

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
