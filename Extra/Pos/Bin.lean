import Batteries

#print prefix ByteArray

#print ByteArray.rec

#exit

set_option bootstrap.genMatcherCode false in
set_option genCtorIdx false in
@[implemented_by Nat]
inductive NumPos where
| one : NumPos
| bit : Fin 2 → NumPos → NumPos

namespace NumPos

@[inline] unsafe def oneImpl : NumPos := unsafeCast (1 : Nat)
attribute [implemented_by oneImpl] NumPos.one

instance : Inhabited NumPos := ⟨one⟩

@[inline] unsafe def bitImpl (b : Fin 2) (x : NumPos) : NumPos :=
    unsafeCast <| 2 * unsafeCast x + b.toNat
attribute [implemented_by bitImpl] NumPos.bit

@[match_pattern] abbrev bit0 := bit 0

@[match_pattern] abbrev bit1 := bit 1

@[inline] unsafe def succImpl (n : NumPos) : NumPos :=
  unsafeCast <| unsafeCast n + 1

set_option trace.compiler.ir.result true in
@[implemented_by succImpl]
def succ : NumPos → NumPos
  | one => bit0 one
  | bit0 n => bit1 n
  | bit1 n => bit0 (succ n)

--#eval succ NumPos.one

@[inline] unsafe def ofNatImpl (n : Nat) [NeZero n] : NumPos := unsafeCast n
@[inline] unsafe def toNatNeZeroImpl (n : NumPos) : { n : Nat // n ≠ 0} := unsafeCast n

@[implemented_by toNatNeZeroImpl]
def toNatNeZero : NumPos → { n : Nat // n ≠ 0 }
  | one => ⟨1, of_decide_eq_true rfl⟩
  | bit0 n => ⟨2 * n.toNatNeZero.1, Nat.mul_ne_zero (Nat.succ_ne_zero _) n.toNatNeZero.2⟩
  | bit1 n => ⟨2 * n.toNatNeZero.1 + 1, Nat.succ_ne_zero _⟩

@[inline] def toNat (n : NumPos) := n.toNatNeZero.1

instance (n : NumPos) : NeZero n.toNat := ⟨n.toNatNeZero.2⟩

@[implemented_by ofNatImpl]
def _root_.Nat.toNumPos : (n : Nat) → [NeZero n] → NumPos
  | 1, _ => one
  | n+2, _ => (n+1).toNumPos.succ

@[simp, grind =] theorem toNumPos_toNat (n : NumPos) : n.toNat.toNumPos = n := sorry
@[simp, grind =] theorem toNat_toNumPos (n : Nat) [inst : NeZero n] : n.toNumPos.toNat = n := by
  match n, inst with
  | 1, _ => simp [Nat.toNumPos, toNat, toNatNeZero]
  | n+2, _ => simp [Nat.toNumPos, toNat]; done

unsafe def recImpl.{u} {motive : NumPos → Sort u} (one : motive one)
  (bit : (a : Fin 2) → (a_1 : NumPos) → motive a_1 → motive (bit a a_1)) (t : NumPos) : motive t :=
  if h : t.toNat = 1 then
    have : t = .one := by rw [← toNumPos_toNat t]; simp [h]; rfl
    this ▸ one
  else
    have : NeZero (t.toNat / 2) := ⟨lcProof⟩
    have : t = .bit ⟨t.toNat % 2, Nat.mod_lt _ Nat.two_pos⟩ (t.toNat / 2).toNumPos := lcProof
    this ▸ bit ⟨t.toNat % 2, Nat.mod_lt _ Nat.two_pos⟩ (t.toNat / 2).toNumPos (recImpl one bit (t.toNat / 2).toNumPos)
attribute [implemented_by recImpl] NumPos.rec

unsafe def casesOnImpl.{u} {motive : NumPos → Sort u} (t : NumPos) (one : motive one)
  (bit : (a : Fin 2) → (a_1 : NumPos) → motive (bit a a_1)) : motive t :=
  if h : t.toNat = 1 then
    have : t = .one := by rw [← toNumPos_toNat t]; simp [h]; rfl
    this ▸ one
  else
    have : NeZero (t.toNat / 2) := ⟨lcProof⟩
    have : t = .bit ⟨t.toNat % 2, Nat.mod_lt _ Nat.two_pos⟩ (t.toNat / 2).toNumPos := lcProof
    this ▸ bit ⟨t.toNat % 2, Nat.mod_lt _ Nat.two_pos⟩ (t.toNat / 2).toNumPos
attribute [implemented_by casesOnImpl] NumPos.casesOn

-- unsafe def recOnImpl.{u} {motive : NumPos → Sort u} (t : NumPos) (one : motive one)
--   (bit : (a : Bool) → (a_1 : NumPos) → motive a_1 → motive (bit a a_1)) : motive t :=
--   if h : t.toNat = 1 then
--     have : t = .one := by rw [← toNumPos_toNat t]; simp [h]; rfl
--     this ▸ one
--   else
--     haveI : NeZero (t.toNat / 2) := ⟨lcProof⟩
--     have : t = .bit (t.toNat.testBit 0) (t.toNat / 2).toNumPos := lcProof
--     this ▸ bit (t.toNat.testBit 0) (t.toNat / 2).toNumPos (recOnImpl (t.toNat / 2).toNumPos one bit)
-- attribute [implemented_by recOnImpl] NumPos.recOn

-- #print NumPos.below
-- #print NumPos.brecOn.go

-- unsafe def brecOnImpl.{u} {motive : NumPos → Sort u} (t : NumPos)
--     (F_1 : (t : NumPos) → NumPos.below (motive := motive) t → motive t) : motive t :=
--   _
