
namespace Nat

/-- Calculates the natural number whose big-endian binary representation is the list `l`. -/
@[inline]
def ofBitList (l : List Bool) : Nat :=
  loop l 0
where
  loop l acc :=
    match l with
    | [] => acc
    | false :: l => loop l (2 * acc)
    | true :: l => loop l (2 * acc + 1)

theorem ofBitList.loop_eq_shiftLeft_length_add :
    loop l acc = ofBitList l + acc <<< l.length := by
  match l with
  | [] => simp [ofBitList, loop]
  | false :: l =>
    simp only [ofBitList, loop, loop_eq_shiftLeft_length_add (acc := 2 * acc), shiftLeft_eq,
      List.length_cons, Nat.pow_add_one]
    grind
  | true :: l =>
    simp only [ofBitList, loop, loop_eq_shiftLeft_length_add (acc := 2 * acc + 1),
      loop_eq_shiftLeft_length_add (acc := 1), shiftLeft_eq, List.length_cons, Nat.pow_add_one]
    grind

theorem ofBitList_append (l₁ l₂ : List Bool) :
    ofBitList (l₂ ++ l₁) = ofBitList l₂ <<< l₁.length + ofBitList l₁ := by
  simp only [ofBitList]
  induction l₂ generalizing l₁ with
  | nil => simp [ofBitList.loop]
  | cons b l₂ ih =>
    cases b
    · simp only [List.cons_append, ofBitList.loop, Nat.mul_zero, ih, shiftLeft_eq]
    · simp only [List.cons_append, ofBitList.loop, Nat.mul_zero, Nat.zero_add,
      ofBitList.loop_eq_shiftLeft_length_add (acc := 1), ofBitList, ih, shiftLeft_eq,
      List.length_append, Nat.pow_add]
      grind

/-- Calculates big-endian bit representation of the natural number `n`. -/
@[inline]
def toBitList (n : Nat) : List Bool :=
  loop n []
where
  loop n acc :=
    match n with
    | 0 => acc
    | 1 => true :: acc
    | n@(_+2) => loop (n / 2) (testBit n 0 :: acc)

@[simp] theorem toBitList.loop_zero : loop 0 acc = acc := by
  simp [loop]

@[simp] theorem toBitList.loop_one : loop 1 acc = true :: acc := by
  simp [loop]

@[simp] theorem toBitList.loop_add_two :
    loop (n+2) acc = loop ((n + 2) / 2) (testBit (n + 2) 0 :: acc) := by
  simp only [loop]

theorem toBitList.loop_eq_toBitList_append :
    loop n acc = toBitList n ++ acc := by
  match n with
  | 0 => simp [toBitList]
  | 1 => simp [toBitList]
  | n+2 =>
    simp only [loop_add_two, zero_lt_succ, add_div_right, testBit_zero, add_mod_right, toBitList]
    rw [loop_eq_toBitList_append]
    rw [loop_eq_toBitList_append]
    simp

@[simp] theorem toBitList_zero : toBitList 0 = [] := by
  simp [toBitList]

theorem toBitList_ne_zero [NeZero n] : n.toBitList = (n / 2).toBitList ++ [n.testBit 0] := by
  have := NeZero.ne n
  match n with
  | 1 => simp [toBitList]
  | n+2 =>
    simp only [toBitList, toBitList.loop_add_two, zero_lt_succ, add_div_right, testBit_zero,
      add_mod_right]
    exact toBitList.loop_eq_toBitList_append ..

#exit

@[implemented_by Nat]
structure NumPos where
  private ofBits ::
  toBits : List Bool

namespace NumPos

@[inline] unsafe def ofBitsImpl (l : List Bool) : NumPos :=
  unsafeCast (Nat.ofBitList.loop l.reverse 1)
attribute [implemented_by ofBitsImpl] NumPos.ofBits

@[inline] unsafe def toBitsImpl (n : NumPos) : List Bool :=
  (Nat.toBitList (unsafeCast n)).tail.reverse
attribute [implemented_by toBitsImpl] NumPos.toBits

@[inline] unsafe def oneImpl : NumPos := unsafeCast 1

@[inline] unsafe def bitImpl (b : Bool) (n : NumPos) : NumPos :=
  unsafeCast <| 2 * unsafeCast n + cond b 1 0

@[match_pattern, implemented_by oneImpl]
protected abbrev one : NumPos :=
  .ofBits []

@[match_pattern, implemented_by bitImpl]
protected abbrev bit (b : Bool) (n : NumPos) : NumPos :=
  .ofBits (b :: n.toBits)

@[match_pattern]
protected abbrev bit0 (n : NumPos) := n.bit false

@[match_pattern]
protected abbrev bit1 (n : NumPos) := n.bit true

def succ (n : NumPos) : NumPos :=
  match n with
  | .one => NumPos.one.bit0
  | .bit0 ⟨l⟩ => (NumPos.ofBits l).bit1
  | .bit1 ⟨l⟩ => (NumPos.ofBits l).succ.bit0
