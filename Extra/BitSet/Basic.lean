/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Extra.Basic
public import Extra.Fin.Basic

/-!
# Bit sets

`Extra.BitSet w` is a set of indices `Fin w`, represented as a `BitVec w`.

Membership `∈`, inclusion `⊆` and equality are decidable, and the Boolean algebra
operations are the corresponding bitwise operations: intersection `∩`, union `∪`,
complement `-x` and difference `x - y`, with bounds `∅` and `univ`.
-/

@[expose] public section

/-- A set of `Fin w` indices, represented as a bit vector of width `w`. -/
def Extra.BitSet (w : Nat) := BitVec w

namespace Extra.BitSet

/-- The underlying bit vector of a bit set. -/
protected def toBitVec (x : BitSet w) : BitVec w := x

/-- Decidable equality for bit sets. -/
instance : DecidableEq (BitSet w) := inferInstanceAs (DecidableEq (BitVec w))

/-- Number of elements of a bit set. -/
def size (x : BitSet w) : Nat :=
  Fin.sum fun (i : Fin w) => x.toBitVec[i].toNat

/-- Membership notation `∈` for bit sets. -/
instance : Membership (Fin w) (BitSet w) where
  mem x i := x.toBitVec[i.val]

/-- Membership `i ∈ x` is decidable. -/
instance : DecidableRel (α := Fin w) (β := BitSet w) (· ∈ ·) :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

/-- Test whether `x` is a subset of `y`. -/
def subset (x y : BitSet w) : Bool :=
  Fin.all fun (i : Fin w) => i ∉ x || i ∈ y

/-- Subset notation `⊆` for bit sets. -/
instance : HasSubset (BitSet w) where
  Subset x y := subset x y

/-- The subset relation `x ⊆ y` is decidable. -/
instance : DecidableRel (α := BitSet w) (β := BitSet w) (· ⊆ ·) :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

/-- The empty bit set. -/
instance : EmptyCollection (BitSet w) where
  emptyCollection := 0#w

/-- The bit set of all elements of `Fin w`. -/
def univ : BitSet w := BitVec.allOnes w

/-- Intersection notation `∩` for bit sets. -/
instance : Inter (BitSet w) where
  inter x y := x.toBitVec &&& y.toBitVec

/-- Union notation `∪` for bit sets. -/
instance : Union (BitSet w) where
  union x y := x.toBitVec ||| y.toBitVec

/-- Complement notation `-x` for bit sets. -/
instance : Neg (BitSet w) where
  neg x := x.toBitVec.not

/-- Difference notation `x - y` for bit sets. -/
instance : Sub (BitSet w) where
  sub x y := x.toBitVec &&& y.toBitVec.not

/-- The bit set whose only element is `i`. -/
def singleton (i : Fin w) : BitSet w := BitVec.twoPow w i

/-- List the elements of a bit set in order. -/
def toList (x : BitSet w) : List (Fin w) :=
  List.finRange w |>.filter (· ∈ x)
