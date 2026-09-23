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
open BitVec

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

theorem mem_def {x : BitSet w} {i : Fin w} :
  i ∈ x ↔ x.toBitVec[i.val] := .rfl

@[simp, grind =]
theorem getElem_toBitVec_eq_decide_mem (x : BitSet w) (i : Fin w) :
  x.toBitVec[i.val] = decide (i ∈ x) := rfl

theorem getElem_toBitVec_eq_true_iff_mem {x : BitSet w} {i : Fin w} :
    x.toBitVec[i.val] = true ↔ i ∈ x := by simp

theorem getElem_toBitVec_eq_false_iff_notmem {x : BitSet w} {i : Fin w} :
    x.toBitVec[i.val] = false ↔ i ∉ x := by simp

@[ext]
protected theorem ext {x y : BitSet w} (h : ∀ i, i ∈ x ↔ i ∈ y) : x = y := by
  simp only [mem_def, ← Bool.eq_iff_iff] at h
  show x.toBitVec = y.toBitVec
  ext i hi
  exact h ⟨i, hi⟩

/-- Test whether `x` is a subset of `y`. -/
def subset (x y : BitSet w) : Bool :=
  Fin.all fun (i : Fin w) => i ∉ x || i ∈ y

/-- Subset notation `⊆` for bit sets. -/
instance : HasSubset (BitSet w) where
  Subset x y := subset x y

/-- The subset relation `x ⊆ y` is decidable. -/
instance : DecidableRel (α := BitSet w) (β := BitSet w) (· ⊆ ·) :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

@[grind =]
theorem subset_def {x y : BitSet w} : x ⊆ y ↔ ∀ {i : Fin w}, i ∈ x → i ∈ y := by
  simp [HasSubset.Subset, subset, ← Fin.all_iff_forall]

theorem subset_iff_forall_mem_imp_mem {x y : BitSet w} :
    x ⊆ y ↔ ∀ i : Fin w, i ∈ x → i ∈ y := by
  constructor
  · intro h _; exact subset_def.mp h
  · intro h; exact subset_def.mpr fun {i} => h i

@[refl]
theorem subset_refl (x : BitSet w) : x ⊆ x := by
  simp [subset_def]

@[trans]
theorem subset_trans {x y z : BitSet w} : x ⊆ y → y ⊆ z → x ⊆ z := by
  simp only [subset_def]
  intro h1 h2 _ h
  exact h2 (h1 h)

theorem subset_antisymm {x y : BitSet w} : x ⊆ y → y ⊆ x → x = y := by
  simp only [subset_def]
  intro h1 h2
  ext i
  constructor
  · exact h1
  · exact h2

instance : Std.Refl (α := BitSet w) (· ⊆ ·) where
  refl := subset_refl

instance : Trans (α := BitSet w) (· ⊆ ·) (· ⊆ ·) (· ⊆ ·) where
  trans := subset_trans

instance : Std.Antisymm (α := BitSet w) (· ⊆ ·) where
  antisymm _ _ := subset_antisymm

/-- The empty bit set. -/
instance : EmptyCollection (BitSet w) where
  emptyCollection := 0#w

@[simp, grind =]
theorem toBitVec_empty : (∅ : BitSet w).toBitVec = 0#w := rfl

@[simp, grind .]
theorem not_mem_empty (i : Fin w) : i ∉ (∅ : BitSet w) := by
  simp only [mem_def]; grind

/-- The bit set of all elements of `Fin w`. -/
def univ : BitSet w := BitVec.allOnes w

@[simp, grind =]
theorem toBitVec_univ : (univ : BitSet w).toBitVec = BitVec.allOnes w := rfl

@[simp, grind .]
theorem mem_univ (i : Fin w) : i ∈ (univ : BitSet w) := by
  simp only [mem_def]; grind

theorem eq_empty_iff_forall_not_mem {x : BitSet w} : x = ∅ ↔ ∀ i, i ∉ x := by
  constructor
  · rintro rfl; grind
  · intro h; ext i; grind

theorem eq_univ_iff_forall_mem {x : BitSet w} : x = univ ↔ ∀ i, i ∈ x := by
  constructor
  · rintro rfl; grind
  · intro h; ext i; grind

@[simp]
theorem empty_subset (x : BitSet w) : ∅ ⊆ x := by
  simp only [subset_def]; grind

@[simp]
theorem subset_univ (x : BitSet w) : x ⊆ univ := by
  simp only [subset_def]; grind

@[simp]
theorem subset_empty_iff_eq_empty {x : BitSet w} : x ⊆ ∅ ↔ x = ∅ := by
  simp only [subset_def, eq_empty_iff_forall_not_mem]; grind

@[simp]
theorem univ_subset_iff_eq_univ {x : BitSet w} : univ ⊆ x ↔ x = univ := by
  simp only [subset_def, eq_univ_iff_forall_mem]; grind

/-- Intersection notation `∩` for bit sets. -/
instance : Inter (BitSet w) where
  inter x y := x.toBitVec &&& y.toBitVec

@[simp, grind =]
theorem toBitVec_inter (x y : BitSet w) :
    (x ∩ y).toBitVec = x.toBitVec &&& y.toBitVec := rfl

@[simp, grind =]
theorem mem_inter_iff_mem_and_mem {x y : BitSet w} {i : Fin w} :
    i ∈ x ∩ y ↔ i ∈ x ∧ i ∈ y := by
  simp only [mem_def]; grind

/-- Union notation `∪` for bit sets. -/
instance : Union (BitSet w) where
  union x y := x.toBitVec ||| y.toBitVec

@[simp, grind =]
theorem toBitVec_union (x y : BitSet w) :
    (x ∪ y).toBitVec = x.toBitVec ||| y.toBitVec := rfl

@[simp, grind =]
theorem mem_union_iff_mem_or_mem {x y : BitSet w} {i : Fin w} :
    i ∈ x ∪ y ↔ i ∈ x ∨ i ∈ y := by
  simp only [mem_def]; grind

/-- Complement notation `-x` for bit sets. -/
instance : Neg (BitSet w) where
  neg x := x.toBitVec.not

@[simp, grind =]
theorem toBitVec_neg (x : BitSet w) : (-x).toBitVec = x.toBitVec.not := rfl

@[simp, grind =]
theorem mem_neg_iff_not_mem {x : BitSet w} {i : Fin w} :
    i ∈ -x ↔ i ∉ x := by
  simp only [mem_def]; grind

/-- Difference notation `x - y` for bit sets. -/
instance : Sub (BitSet w) where
  sub x y := x.toBitVec &&& y.toBitVec.not

@[simp, grind =]
theorem toBitVec_sub (x y : BitSet w) : (x - y).toBitVec = x.toBitVec &&& y.toBitVec.not := rfl

@[simp, grind =]
theorem mem_sub_iff_mem_and_not_mem {x y : BitSet w} {i : Fin w} :
    i ∈ x - y ↔ i ∈ x ∧ i ∉ y := by
  simp only [mem_def]; grind

theorem inter_subset_left (x y : BitSet w) : x ∩ y ⊆ x := by
  simp only [subset_def]; grind

theorem inter_subset_right (x y : BitSet w) : x ∩ y ⊆ y := by
  simp only [subset_def]; grind

theorem subset_inter_of_subset_of_subset {x y z : BitSet w} :
    z ⊆ x → z ⊆ y → z ⊆ x ∩ y := by
  simp only [subset_def]; grind

@[simp]
theorem inter_idem (x : BitSet w) : x ∩ x = x := by
  ext; grind

theorem inter_comm (x y : BitSet w) : x ∩ y = y ∩ x := by
  ext; grind

theorem inter_assoc (x y z : BitSet w) : (x ∩ y) ∩ z = x ∩ (y ∩ z) := by
  ext; grind

instance : Std.Commutative (α := BitSet w) (· ∩ ·) where
  comm := inter_comm

instance : Std.Associative (α := BitSet w) (· ∩ ·) where
  assoc := inter_assoc

instance : Std.IdempotentOp (α := BitSet w) (· ∩ ·) where
  idempotent := inter_idem

theorem subset_union_left (x y : BitSet w) : x ⊆ x ∪ y := by
  simp only [subset_def]; grind

theorem subset_union_right (x y : BitSet w) : y ⊆ x ∪ y := by
  simp only [subset_def]; grind

theorem union_subset_of_subset_of_subset {x y z : BitSet w} :
    x ⊆ z → y ⊆ z → x ∪ y ⊆ z := by
  simp [subset_def]; grind

@[simp]
theorem union_idem (x : BitSet w) : x ∪ x = x := by
  ext; grind

theorem union_comm (x y : BitSet w) : x ∪ y = y ∪ x := by
  ext; grind

theorem union_assoc (x y z : BitSet w) : (x ∪ y) ∪ z = x ∪ (y ∪ z) := by
  ext; grind

instance : Std.Commutative (α := BitSet w) (· ∪ ·) where
  comm := union_comm

instance : Std.Associative (α := BitSet w) (· ∪ ·) where
  assoc := union_assoc

instance : Std.IdempotentOp (α := BitSet w) (· ∪ ·) where
  idempotent := union_idem

@[simp]
theorem inter_empty (x : BitSet w) : x ∩ ∅ = ∅ := by
  ext; grind

@[simp]
theorem empty_inter (x : BitSet w) : ∅ ∩ x = ∅ := by
  ext; grind

@[simp]
theorem inter_univ (x : BitSet w) : x ∩ univ = x := by
  ext; grind

@[simp]
theorem univ_inter (x : BitSet w) : univ ∩ x = x := by
  ext; grind

@[simp]
theorem union_empty (x : BitSet w) : x ∪ ∅ = x := by
  ext; grind

@[simp]
theorem empty_union (x : BitSet w) : ∅ ∪ x = x := by
  ext; grind

@[simp]
theorem union_univ (x : BitSet w) : x ∪ univ = univ := by
  ext; grind

@[simp]
theorem univ_union (x : BitSet w) : univ ∪ x = univ := by
  ext; grind

instance : Std.LawfulCommIdentity (α := BitSet w) (· ∩ ·) univ where
  right_id := inter_univ

instance : Std.LawfulCommIdentity (α := BitSet w) (· ∪ ·) ∅ where
  right_id := union_empty

@[simp]
theorem inter_union_self_left (x y : BitSet w) : x ∩ (x ∪ y) = x := by
  ext; grind

@[simp]
theorem inter_union_self_right (x y : BitSet w) : x ∩ (y ∪ x) = x := by
  ext; grind

@[simp]
theorem union_inter_cancel_left (x y : BitSet w) : (x ∪ y) ∩ x = x := by
  ext; grind

@[simp]
theorem union_inter_cancel_right (x y : BitSet w) : (x ∪ y) ∩ y = y := by
  ext; grind

@[simp]
theorem union_inter_self_left (x y : BitSet w) : x ∪ (x ∩ y) = x := by
  ext; grind

@[simp]
theorem union_inter_self_right (x y : BitSet w) : x ∪ (y ∩ x) = x := by
  ext; grind

@[simp]
theorem inter_union_cancel_left (x y : BitSet w) : (x ∩ y) ∪ x = x := by
  ext; grind

@[simp]
theorem inter_union_cancel_right (x y : BitSet w) : (x ∩ y) ∪ y = y := by
  ext; grind

theorem inter_union_distrib_left (x y z : BitSet w) :
    x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z) := by
  ext; grind

theorem inter_union_distrib_right (x y z : BitSet w) :
    (x ∪ y) ∩ z = (x ∩ z) ∪ (y ∩ z) := by
  ext; grind

theorem union_inter_distrib_left (x y z : BitSet w) :
    x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z) := by
  ext; grind

theorem union_inter_distrib_right (x y z : BitSet w) :
    (x ∩ y) ∪ z = (x ∪ z) ∩ (y ∪ z) := by
  ext; grind

theorem subset_iff_inter_eq_left {x y : BitSet w} : x ⊆ y ↔ x ∩ y = x := by
  simp only [subset_def, BitSet.ext_iff]; grind

theorem subset_iff_union_eq_right {x y : BitSet w} : x ⊆ y ↔ x ∪ y = y := by
  simp only [subset_def, BitSet.ext_iff]; grind

@[simp]
theorem neg_neg (x : BitSet w) : - -x = x := by
  ext; grind

theorem neg_inj {x y : BitSet w} : -x = -y ↔ x = y := by
  constructor
  · intro h; rw [← neg_neg x, ← neg_neg y, h]
  · intro | rfl => rfl

theorem neg_eq_iff_eq_neg {x y : BitSet w} : -x = y ↔ x = -y := by
  constructor <;> (rintro rfl; simp)

@[simp]
theorem neg_empty : -(∅ : BitSet w) = univ := by
  ext; grind

@[simp]
theorem neg_univ : -(univ : BitSet w) = ∅ := by
  ext; grind

@[simp]
theorem inter_neg_self (x : BitSet w) : x ∩ -x = ∅ := by
  ext; grind

@[simp]
theorem neg_inter_self (x : BitSet w) : -x ∩ x = ∅ := by
  ext; grind

@[simp]
theorem union_neg_self (x : BitSet w) : x ∪ -x = univ := by
  ext; grind

@[simp]
theorem neg_union_self (x : BitSet w) : -x ∪ x = univ := by
  ext; grind

/-- De Morgan's law for intersection. -/
theorem neg_inter (x y : BitSet w) : -(x ∩ y) = -x ∪ -y := by
  ext; grind

/-- De Morgan's law for union. -/
theorem neg_union (x y : BitSet w) : -(x ∪ y) = -x ∩ -y := by
  ext; grind

theorem neg_subset_neg_iff_subset {x y : BitSet w} : -x ⊆ -y ↔ y ⊆ x := by
  simp only [subset_iff_forall_mem_imp_mem, mem_neg_iff_not_mem]
  grind

theorem subset_neg_iff_inter_eq_empty {x y : BitSet w} : x ⊆ -y ↔ x ∩ y = ∅ := by
  simp only [subset_iff_forall_mem_imp_mem, mem_neg_iff_not_mem,
    mem_inter_iff_mem_and_mem, eq_empty_iff_forall_not_mem]
  grind

theorem sub_eq_inter_neg (x y : BitSet w) : x - y = x ∩ -y := by
  ext; grind

@[simp]
theorem sub_self (x : BitSet w) : x - x = ∅ := by
  ext; grind

@[simp]
theorem sub_empty (x : BitSet w) : x - ∅ = x := by
  ext; grind

@[simp]
theorem empty_sub (x : BitSet w) : ∅ - x = ∅ := by
  ext; grind

instance : Std.LawfulRightIdentity (α := BitSet w) (· - ·) ∅ where
  right_id := sub_empty

@[simp]
theorem sub_univ (x : BitSet w) : x - univ = ∅ := by
  ext; grind

@[simp]
theorem univ_sub (x : BitSet w) : univ - x = -x := by
  ext; grind

theorem sub_subset (x y : BitSet w) : x - y ⊆ x := by
  simp only [subset_def]; grind

theorem subset_iff_sub_eq_empty {x y : BitSet w} : x ⊆ y ↔ x - y = ∅ := by
  simp only [subset_iff_forall_mem_imp_mem, mem_sub_iff_mem_and_not_mem,
    eq_empty_iff_forall_not_mem]
  grind

theorem sub_sub (x y z : BitSet w) : (x - y) - z = x - (y ∪ z) := by
  ext; grind

theorem sub_inter_distrib_left (x y z : BitSet w) : x - (y ∩ z) = (x - y) ∪ (x - z) := by
  ext; grind

theorem sub_union_distrib_left (x y z : BitSet w) : x - (y ∪ z) = (x - y) ∩ (x - z) := by
  ext; grind

/-- The bit set whose only element is `i`. -/
def singleton (i : Fin w) : BitSet w := twoPow w i

@[simp, grind =]
theorem toBitVec_singleton {i : Fin w} : (singleton i).toBitVec = twoPow w i := rfl

@[simp, grind =]
theorem mem_singleton_iff_eq {i j : Fin w} : i ∈ singleton j ↔ i = j := by
  grind [mem_def]

@[simp, grind =]
theorem singleton_inter_eq_empty_iff_not_mem {x : BitSet w} {i : Fin w} :
    singleton i ∩ x = ∅ ↔ i ∉ x := by
  simp only [eq_empty_iff_forall_not_mem, mem_inter_iff_mem_and_mem, mem_singleton_iff_eq]
  grind

@[simp, grind =]
theorem inter_singleton_eq_empty_iff_not_mem {x : BitSet w} {i : Fin w} :
    x ∩ singleton i = ∅ ↔ i ∉ x := by
  rw [inter_comm, singleton_inter_eq_empty_iff_not_mem]

@[simp, grind =]
theorem singleton_subset_iff_mem {x : BitSet w} {i : Fin w} :
    singleton i ⊆ x ↔ i ∈ x := by
  simp only [subset_iff_forall_mem_imp_mem, mem_singleton_iff_eq]
  grind

/-- List the elements of a bit set in order. -/
def toList (x : BitSet w) : List (Fin w) :=
  List.finRange w |>.filter (· ∈ x)

/-- Make a bit set from a list of elements. -/
def ofList : List (Fin w) → BitSet w
  | [] => ∅
  | i :: l => singleton i ∪ ofList l

/-- Tail-recursive version of `ofList`. Public because the `@[csimp]` theorem
below must be public, and it mentions this definition. -/
def ofListTR (l : List (Fin w)) : BitSet w :=
  loop ∅ l
where
  loop
  | acc, [] => acc
  | acc, i :: l => loop (acc ∪ singleton i) l

theorem ofListTR.loop_eq (l : List (Fin w)) :
    loop acc l = acc ∪ ofList l := by
  induction l generalizing acc with
  | nil => simp only [ofList, loop, union_empty]
  | cons i l ih => simp only [ofList, loop, ih, union_assoc]

@[csimp]
theorem ofList_eq_ofListTR : @ofList = @ofListTR := by
  funext _ _; simp only [ofListTR, ofListTR.loop_eq, empty_union]

theorem mem_toList_iff_mem {x : BitSet w} {i : Fin w} : i ∈ x.toList ↔ i ∈ x := by
  simp [toList]
