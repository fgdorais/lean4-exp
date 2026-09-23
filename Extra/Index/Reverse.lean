/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Extra.Index.Basic

public section

namespace List

namespace Index

@[inline, expose]
def reverseAux : {xs ys : List α} → Sum (Index xs) (Index ys) → Index (List.reverseAux xs ys)
  | [], _, .inr j => j
  | _ :: _, _, .inl .head => reverseAux_cons.symm ▸ reverseAux (.inr .head)
  | _ :: _, _, .inl (.tail i) => reverseAux_cons.symm ▸ reverseAux (.inl i)
  | _ :: _, _, .inr j => reverseAux_cons.symm ▸ reverseAux (.inr (.tail j))

@[inline, expose]
def reverse {xs : List α} (i : Index xs) : Index xs.reverse := reverseAux (.inl i)

@[inline, expose]
def unreverse {xs : List α} (i : Index xs.reverse) : Index xs := xs.reverse_reverse ▸ i.reverse

/-- `reverseAux` on a reversed list is `++`. Stated at list level so that the
transport in `appendTR` below is one that `toNat_eq_of_heq` can see through;
transporting along `List.append_eq_appendTR`, an equality of *functions*, cannot
be rewritten by it. -/
theorem reverse_reverseAux (xs ys : List α) :
    xs.reverse.reverseAux ys = List.append xs ys := by
  rw [List.reverseAux_eq, List.reverse_reverse]; rfl

@[inline, expose]
def appendTR {xs ys : List α} : Sum (Index xs) (Index ys) → Index (List.append xs ys)
  | .inl i => reverse_reverseAux xs ys ▸ reverseAux (.inl i.reverse)
  | .inr j => reverse_reverseAux xs ys ▸ reverseAux (.inr j)

/-- Transporting an index along an equality of lists does not change its value. -/
theorem val_eq_of_heq {xs ys : List α} (h : xs = ys) (i : Index xs) : (h ▸ i).val = i.val := by
  cases h; rfl

/-- Transporting an index along an equality of lists does not change its position. -/
theorem toNat_eq_of_heq {xs ys : List α} (h : xs = ys) (i : Index xs) :
    (h ▸ i).toNat = i.toNat := by
  cases h; rfl

theorem val_reverseAux {xs ys : List α} (k : Sum (Index xs) (Index ys)) :
    (reverseAux k).val = k.elim val val := by
  induction xs generalizing ys with
  | nil => match k with
    | .inr j => rfl
  | cons x xs ih =>
    match k with
    | .inl head => simp only [reverseAux]; exact ih (.inr head)
    | .inl (tail i) => simp only [reverseAux]; exact ih (.inl i)
    | .inr j => simp only [reverseAux]; exact ih (.inr (tail j))

theorem val_reverse {xs : List α} (i : Index xs) : i.reverse.val = i.val :=
  val_reverseAux (.inl i)

theorem toNat_reverseAux {xs ys : List α} (k : Sum (Index xs) (Index ys)) :
    (reverseAux k).toNat
      = k.elim (fun i => xs.length - 1 - i.toNat) (fun j => xs.length + j.toNat) := by
  induction xs generalizing ys with
  | nil =>
    match k with
    | .inr j => simp [reverseAux]
  | cons x xs ih =>
    -- `simp only [reverseAux]` leaves the `match` stuck for `rw`, but it reduces
    -- definitionally, so thread the arithmetic through `Eq.trans` instead.
    match k with
    | .inl head => exact (ih (.inr head)).trans (by simp [Index.toNat])
    | .inl (tail i) => exact (ih (.inl i)).trans (by simp [Index.toNat]; omega)
    | .inr j => exact (ih (.inr (tail j))).trans (by simp [Index.toNat]; omega)

theorem toNat_reverse {xs : List α} (i : Index xs) :
    i.reverse.toNat = xs.length - 1 - i.toNat :=
  toNat_reverseAux (.inl i)

theorem unreverse_reverse {xs : List α} (i : Index xs) : unreverse i.reverse = i := by
  apply eq_of_toNat_eq
  show (xs.reverse_reverse ▸ i.reverse.reverse).toNat = i.toNat
  rw [toNat_eq_of_heq, toNat_reverse, toNat_reverse, List.length_reverse]
  have := i.toNat_lt_length
  omega

theorem reverse_unreverse {xs : List α} (i : Index xs.reverse) : (unreverse i).reverse = i := by
  apply eq_of_toNat_eq
  rw [toNat_reverse]
  show xs.length - 1 - (xs.reverse_reverse ▸ i.reverse).toNat = i.toNat
  rw [toNat_eq_of_heq, toNat_reverse, List.length_reverse]
  have := i.toNat_lt_length
  rw [List.length_reverse] at this
  omega
