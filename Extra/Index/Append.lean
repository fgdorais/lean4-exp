/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Extra.Index.Basic
public import Extra.Index.Reverse

@[expose] public section

namespace List.Index

def append : {xs ys : List α} → Sum (Index xs) (Index ys) → Index (List.append xs ys)
  | [], _, .inr i => i
  | _::_, _, .inr i => tail (append (.inr i))
  | _::_, _, .inl head => head
  | _::_, _, .inl (tail i) => tail (append (.inl i))

theorem toNat_append {xs ys : List α} (k : Sum (Index xs) (Index ys)) :
    (append k).toNat = k.elim (fun i => i.toNat) (fun j => xs.length + j.toNat) := by
  induction xs generalizing ys with
  | nil => match k with
    | .inr j => simp [append]
  | cons x xs ih =>
    match k with
    | .inl head => rfl
    | .inl (tail i) => exact congrArg (· + 1) (ih (.inl i))
    | .inr j => exact (congrArg (· + 1) (ih (.inr j))).trans (by simp; omega)

/-- The tail-recursive implementation agrees with `append`; this replaces an
unverified `@[implemented_by]`. Both sides are compared by position, since an
index is determined by its `toNat`. -/
@[csimp]
theorem append_eq_appendTR : @append = @appendTR := by
  funext α xs ys k
  apply eq_of_toNat_eq
  rw [toNat_append]
  match k with
  | .inl i =>
    unfold appendTR
    simp only [Sum.elim_inl]
    rw [toNat_eq_of_heq, toNat_reverseAux]
    simp only [Sum.elim_inl, List.length_reverse, toNat_reverse]
    have := i.toNat_lt_length
    omega
  | .inr j =>
    unfold appendTR
    simp only [Sum.elim_inr]
    rw [toNat_eq_of_heq, toNat_reverseAux]
    simp only [Sum.elim_inr, List.length_reverse]

abbrev append_inl (i : Index xs) : Index (xs ++ ys) := append (.inl i)

abbrev append_inr (j : Index ys) : Index (xs ++ ys) := append (.inr j)

def unappend : {xs ys : List α} → Index (xs ++ ys) → Sum (Index xs) (Index ys)
  | [], _, i => .inr i
  | x::xs, ys, i =>
    match (i : Index (x :: (xs ++ ys))) with
    | head => .inl head
    | tail i =>
      match unappend i with
      | .inl i => .inl (tail i)
      | .inr i => .inr i

theorem unappend_append (i : Sum (Index xs) (Index ys)) : unappend (append i) = i := by
  induction xs generalizing ys with
  | nil =>
    match i with
    | .inl i => contradiction
    | .inr j => rfl
  | cons x xs ih =>
    match i with
    | .inl .head => rfl
    | .inl (.tail i) => simp only [append, unappend, ih]
    | .inr j => simp only [append, unappend, ih]

theorem append_unappend (k : Index (xs ++ ys)) : append (unappend k) = k := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    match k with
    | .head => rfl
    | .tail k =>
      simp only [unappend]
      split
      next h => rw [append, ←h, ih]
      next h => rw [append, ←h, ih]

theorem append_eq_iff_eq_unappend (i : Sum (Index xs) (Index ys)) (j : Index (xs ++ ys)) : append i = j ↔ i = unappend j := by
  constructor
  · intro h; rw [←h, unappend_append]
  · intro h; rw [h, append_unappend]

theorem unappend_eq_iff_eq_append (i : Index (xs ++ ys)) (j : Sum (Index xs) (Index ys)) : unappend i = j ↔ i = append j := by
  constructor
  · intro h; rw [←h, append_unappend]
  · intro h; rw [h, unappend_append]

def appendEquiv (xs ys : List α) : Equiv (Sum (Index xs) (Index ys)) (Index (xs ++ ys)) where
  fwd := append
  rev := unappend
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unappend_append ..
    · intro | rfl => exact append_unappend ..

theorem val_append_inl (i : Index xs) : (append_inl (ys:=ys) i).val = i.val := by
  induction i with
  | head => rfl
  | tail _ ih => exact ih

theorem val_append_inr (j : Index ys) : (append_inr (xs:=xs) j).val = j.val := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem val_append {xs ys : List α} (i : Sum (Index xs) (Index ys)) :
    (append i).val = match i with | .inl i => i.val | .inr j => j.val :=
  match i with
  | .inl _ => val_append_inl ..
  | .inr _ => val_append_inr ..

theorem val_unappend {xs ys : List α} (k : Index (xs ++ ys)) :
    (match unappend k with | .inl i => i.val | .inr j => j.val) = k.val := by
  rw [←append_unappend k, val_append, unappend_append]
