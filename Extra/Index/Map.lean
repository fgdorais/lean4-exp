/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Extra.Index.Basic

public section

namespace List.Index

@[inline, expose]
def mapImpl (f : α → β) {xs : List α} (i : Index xs) : Index (xs.map f) :=
  Index.ofFin ⟨i.toNat, xs.length_map f ▸ i.toNat_lt_length⟩

@[expose]
def map (f : α → β) : {xs : List α} → Index xs → Index (xs.map f)
  | _, head => head
  | _, tail i => tail (map f i)

@[inline, expose]
def unmapImpl (f : α → β) {xs : List α} (i : Index (xs.map f)) : Index xs :=
  Index.ofFin ⟨i.toNat, xs.length_map f ▸ i.toNat_lt_length⟩

@[expose]
def unmap (f : α → β) : {xs : List α} → Index (xs.map f) → Index xs
  | _::_, head => head
  | _::_, tail i => tail (unmap f i)

theorem toNat_map (f : α → β) {xs : List α} (i : Index xs) : (i.map f).toNat = i.toNat := by
  induction i with
  | head => rfl
  | tail i ih => exact congrArg (· + 1) ih

theorem toNat_unmap (f : α → β) {xs : List α} (i : Index (xs.map f)) :
    (i.unmap f).toNat = i.toNat := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    match i with
    | head => rfl
    | tail i => exact congrArg (· + 1) (ih i)

@[csimp]
theorem map_eq_mapImpl : @map = @mapImpl := by
  funext α β f xs i
  show _ = Index.ofFin _
  rw [← ofFin_toFin (map f i)]
  congr 1
  apply Fin.ext
  show (map f i).toNat = i.toNat
  exact toNat_map f i

@[csimp]
theorem unmap_eq_unmapImpl : @unmap = @unmapImpl := by
  funext α β f xs i
  show _ = Index.ofFin _
  rw [← ofFin_toFin (unmap f i)]
  congr 1
  apply Fin.ext
  show (unmap f i).toNat = i.toNat
  exact toNat_unmap f i

theorem unmap_map (f : α → β) {xs : List α} (i : Index xs) : (i.map f).unmap f = i := by
  induction i with
  | head => rfl
  | tail i ih => exact congrArg tail ih

theorem map_unmap (f : α → β) {xs : List α} (i : Index (xs.map f)) : (i.unmap f).map f = i := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    match i with
    | head => rfl
    | tail i => exact congrArg tail (ih i)

theorem map_eq_iff_eq_unmap (f : α → β) {xs : List α} (i : Index xs) (j : Index (xs.map f)) : i.map f = j ↔ i = j.unmap f := by
  constructor
  · intro h; rw [←h, unmap_map]
  · intro h; rw [h, map_unmap]

theorem unmap_eq_iff_eq_map (f : α → β) {xs : List α} (i : Index (xs.map f)) (j : Index xs) : i.unmap f = j ↔ i = j.map f := by
  constructor
  · intro h; rw [←h, map_unmap]
  · intro h; rw [h, unmap_map]

@[expose]
def mapEquiv (f : α → β) (xs : List α) : Equiv (Index xs) (Index (xs.map f)) where
  fwd := map f
  rev := unmap f
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unmap_map ..
    · intro | rfl => exact map_unmap ..

theorem val_map (f : α → β) {xs : List α} (i : Index xs) : (i.map f).val = f i.val := by
  induction i with
  | head => rfl
  | tail _ ih => exact ih

theorem val_unmap (f : α → β) {xs : List α} (i : Index (xs.map f)) : i.val = f (i.unmap f).val := by
  rw [←map_unmap f i, val_map, unmap_map]
