/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Index.Basic
import Extra.Index.Flatten
import Extra.Index.Map

namespace List.Index

def flatMap (f : α → List β) (k : (i : Index xs) × (Index (f i.val))) :
    Index (xs.flatMap f) :=
  flatten ⟨map f k.1, val_map f k.1 ▸ k.2⟩

def unFlatMap (f : α → List β) {xs : List α} (k : Index (xs.flatMap f)) :
    (i : Index xs) × (Index (f i.val)) :=
  match unflatten k with
  | ⟨k₁, k₂⟩ => ⟨unmap f k₁, val_unmap f k₁ ▸ k₂⟩

theorem unFlatMap_flatMap (f : α → List β) {xs : List α} (i : Index xs)
    (j : Index (f i.val)) : unFlatMap f (flatMap f ⟨i, j⟩) = ⟨i, j⟩ := by
  -- Unfold `flatMap` and `unFlatMap` in *separate* steps. Doing both in one
  -- `simp only [flatMap, unFlatMap]` call leaves the `match` as `.fst`/`.snd`
  -- projections; the transported proof then mentions the scrutinee, and
  -- `unflatten_flatten` can no longer be rewritten ("motive is not type
  -- correct"). Splitting the unfolding any way at all avoids this.
  show unFlatMap f (flatten ⟨map f i, val_map f i ▸ j⟩) = ⟨i, j⟩
  unfold unFlatMap
  rw [unflatten_flatten]
  simp [unmap_map]

theorem flatMap_unFlatMap (f : α → List β) {xs : List α} (k : Index (xs.flatMap f)) :
    flatMap f (unFlatMap f k) = k := by
  match h : unflatten k with
  | ⟨i, j⟩ =>
    unfold unFlatMap
    rw [h]
    rw [unflatten_eq_iff_eq_flatten] at h
    subst h
    unfold flatMap
    congr 1
    simp [map_unmap]

theorem flatMap_eq_iff_eq_unFlatMap (f : α → List β) (i : (i : Index xs) × Index (f i.val))
    (j : Index (xs.flatMap f)) : flatMap f i = j ↔ i = unFlatMap f j := by
  constructor
  · intro h; rw [←h, unFlatMap_flatMap]
  · intro h; rw [h, flatMap_unFlatMap]

theorem unFlatMap_eq_iff_eq_flatMap (f : α → List β) (i : Index (xs.flatMap f))
    (j : (i : Index xs) × Index (f i.val)) : unFlatMap f i = j ↔ i = flatMap f j := by
  constructor
  · intro h; rw [←h, flatMap_unFlatMap]
  · intro h; rw [h, unFlatMap_flatMap]

def flatMapEquiv (f : α → List β) (xs : List α) :
    Equiv ((i : Index xs) × Index (f i.val)) (Index (xs.flatMap f)) where
  fwd := flatMap f
  rev := unFlatMap f
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unFlatMap_flatMap ..
    · intro | rfl => exact flatMap_unFlatMap ..

private theorem val_flatMap_eq (f : α → List β) (k : (i : Index xs) × Index (f i.val)) :
    (flatMap f k).val = (flatten ⟨map f k.1, val_map f k.1 ▸ k.2⟩).val := rfl

theorem val_flatMap (f : α → List β) (k : (i : Index xs) × Index (f i.val)) :
    (flatMap f k).val = k.snd.val := by
  simp only [val_flatMap_eq, val_flatten]
  congr <;> simp [val_map]

theorem val_unFlatMap (f : α → List β)  {xs : List α} (i : Index (xs.flatMap f)) :
    (unFlatMap f i).snd.val = i.val := by
  rw [←flatMap_unFlatMap f i, val_flatMap, unFlatMap_flatMap]
