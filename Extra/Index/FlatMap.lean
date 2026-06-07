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
  simp only [flatMap, unFlatMap]
  congr
  · rw [unflatten_flatten, unmap_map]
  · simp only [eqRec_heq_iff_heq]
    rw [unflatten_flatten]
    simp

theorem flatMap_unFlatMap (f : α → List β) {xs : List α} (k : Index (xs.flatMap f)) :
    flatMap f (unFlatMap f k) = k := by
  match h : unflatten k with
  | ⟨i, j⟩ =>
    rw [unflatten_eq_iff_eq_flatten] at h
    simp only [flatMap, unFlatMap, h]
    congr
    · rw [map_unmap, h, unflatten_flatten]
    · simp only [eqRec_heq_iff_heq]; rw [h, unflatten_flatten]

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
