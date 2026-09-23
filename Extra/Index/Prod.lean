/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Extra.Index.Basic
public import Extra.Index.FlatMap
public import Extra.Index.Map

@[expose] public section

namespace List

namespace Index
variable {α β} {xs : List α} {ys : List β}

def prod : Index xs × Index ys → Index (List.product xs ys)
| (i,j) => Index.flatMap (λ x => ys.map (Prod.mk x)) ⟨i, j.map (Prod.mk i.val)⟩

def unprod (k : Index (List.product xs ys)) : Index xs × Index ys :=
  match unFlatMap (λ x => ys.map (Prod.mk x)) k with
  | ⟨i,j⟩ => (i, j.unmap (Prod.mk i.val))

theorem unprod_prod (i : Index xs × Index ys) : unprod (prod i) = i := by
  simp only [prod, unprod]
  rw [unFlatMap_flatMap, unmap_map]

theorem prod_unprod (k : Index (List.product xs ys)) : prod (unprod k) = k := by
  simp only [prod, unprod, map_unmap]
  exact flatMap_unFlatMap ..

theorem prod_eq_iff_eq_unprod (i : Index xs × Index ys) (k : Index (List.product xs ys)) : prod i = k ↔ i = unprod k := by
  constructor
  · intro h; rw [←h, unprod_prod]
  · intro h; rw [h, prod_unprod]

theorem unprod_eq_iff_eq_prod (i : Index (List.product xs ys)) (j : Index xs × Index ys) : unprod i = j ↔ i = prod j := by
  constructor
  · intro h; rw [←h, prod_unprod]
  · intro h; rw [h, unprod_prod]

def prodEquiv (xs ys : List α) : Equiv (Index xs × Index ys) (Index (List.product xs ys)) where
  fwd := prod
  rev := unprod
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unprod_prod ..
    · intro | rfl => exact prod_unprod ..

theorem val_prod (i : Index xs × Index ys) : (prod i).val = (i.fst.val, i.snd.val) := by
  -- `List.product` is semireducible, so it must be unfolded explicitly: the goal
  -- carries `Index (xs.product ys)` while `val_flatMap` expects `Index (xs.flatMap _)`.
  unfold List.product
  rw [prod, val_flatMap, val_map]

theorem val_unprod (i : Index (List.product xs ys)) : ((unprod i).fst.val, (unprod i).snd.val) = i.val := by
  rw [←prod_unprod i, val_prod, unprod_prod]
