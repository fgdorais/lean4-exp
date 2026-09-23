/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Extra.Array

@[expose] public section

namespace Vector

@[simp] theorem cast_self (v : Vector α n) (h : n = n) : v.cast h = v := rfl

theorem getElem_eq_getElem_toArray (v : Vector α n) (i) (h : i < n) :
    v[i] = v.toArray[i]'(v.size_toArray.symm ▸ h) := rfl

@[simp] theorem uget_eq_getElem (v : Vector α n) (i : USize) (h : i.toNat < n) :
    v.uget i h = v[i.toNat] := rfl
