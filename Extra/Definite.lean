/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

structure Definite (α : Type _) where
  is_eq : α → Prop
  is_subsingleton : is_eq x → is_eq y → x = y
  is_nonempty : ∃ x, is_eq x

def Definite.inj (x : α) : Definite α where
  is_eq := (· = x)
  is_subsingleton h₁ h₂ := by rw [h₁, h₂]
  is_nonempty := ⟨x, rfl⟩
