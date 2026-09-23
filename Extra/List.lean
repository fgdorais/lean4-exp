/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Extra.Basic

@[expose] public section

namespace List

/-! ### extract -/

theorem extract_stop (as : List α) (stop : Nat) : as.extract stop stop = [] := by
  unfold extract
  rw [Nat.sub_self]
  rw [take_zero]

theorem extract_step (as : List α) (start stop : Nat) (hstart : start < stop) (hstop : stop ≤ as.length) :
  as.extract start stop = as[start]'(Nat.lt_of_lt_of_le hstart hstop) :: as.extract (start+1) stop := by
  unfold extract
  induction start, stop using Nat.recDiag generalizing as with
  | zero_zero => contradiction
  | succ_zero start => contradiction
  | zero_succ stop => match as with | a :: as => simp
  | succ_succ start stop ih =>
    match as with
    | a :: as =>
      simp
      rw [ih]
      exact Nat.lt_of_succ_lt_succ hstart
      exact Nat.le_of_succ_le_succ hstop

theorem extract_all (as : List α) : as.extract 0 as.length = as := by
  unfold extract
  rw [Nat.sub_zero]
  rw [List.drop]
  rw [take_length]

/-! ### replicate -/

theorem replicate_add {α} (a : α) : (m n : Nat) → replicate n a ++ replicate m a = replicate (m + n) a
| _, 0 => rfl
| _, _+1 => congrArg (a :: .) (replicate_add ..)

/-! ### map -/

theorem map_pure {α β} (f : α → β) (a : α) : [a].map f = [f a] := rfl

theorem map_comp {α β γ} (f : α → β) (g : β → γ) (as : List α) : as.map (g ∘ f) = (as.map f).map g := (map_map ..).symm

/-! ### bind -/

@[simp] theorem pure_bind {α β} (f : α → List β) (a : α) : [a].flatMap f = f a := by rw [flatMap_cons, flatMap_nil, append_nil]

/-! ### repeat -/

def «repeat» (n : Nat) (l : List α) := n.fold (fun _ _ r => l ++ r) []

-- `Nat.fold`'s body is not exposed, so these cannot be `rfl` in a `module`:
-- a public theorem may only unfold exposed definitions.
@[simp] theorem repeat_zero (l : List α) : l.repeat 0 = [] := by
  rw [«repeat», Nat.fold_zero]

theorem repeat_succ (l : List α) (n) : l.repeat (n+1) = l ++ l.repeat n := by
  rw [«repeat», Nat.fold_succ]; rfl

theorem length_filter_eq_sum_map (l : List α) (p : α → Bool) :
    (l.filter p).length = (l.map (fun a => (p a).toNat)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : p a
    · simp [h, ih]
    · simp [h, ih, List.sum_cons]
      lia
