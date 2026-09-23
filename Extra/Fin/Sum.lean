/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Extra.Basic

/-!
# Sums over `Fin`

Basic arithmetic for `Fin.sum`, proved by recursion on the bound. `Batteries`
supplies `Fin.sum_zero` and `Fin.sum_succ`; these build on them.
-/

public section

namespace Fin

theorem sum_add_sum : ∀ {n} (f g : Fin n → Nat),
    Fin.sum (fun i => f i + g i) = Fin.sum f + Fin.sum g
  | 0, _, _ => by simp [Fin.sum_zero]
  | _+1, f, g => by
    simp only [Fin.sum_succ]
    rw [sum_add_sum (fun i => f i.succ) (fun i => g i.succ)]
    lia

theorem sum_le_sum : ∀ {n} {f g : Fin n → Nat}, (∀ i, f i ≤ g i) →
    Fin.sum f ≤ Fin.sum g
  | 0, _, _, _ => by simp [Fin.sum_zero]
  | _+1, f, g, h => by
    simp only [Fin.sum_succ]
    exact Nat.add_le_add (h 0) (sum_le_sum fun i => h i.succ)

theorem sum_const : ∀ {n} (c : Nat), Fin.sum (fun _ : Fin n => c) = n * c
  | 0, _ => by simp [Fin.sum_zero]
  | _+1, c => by
    simp only [Fin.sum_succ]
    rw [sum_const c, Nat.succ_mul]
    lia

theorem sum_ite_eq : ∀ {n} (i : Fin n),
    Fin.sum (fun j : Fin n => if j = i then 1 else 0) = 1
  | 0, i => i.elim0
  | n+1, i => by
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.sum_succ]
      have h : (fun j : Fin n => if j.succ = (0 : Fin (n+1)) then 1 else 0) = fun _ => 0 := by
        funext j; simp [Fin.succ_ne_zero]
      rw [h, Fin.sum_const]
      simp
    | succ k =>
      simp only [Fin.sum_succ]
      have h : (fun j : Fin n => if j.succ = k.succ then 1 else 0)
             = fun j => if j = k then 1 else 0 := by
        funext j; simp
      rw [h, sum_ite_eq k]
      simp [(Fin.succ_ne_zero k).symm]
