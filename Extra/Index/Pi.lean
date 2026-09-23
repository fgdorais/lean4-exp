/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Index.Basic
import Extra.Index.FlatMap
import Extra.Index.Map

namespace List

protected def pi {α} {β : α → Type _} (f : (x : α) → List (β x)) : (xs : List α) → List ((i : Index xs) → β i.val)
| [] => [(nomatch .)]
| x::xs => (List.pi f xs).flatMap fun ys => (f x).map fun y i => match i with | .head => y | .tail i => ys i

namespace Index
variable {α} {β : α → Type _} {f : (x : α) → List (β x)} {xs : List α}

def pi : {xs : List α} → ((i : Index xs) → Index (f i.val)) → Index (xs.pi f)
| [], _ => head
| _::_, y => flatMap _ ⟨pi fun i => y i.tail, map _ (y head)⟩

def unpi : {xs : List α} → (Index (xs.pi f)) → (i : Index xs) → Index (f i.val)
| _::_, k, head => unmap _ (unFlatMap _ k).snd
| _::_, k, tail i => unpi (unFlatMap _ k).fst i

set_option backward.isDefEq.respectTransparency false in
theorem unpi_pi (h : (i : Index xs) → Index (f i.val)) : unpi (pi h) = h := by
  funext i
  induction i with
  | head => simp only [pi, unpi]; rw [unFlatMap_flatMap, unmap_map]
  | tail i ih => simp only [pi, unpi]; rw [unFlatMap_flatMap, ih]

private theorem sigma_eta {β : α → Type _} (p : (a : α) × β a) :
    (⟨p.fst, p.snd⟩ : (a : α) × β a) = p := rfl

/-- Peel `unpi` at `head`. Stated so that it rewrites without `List.pi` having
to unfold, which it will not do at `implicit` transparency. -/
theorem unpi_head {x : α} {xs : List α} (k : Index ((x::xs).pi f)) :
    unpi k head = unmap _ (unFlatMap _ k).snd := rfl

/-- Peel `unpi` at `tail`, as an equation between *functions*. Rewriting under
the binder instead would retype the body from `Index (f (tail i).val)` to
`Index (f i.val)`, which is a definitional but not a syntactic change, so `simp`
refuses it. -/
theorem unpi_comp_tail {x : α} {xs : List α} (k : Index ((x::xs).pi f)) :
    (fun i => unpi k (tail i)) = unpi (unFlatMap _ k).fst := rfl

set_option backward.isDefEq.respectTransparency false in
theorem pi_unpi (k : Index (xs.pi f)) : pi (unpi k) = k := by
  induction xs with
  | nil =>
    cases k
    · rfl
    · contradiction
  | cons x xs ih =>
    match h : unFlatMap _ k with
    | ⟨k₁,k₂⟩ =>
      rw [unFlatMap_eq_iff_eq_flatMap] at h
      cases h
      -- Unfold `pi` exactly once: `simp only [pi, unpi]` would also unfold the
      -- `pi` in the induction hypothesis position, after which `ih` no longer
      -- matches.
      rw [pi]
      simp only [unpi_head, unpi_comp_tail]
      rw [ih, map_unmap]
      -- What is left is `⟨p.fst, p.snd⟩`; collapse it so that
      -- `unFlatMap_flatMap` can rewrite `p` as a whole. Rewriting either
      -- projection on its own would leave the pair ill-typed.
      simp only [sigma_eta, unFlatMap_flatMap]

theorem pi_eq_iff_eq_unpi (h : (i : Index xs) → Index (f i.val)) (k : Index (xs.pi f)) : pi h = k ↔ h = unpi k := by
  constructor
  · intro h; rw [←h, unpi_pi]
  · intro h; rw [h, pi_unpi]

theorem unpi_eq_iff_eq_pi (k : Index (xs.pi f)) (h : (i : Index xs) → Index (f i.val)) : unpi k = h ↔ k = pi h := by
  constructor
  · intro h; rw [←h, pi_unpi]
  · intro h; rw [h, unpi_pi]

def piEquiv (xs : List α) (f : (x : α) → List (β x)) : Equiv ((i : Index xs) → Index (f i.val)) (Index (xs.pi f)) where
  fwd := pi
  rev := unpi
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unpi_pi ..
    · intro | rfl => exact pi_unpi ..

theorem val_pi {xs : List α} (y : (i : Index xs) → Index (f i.val)) :
    (pi y).val = fun i => (y i).val := by
  induction xs with
  | nil => funext i; cases i
  | cons x xs ih =>
    -- `List.pi` is semireducible, so name it explicitly: otherwise the goal
    -- carries `Index ((x::xs).pi f)` while `val_flatMap` expects
    -- `Index (_.flatMap _)`.
    simp only [List.pi]
    rw [pi, val_flatMap, val_map]
    funext i
    cases i with
    | head => rfl
    | tail i => exact congrFun (ih fun i => y i.tail) i
