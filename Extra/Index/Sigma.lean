import Extra.Index.Basic
import Extra.Index.Append
import Extra.Index.Map

-- Set file-wide, not per declaration. With `set_option ... in` the option is
-- applied unreliably when Lean elaborates declarations in parallel, and proofs
-- in this file then fail intermittently -- including ones that carry no flag of
-- their own, such as `val_iota` and `unsigma_sigma`. Six consecutive clean
-- builds pass with the option set file-wide; roughly one in three failed with
-- the per-declaration form.
set_option backward.isDefEq.respectTransparency false

namespace List.Index

def sigma : {xs : List α} → (i : Index xs) × Index (f i.val) → Index (xs.sigma f)
  | x::_, ⟨head, j⟩ => append (.inl (j.map (Sigma.mk x)))
  | _::_, ⟨tail i, j⟩ => append (.inr (sigma ⟨i, j⟩))

def unsigma : {xs : List α} → Index (xs.sigma f) → (i : Index xs) × Index (f i.val)
| x::_, k =>
  match unappend k with
  | .inl j => ⟨head, j.unmap (Sigma.mk x)⟩
  | .inr k => ⟨tail (unsigma k).fst, (unsigma k).snd⟩

theorem unsigma_sigma {β : α → Type _} {f : (x : α) → List (β x)} (i : (i : Index xs) × Index (f i.val)) : unsigma (sigma i) = i := by
  induction xs with
  | nil => cases i; contradiction
  | cons x xs ih =>
    match i with
    | ⟨head, j⟩ => simp only [sigma, unsigma, unappend_append, unmap_map]
    | ⟨tail i, j⟩ => simp only [sigma, unsigma, unappend_append]; rw [ih]

theorem sigma_unsigma {xs : List α} (k : Index (xs.sigma f)) : sigma (unsigma k) = k := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    match h : unappend k with
    | .inl j => rw [unappend_eq_iff_eq_append] at h; cases h; rw [unsigma, unappend_append, sigma, map_unmap]
    | .inr k => rw [unappend_eq_iff_eq_append] at h; cases h; rw [unsigma, unappend_append, sigma, ih]

theorem sigma_eq_iff_eq_unsigma {β : α → Type _} {f : (x : α) → List (β x)} (i : (i : Index xs) × Index (f i.val)) (k : Index (xs.sigma f)) : sigma i = k ↔ i = unsigma k := by
  constructor
  · intro h; cases h; rw [unsigma_sigma]
  · intro h; cases h; rw [sigma_unsigma]

theorem unsigma_eq_iff_eq_sigma {β : α → Type _} {f : (x : α) → List (β x)} (k : Index (xs.sigma f)) (i : (i : Index xs) × Index (f i.val)) : unsigma k = i ↔ k = sigma i := by
  constructor
  · intro h; cases h; rw [sigma_unsigma]
  · intro h; cases h; rw [unsigma_sigma]

def sigmaEquiv {β : α → Type _} (f : (x : α) → List (β x)) (xs : List α) : Equiv ((i : Index xs) × (Index (f i.val))) (Index (xs.sigma f)) where
  fwd := sigma
  rev := unsigma
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unsigma_sigma ..
    · intro | rfl => exact sigma_unsigma ..

theorem val_sigma {β : α → Type _} {f : (x : α) → List (β x)} (i : (i : Index xs) × Index (f i.val)) : (sigma i).val = ⟨i.fst.val, i.snd.val⟩ := by
  induction xs with
  | nil => cases i; contradiction
  | cons x xs ih =>
    -- Name `List.sigma`, and use the general `val_append` rather than
    -- `val_append_inl`/`_inr`: the goal holds `append (Sum.inr _)`, which does
    -- not match the `append_inr` abbrev syntactically.
    match i with
    | ⟨head, j⟩ => simp [List.sigma, sigma, val_append, val_map]
    | ⟨tail i, j⟩ => simp [List.sigma, sigma, val_append]; exact ih ⟨i, j⟩

theorem val_unsigma {β : α → Type _} {f : (x : α) → List (β x)} {xs : List α} (k : Index (xs.sigma f)) : ⟨(unsigma k).fst.val, (unsigma k).snd.val⟩ = k.val := by
  rw [←sigma_unsigma k, val_sigma, unsigma_sigma]
