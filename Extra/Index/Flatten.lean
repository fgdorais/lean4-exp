import Extra.Index.Basic
import Extra.Index.Append

namespace List.Index

def flatten : {xss : List (List α)} → (i : Index xss) × (Index i.val) → Index xss.flatten
  | _, ⟨head, j⟩ => append (.inl j)
  | _, ⟨tail i, j⟩ => append (.inr (flatten ⟨i, j⟩))

def unflatten : {xss : List (List α)} → Index xss.flatten → (i : Index xss) × (Index i.val)
  | _::_, k =>
    match unappend k with
    | .inl j => ⟨head, j⟩
    | .inr k => ⟨tail (unflatten k).fst, (unflatten k).snd⟩

theorem unflatten_flatten (i : (i : Index xss) × (Index i.val)) :
    unflatten (flatten i) = i := by
  induction xss with
  | nil => cases i; contradiction
  | cons xs xss ih =>
    match i with
    | ⟨head, _⟩ => simp only [flatten, unflatten, unappend_append]
    | ⟨tail _, _⟩ => simp only [flatten, unflatten, unappend_append]; rw [ih]

theorem flatten_unflatten {xss : List (List α)} (k : Index xss.flatten) :
    flatten (unflatten k) = k := by
  induction xss with
  | nil => contradiction
  | cons xs xss ih =>
    match h : unappend k with
    | .inl j => rw [unappend_eq_iff_eq_append] at h; rw [h, unflatten, unappend_append, flatten]
    | .inr k => rw [unappend_eq_iff_eq_append] at h; rw [h, unflatten, unappend_append, flatten, ih]

theorem flatten_eq_iff_eq_unflatten {i : (i : Index xss) × (Index i.val)}
    {k : Index xss.flatten} : flatten i = k ↔ i = unflatten k := by
  constructor
  · intro h; rw [←h, unflatten_flatten]
  · intro h; rw [h, flatten_unflatten]

theorem unflatten_eq_iff_eq_flatten {k : Index xss.flatten} {i : (i : Index xss) × (Index i.val)} :
    unflatten k = i ↔ k = flatten i := by
  constructor
  · intro h; rw [←h, flatten_unflatten]
  · intro h; rw [h, unflatten_flatten]

def flattenEquiv (xss : List (List α)) :
    Equiv ((i : Index xss) × Index i.val) (Index xss.flatten) where
  fwd := flatten
  rev := unflatten
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unflatten_flatten ..
    · intro | rfl => exact flatten_unflatten ..

--set_option backward.isDefEq.respectTransparency false in
--set_option trace.Meta.isDefEq true in
theorem val_flatten (i : (i : Index xss) × Index i.val) :
    (flatten i).val = i.snd.val := by
  induction xss with
  | nil => cases i; contradiction
  | cons xs xss ih =>
    match i with
    | ⟨head, j⟩ => simp [flatten, val_head, val_append_inl]
    | ⟨tail i, j⟩ => simp [flatten, val_append_inr, ih]

theorem val_unflatten {xss : List (List α)} (k : Index xss.flatten) : (unflatten k).snd.val = k.val := by
  rw [←flatten_unflatten k, val_flatten, unflatten_flatten]
