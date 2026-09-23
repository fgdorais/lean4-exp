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

namespace List

def indexIotaTR {α} (xs : List α) : List (Index xs) :=
  let rec loop : (xs : List α) → (ys : List α) → Array (Index (ys.reverse ++ xs)) → List (Index (ys.reverse ++ xs))
  | [], ys, rs => List.append_nil ys.reverse ▸ rs.toList
  | x :: xs, ys, rs =>
    have : ys.reverse ++ (x :: xs) = (x :: ys).reverse ++ xs := by
      rw [reverse_cons, append_assoc, singleton_append]
    this ▸ loop xs (x :: ys) (this ▸ rs.push (Index.append_inr Index.head))
  loop xs [] #[]

@[implemented_by indexIotaTR] -- TODO: use csimp
def indexIota {α} : (xs : List α) → List (Index xs)
| [] => []
| _::xs => Index.head :: (indexIota xs).map Index.tail

namespace Index

def iota : {xs : List α} → Index xs → Index xs.indexIota
| _::_, head => head
| _::_, tail i => tail (map tail (iota i))

theorem val_iota (i : Index xs) : val (iota i) = i := by
  induction i with
  | head => rfl
  -- `List.indexIota` must be named explicitly, so that `val_tail` sees the
  -- ambient `Index (xs.indexIota)` as an index into a `cons`.
  | tail i ih => simp only [iota, List.indexIota, val_tail, val_map, ih]

theorem iota_val {xs : List α} (i : Index xs.indexIota) : iota (val i) = i := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    match i with
    | head => rfl
    | tail i => rw [←map_unmap Index.tail i, val_tail, val_unmap Index.tail, iota, ih, map_unmap]

theorem iota_eq_iff_eq_val {xs : List α} (i : Index xs) (k : Index xs.indexIota) :
    iota i = k ↔ i = val k := by
  constructor
  · intro h; rw [←h, val_iota]
  · intro h; rw [h, iota_val]

theorem val_eq_iff_eq_iota {xs : List α} (k : Index xs.indexIota) (i : Index xs) :
    val k = i ↔ k = iota i := by
  constructor
  · intro h; rw [←h, iota_val]
  · intro h; rw [h, val_iota]

def iotaEquiv (xs : List α) : Equiv (Index xs) (Index xs.indexIota) where
  fwd := iota
  rev := val
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact val_iota ..
    · intro | rfl => exact iota_val ..
