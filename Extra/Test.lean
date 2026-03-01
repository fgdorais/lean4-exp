theorem Array.getElem_append (as bs : Array α) (i) (hi : i < (as ++ bs).size) :
    (as ++ bs)[i] = if h : i < as.size then as[i] else
      have : i - as.size < bs.size := by
        apply Nat.sub_lt_left_of_lt_add
        · exact Nat.le_of_not_gt h
        · rw [← size_append]; exact hi
      bs[i - as.size] := by
  rw [getElem_eq_data_getElem]
  conv => lhs; arg 1; rw [append_data]
  split
  · rw [List.getElem_append_left]; rfl
  · next h =>
    rw [List.getElem_append_right]
    rw [size_eq_length_data] at h; rfl
    exact h

inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

def tailAux' (v : Vector α m) (h : m = n + 1) : Vector α n := 
  match m, v, h with
  | _, .cons _ v, rfl => v

def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
  Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun (a : α) (m : Nat) (as : Vector α m) =>
     fun (h : m + 1 = n + 1) =>
       Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail (v : Vector α (n+1)) : Vector α n :=
  tailAux v rfl

#check Vector.casesOn