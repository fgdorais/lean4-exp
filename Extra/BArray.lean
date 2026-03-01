import Extra.Basic
import Extra.Eqns

namespace Array

theorem size_insertAt_loop (as : Array α) (i : Fin (as.size+1)) (j : Fin bs.size) :
    (insertAt.loop as i bs j).size = bs.size := by
  unfold insertAt.loop
  split
  · rw [size_insertAt_loop, size_swap]
  · rfl

theorem get_insertAt_loop_lt (as : Array α) (i : Fin (as.size+1)) (j : Fin bs.size)
    (k) (hk : k < (insertAt.loop as i bs j).size) (h : k < i) :
    (insertAt.loop as i bs j)[k] = bs[k]'(size_insertAt_loop .. ▸ hk) := by
  unfold insertAt.loop
  split
  · have h1 : k ≠ j - 1 := by omega
    have h2 : k ≠ j := by omega
    rw [get_insertAt_loop_lt, get_swap, if_neg h1, if_neg h2]
    exact h
  · rfl

theorem get_insertAt_loop_gt (as : Array α) (i : Fin (as.size+1)) (j : Fin bs.size)
    (k) (hk : k < (insertAt.loop as i bs j).size) (hgt : j < k) :
    (insertAt.loop as i bs j)[k] = bs[k]'(size_insertAt_loop .. ▸ hk) := by
  unfold insertAt.loop
  split
  · have h1 : k ≠ j - 1 := by omega
    have h2 : k ≠ j := by omega
    rw [get_insertAt_loop_gt, get_swap, if_neg h1, if_neg h2]
    exact Nat.lt_of_le_of_lt (Nat.pred_le _) hgt
  · rfl

theorem get_insertAt_loop_eq (as : Array α) (i : Fin (as.size+1)) (j : Fin bs.size)
    (k) (hk : k < (insertAt.loop as i bs j).size) (heq : i = k) (h : i.val ≤ j.val) :
    (insertAt.loop as i bs j)[k] = bs[j] := by
  unfold insertAt.loop
  split
  · next h =>
    rw [get_insertAt_loop_eq, Fin.getElem_fin, get_swap, if_pos rfl]
    exact Nat.lt_of_le_of_lt (Nat.pred_le _) j.is_lt
    exact heq
    exact Nat.le_pred_of_lt h
  · congr; omega

theorem get_insertAt_loop_gt_le (as : Array α) (i : Fin (as.size+1)) (j : Fin bs.size)
    (k) (hk : k < (insertAt.loop as i bs j).size) (hgt : i < k) (hle : k ≤ j) :
    (insertAt.loop as i bs j)[k] = bs[k-1] := by
  unfold insertAt.loop
  split
  · next h =>
    if h0 : k = j then
      cases h0
      have h1 : j.val ≠ j - 1 := by omega
      rw [get_insertAt_loop_gt, get_swap, if_neg h1, if_pos rfl]; rfl
      · exact j.is_lt
      · exact Nat.pred_lt_of_lt hgt
    else
      have h1 : k - 1 ≠ j - 1 := by omega
      have h2 : k - 1 ≠ j := by omega
      rw [get_insertAt_loop_gt_le, get_swap, if_neg h1, if_neg h2]
      exact hgt
      apply Nat.le_of_lt_add_one
      rw [Nat.sub_one_add_one]
      exact Nat.lt_of_le_of_ne hle h0
      exact Nat.not_eq_zero_of_lt h
  · next h =>
    absurd h
    exact Nat.lt_of_lt_of_le hgt hle

theorem size_insertAt (as : Array α) (i : Fin (as.size+1)) (v : α) :
    (as.insertAt i v).size = as.size + 1 := by
  rw [insertAt, size_insertAt_loop, size_push]

theorem getElem_insertAt_lt (as : Array α) (i : Fin (as.size+1)) (v : α)
    (k) (hlt : k < i.val) {hk : k < (as.insertAt i v).size} {hk' : k < as.size} :
    (as.insertAt i v)[k] = as[k] := by
  simp only [insertAt]
  rw [get_insertAt_loop_lt, get_push, dif_pos hk']
  exact hlt

theorem getElem_insertAt_gt (as : Array α) (i : Fin (as.size+1)) (v : α)
    (k) (hgt : k > i.val) {hk : k < (as.insertAt i v).size} {hk' : k - 1 < as.size} :
    (as.insertAt i v)[k] = as[k - 1] := by
  simp only [insertAt]
  rw [get_insertAt_loop_gt_le, get_push, dif_pos hk']
  exact hgt
  rw [size_insertAt] at hk
  exact Nat.le_of_lt_succ hk

theorem getElem_insertAt_eq (as : Array α) (i : Fin (as.size+1)) (v : α)
    (k) (heq : i.val = k) {hk : k < (as.insertAt i v).size} {hk' : k - 1 < as.size} :
    (as.insertAt i v)[k] = v := by
  simp only [insertAt]
  rw [get_insertAt_loop_eq, Fin.getElem_fin, get_push_eq]
  exact heq
  exact Nat.le_of_lt_succ i.is_lt

end Array

inductive BNode (α : Type _) : Nat → Nat → Type _
| leaf (as : Array α) (hs : s = as.size) : BNode α 0 s
| node : BNode α r s → t = s → BNode α (r+1) t
| cons : BNode α r s → BNode α (r+1) t → u = t + s → BNode α (r+1) u

namespace BNode

def length : BNode α s r → Nat
| leaf as _ => as.size
| node _ _ => 1
| cons _ b _ => b.length + 1

def valid (p : Nat) : {s r : Nat} → BNode α s r → Bool
| _, _, leaf _ _ => true
| _, _, node b _ => p < b.length && b.length ≤ 2 * p + 1 && b.valid p
| _, _, cons b bs _ => p < b.length && b.length ≤ 2 * p + 1 && b.valid p && bs.valid p

def get (b : BNode α r s) (i) (hi : i < s) : α :=
  match b with
  | leaf as _ => as[i]
  | node b rfl => b.get i hi
  | cons (s:=s) b bs rfl =>
    if h : i < s then
      b.get i h
    else
      bs.get (i - s) (Nat.sub_lt_right_of_lt_add (Nat.le_of_not_gt h) hi)

def set (b : BNode α r s) (i) (hi : i < s) (v : α) : BNode α r s :=
  match b with
  | leaf as rfl => leaf (as.set ⟨i, hi⟩ v) (as.size_set ..).symm
  | node b rfl => node (b.set i hi v) rfl
  | cons (s:=s) b bs rfl =>
    if h : i < s then
      cons (b.set i h v) bs rfl
    else
      cons b (bs.set (i - s) (Nat.sub_lt_right_of_lt_add (Nat.le_of_not_gt h) hi) v) rfl

def ins (b : BNode α r s) (i) (hi : i ≤ s) (v : α) : BNode α r (s+1) :=
  match b with
  | leaf as rfl => leaf (as.insertAt ⟨i, Nat.lt_succ_of_le hi⟩ v) (as.size_insertAt ..).symm
  | node b rfl => node (b.ins i hi v) rfl
  | cons (s := s) b bs rfl =>
    if h : i ≤ s then
      cons (b.ins i h v) bs rfl
    else
      cons b (bs.ins (i - s) (Nat.sub_le_of_le_add hi) v) (Nat.succ_add ..).symm

def del (b : BNode α r s) (i) (hi : i < s) : BNode α r (s-1) :=
  match b with
  | leaf as rfl => leaf (as.feraseIdx ⟨i, hi⟩) (as.size_feraseIdx ..).symm
  | node b rfl => node (b.del i hi) rfl
  | cons (s := s) (t := t) b bs rfl =>
    if h : i < s then
      have : (t + s) - 1 = t + (s - 1) := by omega
      cons (b.del i h) bs this
    else
      have : (t + s) - 1 = (t - 1) + s := by omega
      cons b (bs.del (i-s) (Nat.sub_lt_right_of_lt_add (Nat.le_of_not_gt h) hi)) this

def cast (b : BNode α r s) (h : t = s) : BNode α r t :=
  match b with
  | leaf as rfl => leaf as h
  | node b rfl => node b h
  | cons b bs rfl => cons b bs h

def split (b : BNode α r s) (i) (hi : i < s) (hi' : 0 < i) : BNode α r i × BNode α r (s-i) :=
  match b with
  | leaf as heq =>
    let as0 := as.extract 0 i
    have has0 : i = as0.size := by
      simp [as.size_extract, heq.symm, Nat.sub_zero, Nat.min_eq_left (Nat.le_of_lt hi)]
    let as1 := as.extract i as.size
    have has1 : s - i = as1.size := by
      simp [as.size_extract, heq.symm, Nat.min_self]
    (leaf as0 has0, leaf as1 has1)
  | node b rfl => match split b i hi hi' with
    | ⟨b1, b2⟩ => (node b1 rfl, node b2 rfl)
  | cons (s := s) (t := t) b bs rfl =>
    if hlt : i < s then
      match split b i hlt hi' with
      | (b1, b2) =>
        have : t + s - i = t + (s - i) := by
          rw [Nat.add_sub_assoc]
          exact Nat.le_of_lt hlt
        (node b1 rfl, cons b2 bs this)
    else if hgt : i > s then
      have h : i - s < t := by omega
      have hi' : 0 < i - s := by omega
      match split bs (i-s) h hi' with
      | (b1, b2) =>
        have h1 : i = (i - s) + s := by omega
        have h2 : (t + s) - i = t - (i - s) := by omega
        (cons b b1 h1, cast b2 h2)
    else
      have h1 : i = s := by omega
      have h2 : t + s - i = t := by omega
      (node b h1, cast bs h2)

def merge (b₁ : BNode α r s₁) (b₂ : BNode α r s₂) : BNode α r (s₁ + s₂) :=
  match b₁ with
  | leaf as₁ rfl => match b₂ with | leaf as₂ rfl => leaf (as₁ ++ as₂) (Array.size_append ..).symm
  | node b₁ rfl => cons b₁ b₂ (Nat.add_comm ..)
  | cons b₁ bs₁ rfl => cons b₁ (merge bs₁ b₂) (Nat.add_right_comm ..)

theorem get_set_eq (b : BNode α r s) (i) (hi : i < s) (v : α) :
    (b.set i hi v).get i hi = v := by
  induction b generalizing i with
  | leaf as heq => cases heq; simp only [get, set, as.getElem_set]; rfl
  | node _ heq ih => cases heq; simp only [get, set]; exact ih ..
  | cons _ _ heq ih₁ ih₂ =>
    cases heq; next s _ _ _ =>
    if hi : i < s then
      simp [get, set, hi, ih₁]
    else
      simp [get, set, hi, ih₂]

theorem get_set_ne (b : BNode α r s) (i j) (hi : i < s) (hj : j < s) (v : α) (h : i ≠ j) :
    (b.set i hi v).get j hj = b.get j hj := by
  induction b generalizing i j with
  | leaf as heq => cases heq; simp only [get, set, as.getElem_set, h]; rfl
  | node _ heq ih => cases heq; simp only [get, set]; exact ih i j hi hj h
  | cons _ _ heq ih₁ ih₂ =>
    cases heq; next s t _ _ =>
    if hj' : j < s then
      if hi' : i < s then
        simp [get, set, hi', hj']; exact ih₁ i j hi' hj' h
      else
        simp [get, set, hi', hj']
    else
      if hi' : i < s then
        simp [get, set, hi', hj']
      else
        have h : i - s ≠ j - s := by
          intro h
          rw [Nat.sub_eq_iff_eq_add (Nat.le_of_not_gt hi')] at h
          rw [Nat.sub_add_cancel (Nat.le_of_not_gt hj')] at h
          contradiction
        have hi : i - s < t := Nat.sub_lt_right_of_lt_add (Nat.le_of_not_gt hi') hi
        have hj : j - s < t := Nat.sub_lt_right_of_lt_add (Nat.le_of_not_gt hj') hj
        simp [get, set, hi', hj']; exact ih₂ (i-s) (j-s) hi hj h

end BNode

#exit

structure BNode (α rank) where
  {size : Nat}
  (item : BNodeI α rank size)

namespace BNode

def leaf (as : Array α) : BNode α 0 where
  item := .leaf as rfl

def node (b : BNode α r) : BNode α (r+1) where
  item := .node b.item

def cons (b : BNode α r) (bs : BNode α (r+1)) : BNode α (r+1) where
  item := .cons b.item bs.item

abbrev length : BNode α r → Nat | ⟨b⟩ => b.length

end BNode

structure BArray (α branch bucket) where
  {size : Nat}
  {rank : Nat}
  root : BNodeI α size (rank + 1)
  valid_root : root.valid branch bucket
  length_root : root.length ≤ 2 * branch + 1

#exit

-- theorem BNode.valid_leaf (p : Nat) (as : Array α) (hs : s = as.size) :
--   (leaf as hs).valid p = (p < as.size && as.size ≤ 2 * p + 1) := by
--   unfold valid; split <;> simp_all

theorem BNode.valid_node (p : Nat) (bs : BNodeList α s d) :
  (node bs).valid p = (p < bs.length && bs.length ≤ 2 * p + 1 && bs.valid p) := by
  simp only [valid]

attribute [eqns BNode.valid_node] BNode.valid

namespace BNodeList

def split (bs : BNodeList α s d) (p : Nat) (h : p ≤ bs.length) :
    (s₁ s₂ : Nat) × BNodeList α s₁ d × BNodeList α s₂ d := loop nil bs p h
where
  loop : {s₁ s₂ : Nat} → (bs₁ : BNodeList α s₁ d) → (bs₂ : BNodeList α s₂ d) → (p : Nat) → p ≤ bs₂.length → (s₁ s₂ : Nat) × BNodeList α s₁ d × BNodeList α s₂ d
  | _, _, bs₁, bs₂, 0, _ => ⟨_, _, bs₁, bs₂⟩
  | _, _, bs₁, cons b bs₂, p + 1, h =>
    match loop bs₁ bs₂ p (by simp at h; exact h) with
    | ⟨_, _, bs₁, bs₂⟩ => ⟨_, _, cons b bs₁, bs₂⟩
  | _, _, _, nil, p + 1, h => False.elim (by simp at h)

def split₁ (bs : BNodeList α s d) (p : Nat) (h : p ≤ bs.length) : (s : Nat) × BNodeList α s d :=
  match bs.split p h with | ⟨s₁, _, bs₁, _⟩ => ⟨s₁, bs₁⟩

def split₂ (bs : BNodeList α s d) (p : Nat) (h : p ≤ bs.length) : (s : Nat) × BNodeList α s d :=
  match bs.split p h with | ⟨_, s₂, _, bs₂⟩ => ⟨s₂, bs₂⟩

theorem size_split_loop (bs₁ : BNodeList α s₁ d) (bs₂ : BNodeList α s₂ d) (p : Nat)
    {h : p ≤ bs₂.length} : (split.loop bs₁ bs₂ p h).1 + (split.loop bs₁ bs₂ p h).2.1 = s₁ + s₂ := by
  match s₁, s₂, bs₁, bs₂, p, h with
  | _, _, bs₁, cons b bs₂, p+1, _ => simp +arith [split.loop, size_split_loop]
  | _, _, bs₁, nil, p+1, h => simp at h
  | _, _, bs₁, bs₂, 0, _ => cases bs₂ <;> simp [split.loop]

theorem size_split (bs : BNodeList α s d) (p : Nat) {h : p ≤ bs.length} :
    (split₁ bs p h).1 + (split₂ bs p h).1 = s := by
  simp [split₁, split₂, split, size_split_loop]

theorem length_split_loop₁ (bs₁ : BNodeList α s₁ d) (bs₂ : BNodeList α s₂ d) (p : Nat)
    {h : p ≤ bs₂.length} : (split.loop bs₁ bs₂ p h).2.2.1.length = p + bs₁.length := by
  match s₁, s₂, bs₁, bs₂, p, h with
  | _, _, bs₁, cons b bs₂, p+1, _ => simp +arith [split.loop, length_split_loop₁]
  | _, _, bs₁, nil, p+1, h => simp at h
  | _, _, bs₁, bs₂, 0, _ => cases bs₂ <;> simp [split.loop]

theorem length_split_loop₂ (bs₁ : BNodeList α s₁ d) (bs₂ : BNodeList α s₂ d) (p : Nat)
    {h : p ≤ bs₂.length} : (split.loop bs₁ bs₂ p h).2.2.2.length = bs₂.length - p := by
  match s₁, s₂, bs₁, bs₂, p, h with
  | _, _, bs₁, cons b bs₂, p+1, _ => simp +arith [split.loop, length_split_loop₂]
  | _, _, bs₁, nil, p+1, h => simp at h
  | _, _, bs₁, bs₂, 0, _ => cases bs₂ <;> simp [split.loop]

theorem length_split₁ (bs : BNodeList α s d) (p : Nat) {h : p ≤ bs.length} :
    (bs.split₁ p h).2.length = p := by
  simp [split, split₁, length_split_loop₁]

theorem length_split₂ (bs : BNodeList α s d) (p : Nat) {h : p ≤ bs.length} :
    (bs.split₂ p h).2.length = bs.length - p := by
  simp [split, split₂, length_split_loop₂]

theorem length_split (bs : BNodeList α s d) (p : Nat) {h : p ≤ bs.length} :
    (bs.split₁ p h).2.length + (bs.split₂ p h).2.length = bs.length := by
  rw [length_split₁, length_split₂, Nat.add_comm, Nat.sub_add_cancel h]

end BNodeList

structure BArray (α : Type _) (p : Nat) where
  {size : Nat}
  {rank : Nat}
  root : BNodeList α size rank
  root_length_le : root.length ≤ 2 * p + 1
  root_is_valid : root.valid p

namespace BArray

def empty : BArray α p where
  rank := 0
  size := 0
  root := .nil
  root_length_le := by rw [BNodeList.length]; exact Nat.zero_le ..
  root_is_valid := by rw [BNodeList.valid]

instance (α p) : EmptyCollection (BArray α p) where
  emptyCollection := empty

instance (α p) : Inhabited (BArray α p) where
  default := empty

def get (as : BArray α p) (i : Fin as.size) : α :=
  loop as.root i i.is_lt
where
  loop {s d : Nat} (bs : BNodeList α s d) (i : Nat) (hi : i < s) :=
    match bs with
    | .cons (s := s) b bs =>
      if h : i < s then
        match s, d, b with
        | _, 0, .leaf as rfl => as[i]
        | _, _+1, .node bs => loop bs i h
      else
        loop bs (i - s) (Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt h) hi)

abbrev getAux := @get.loop

@[simp]
theorem getAux_lt_leaf {s t : Nat} (bs : BNodeList α t 0) (i : Nat) (hi : i < s + t) (h : i < s)
    (heq : s = as.size) : getAux (.cons (.leaf as heq) bs) i hi = as[i] := by
  cases heq; simp [getAux, get.loop, h]

@[simp]
theorem getAux_lt_node {s t : Nat} (as : BNodeList α s p) (bs : BNodeList α t (p+1)) (i : Nat) (hi : i < s + t) (h : i < s) :
    getAux (.cons (.node as) bs) i hi = getAux as i h := by
  simp [getAux, get.loop, h]

@[simp]
theorem getAux_ge {s t : Nat} (b : BNode α s p) (bs : BNodeList α t p) (i : Nat) (hi : i < s + t) (h : i ≥ s) :
    getAux (.cons b bs) i hi = getAux bs (i - s) (Nat.sub_lt_left_of_lt_add h hi) := by
  simp [getAux, get.loop, Nat.not_lt_of_ge h]

instance (α p) : GetElem (BArray α p) Nat α (fun as i => i < as.size) where
  getElem as i h := as.get ⟨i, h⟩

@[simp]
theorem get_eq_getElem (as : BArray α p) (i : Fin as.size) : as.get i = as[i.val] := rfl

@[simp]
theorem getAux_eq_getElem (as : BArray α p) (i) (hi : i < as.size) : getAux as.root i hi = as[i] := rfl

def setAux {s d : Nat} (bs : BNodeList α s d) (i : Nat) (hi : i < s) (v : α) : BNodeList α s d :=
  match bs with
  | .cons (s := s) (t:=t) (d:=d) b bs =>
    if h : i < s then
      match s, d, b with
      | _, 0, .leaf as hs => .cons (.leaf (as.set ⟨i, hs ▸ h⟩ v) (by rw [as.size_set, hs])) bs
      | s, _+1, .node bs' => .cons (.node (setAux bs' i h v)) bs
    else
      .cons b (setAux bs (i - s) (Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt h) hi) v)

theorem length_setAux {s d : Nat} (bs : BNodeList α s d) (i : Nat) (hi : i < s) (v : α) :
    (setAux bs i hi v).length = bs.length := by
  unfold setAux
  match d, s, bs with
  | _, _, .cons (s := s) (t:=t) (d:=d) b bs =>
    simp only; split
    · split <;> simp [BNodeList.length]
    · simp [BNodeList.length]; rw [length_setAux]

theorem valid_setAux {s d : Nat} (bs : BNodeList α s d) (i : Nat) (hi : i < s) (v : α) :
    (setAux bs i hi v).valid p = bs.valid p := by
  unfold setAux
  match d, s, bs with
  | _, _, .cons (s := s) (t:=t) (d:=d) b bs =>
    simp only; split
    · split
      · simp [BNodeList.valid]
      · simp [BNode.valid_node, BNodeList.valid, length_setAux]; rw [valid_setAux]
    · simp [BNode.valid, BNodeList.valid]; rw [valid_setAux]

theorem getAux_setAux {s d : Nat} (bs : BNodeList α s d) (i : Nat) (hi : i < s) (v : α) :
    getAux (setAux bs i hi v) i hi = v := by
  unfold setAux
  split
  · split
    · split
      · next heq =>
        cases heq; rw [getAux_lt_leaf, Array.get_set, if_pos rfl] <;> assumption
      · rw [getAux_lt_node, getAux_setAux]; done
    · next hge =>
      rw [getAux_ge, getAux_setAux]
      exact Nat.le_of_not_gt hge

def set (as : BArray α p) (i : Fin as.size) (v : α) : BArray α p where
  root := setAux as.root i i.is_lt v
  root_length_le := by rw [length_setAux]; exact as.root_length_le
  root_is_valid := by rw [valid_setAux]; exact as.root_is_valid

theorem getElem_set_eq (as : BArray α p) (i : Fin as.size) (v : α) (j : Nat) (heq : j = i)
    {h' : j < (as.set i v).size} : (as.set i v)[j] = v := by
  rw [← getAux_eq_getElem]
  simp only [set]
  done
