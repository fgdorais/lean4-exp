import Extra.Basic


#check List.insertP

namespace Array

def insertP (p : α → Bool) (x : α) (as : Array α) : Array α :=
  loop 0 (Nat.zero_le _)
where
  loop (i : Nat) (hi : i ≤ as.size) := 
    if h : i < as.size then
      if p as[i] then
        as.insertIdx i x
      else
        loop (i+1) (Nat.succ_le_of_lt h)
    else
      as.push x

end Array

structure OrderedArray (α) (r : α → α → Bool) extends Array α where
  isOrdered : toArray.Pairwise (r · ·)

namespace OrderedArray

def insert (as : OrderedArray α r) (x : α) : OrderedArray α r where
  toArray := as.toArray