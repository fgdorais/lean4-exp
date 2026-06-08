import Extra.Index.Basic

namespace List

namespace Index

@[inline]
def reverseAux : {xs ys : List α} → Sum (Index xs) (Index ys) → Index (List.reverseAux xs ys)
  | [], _, .inr j => j
  | _ :: _, _, .inl .head => reverseAux_cons.symm ▸ reverseAux (.inr .head)
  | _ :: _, _, .inl (.tail i) => reverseAux_cons.symm ▸ reverseAux (.inl i)
  | _ :: _, _, .inr j => reverseAux_cons.symm ▸ reverseAux (.inr (.tail j))

@[inline]
def reverse {xs : List α} (i : Index xs) : Index xs.reverse := reverseAux (.inl i)

@[inline]
def unreverse {xs : List α} (i : Index xs.reverse) : Index xs := xs.reverse_reverse ▸ i.reverse

@[inline]
def appendTR {xs ys : List α} : Sum (Index xs) (Index ys) → Index (List.append xs ys)
  | .inl i => List.append_eq_appendTR ▸ reverseAux (.inl i.reverse)
  | .inr j => List.append_eq_appendTR ▸ reverseAux (.inr j)
