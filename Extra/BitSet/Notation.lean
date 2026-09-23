/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Extra.BitSet.Lemmas
public import Extra.BitSet.Card
public meta import Lean  -- `@[app_delab]` requires public declarations, so the
                        -- delaborators below are public `meta` and need this public too

/-!
# Bit sets from lists

Building an `Extra.BitSet` from a list of indices, and the `b{i, ...}#w`
notation for bit set literals.
-/

public section

namespace Extra.BitSet

/-- Make a bit set from a list of elements. -/
@[expose]
def ofList : List (Fin w) → BitSet w
  | [] => ∅
  | [i] => singleton i
  | i :: l => singleton i ∪ ofList l

@[simp, grind =]
theorem ofList_nil : ofList ([] : List (Fin w)) = ∅ := rfl

@[simp, grind =]
theorem ofList_singleton (i : Fin w) : ofList [i] = singleton i := rfl

@[simp, grind =]
theorem ofList_cons (i : Fin w) (l : List (Fin w)) :
    ofList (i :: l) = singleton i ∪ ofList l := by
  cases l with
  | nil => show singleton i = singleton i ∪ ∅; rw [union_empty]
  | cons => rfl

theorem mem_ofList_iff_mem {l : List (Fin w)} {i : Fin w} : i ∈ ofList l ↔ i ∈ l := by
  induction l with
  | nil => simp
  | cons j l ih => simp [ofList_cons, ih]

@[simp]
theorem ofList_toList (x : BitSet w) : ofList (toList x) = x := by
  ext i; rw [mem_ofList_iff_mem, mem_toList_iff_mem]

theorem card_ofList_le_length (l : List (Fin w)) : (ofList l).card ≤ l.length := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [ofList_cons, List.length_cons]
    lia [card_union_le_card_add_card (singleton i) (ofList l), card_singleton i]

theorem card_ofList_eq_length_of_nodup {l : List (Fin w)} (h : l.Nodup) :
    (ofList l).card = l.length := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.nodup_cons] at h
    rw [ofList_cons, List.length_cons]
    have hdisj : singleton i ∩ ofList l = ∅ :=
      singleton_inter_eq_empty_iff_not_mem.mpr (fun hm => h.1 (mem_ofList_iff_mem.mp hm))
    lia [card_union_eq_card_add_card_iff_disjoint.mpr hdisj, card_singleton i, ih h.2]

/-- Tail-recursive version of `ofList`. -/
@[local expose]
def ofListTR (l : List (Fin w)) : BitSet w :=
  loop ∅ l
where
  loop
  | acc, [] => acc
  | acc, i :: l => loop (acc ∪ singleton i) l

theorem ofListTR.loop_eq (l : List (Fin w)) :
    loop acc l = acc ∪ ofList l := by
  induction l generalizing acc with
  | nil => simp only [ofList_nil, loop, union_empty]
  | cons i l ih => simp only [ofList_cons, loop, ih, union_assoc]

@[csimp]
theorem ofList_eq_ofListTR : @ofList = @ofListTR := by
  funext _ _; simp only [ofListTR, ofListTR.loop_eq, empty_union]

/--
`b{i, ...}#w` is the bit set with elements `i, ...`, that is, `ofList [i, ...]`.

The width `w` is optional, and is written after `#` as for `BitVec` literals.
When present it interprets the elements as terms of type `Fin w`, which is what
makes a literal such as `b{0, 3, 5}#8 : BitSet 8` elaborate; without it the width
is inferred from the elements, as in `b{i, j}`.

No whitespace is allowed around the `#`.
-/
syntax:max "b{" term,* "}" (noWs "#" noWs num)? : term

macro_rules
  | `(b{$is,*}) => `(ofList [$is,*])
  | `(b{$is,*}#$w:num) => `(ofList (w := $w) [$is,*])

section Delab
open Lean PrettyPrinter Delaborator SubExpr

/-- Delaborate the elements of a `List` literal, failing if it is not a literal. -/
private meta partial def delabListLitElems (acc : Array Term) : DelabM (Array Term) := do
  let e ← getExpr
  if e.isAppOfArity ``List.nil 1 then
    return acc
  else if e.isAppOfArity ``List.cons 3 then
    let i ← withNaryArg 1 delab
    withNaryArg 2 <| delabListLitElems (acc.push i)
  else
    failure

/--
Delaborate `ofList [i, ...]` using the `b{i, ...}#w` notation.

The width is printed when it is a numeral, so that the result parses back; it is
omitted when the width is not literally known, as in `b{i}` with `i : Fin w`.
-/
@[app_delab ofList]
meta def delabOfList : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 2 do
    let is ← withNaryArg 1 <| delabListLitElems #[]
    match (← getExpr).getArg! 0 |>.nat? with
    | some w => `(b{$is,*}#$(quote w):num)
    | none => `(b{$is,*})

/--
Delaborate `singleton i` using the `b{i}#w` notation.

This is the same term as `ofList [i]` up to definitional unfolding, so the two
print alike.
-/
@[app_delab singleton]
meta def delabSingleton : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 2 do
    let i ← withNaryArg 1 delab
    match (← getExpr).getArg! 0 |>.nat? with
    | some w => `(b{$i}#$(quote w):num)
    | none => `(b{$i})

end Delab
