/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

inductive Path {α : Type _} : α → α → Type _
| protected id x : Path x x
| protected cons x {y z} : Path y z → Path x z
deriving DecidableEq

namespace Path

private def revAppend : {x y z : α} → Path x y → Path x z → Path y z
  | _, _, _, .id _, q => q
  | _, _, _, .cons _ p, q => revAppend p (.cons _ q)

@[simp, grind =]
private theorem id_revAppend {x y : α} (p : Path x y) : (Path.id x).revAppend p = p := rfl

@[simp, grind =]
private theorem cons_revAppend {w x y z : α} (p : Path x y) (q : Path w z) :
    (p.cons w).revAppend q = p.revAppend (q.cons x) := rfl

private theorem revAppend_revAppend (p : Path x y) (q : Path x z) (r : Path y w) :
    revAppend (revAppend p q) r = revAppend q (revAppend (revAppend p (.id _)) r) := by
  induction p generalizing z w with grind

@[irreducible]
def reverse (p : Path x y) : Path y x := revAppend p (.id _)

@[simp, grind =]
theorem revAppend_id {x y : α} (p : Path x y) : p.revAppend (Path.id x) = p.reverse := by
  rw [reverse]

@[simp, grind =]
theorem reverse_id {x : α} : (Path.id x).reverse = Path.id x := by
  rw [reverse, id_revAppend]

@[simp, grind =]
theorem reverse_reverse {x y : α} (p : Path x y) : p.reverse.reverse = p := by
  simp only [reverse]; induction p with grind [revAppend_revAppend]

@[irreducible]
def append {x y z : α} (p : Path x y) (q : Path y z) : Path x z := p.reverse.revAppend q

instance (x y z : α) : HAppend (Path x y) (Path y z) (Path x z) where
  hAppend := append

@[simp, grind =]
theorem append_eq {x y z : α} (p : Path x y) (q : Path y z) : p.append q = p ++ q := rfl

@[simp, grind =]
theorem revAppend_eq {x y : α} (p : Path x y) (q : Path x z) :
    p.revAppend q = p.reverse ++ q := by rw [← append_eq, append, reverse_reverse]

@[simp, grind =]
theorem id_append {x y : α} (p : Path x y) : Path.id x ++ p = p := by
  rw [← append_eq, append, reverse_id, id_revAppend]

@[simp, grind =]
theorem append_id {x y : α} (p : Path x y) : p ++ Path.id y = p := by
  simp only [← append_eq, append, reverse]
  induction p with grind [revAppend_revAppend]

@[simp, grind =]
theorem cons_append {w x y z : α} (p : Path x y) (q : Path y z) :
    Path.cons w p ++ q = Path.cons w (p ++ q) := by
  simp only [← append_eq, append, reverse]
  induction p generalizing z w with grind [revAppend_revAppend]

@[simp, grind _=_]
theorem append_assoc {w x y z : α} (p : Path w x) (q : Path x y) (r : Path y z) :
    (p ++ q) ++ r = p ++ (q ++ r) := by
  induction p with grind

@[simp, grind =]
theorem reverse_cons {w x y : α} (p : Path x y) :
    (p.cons w).reverse = p.reverse ++ ((Path.id w).cons x) := by
  simp only [reverse, cons_revAppend]; grind [revAppend_revAppend]

@[simp, grind _=_]
theorem reverse_append {x y z : α} (p : Path x y) (q : Path y z) :
    (p ++ q).reverse = q.reverse ++ p.reverse := by
  induction p with grind

def toList {x y : α} : Path x y → List α
  | .id x => [x]
  | .cons x p => x :: toList p

private def toListTR {x y : α} (p : Path x y) : List α :=
  loop [] p |>.reverse
where
  loop : {x y : α} → List α → Path x y → List α
    | _, _, l, .id x => x :: l
    | _, _, l, .cons x p => loop (x :: l) p

private theorem toListTR.loop_eq {x y : α} (p : Path x y) (l : List α) :
    toListTR.loop l p = toListTR.loop [] p ++ l := by
  induction p generalizing l with grind [loop]

@[csimp]
private theorem toList_eq_toListTR : @toList = @toListTR := by
  funext α x y p
  simp only [toListTR]
  induction p with grind [toList, toListTR.loop, toListTR.loop_eq]
