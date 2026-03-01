import Logic.Basic

namespace Logic

inductive PForm : List α → Type
| atomic : List.Index xs → PForm xs
| falsum : PForm xs
| conj : PForm xs → PForm xs → PForm xs
| disj : PForm xs → PForm xs → PForm xs
| cond : PForm xs → PForm xs → PForm xs

structure PSeq (xs : List α) where
  is : List (PForm xs) := []
  hs : List (PForm xs)
  g : PForm xs

namespace PForm

private def toProp (val : List.Index xs → Prop) : PForm xs → Prop
| atomic i => val i
| falsum => False
| conj a b => a.toProp val ∧ b.toProp val
| disj a b => a.toProp val ∨ b.toProp val
| cond a b => a.toProp val → b.toProp val

end Logic.PForm
