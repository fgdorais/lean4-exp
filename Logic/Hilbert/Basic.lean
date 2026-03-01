
namespace Minimal

/-- Minimal propositional logic formula -/
inductive Formula where
| symb : String → Formula
| cond : Formula → Formula → Formula
| conj : Formula → Formula → Formula
| disj : Formula → Formula → Formula
deriving Inhabited, Repr

namespace Formula

protected def toString : Formula → String
  | symb s => s
  | cond a b => "(" ++ a.toString ++ " → " ++ b.toString ++ ")"
  | conj a b => "(" ++ a.toString ++ " ∧ " ++ b.toString ++ ")"
  | disj a b => "(" ++ a.toString ++ " ∨ " ++ b.toString ++ ")"

end Formula

structure Sequent where
  hyps : List Formula
  goal : Formula

inductive Provable : Sequent → Prop where
| hyp : Provable ⟨h :: hs, h⟩
| xchg : Provable ⟨h₁ :: h₂ :: hs, g⟩ → Provable ⟨h₂ :: h₁ :: hs, g⟩
| weak : Provable ⟨hs, g⟩ → Provable ⟨h :: hs, g⟩
| imp_elim : Provable ⟨hs, .cond g₁ g₂⟩ → Provable ⟨hs, g₁⟩ → Provable ⟨hs, g₂⟩
| imp_intro : Provable ⟨h :: hs, g⟩ → Provable ⟨hs, .cond h g⟩
| and_left : Provable ⟨hs, .conj g₁ g₂⟩ → Provable ⟨hs, g₁⟩
| and_right : Provable ⟨hs, .conj g₁ g₂⟩ → Provable ⟨hs, g₂⟩
| and_intro : Provable ⟨hs, g₁⟩ → Provable ⟨hs, g₂⟩ → Provable ⟨hs, .conj g₁ g₂⟩
| or_left : Provable ⟨hs, g₁⟩ → Provable ⟨hs, .disj g₁ g₂⟩
| or_right : Provable ⟨hs, g₂⟩ → Provable ⟨hs, .disj g₁ g₂⟩
| or_elim : Provable ⟨hs, .disj g₁ g₂⟩ → Provable ⟨hs, .cond g₁ g⟩ → Provable ⟨hs, .cond g₂ g⟩ → Provable ⟨hs, g⟩

namespace Provable

@[simp, grind]
theorem and_iff : Provable ⟨hs, .conj g₁ g₂⟩ ↔ Provable ⟨hs, g₁⟩ ∧ Provable ⟨hs, g₂⟩ := by
  constructor
  · intro hconj
    constructor
    · exact and_left hconj
    · exact and_right hconj
  · intro ⟨hleft, hright⟩
    exact and_intro hleft hright

theorem imp_iff : Provable ⟨hs, .cond h g⟩ ↔ Provable ⟨h :: hs, g⟩ := by
  constructor
  · intro h

    done
  · exact imp_intro
