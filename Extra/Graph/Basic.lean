import Extra.Basic

structure Graph (α ε : Type _) where
  source : ε → α
  target : ε → α

namespace Graph

def Adjacent (g : Graph α ε) (x y : α) := ∃ e, g.source e = x ∧ g.target e = y
