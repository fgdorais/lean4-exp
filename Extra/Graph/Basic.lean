/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

structure Graph (α ε : Type _) where
  source : ε → α
  target : ε → α

namespace Graph

def Adjacent (g : Graph α ε) (x y : α) := ∃ e, g.source e = x ∧ g.target e = y
