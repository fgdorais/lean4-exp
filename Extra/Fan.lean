import Extra.Fin

namespace Fan

structure Tree (α : Type _) where
  mem : List α → Bool
  mem_of_mem_cons : mem (x :: xs) → mem xs

structure Path (α : Type _) extends Tree α where
  split : mem (x₁ :: xs) → mem (x₂ :: xs) → x₁ = x₂
