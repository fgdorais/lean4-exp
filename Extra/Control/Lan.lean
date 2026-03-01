import Extra.Control.Basic

namespace Control

structure Lan (F G : Type _ → Type _) (α : Type _) where
  run : (ω : Type _) × (F ω → α) × G ω

instance (F G) : Functor (Lan F G) where
  map f x := {
    run := ⟨x.run.1, f ∘ x.run.2.1, x.run.2.2⟩
  }

instance (F G) : LawfulFunctor (Lan F G) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

def Lan.unit (F G) : NaturalTransformation G (Lan F G ∘ F) where
  app {α} x := {
    run := ⟨α, id, x⟩
  }

instance (F G) [Functor F] [Functor G] [LawfulFunctor F] [LawfulFunctor G] :
    LawfulNaturalTransformation (Lan.unit F G) where
  app_map_eq_map_app f x := by
    simp [Functor.map, Lan.unit]
    done


def Lan.univ [Functor H] (η : NaturalTransformation G (H ∘ F)) :
    NaturalTransformation (Lan F G) H where
  app _ x := x.run.2.1 <$> η.app x.run.2.2
