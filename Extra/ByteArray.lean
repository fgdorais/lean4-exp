import Extra.Basic

open Std.Iterators

namespace UInt16

structure IteratorLE (α m) [Monad m] [Iterator α m UInt8] where
  inner : IterM (α := α) m UInt8
  state : UInt16 := 0
  stage : Fin 2 := 0

instance [Monad m] [Iterator α m UInt8] : Iterator (IteratorLE α m) m UInt16 where
  IsPlausibleStep it := fun
    | .yield it' x => _
    | .skip it' => it.internalState.inner.IsPlausibleStep (.skip it)
    | .done => it.internalState.inner.IsPlausibleStep .done
  step it :=
    it.internalState.inner.step >>= fun
      | .yield it' x _ => pure <| _
      | .skip it' _ => pure <| .skip ⟨{it with inner := it'}⟩ sorry
      | .done _ => pure <| .done sorry
