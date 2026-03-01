
namespace Std.Iterators

structure Window (α : Type _) (m : Type _ → Type _) (β : Type _) where
  size : Nat
  window : List β
  inner : Std.IterM (α := α) m β

def IterM.window (n : Nat) (l : List β) (it : IterM (α := α) m β) :
    IterM (α := Window α m β) m (List β) :=
  toIterM ⟨n, l, it⟩ m (List β)

inductive Window.PlausibleStep [Iterator α m β] (it : IterM (α := Window α m β) m β) :
    (step : IterStep (IterM (α := Window α m β) m β) β) → Prop where
  | yield : ∀ {it' out k}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      it.internalState.window.length = it.internalState.size →
      PlausibleStep it (.yield (it'.window k) out)
  | skip : ∀ {it' k}, it.internalState.inner.IsPlausibleStep (.skip it') →
      it.internalState.remaining = k + 1 → PlausibleStep it (.skip (it'.take (k + 1)))
  | done : it.internalState.inner.IsPlausibleStep .done → PlausibleStep it .done
  | depleted : it.internalState.remaining = 0 →
      PlausibleStep it .done
