/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Batteries
import Extra.Basic

class Iterable (α : Type _) where
  IT : Type _
  init : IT
  [iter : Std.Iterator IT Id α]

#print prefix Std.Iter

namespace Iterable

instance : Iterable Empty where
  IT := Option Empty
  iter := {
    IsPlausibleStep
      | _, .done => True
      | _, _ => False
    step _ := .deflate <| ⟨.done, trivial⟩
  }
  init := none

instance : Iterable PUnit where
  IT := Option PUnit
  iter := {
    IsPlausibleStep
      | ⟨some _⟩, .yield ⟨none⟩ _ => True
      | ⟨none⟩, .done => True
      | _, _ => False
    step
      | ⟨some s⟩ => .deflate <| ⟨.yield ⟨none⟩ s, trivial⟩
      | ⟨none⟩ => .deflate <| ⟨.done, trivial⟩
  }
  init := some .unit

instance : Iterable Bool where
  IT := Option Bool
  iter := {
    IsPlausibleStep
      | ⟨some false⟩, .yield ⟨some true⟩ false => True
      | ⟨some true⟩, .yield ⟨none⟩ true => True
      | ⟨none⟩, .done => True
      | _, _ => False
    step
      | ⟨some false⟩ => .deflate <| ⟨.yield ⟨some true⟩ false, trivial⟩
      | ⟨some true⟩ => .deflate <| ⟨.yield ⟨none⟩ true, trivial⟩
      | ⟨none⟩ => .deflate <| ⟨.done, trivial⟩
  }
  init := some false

instance : Iterable Ordering where
  IT := Option Ordering
  init := some .lt
  iter := {
    IsPlausibleStep
      | ⟨some .lt⟩, .yield ⟨some .eq⟩ .lt => True
      | ⟨some .eq⟩, .yield ⟨some .gt⟩ .eq => True
      | ⟨some .gt⟩, .yield ⟨none⟩ .gt => True
      | ⟨none⟩, .done => True
      | _, _ => False
    step
      | ⟨some .lt⟩ => .deflate <| ⟨.yield ⟨some .eq⟩ .lt, trivial⟩
      | ⟨some .eq⟩ => .deflate <| ⟨.yield ⟨some .gt⟩ .eq, trivial⟩
      | ⟨some .gt⟩ => .deflate <| ⟨.yield ⟨none⟩ .gt, trivial⟩
      | ⟨none⟩ => .deflate <| ⟨.done, trivial⟩
  }

instance [Iterable α] : Iterable (Option α) where
  IT := Option (IT α)
  init := none
  iter := {
    IsPlausibleStep
      | ⟨none⟩, .yield ⟨some t⟩ none => t = init
      | ⟨some s⟩, .yield ⟨some t⟩ (some out) => iter.IsPlausibleStep ⟨s⟩ (.yield ⟨t⟩ out)
      | ⟨some s⟩, .skip ⟨some t⟩ => iter.IsPlausibleStep ⟨s⟩ (.skip ⟨t⟩)
      | ⟨some s⟩, .done => iter.IsPlausibleStep ⟨s⟩ .done
      | _, _ => False
    step
      | ⟨none⟩ => .deflate <| ⟨.yield ⟨some init⟩ none, rfl⟩
      | ⟨some s⟩ => .deflate <|
        match iter.step ⟨s⟩ |>.inflate with
        | ⟨.yield ⟨t⟩ out, h⟩ => ⟨.yield ⟨some t⟩ (some out), h⟩
        | ⟨.skip ⟨t⟩, h⟩ => ⟨.skip ⟨some t⟩, h⟩
        | ⟨.done, h⟩ => ⟨.done, h⟩
  }

instance [Iterable α] [Iterable β] : Iterable (Sum α β) where
  IT := Bool × IT α × IT β
  init := (true, init, init)
  iter := {
    IsPlausibleStep
      | ⟨true, s, t⟩, .yield ⟨(false, s', t')⟩ (.inl out) =>
        t' = t ∧ iter.IsPlausibleStep ⟨s⟩ (.yield ⟨s'⟩ out)
      | ⟨true, s, t⟩, .skip ⟨(false, s', t')⟩ =>
        t' = t ∧ (iter.IsPlausibleStep ⟨s⟩ (.skip ⟨s'⟩) ∨
          (s' = s ∧ iter.IsPlausibleStep ⟨s⟩ .done))
      | ⟨false, s, t⟩, .yield ⟨(true, s', t')⟩ (.inr out) =>
        s' = s ∧ iter.IsPlausibleStep ⟨t⟩ (.yield ⟨t'⟩ out)
      | ⟨false, s, t⟩, .skip ⟨(true, s', t')⟩ =>
        s' = s ∧ (iter.IsPlausibleStep ⟨t⟩ (.skip ⟨t'⟩) ∨
          (t = t' ∧ iter.IsPlausibleStep ⟨t⟩ .done))
      | ⟨_, s, t⟩, .done =>
        iter.IsPlausibleStep ⟨s⟩ .done ∧ iter.IsPlausibleStep ⟨t⟩ .done
      | _, _ => False
    step
      | ⟨true, s, t⟩ => .deflate <|
        match iter.step ⟨s⟩ |>.inflate with
        | ⟨.yield ⟨s'⟩ out, hs⟩ =>
          ⟨.yield ⟨(false, s', t)⟩ (.inl out), rfl, hs⟩
        | ⟨.skip ⟨s'⟩, hs⟩ =>
          ⟨.skip ⟨(false, s', t)⟩, rfl, .inl hs⟩
        | ⟨.done, hs⟩ =>
          match iter.step ⟨t⟩ |>.inflate with
          | ⟨.done, ht⟩ => ⟨.done, hs, ht⟩
          | _ => ⟨.skip ⟨(false, s, t)⟩, rfl, .inr ⟨rfl, hs⟩⟩
      | ⟨false, s, t⟩ => .deflate <|
        match iter.step ⟨t⟩ |>.inflate with
        | ⟨.yield ⟨t'⟩ out, ht⟩ =>
          ⟨.yield ⟨(true, s, t')⟩ (.inr out), rfl, ht⟩
        | ⟨.skip ⟨t'⟩, ht⟩ =>
          ⟨.skip ⟨(true, s, t')⟩, rfl, .inl ht⟩
        | ⟨.done, ht⟩ =>
          match iter.step ⟨s⟩ |>.inflate with
          | ⟨.done, hs⟩ => ⟨.done, hs, ht⟩
          | _ => ⟨.skip ⟨(true, s, t)⟩, rfl, .inr ⟨rfl, ht⟩⟩
  }

instance [Iterable α] [Iterable β] : Iterable (α × β) where
  IT := IT α × IT β × (xs : Array α) × (ys : Array β) × (Fin (xs.size+1) ⊕ Fin (ys.size+1))
  init := ⟨init, init, #[], #[], .inl 0⟩
  iter := {
    IsPlausibleStep
      | ⟨⟨s, t, xs, ys, .inl i⟩⟩, .yield ⟨⟨s', t', xs', ys', .inl i'⟩⟩ (x, y) => _
      | ⟨⟨s, t, xs, ys, .inl i⟩⟩, .skip ⟨⟨s', t', xs', ys', .inl i'⟩⟩ => _
      | ⟨⟨s, t, xs, ys, .inl i⟩⟩, .skip ⟨⟨s', t', xs', ys', .inr 0⟩⟩ =>
        i = xs.size ∧ s' = s ∧ xs' = xs
      | ⟨⟨s, t, xs, ys, .inl i⟩⟩, .done =>
        i = xs.size ∧ iter.IsPlausibleStep ⟨s⟩ .done ∧ iter.IsPlausibleStep ⟨t⟩ .done
      | ⟨⟨s, t, xs, ys, .inr j⟩⟩, .yield ⟨⟨s', t', xs', ys', .inr j'⟩⟩ (x, y) => _
      | ⟨⟨s, t, xs, ys, .inr j⟩⟩, .skip ⟨⟨s', t', xs', ys', .inr j'⟩⟩ => _
      | ⟨⟨s, t, xs, ys, .inr j⟩⟩, .skip ⟨⟨s', t', xs', ys', .inl 0⟩⟩ => _
      | ⟨⟨s, t, xs, ys, .inr j⟩⟩, .done =>
        j = ys.size ∧ iter.IsPlausibleStep ⟨s⟩ .done ∧ iter.IsPlausibleStep ⟨t⟩ .done
      | _, _ => False
    step := _
  }

#exit

instance (β : α → Type _) [Iterable α] [(x : α) → Iterable (β x)] :
    Iterable ((x : α) × β x) where
  IT := IT α × Nat × Array ((x : α) × IT (β x))
  init := (init, 0, #[])
  iter := {
    IsPlausibleStep
      | ⟨s, i, ts⟩, .yield ⟨s', i', ts'⟩ ⟨x, y⟩ =>
        if h : i < ts.size then
          s' = s ∧ i' = i+1 ∧ ts[i].1 = ts'[i].1 ∧
            iter.IsPlausibleStep ⟨ts[i].2⟩ (.yield ⟨ts'[i].2⟩ y
        else False
      | ⟨s, i, ts⟩, .skip ⟨s', i', ts'⟩ => _
      | ⟨s, i, ts⟩, .done =>
        iter.IsPlausibleStep ⟨s⟩ .done ∧
          (∀ _ : i < ts.size, iter.IsPlausibleStep ⟨ts[i].2⟩ .done)
    step := _
  }


#print Std.PlausibleIterStep

instance natIterable : Iterable Nat where
  IT := Nat
  init := 0
  iter := {
    IsPlausibleStep
      | it, .yield it' n => n = it.internalState ∧ it'.internalState = n + 1
      | _, _ => False
    step it := .deflate <| ⟨.yield ⟨it.internalState+1⟩ it.internalState, by trivial⟩
  }

instance finIterable (n) : Iterable (Fin n) where
  IT := Fin (n+1)
  init := 0
  iter := {
    IsPlausibleStep
      | ⟨⟨i, _⟩⟩, .yield ⟨⟨j, _⟩⟩ ⟨k, _⟩ => k = i ∧ j = i+1
      | ⟨⟨i, _⟩⟩, .done => ¬ i < n
      | _, _ => False
    step
      | ⟨⟨i, _⟩⟩ =>
        if h : i < n then
          .deflate <| ⟨.yield ⟨⟨i+1, Nat.succ_lt_succ h⟩⟩ ⟨i, h⟩, ⟨rfl, rfl⟩⟩
        else
          .deflate <| ⟨.done, h⟩
  }

#print Std.Iter
#print Std.Iterator
