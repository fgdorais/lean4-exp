import Batteries
import Extra.Cast.Basic

def Functor.Poly {α : Type _} (β : α → Type _) (ω : Type _) := Sigma fun i => β i → ω

instance (β : α → Type _) : Functor (Functor.Poly β) where
  map | f, ⟨i, w⟩ => ⟨i, f ∘ w⟩

instance (β : α → Type _) : LawfulFunctor (Functor.Poly β) where
  map_const := by intros; rfl
  id_map := by intros; rfl
  comp_map := by intros; rfl

class Functor.Algebra (φ : outParam <| Type _ → Type _) (α : Type _) where
  eval : φ α → α

class Functor.Algebra.Hom (φ : outParam <| Type _ → Type _) [Functor φ] [Functor.Algebra φ α] [Functor.Algebra φ β] (f : α → β) : Prop where
  comm (x : φ α) : f (eval x) = eval (f <$> x)

class Functor.Coalgebra (φ : outParam <| Type _ → Type _) (α : Type _) where
  dest : α → φ α

class Functor.Coalgebra.Hom (φ : outParam <| Type _ → Type _) [Functor φ] [Functor.Coalgebra φ α] [Functor.Coalgebra φ β] (f : α → β) : Prop where
  comm (x : α) : dest (f x) = f <$> dest x

inductive W {α : Type _} (β : α → Type _) : Type _ where
  | sup (f : (i : α) → β i → W β) : W β

inductive M.Core {α : Type _} (β : α → Type _) : Type _
  | mk {ω : Type _} : (ω → Functor.Poly β ω) → ω → M.Core β

abbrev M.Core.head {β : α → Type _} : M.Core β → α
  | mk d m => (d m).fst

abbrev M.Core.tail {β : α → Type _} : (m : M.Core β) → β m.head → M.Core β
  | mk d m, x => mk d ((d m).snd x)

inductive M.Equiv {β : α → Type _} : M.Core β → M.Core β → Prop
  | protected refl (x) : Equiv x x
  | protected eucl : Equiv x y → Equiv x z → Equiv y z
  | protected comm {f : ω → ω'} : ((w : ω) → d' (f w) = f <$> d w) → Equiv (.mk d w) (.mk d' (f w))

namespace M.Equiv
variable {β : α → Type _}

protected def rfl {x : M.Core β} : Equiv x x := Equiv.refl x

protected def symm : Equiv x y → Equiv y x :=
  fun h => Equiv.eucl h Equiv.rfl

protected def trans : Equiv x y → Equiv y z → Equiv x z :=
  fun hy hz => Equiv.eucl hy.symm hz

protected def eucr : Equiv x z → Equiv y z → Equiv x y :=
  fun hy hz => Equiv.trans hy hz.symm

end M.Equiv

def M.setoid (β : α → Type _) : Setoid (M.Core β) where
  r := M.Equiv
  iseqv := .mk Equiv.refl Equiv.symm Equiv.trans

def M (β : α → Type _) : Type _ := Quotient (M.setoid β)

def M.Impl (β : α → Type _) : Type _ := Quotient (M.setoid β)

def M.mk {β : α → Type _} (d : ω → Functor.Poly β ω) (w : ω) : M β :=
  Quotient.mk _ (.mk d w)

-- def M.head {β : α → Type _} : M β → α :=
--   Quotient.lift Core.head fun m i h => by
--     induction h with
--     | refl => rfl
--     | eucl _ _ ih₁ ih₂ => rw [←ih₁, ih₂]
--     | comm h => simp [Functor.map, Core.head, h]; rfl

def M.dest {β : α → Type _} : M β → Sigma fun i => β i → M β :=
  Quotient.lift (fun m => ⟨m.head, fun x => Quotient.mk (M.setoid β) (m.tail x)⟩) fun m i h => by
    simp only [HasEquiv.Equiv, M.setoid] at h
    induction h with
    | refl => rfl
    | eucl _ _ hy hz => rw [← hy, ← hz]
    | @comm _ _ _ d w _ h =>
      simp only [Core.head, Core.tail]
      have hw := h w
      match hw' : d w with
      | ⟨_, _⟩ =>
        simp [hw'] at hw
        rw [hw]
        congr
        funext
        apply Quotient.sound
        exact Equiv.comm h

abbrev M.head {β : α → Type _} (m : M β) : α := m.dest.1

abbrev M.tail {β : α → Type _} (m : M β) : β m.head → M β := m.dest.2

inductive M.Level {α : Type _} (β : α → Type _) : Nat → Type _
  | base (i : α) : M.Level β 0
  | cons (i : α) (t : β i → M.Level β n) : M.Level β (n+1)

def M.Level.head {β : α → Type _} : M.Level β n → α
  | base i => i
  | cons i _ => i

def M.Level.tail {β : α → Type _} : (m : M.Level β (n+1)) → β m.head → M.Level β n
  | cons _ u, x => u x

inductive M.LevelExtend {α : Type _} {β : α → Type _} : {n : Nat} → M.Level β n → M.Level β (n + 1) → Prop
  | base (i : α) (t : β i → M.Level β 0) : M.LevelExtend (.base i) (.cons i t)
  | cons (i : α) (t : β i → M.Level β n) (t' : β i → M.Level β (n+1)) :
      (∀ x, M.LevelExtend (t x) (t' x)) → M.LevelExtend (.cons i t) (.cons i t')

theorem M.Level.head_eq_head {β : α → Type _} :
    {a : M.Level β n} → {b : M.Level β (n+1)} → M.LevelExtend a b → a.head = b.head
  | _, _, .base _ _ => rfl
  | _, _, .cons _ _ _ _ => rfl

theorem M.Level.tail_extend_tail {β : α → Type _} {t : M.Level β (n+1)} {t' : M.Level β (n+2)}
    {x : β t.head} {x' : β t'.head} (h : M.LevelExtend t t') (heq : HEq x x') :
    M.LevelExtend (t.tail x) (t'.tail x') := by
  cases h with | cons i t t' h => cases heq; exact h ..

structure M.Tree (β : α → Type _) where
  level (n : Nat) : M.Level β n
  extend (n : Nat) : M.LevelExtend (level n) (level (n+1))

namespace M.Tree

def head {β : α → Type _} (t : M.Tree β) : α := (t.level 0).head

theorem head_eq {β : α → Type _} (t : M.Tree β) (n : Nat) :
  (t.level n).head = t.head := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← ih, ← M.Level.head_eq_head (t.extend n)]

def tail (t : M.Tree β) (x : β t.head) : M.Tree β where
  level n := (t.level (n+1)).tail (t.head_eq (n+1) ▸ x)
  extend n := by
    apply M.Level.tail_extend_tail
    · exact t.extend ..
    · simp

end M.Tree

def M.toLevel {β : α → Type _} (d : ω → Functor.Poly β ω) (w : ω) : (n : Nat) → M.Level β n
  | 0 => match d w with | ⟨i, _⟩ => .base i
  | n+1 => match d w with | ⟨i, w⟩ => .cons i fun x => M.toLevel d (w x) n

theorem M.toLevel_extend {β : α → Type _} (d : ω → Functor.Poly β ω) (w : ω) (n : Nat) :
    M.LevelExtend (M.toLevel d w n) (M.toLevel d w (n+1)) := by
  induction n generalizing d w with
  | zero => exact M.LevelExtend.base ..
  | succ n ih => cases d w; apply M.LevelExtend.cons; intro; exact ih ..

def M.toTree {β : α → Type _} (d : ω → Functor.Poly β ω) (w : ω) : M.Tree β where
  level := M.toLevel d w
  extend := M.toLevel_extend d w

#exit

protected def W.Nat := W (α:=Bool) fun | false => Empty | true => Unit

@[reducible]
protected def M.Nat := M (α:=Bool) fun | false => Empty | true => Unit

namespace M.Nat

def pred (n : M.Nat) (h : n.head = true) : M.Nat := M.tail n (h ▸ ())

#exit

inductive ListF (α ω : Type _) where
  | nil : ListF α ω
  | cons : α → ω → ListF α ω
  deriving Inhabited, Repr

inductive Colist (α : Type _) where
  | intro : (ω → ListF α ω) → ω → Colist α

def Colist.dest : Colist α → ListF α (Colist α)
  | intro d w => match d w with
    | .nil => .nil
    | .cons x w => .cons x (intro d w)

def Colist.next? (s : Colist α) : Option (α × Colist α) :=
  match s.dest with
  | .nil => none
  | .cons x s => some (x, s)

def Colist.nil : Colist α :=
  intro (fun _ => .nil) ()

def Colist.cons (x : α) : Colist α → Colist α
  | intro d w =>
    let dest
      | (some x, w) => .cons x (none, w)
      | (none, w) =>
        match d w with
        | .nil => .nil
        | .cons x w => .cons x (none, w)
    intro dest (some x, w)

def Colist.take : Nat → Colist α → List α
  | 0, _ => []
  | n+1, intro d w =>
    match d w with
    | .nil => []
    | .cons x w => x :: take n (intro d w)


#exit

inductive ListT.Spec (ω : Type _ → Type _) : Type _ → Type _
  | nil : ListT.Spec ω α
  | cons : α → ω α → ListT.Spec ω α

class ListT.View (ω : Type _ → Type _) (α : Type _) where
  dest : ω α → ListT.Spec ω α

def NProdT (m : Type _ → Type _) (α : Type _) : Nat → Type _
  | 0 => PUnit
  | n+1 => α × m (NProdT m α n)

def ProdT (m : Type _ → Type _) (α : Type _) := Sigma (NProdT m α)
