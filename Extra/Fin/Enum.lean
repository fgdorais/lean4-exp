import Extra.Equiv
import Extra.Equiv.Fin
import Extra.Find

namespace Fin

class Enum (α : Type _) where
  size : Nat
  enum : Fin size → α
  find : α → Fin size
  enum_eq_iff_find_eq : enum i = x ↔ find x = i

@[simp] theorem Enum.find_enum [Enum α] (i : Fin (Enum.size α)) :
    Enum.find (Enum.enum i) = i := by rw [← enum_eq_iff_find_eq]

@[simp] theorem Enum.enum_find [Enum α] (x : α) :
    Enum.enum (Enum.find x) = x := by rw [enum_eq_iff_find_eq]

@[implicit_reducible]
def Enum.ofEquiv (e : Equiv (Fin n) α) : Enum α where
  size := n
  enum := e.fwd
  find := e.rev
  enum_eq_iff_find_eq := e.fwd_eq_iff_rev_eq

def Enum.toEquiv (α) [Enum α] : Equiv (Fin (Enum.size α)) α where
  fwd := Enum.enum
  rev := Enum.find
  fwd_eq_iff_rev_eq := Enum.enum_eq_iff_find_eq

instance (α) [Enum α] : DecidableEq α :=
  fun x y =>
    if h : Enum.find x = Enum.find y then
      isTrue <| by
        rw [← Enum.enum_eq_iff_find_eq] at h
        rw [← h, Enum.enum_find]
    else
      isFalse <| fun | rfl => h rfl

--instance (α) [Enum α] : Find α := Find.ofEquiv (Enum.toEquiv α)

instance : Enum Empty := .ofEquiv Equiv.equivEmpty

instance : Enum PUnit := .ofEquiv Equiv.equivPUnit

instance : Enum Unit := .ofEquiv Equiv.equivPUnit

instance : Enum Bool := .ofEquiv Equiv.equivBool

instance (n) : Enum (Fin n) := .ofEquiv .id

instance (α) [Enum α] : Enum (Option α) :=
  .ofEquiv <| .comp (Option.equiv (Enum.toEquiv α)) Equiv.equivOption

instance (α β) [Enum α] [Enum β] : Enum (Sum α β) :=
  .ofEquiv <| .comp (Sum.equiv (Enum.toEquiv α) (Enum.toEquiv β)) Equiv.equivSum

instance (α β) [Enum α] [Enum β] : Enum (Prod α β) :=
  .ofEquiv <| .comp (Prod.equiv (Enum.toEquiv α) (Enum.toEquiv β)) Equiv.equivProd

instance (β : α → Type _) [Enum α] [(x : α) → Enum (β x)] : Enum (Sigma β) :=
  .ofEquiv <| .comp (Sigma.equiv (Enum.toEquiv α) (fun x => Enum.toEquiv (β (Enum.enum x)))) (Equiv.equivSigma _)

instance (β : α → Type _) [Enum α] [(x : α) → Enum (β x)] : Enum ((x : α) → β x) :=
  .ofEquiv <| .comp (Fun.equiv (Enum.toEquiv α) (fun x => Enum.toEquiv (β (Enum.enum x)))) (Equiv.equivPi _)

-- instance (p : α → Prop) [DecidablePred p] [Enum α] : Enum { x // p x } :=
--   .ofEquiv <| .comp (Subtype.equiv (Enum.toEquiv α) spec) (Equiv.equivSubtype _)
-- where
--   spec := by intros; simp [Enum.toEquiv]

-- instance (s : Setoid α) [DecidableRel s.r] [Enum α] : Enum (Quotient s) :=
--   .ofEquiv <| .comp (Quotient.equiv (Enum.toEquiv α) spec) (equivQuotient (s.map fun i => Enum.enum i))
-- where
--   spec := by intros; simp [Enum.toEquiv, HasEquiv.Equiv]; rfl
