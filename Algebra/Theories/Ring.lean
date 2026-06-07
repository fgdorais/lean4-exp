/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Algebra.Theories.Basic
import Algebra.Theories.Group
import Algebra.Theories.Monoid
import Algebra.Theories.Semigroup
import Algebra.Theories.UnitalRig

namespace Algebra
variable {α} (s : RingSig α)

local infixr:70 " ⋆ " => s.mul
local infixr:65 " ⊹ " => s.add
local prefix:100 "∼" => s.neg
local notation "𝟘" => s.zero

class Ring : Prop extends Semiring (no_index s.toSemiringSig) where
  protected add_right_id (x) : x ⊹ 𝟘 = x
  protected add_right_inv (x) : x ⊹ ∼x = 𝟘

@[implicit_reducible]
protected def Ring.infer [OpAssoc s.add] [OpComm s.add] [OpRightInv s.add s.neg s.zero] [OpRightId s.add s.zero] [OpAssoc s.mul] [OpLeftDistrib s.mul s.add] [OpRightDistrib s.mul s.add] : Ring s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_id := op_right_id _
  add_right_inv := op_right_inv _
  mul_assoc := op_assoc _
  mul_left_distrib := op_left_distrib _
  mul_right_distrib := op_right_distrib _

namespace Ring
variable {s} [self : Ring s]

local instance : OpRightId (no_index s.add) (no_index s.zero) := ⟨Ring.add_right_id⟩
local instance : OpRightInv (no_index s.add) (no_index s.neg) (no_index s.zero) := ⟨Ring.add_right_inv⟩

instance toAddCommGroup : CommGroup (no_index s.toAddGroupSig) := CommGroup.infer _

instance toCancelRig : CancelRig (no_index s.toRigSig) := CancelRig.infer _

end Ring

class CommRing: Prop extends CommSemiring (no_index s.toSemiringSig) where
  protected add_right_id (x) : x ⊹ 𝟘 = x
  protected add_right_inv (x) : x ⊹ ∼x = 𝟘

@[implicit_reducible]
protected def CommRing.infer [OpAssoc s.add] [OpComm s.add] [OpRightInv s.add s.neg s.zero] [OpRightId s.add s.zero] [OpAssoc s.mul] [OpComm s.mul] [OpRightDistrib s.mul s.add] : CommRing s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_id := op_right_id _
  add_right_inv := op_right_inv _
  mul_assoc := op_assoc _
  mul_comm := op_comm _
  mul_right_distrib := op_right_distrib _

namespace CommRing
variable {s} [self : CommRing s]

local instance : OpRightId (no_index s.add) (no_index s.zero) := ⟨CommRing.add_right_id⟩
local instance : OpRightInv (no_index s.add) (no_index s.neg) (no_index s.zero) := ⟨CommRing.add_right_inv⟩

instance toRing : Ring s := Ring.infer _

instance toCancelCommRig : CancelCommRig (no_index s.toRigSig) := CancelCommRig.infer _

end CommRing

end Algebra
