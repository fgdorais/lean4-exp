/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Algebra.Theories.Basic
import Algebra.Theories.Group
import Algebra.Theories.Semiring
import Algebra.Theories.Ring
import Algebra.Theories.UnitalRig

namespace Algebra
variable {α} (s : UnitalRingSig α)

local infixr:65 " ⊹ " => s.add
local prefix:100 "∼" => s.neg
local notation "𝟘" => s.zero
local infixr:70 " ⋆ " => s.mul
local notation "𝟙" => s.one

class UnitalRing : Prop extends Ring (no_index s.toRingSig), UnitalSemiring (no_index s.toUnitalRigSig.toUnitalSemiringSig)

@[implicit_reducible]
protected def UnitalRing.infer [OpAssoc s.add] [OpComm s.add] [OpRightInv s.add s.neg s.zero] [OpRightId s.add s.zero] [OpAssoc s.mul] [OpLeftDistrib s.mul s.add] [OpRightDistrib s.mul s.add] [OpLeftId s.mul s.one] [OpRightId s.mul s.one] : UnitalRing s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_inv := op_right_inv _
  add_right_id := op_right_id _
  mul_assoc := op_assoc _
  mul_left_distrib := op_left_distrib _
  mul_right_distrib := op_right_distrib _
  mul_left_id := op_left_id _
  mul_right_id := op_right_id _

namespace UnitalRing
variable {s} [self : UnitalRing s]

local instance : OpLeftId (no_index s.mul) (no_index s.one) := ⟨UnitalRing.mul_left_id⟩
local instance : OpRightId (no_index s.mul) (no_index s.one) := ⟨UnitalRing.mul_right_id⟩

instance toCancelUnitalRig : CancelUnitalRig (no_index s.toUnitalRigSig) := CancelUnitalRig.infer _

end UnitalRing

class UnitalCommRing : Prop extends CommRing (no_index s.toRingSig), UnitalCommSemiring (no_index s.toUnitalRigSig.toUnitalSemiringSig)

@[implicit_reducible]
protected def UnitalCommRing.infer [OpAssoc s.add] [OpComm s.add] [OpRightInv s.add s.neg s.zero] [OpRightId s.add s.zero] [OpAssoc s.mul] [OpComm s.mul] [OpRightDistrib s.mul s.add] [OpRightId s.mul s.one] : UnitalCommRing s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_inv := op_right_inv _
  add_right_id := op_right_id _
  mul_assoc := op_assoc _
  mul_comm := op_comm _
  mul_right_distrib := op_right_distrib _
  mul_right_id := op_right_id _

namespace UnitalCommRing
variable {s} [self : UnitalCommRing s]

local instance : OpRightId (no_index s.mul) (no_index s.one) := ⟨UnitalCommRing.mul_right_id⟩

instance toCancelUnitalCommRig : CancelUnitalCommRig (no_index s.toUnitalRigSig) := CancelUnitalCommRig.infer _

instance toMulCommMonoid : CommMonoid (no_index s.toUnitalRigSig.toUnitalSemiringSig.toMulMonoidSig) := CommMonoid.infer _

instance toUnitalRing : UnitalRing s := UnitalRing.infer _

end UnitalCommRing
