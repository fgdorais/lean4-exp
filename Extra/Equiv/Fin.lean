/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Equiv.Basic

namespace Equiv

def equivEmpty : Equiv (Fin 0) Empty where
  fwd := Fin.decodeEmpty
  rev := Fin.encodeEmpty
  fwd_eq_iff_rev_eq := ⟨by intro | rfl => simp, by intro | rfl => simp⟩

def equivPUnit : Equiv (Fin 1) PUnit where
  fwd := Fin.decodePUnit
  rev := Fin.encodePUnit
  fwd_eq_iff_rev_eq := ⟨by intro h; cases h; simp, by intro | rfl => simp⟩

def equivBool : Equiv (Fin 2) Bool where
  fwd := Fin.decodeBool
  rev := Fin.encodeBool
  fwd_eq_iff_rev_eq := ⟨by intro | rfl => simp, by intro | rfl => simp⟩

def equivOrdering : Equiv (Fin 3) Ordering where
  fwd := Fin.decodeOrdering
  rev := Fin.encodeOrdering
  fwd_eq_iff_rev_eq := ⟨by intro | rfl => simp, by intro | rfl => simp⟩

def equivOption : Equiv (Fin (n+1)) (Option (Fin n)) where
  fwd x := Fin.decodeOption x
  rev x := Fin.encodeOption x
  fwd_eq_iff_rev_eq := ⟨by intro | rfl => simp, by intro | rfl => simp⟩

def equivSum : Equiv (Fin (n+m)) (Sum (Fin n) (Fin m)) where
  fwd x := Fin.decodeSum x
  rev x := Fin.encodeSum x
  fwd_eq_iff_rev_eq := ⟨by intro | rfl => simp, by intro | rfl => simp⟩

def equivProd : Equiv (Fin (n*m)) (Fin n × Fin m) where
  fwd x := Fin.decodeProd x
  rev x := Fin.encodeProd x
  fwd_eq_iff_rev_eq := ⟨by intro | rfl => simp, by intro | rfl => simp⟩

def equivFun : Equiv (Fin (n^m)) (Fin m → Fin n) where
  fwd x := Fin.decodeFun x
  rev x := Fin.encodeFun x
  fwd_eq_iff_rev_eq := ⟨by intro | rfl => simp, by intro | rfl => simp⟩

def equivSigma (f : Fin n → Nat) : Equiv (Fin (Fin.sum f)) ((i : Fin n) × Fin (f i)) where
  fwd x := Fin.decodeSigma f x
  rev x := Fin.encodeSigma f x
  fwd_eq_iff_rev_eq := ⟨by intro | rfl => simp, by intro | rfl => simp⟩

def equivPi (f : Fin n → Nat) : Equiv (Fin (Fin.prod f)) ((i : Fin n) → Fin (f i)) where
  fwd x := Fin.decodePi f x
  rev x := Fin.encodePi f x
  fwd_eq_iff_rev_eq := ⟨by intro | rfl => simp, by intro | rfl => simp⟩

def equivSubtype (P : Fin n → Prop) [DecidablePred P] : Equiv (Fin (Fin.countP (P ·))) { i : Fin n // P i} where
  fwd x := Fin.decodeSubtype P x
  rev x := Fin.encodeSubtype P x
  fwd_eq_iff_rev_eq := ⟨by intro | rfl => simp, by intro | rfl => simp⟩
