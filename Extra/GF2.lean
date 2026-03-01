import Batteries

open Batteries

def BitVec.lsbScan (v : BitVec w) : Option (Fin w) :=
  Fin.foldr w (fun i r => if v[i] then some i else r) none

def BitVec.msbScan (v : BitVec w) : Option (Fin w) :=
  Fin.foldl w (fun r i => if v[i] then some i else r) none

namespace GF2

inductive Poly
| zero : Poly
| monic : BitVec d → Poly
deriving Repr, DecidableEq

namespace Poly

protected def toString (var : String) : Poly → String
  | zero => "0"
  | monic (d := d) m => Id.run do
    let mut s := var ++ d.toSuperscriptString
    for i in [0:d] do
      if m[d - i - 1]! then
        s := s ++ " + " ++ var ++ (d - i - 1).toSuperscriptString
    return s

instance : ToString Poly where
  toString p := p.toString "x"

@[inline] def ofCoeffs (m : BitVec d) : Poly :=
  match m.msbScan with
  | none => zero
  | some d => .monic (m.truncate d)

@[inline] def isZero : Poly → Bool
  | zero => true
  | monic _ => false

@[inline] def degree : Poly → Option Nat
  | zero => none
  | monic (d := d) _ => some d

@[inline] def varPow (d : Nat) : Poly := @monic d 0

protected abbrev var : Poly := varPow 1

instance : OfNat Poly (nat_lit 0) := ⟨zero⟩
instance : OfNat Poly (nat_lit 1) := ⟨varPow 0⟩

@[inline]
protected def add : Poly → Poly → Poly
  | zero, p => p
  | p, zero => p
  | monic (d := d₁) m₁, monic (d := d₂) m₂ =>
    match compare d₁ d₂ with
    | .gt => monic (m₁ ^^^ m₂.setWidth d₁ ^^^ .twoPow d₁ d₂)
    | .lt => monic (m₁.setWidth d₂ ^^^ m₂ ^^^ .twoPow d₂ d₁)
    | .eq => ofCoeffs (m₁ ^^^ m₂.setWidth d₁)
instance : Add Poly := ⟨Poly.add⟩

protected def mul : Poly → Poly → Poly
  | _, zero => zero
  | zero, _ => zero
  | monic (d := d₁) m₁, monic (d := d₂) m₂ => Id.run do
    let mut m : BitVec (d₁ + d₂) := 0
    let mut r : BitVec (d₁ + d₂) := m₂.setWidth' (by omega) ||| .twoPow _ d₂
    for hi : i in [0:d₁] do
      if m₁[i] then
        m := m ^^^ r
      r := r + r
    return monic (m ^^^ r)
instance : Mul Poly := ⟨Poly.mul⟩

protected def pow (p : Poly) (n : Nat) : Poly := Id.run do
  let mut r := 1
  let mut p := p
  let mut n := n
  while n > 0 do
    if n % 2 == 1 then
      r := r * p
    p := p * p
    n := n / 2
  return r
instance : HPow Poly Nat Poly := ⟨Poly.pow⟩

private def divRaw (a : BitVec n) (d : BitVec m) : BitVec (n - m) × BitVec m := Id.run do
  let mut q : BitVec (n - m) := 0
  let mut r : BitVec m := (a >>> (n - m)).setWidth m ^^^ d
  for i in [0:n-m] do
    let (b, t) := BitVec.adc r r a[n-m-i-1]!
    r := bif b then t ^^^ d else t
    q := BitVec.adc q q b |>.2
  return (q, r)

protected def div : Poly → Poly → Poly
  | zero, _ => zero
  | _, zero => zero
  | monic (d := d₁) a₁, monic (d := d₂) a₂ =>
    if d₁ < d₂ then zero else monic (divRaw a₁ a₂).1
instance : Div Poly := ⟨Poly.div⟩

protected def mod : Poly → Poly → Poly
  | zero, _ => zero
  | a, zero => a
  | monic (d := d₁) a₁, monic (d := d₂) a₂ =>
    if d₁ < d₂ then monic a₁ else ofCoeffs (divRaw a₁ a₂).2
instance : Mod Poly := ⟨Poly.mod⟩

end Poly

abbrev BitMat (row col : Nat) := Vector (BitVec row) col

namespace BitMat

protected def toString (a : BitMat m n) : String :=
  let s := ";".intercalate <| .ofFn fun (i : Fin m) =>
    ",".intercalate (a.map fun v => bif v[i] then "1" else "0").toList
  "#m[" ++ s ++ "]"
instance (m n) : ToString (BitMat m n) := ⟨BitMat.toString⟩

def mulVec (a : BitMat m n) (v : BitVec n) : BitVec m :=
  Fin.foldr n (fun i r => bif v[i] then r ^^^ a[i] else r) 0
instance (m n) : HMul (BitMat m n) (BitVec n) (BitVec m) := ⟨mulVec⟩

protected def mul (a : BitMat m n) (b : BitMat n k) : BitMat m k :=
  Vector.ofFn fun i => a.mulVec b[i]
instance (m n k) : HMul (BitMat m n) (BitMat n k) (BitMat m k) := ⟨BitMat.mul⟩

def transpose (a : BitMat m n) : BitMat n m :=
  Vector.ofFn fun i => Fin.foldr n (fun j r => bif a[j][i] then r ||| .twoPow n j else r) 0

protected def zero : BitMat m n := Vector.mkVector n 0

protected def identity : BitMat n n := Vector.ofFn fun i => BitVec.twoPow n i

end BitMat
