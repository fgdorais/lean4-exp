import Extra.Vector

class Std.LeftDistrib {α β : Type _} (mul : α → β → β) (add : β → β → β) : Prop where
  left_distrib : mul a (add b₁ b₂) = add (mul a b₁) (mul a b₂)

class Std.RightDistrib {β α : Type _} (mul : β → α → β) (add : β → β → β) : Prop where
  right_distrib : mul (add b₁ b₂) a = add (mul b₁ a) (mul b₂ a)

class Std.RightInverse {α β γ : Type _} (op : α → β → γ)
    (inv : outParam <| α → β) (e : outParam γ) : Prop where
  right_inverse : op a (inv b) = e

class Std.LeftInverse {α β γ : Type _} (op : α → β → γ)
    (inv : outParam <| β → α) (e : outParam γ) : Prop where
  left_inverse : op (inv a) b = e

class abbrev Std.Inverse (op : α → α → β) (inv : outParam <| α → α) (e : outParam β) : Prop :=
  Std.LeftInverse op inv e, Std.RightInverse op inv e

class abbrev Std.Distrib {α : Type _} (add mul : α → α → α) : Prop :=
  LeftDistrib add mul, RightDistrib add mul

class Std.LeftZero {α : Type _} (op : α → α → α) (z : outParam α) : Prop where
  left_zero : op z a = z

class Std.RightZero {α : Type _} (op : α → α → α) (z : outParam α) : Prop where
  right_zero : op a z = z

class abbrev Std.Zero {α : Type _} (op : α → α → α) (z : outParam α) : Prop :=
  Std.LeftZero op z, Std.RightZero op z

class Std.Monoid {α : Type _} (op : α → α → α) (e : outParam α)
  extends Std.Associative op, Std.Identity op e

class Std.Semiring {α : Type _} (add : α → α → α) (mul : α → α → α) (z e : outParam α) : Prop where
  [toAddMonoid : Std.Monoid add z]
  [toMulMonoid : Std.Monoid mul e]
  [toDistrib : Std.Distrib add mul]
  [toZero : Std.Zero add z]

class Std.Ring {α : Type _}

abbrev Matrix (α rows cols) := Vector (Vector α cols) rows

namespace Matrix

protected abbrev size (_ : Matrix α r c) := (r, c)

protected abbrev row (m : Matrix α r c) (i) (h : i < r := by get_elem_tactic) :
    Vector α c := m[i]

@[inline]
protected def col (m : Matrix α r c) (i) (h : i < c := by get_elem_tactic) :
    Vector α r := .ofFn fun j => m[j][i]

@[simp]
theorem getElem_row (m : Matrix α r c) (i j) (hi : i < r) (hj : j < c) :
    (m.row i)[j] = m[i][j] := rfl

@[simp]
theorem getElem_col (m : Matrix α r c) (i j) (hi : i < r) (hj : j < c) :
    (m.col j)[i] = m[i][j] := by
  simp [Matrix.col]

@[inline]
protected def ofFn (f : Fin r → Fin c → α) : Matrix α r c :=
  Vector.ofFn fun i => Vector.ofFn fun j => f i j

@[simp, grind =]
theorem getElem_ofFn (f : Fin r → Fin c → α) (i j) (hi : i < r) (hj : j < c) :
    (Matrix.ofFn f)[i][j] = f ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [Matrix.ofFn]

@[simp, grind =]
theorem get_ofFn (f : Fin r → Fin c → α) (i j) : ((Matrix.ofFn f).get i).get j = f i j := by
  simp [Matrix.ofFn]

@[inline]
def transpose (m : Matrix α c r) : Matrix α r c :=
  .ofFn fun i j => m[j][i]

@[simp, grind =]
theorem getElem_transpose (m : Matrix α c r) (i j) (hi : i < r) (hj : j < c) :
    m.transpose[i][j] = m[j][i] := by
  simp [transpose]

@[inline]
protected def mulVecWithDot (dot : Vector α c → Vector α c → α)
    (m : Matrix α r c) (v : Vector α c) : Vector α r :=
  .ofFn fun i => dot m[i] v

@[simp, grind =]
theorem getElem_mulVec (m : Matrix α r c) (v : Vector α c) (i) (h : i < r) :
    (m.mulVecWithDot dot v)[i] = dot m[i] v := by
  simp [Matrix.mulVecWithDot]

@[inline]
protected def mulWithDot (dot : Vector α k → Vector α k → α)
    (m : Matrix α r k) (n : Matrix α k c) : Matrix α r c :=
  Matrix.ofFn fun i j => dot (m.row i) (n.col j)

@[inline]
def diag [Zero α] (d : Vector α n) : Matrix α n n :=
  Matrix.ofFn fun i j => if i = j then d[i] else 0

@[simp, grind =]
theorem getElem_diag_ne [Zero α] (d : Vector α n)
    (i j) (h : i ≠ j) (hi : i < n) (hj : j < n) :
    (diag d)[i][j] = 0 := by
  simp [diag, h]

@[simp, grind =]
theorem getElem_diag_eq [Zero α] (d : Vector α n) (i) (hi : i < n) :
    (diag d)[i][i] = d[i] := by
  simp [diag]

theorem getElem_diag [Zero α] (d : Vector α n) (i j) (hi : i < n) (hj : j < n) :
    (diag d)[i][j] = if i = j then d[i] else 0 := by
  simp [diag]

def dot [Std.SemiRing α]
