/-
# Minimal Exact Fractions

A simple fraction type for exact rational arithmetic.
Comparison uses cross-multiplication, which is decidable.

This avoids needing Mathlib's Rat while giving us exact proofs.
-/

namespace Frac

/-- A fraction with natural number numerator and positive denominator -/
structure Frac where
  num : Nat
  den : Nat
  den_pos : den > 0 := by decide
  deriving Repr

instance : Inhabited Frac := ⟨⟨0, 1, by decide⟩⟩

/-- Create a fraction (denominator must be positive) -/
def mk (n d : Nat) (h : d > 0 := by decide) : Frac := ⟨n, d, h⟩

/-- Fraction from a natural number -/
def ofNat (n : Nat) : Frac := ⟨n, 1, by decide⟩

instance (n : Nat) : OfNat Frac n := ⟨ofNat n⟩

-- ============================================================================
-- Comparison (via cross-multiplication)
-- ============================================================================

/-- a/b < c/d iff a*d < c*b (for positive denominators) -/
def lt (x y : Frac) : Prop := x.num * y.den < y.num * x.den

/-- a/b ≤ c/d iff a*d ≤ c*b -/
def le (x y : Frac) : Prop := x.num * y.den ≤ y.num * x.den

/-- a/b = c/d iff a*d = c*b -/
def eq (x y : Frac) : Prop := x.num * y.den = y.num * x.den

instance : LT Frac := ⟨lt⟩
instance : LE Frac := ⟨le⟩

/-- Decidable less-than (reduces to Nat comparison) -/
instance decLt (x y : Frac) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.num * y.den < y.num * x.den))

/-- Decidable less-equal -/
instance decLe (x y : Frac) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.num * y.den ≤ y.num * x.den))

/-- Decidable equality (by cross-multiplication) -/
instance decEq (x y : Frac) : Decidable (eq x y) :=
  inferInstanceAs (Decidable (x.num * y.den = y.num * x.den))

/-- BEq instance -/
instance : BEq Frac := ⟨fun x y => x.num * y.den == y.num * x.den⟩

-- ============================================================================
-- Arithmetic
-- ============================================================================

/-- Addition: a/b + c/d = (ad + cb) / bd -/
def add (x y : Frac) : Frac :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den,
   Nat.mul_pos x.den_pos y.den_pos⟩

/-- Multiplication: a/b * c/d = ac / bd -/
def mul (x y : Frac) : Frac :=
  ⟨x.num * y.num, x.den * y.den, Nat.mul_pos x.den_pos y.den_pos⟩

/-- Division: (a/b) / (c/d) = ad / bc (requires c > 0) -/
def div (x y : Frac) (h : y.num > 0 := by decide) : Frac :=
  ⟨x.num * y.den, x.den * y.num, Nat.mul_pos x.den_pos h⟩

instance : Add Frac := ⟨add⟩
instance : Mul Frac := ⟨mul⟩

-- ============================================================================
-- Useful constants and helpers
-- ============================================================================

def zero : Frac := ⟨0, 1, by decide⟩
def one : Frac := ⟨1, 1, by decide⟩

/-- Check if fraction is zero -/
def isZero (x : Frac) : Bool := x.num == 0

/-- Check if fraction is positive -/
def isPos (x : Frac) : Bool := x.num > 0

-- ============================================================================
-- Basic properties
-- ============================================================================

theorem lt_iff_cross (x y : Frac) : x < y ↔ x.num * y.den < y.num * x.den := Iff.rfl

theorem le_iff_cross (x y : Frac) : x ≤ y ↔ x.num * y.den ≤ y.num * x.den := Iff.rfl

theorem eq_iff_cross (x y : Frac) : eq x y ↔ x.num * y.den = y.num * x.den := Iff.rfl

-- ============================================================================
-- Display
-- ============================================================================

instance : ToString Frac where
  toString x := if x.den == 1 then s!"{x.num}" else s!"{x.num}/{x.den}"

end Frac
