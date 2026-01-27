/-
# Core/QUD.lean

QUD (Question Under Discussion) infrastructure for semantics and pragmatics.

## Key Concept

A QUD partitions the meaning space into equivalence classes. Two meanings are
equivalent under a QUD if they "answer the question the same way."

This is general semantics machinery used in:
- Information structure (Roberts 2012)
- RSA pragmatic models (Kao et al. 2014)
- Focus semantics
- Discourse coherence

## Example

For meaning space `Price × Affect`:
- QUD "price": (p1, a1) ≡ (p2, a2) iff p1 = p2
- QUD "affect": (p1, a1) ≡ (p2, a2) iff a1 = a2
- QUD "both": (p1, a1) ≡ (p2, a2) iff p1 = p2 ∧ a1 = a2

## References

- Roberts (2012). Information structure in discourse.
- Kao et al. (2014). Nonliteral understanding of number words. PNAS.
-/

-- ============================================================================
-- QUD: Question Under Discussion
-- ============================================================================

/--
A QUD (Question Under Discussion) partitions the meaning space.

Two meanings are equivalent under a QUD if they "answer the question the same way."
Speakers optimize informativity only within equivalence classes.
-/
structure QUD (M : Type) where
  /-- Are two meanings equivalent under this QUD? -/
  sameAnswer : M → M → Bool
  /-- Name for display/debugging -/
  name : String := ""

namespace QUD

variable {M : Type} [BEq M]

/-- The identity QUD: speaker wants to convey exact meaning -/
def exact : QUD M where
  sameAnswer m1 m2 := m1 == m2
  name := "exact"

/-- Trivial QUD: all meanings are equivalent (speaker doesn't care about this dimension) -/
def trivial : QUD M where
  sameAnswer _ _ := true
  name := "trivial"

/-- Build QUD from a projection function -/
def ofProject {A : Type} [BEq A] (f : M → A) (name : String := "") : QUD M where
  sameAnswer m1 m2 := f m1 == f m2
  name := name

/-- Compose two QUDs: equivalent iff equivalent under both -/
def compose (q1 q2 : QUD M) : QUD M where
  sameAnswer m1 m2 := q1.sameAnswer m1 m2 && q2.sameAnswer m1 m2
  name := s!"{q1.name}∧{q2.name}"

instance : Mul (QUD M) where
  mul := compose

end QUD

-- ============================================================================
-- Product QUDs: Common pattern for multi-dimensional meaning spaces
-- ============================================================================

-- For product meaning spaces M = A × B, common QUD patterns:
-- - Project to first component (care about A only)
-- - Project to second component (care about B only)
-- - Identity (care about both)

namespace ProductQUD

variable {A B : Type} [BEq A] [BEq B]

/-- QUD that cares only about first component -/
def fst : QUD (A × B) :=
  QUD.ofProject Prod.fst "fst"

/-- QUD that cares only about second component -/
def snd : QUD (A × B) :=
  QUD.ofProject Prod.snd "snd"

/-- QUD that cares about both components (exact) -/
def both : QUD (A × B) :=
  QUD.exact (M := A × B)

end ProductQUD

-- ============================================================================
-- Precision Projections: For approximate communication
-- ============================================================================

/--
Precision projection for numeric meanings.

Allows modeling "approximate" vs "exact" communication:
- Exact: speaker cares about precise value
- Approximate: speaker cares about rounded value

Used in Kao et al. (2014) to model pragmatic halo effect.
-/
structure PrecisionProjection (N : Type) where
  /-- Round/approximate the value -/
  round : N → N
  /-- Name -/
  name : String := ""

namespace PrecisionProjection

/-- Exact precision: no rounding -/
def exact {N : Type} : PrecisionProjection N where
  round := id
  name := "exact"

/-- Round to nearest multiple of k -/
def roundTo (k : Nat) : PrecisionProjection Nat where
  round n := (n / k) * k
  name := s!"round{k}"

/-- Compose precision with a QUD -/
def applyToQUD {M N : Type} [BEq N]
    (prec : PrecisionProjection N) (proj : M → N) : QUD M where
  sameAnswer m1 m2 := prec.round (proj m1) == prec.round (proj m2)
  name := prec.name

end PrecisionProjection
