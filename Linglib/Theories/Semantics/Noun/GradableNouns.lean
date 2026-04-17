import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Linglib.Core.Scales.Scale

/-!
# Gradable Nouns as Measure Functions

@cite{morzycki-2009} @cite{kennedy-mcnally-2005}

Gradable nouns denote measure functions from individuals to degrees (eq. 48b):
⟦idiot⟧ = λx . ιd[x is d-idiotic] = *idiot*.

Size adjectives in degree readings are introduced by MEAS_N (eq. 76),
the nominal counterpart of the adjectival MEAS morpheme. The Bigness
Generalization (§2.2) follows from scale structure: min{d : small(d)} = d₀,
making "small" vacuous.

**Simplification**: Our `measN` omits the `d ∈ scale(g)` restriction from
Morzycki's full MEAS_N (eq. 76), since all examples here use a single shared
degree scale. The full denotation is:
  ⟦MEAS_N⟧ = λg.λm.λx . [min{d : d ∈ scale(g) ∧ m(d)} ≤ g(x)] ∧ [standard(g) ≤ g(x)]
-/

namespace Semantics.Noun.GradableNouns

open Core.Scale

/-- Degree on a 0–10 scale, backed by the canonical `Degree 10` type. -/
abbrev Degree := Core.Scale.Degree 10

/-- All degrees on the 0–10 scale. -/
def allDegrees : List Degree := Core.Scale.allDegrees 10

/-- d0 is the minimum degree (from BoundedOrder). -/
theorem d0_is_minimum : ∀ d : Degree, deg 0 ≤ d := λ d => bot_le (a := d)


/-- A gradable noun maps individuals to degrees: ⟦idiot⟧ = λx.ιd[x is d-idiotic]. -/
structure GradableNoun (Entity : Type) where
  name : String
  /-- The measure function: entity -> degree. -/
  measure : Entity → Degree
  /-- The contextual standard for this predicate. -/
  standard : Degree

/-- Apply POS to a gradable noun: λx. standard(g) < g(x).

Uses strict inequality, matching `positiveMeaning` in `Degree.Core`:
an entity satisfies POS(N) iff its degree *exceeds* the standard
(@cite{kennedy-2007}). -/
def GradableNoun.pos {E : Type} (n : GradableNoun E) : E → Bool :=
  λ x => n.standard < n.measure x


/-- Size adjectives characterized by polarity (big vs small). -/
inductive SizePolarity where
  | big    -- measures bigness (positive)
  | small  -- measures smallness (negative/inverted)
  deriving Repr, DecidableEq

/-- Big: maps degrees to their "bigness" (identity on the degree scale). -/
def bigness (d : Degree) : Degree := d

/-- Small: inverted ordering (0 maximally small, 10 minimally small). -/
def smallness (d : Degree) : Degree :=
  Core.Scale.Degree.ofNat 10 (10 - d.toNat)

/-- Standard for "big" (contextual, typically middling). -/
def bigStandard : Degree := deg 5

/-- Standard for "small" (contextual). -/
def smallStandard : Degree := deg 5

/-- POS applied to size adjective: λd. standard(size) ≤ size(d). -/
def posBig (d : Degree) : Bool := bigStandard ≤ bigness d
def posSmall (d : Degree) : Bool := smallStandard ≤ smallness d


section MEASN

/-- Find minimum degree satisfying a predicate. -/
def minDegree (p : Degree → Bool) : Option Degree :=
  allDegrees.find? p

/-- Simplified MEAS_N: ⟦MEAS_N⟧(g)(m)(x) = [min{d : m(d)} ≤ g(x)] ∧ [standard(g) ≤ g(x)].
    Full version (Morzycki eq. 76) has min over {d : d ∈ scale(g) ∧ m(d)}. -/
def measN {E : Type}
    (noun : GradableNoun E)
    (sizeAdj : Degree → Bool)  -- The [POS size-adj] predicate on degrees
    : E → Bool :=
  λ x =>
    match minDegree sizeAdj with
    | none => false
    | some minD => minD ≤ noun.measure x ∧ noun.standard < noun.measure x


/-- Example: an "idiot" gradable noun with standard at d3. -/
def idiotNoun {E : Type} (measure : E → Degree) : GradableNoun E :=
  { name := "idiot"
  , measure := measure
  , standard := deg 3
  }

/-- "big idiot" = MEASN(idiot)(POS big). -/
def bigIdiot {E : Type} (noun : GradableNoun E) : E → Bool :=
  measN noun posBig

/-- "small idiot" = MEASN(idiot)(POS small). -/
def smallIdiot {E : Type} (noun : GradableNoun E) : E → Bool :=
  measN noun posSmall


/-- Minimum degree satisfying "big" is d5. -/
theorem min_big_is_d5 : minDegree posBig = some (deg 5) := by native_decide

/-- Minimum degree satisfying "small" is d0 (the scale minimum). -/
theorem min_small_is_d0 : minDegree posSmall = some (deg 0) := by native_decide

/-- d0 always satisfies smallness because it is maximally small. -/
theorem d0_satisfies_small : posSmall (deg 0) = true := by native_decide

/-- d0 is the unique minimum for smallness. -/
theorem d0_is_min_for_small : ∀ d : Degree, posSmall d → deg 0 ≤ d := by
  intro d _
  exact d0_is_minimum d

end MEASN

section BigGeneralization

/-- "small idiot" is equivalent to just "idiot" (size adj is vacuous). -/
theorem small_idiot_vacuous {E : Type} (noun : GradableNoun E) (x : E) :
    smallIdiot noun x = noun.pos x := by
  simp only [smallIdiot, measN, min_small_is_d0]
  simp only [GradableNoun.pos]
  -- deg 0 ≤ noun.measure x is always true
  have h : deg 0 ≤ noun.measure x := d0_is_minimum _
  simp only [h, true_and]

/-- "big idiot" is more restrictive than just "idiot". -/
theorem big_idiot_restrictive {E : Type} (noun : GradableNoun E)
    (_h : noun.standard < deg 5) :
    ∀ x, bigIdiot noun x → noun.pos x := by
  intro x hbig
  simp only [bigIdiot, measN, min_big_is_d5, GradableNoun.pos] at *
  simp only [decide_eq_true_eq] at *
  exact hbig.2


end BigGeneralization

section Examples

/-- A simple entity type for examples. -/
inductive Person where
  | george | sarah | floyd
  deriving Repr, DecidableEq

/-- George: d8, Sarah: d4, Floyd: d1. -/
def idiocyMeasure : Person → Degree
  | .george => deg 8
  | .sarah => deg 4
  | .floyd => deg 1

def exampleIdiot : GradableNoun Person := idiotNoun idiocyMeasure

/-- George is an idiot. -/
theorem george_is_idiot : exampleIdiot.pos .george = true := by native_decide

/-- George is a big idiot. -/
theorem george_is_big_idiot : bigIdiot exampleIdiot .george = true := by native_decide

/-- Sarah is an idiot but not a big idiot. -/
theorem sarah_is_idiot_not_big :
    exampleIdiot.pos .sarah = true ∧ bigIdiot exampleIdiot .sarah = false := by
  constructor <;> native_decide

/-- "Small idiot" gives same result as "idiot" (vacuous). -/
theorem small_idiot_same_as_idiot :
    smallIdiot exampleIdiot .george = exampleIdiot.pos .george ∧
    smallIdiot exampleIdiot .sarah = exampleIdiot.pos .sarah ∧
    smallIdiot exampleIdiot .floyd = exampleIdiot.pos .floyd := by
  constructor
  · rw [small_idiot_vacuous]
  constructor
  · rw [small_idiot_vacuous]
  · rw [small_idiot_vacuous]


end Examples

end Semantics.Noun.GradableNouns
