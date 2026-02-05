/-
Gradable nouns as measure functions with degree arguments (Morzycki 2009).

Size adjectives in degree readings use MEASN; the Bigness Generalization
follows from scale structure (min{d : small(d)} = d0, making "small" vacuous).

- Morzycki (2009). Degree modification of gradable nouns. NLS 17:175-203.
- Kennedy & McNally (2005). Scale structure, degree modification. Language 81(2).
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

namespace Montague.Noun.GradableNouns


/-- A degree on a scale (discretized). -/
inductive Degree where
  | d0 | d1 | d2 | d3 | d4 | d5 | d6 | d7 | d8 | d9 | d10
  deriving Repr, DecidableEq, BEq, Ord

def Degree.toNat : Degree → Nat
  | .d0 => 0 | .d1 => 1 | .d2 => 2 | .d3 => 3 | .d4 => 4
  | .d5 => 5 | .d6 => 6 | .d7 => 7 | .d8 => 8 | .d9 => 9 | .d10 => 10

instance : LE Degree where
  le d1 d2 := d1.toNat ≤ d2.toNat

instance : LT Degree where
  lt d1 d2 := d1.toNat < d2.toNat

instance : DecidableRel (α := Degree) (· ≤ ·) :=
  λ d1 d2 => inferInstanceAs (Decidable (d1.toNat ≤ d2.toNat))

instance : DecidableRel (α := Degree) (· < ·) :=
  λ d1 d2 => inferInstanceAs (Decidable (d1.toNat < d2.toNat))

def allDegrees : List Degree := [.d0, .d1, .d2, .d3, .d4, .d5, .d6, .d7, .d8, .d9, .d10]

/-- d0 is the minimum degree. -/
theorem d0_is_minimum : ∀ d : Degree, Degree.d0 ≤ d := by
  intro d; cases d <;> decide


/-- A gradable noun maps individuals to degrees: ⟦idiot⟧ = λx.ιd[x is d-idiotic]. -/
structure GradableNoun (Entity : Type) where
  name : String
  /-- The measure function: entity -> degree. -/
  measure : Entity → Degree
  /-- The contextual standard for this predicate. -/
  standard : Degree

/-- Apply POS to a gradable noun: λx. standard(g) ≤ g(x). -/
def GradableNoun.pos {E : Type} (n : GradableNoun E) : E → Bool :=
  λ x => n.standard ≤ n.measure x


/-- Size adjectives characterized by polarity (big vs small). -/
inductive SizePolarity where
  | big    -- measures bigness (positive)
  | small  -- measures smallness (negative/inverted)
  deriving Repr, DecidableEq, BEq

/-- Big: maps degrees to their "bigness" (identity on the degree scale). -/
def bigness (d : Degree) : Degree := d

/-- Small: inverted ordering (d0 maximally small, d10 minimally small). -/
def smallness (d : Degree) : Degree :=
  match d with
  | .d0 => .d10 | .d1 => .d9 | .d2 => .d8 | .d3 => .d7 | .d4 => .d6
  | .d5 => .d5 | .d6 => .d4 | .d7 => .d3 | .d8 => .d2 | .d9 => .d1 | .d10 => .d0

/-- Standard for "big" (contextual, typically middling). -/
def bigStandard : Degree := .d5

/-- Standard for "small" (contextual). -/
def smallStandard : Degree := .d5

/-- POS applied to size adjective: λd. standard(size) ≤ size(d). -/
def posBig (d : Degree) : Bool := bigStandard ≤ bigness d
def posSmall (d : Degree) : Bool := smallStandard ≤ smallness d


section MEASN

/-- Find minimum degree satisfying a predicate. -/
def minDegree (p : Degree → Bool) : Option Degree :=
  allDegrees.find? p

/-- ⟦MEASN⟧ = λg.λm.λx. [min{d : m(d)} ≤ g(x)] ∧ [standard(g) ≤ g(x)]. -/
def measN {E : Type}
    (noun : GradableNoun E)
    (sizeAdj : Degree → Bool)  -- The [POS size-adj] predicate on degrees
    : E → Bool :=
  λ x =>
    match minDegree sizeAdj with
    | none => false
    | some minD => minD ≤ noun.measure x ∧ noun.standard ≤ noun.measure x


/-- Example: an "idiot" gradable noun with standard at d3. -/
def idiotNoun {E : Type} (measure : E → Degree) : GradableNoun E :=
  { name := "idiot"
  , measure := measure
  , standard := .d3
  }

/-- "big idiot" = MEASN(idiot)(POS big). -/
def bigIdiot {E : Type} (noun : GradableNoun E) : E → Bool :=
  measN noun posBig

/-- "small idiot" = MEASN(idiot)(POS small). -/
def smallIdiot {E : Type} (noun : GradableNoun E) : E → Bool :=
  measN noun posSmall


/-- Minimum degree satisfying "big" is d5. -/
theorem min_big_is_d5 : minDegree posBig = some .d5 := by native_decide

/-- Minimum degree satisfying "small" is d0 (the scale minimum). -/
theorem min_small_is_d0 : minDegree posSmall = some .d0 := by native_decide

/-- d0 always satisfies smallness because it is maximally small. -/
theorem d0_satisfies_small : posSmall .d0 = true := by native_decide

/-- d0 is the unique minimum for smallness. -/
theorem d0_is_min_for_small : ∀ d : Degree, posSmall d → .d0 ≤ d := by
  intro d _
  exact d0_is_minimum d

end MEASN

section BigGeneralization

/-- "small idiot" is equivalent to just "idiot" (size adj is vacuous). -/
theorem small_idiot_vacuous {E : Type} (noun : GradableNoun E) (x : E) :
    smallIdiot noun x = noun.pos x := by
  simp only [smallIdiot, measN, min_small_is_d0]
  simp only [GradableNoun.pos]
  -- d0 ≤ noun.measure x is always true
  have h : Degree.d0 ≤ noun.measure x := d0_is_minimum _
  simp only [h, true_and]

/-- "big idiot" is more restrictive than just "idiot". -/
theorem big_idiot_restrictive {E : Type} (noun : GradableNoun E)
    (h : noun.standard < .d5) :
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
  deriving Repr, DecidableEq, BEq

/-- George: d8, Sarah: d4, Floyd: d1. -/
def idiocyMeasure : Person → Degree
  | .george => .d8
  | .sarah => .d4
  | .floyd => .d1

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

section ThresholdPattern

/-- Abstract threshold predicate unifying adjectives, generics, and gradable nouns. -/
structure ThresholdPredicate (Entity : Type) where
  /-- Name of the predicate. -/
  name : String
  /-- Measure function: entity -> degree. -/
  measure : Entity → Degree
  /-- The threshold degree. -/
  threshold : Degree

/-- Threshold predicate semantics: true iff measure(x) >= threshold. -/
def ThresholdPredicate.apply {E : Type} (p : ThresholdPredicate E) (x : E) : Bool :=
  p.threshold ≤ p.measure x

/-- "big idiot" as a threshold predicate with theta = d5. -/
def bigIdiotAsThreshold {E : Type} (measure : E → Degree) : ThresholdPredicate E :=
  { name := "big idiot"
  , measure := measure
  , threshold := .d5
  }

/-- bigIdiot = threshold predicate with theta = d5 (when standard <= d5). -/
theorem bigIdiot_is_threshold_example :
    bigIdiot exampleIdiot .george = (bigIdiotAsThreshold idiocyMeasure).apply .george ∧
    bigIdiot exampleIdiot .sarah = (bigIdiotAsThreshold idiocyMeasure).apply .sarah ∧
    bigIdiot exampleIdiot .floyd = (bigIdiotAsThreshold idiocyMeasure).apply .floyd := by
  constructor <;> [native_decide; constructor <;> native_decide]

end ThresholdPattern

end Montague.Noun.GradableNouns
