import Linglib.Theories.Semantics.Lexical.Noun.Kind.Generics
import Linglib.Core.Genericity

/-!
# @cite{krifka-2013}: Definitional Generics

Manfred Krifka, "Definitional Generics", ch. 15 of
*Genericity* (eds. Mari, Beyssade, Del Prete), Oxford University Press, 2013.

## Main Contribution

Krifka distinguishes two fundamentally different types of generic statement:

1. **Descriptive generics** ("Dogs bark"): empirical generalizations about
   patterns in the world. These restrict the set of possible *worlds*.
2. **Definitional generics** ("A madrigal is polyphonic"): statements that
   restrict the *interpretation* of linguistic expressions. These restrict
   the set of admissible *interpretations*.

## Two-Index Semantics

The key formal innovation is splitting the traditional evaluation index
into two components:

- **i** (interpretation index): how expressions are interpreted
- **w** (world index): what the world is like

A common ground is a pair ⟨I, W⟩ where I is the set of admissible
interpretations and W is the set of possible worlds.

## Update Operations

- **DES(⟦Φ⟧)**: descriptive update — restricts worlds, keeps interpretations
  ⟨I, W⟩ + DES(⟦Φ⟧) = ⟨I, {w∈W | ∃i∈I. ⟦Φ⟧^{i,w}}⟩

- **DEF(⟦Φ⟧)**: definitional update — restricts interpretations, keeps worlds
  ⟨I, W⟩ + DEF(⟦Φ⟧) = ⟨{i∈I | ∀w∈W. ⟦Φ⟧^{i,w}}, W⟩

## Connection to GEN Eliminability

The `gen_eliminable` theorem in `Comparisons/GenericSemantics.lean` applies
only to descriptive generics. Definitional generics cannot be reduced to
prevalence thresholds because they operate on the interpretation index.
-/

namespace Phenomena.Generics.Studies.Krifka2013

-- Two-Index Semantics

/-- An interpretation index: determines how expressions are interpreted. -/
structure Interp where
  id : Nat
  deriving DecidableEq, Repr, BEq

/-- A world index: determines what factual state of affairs obtains. -/
structure World where
  id : Nat
  deriving DecidableEq, Repr, BEq

/-- A denotation under two indices: maps an interpretation and world to a truth value. -/
abbrev Denotation := Interp → World → Bool

/-- A common ground: a set of admissible interpretations paired with
    a set of possible worlds. -/
structure CommonGround where
  interps : List Interp
  worlds : List World
  deriving Repr

-- Update Operations

/-- **DES** (Descriptive update): restricts worlds, keeps interpretations.

    ⟨I, W⟩ + DES(⟦Φ⟧) = ⟨I, {w∈W | ∃i∈I. ⟦Φ⟧^{i,w}}⟩

    Descriptive assertions inform about the world under some admissible
    interpretation. We keep all interpretations but restrict to worlds
    where the proposition holds under at least one interpretation. -/
def des (cg : CommonGround) (φ : Denotation) : CommonGround where
  interps := cg.interps
  worlds := cg.worlds.filter λ w => cg.interps.any λ i => φ i w

/-- **DEF** (Definitional update): restricts interpretations, keeps worlds.

    ⟨I, W⟩ + DEF(⟦Φ⟧) = ⟨{i∈I | ∀w∈W. ⟦Φ⟧^{i,w}}, W⟩

    Definitional assertions restrict the language: only interpretations
    under which the proposition holds in ALL worlds survive. -/
def def_ (cg : CommonGround) (φ : Denotation) : CommonGround where
  interps := cg.interps.filter λ i => cg.worlds.all λ w => φ i w
  worlds := cg.worlds

-- Key Properties

/-- DES preserves interpretations. -/
theorem des_preserves_interps (cg : CommonGround) (φ : Denotation) :
    (des cg φ).interps = cg.interps := rfl

/-- DEF preserves worlds. -/
theorem def_preserves_worlds (cg : CommonGround) (φ : Denotation) :
    (def_ cg φ).worlds = cg.worlds := rfl

/-- DES restricts worlds (result is a subset). -/
theorem des_restricts_worlds (cg : CommonGround) (φ : Denotation) :
    ∀ w, w ∈ (des cg φ).worlds → w ∈ cg.worlds :=
  λ _ hw => (List.mem_filter.mp hw).1

/-- DEF restricts interpretations (result is a subset). -/
theorem def_restricts_interps (cg : CommonGround) (φ : Denotation) :
    ∀ i, i ∈ (def_ cg φ).interps → i ∈ cg.interps :=
  λ _ hi => (List.mem_filter.mp hi).1

-- Rule Types (discussed in Krifka 2013)

/-- Types of rules that definitional generics can express. -/
inductive RuleType where
  | physical    -- "An electron has a negative electric charge"
  | moral       -- "A gentleman opens doors for ladies"
  | legal       -- "A bishop moves diagonally" (in chess)
  | linguistic  -- "A madrigal is polyphonic"
  deriving DecidableEq, Repr, BEq

-- Madrigal Example (Krifka's running example)

/-- Three interpretations of "madrigal" varying in strictness. -/
def i₁ : Interp := ⟨1⟩  -- Strict: only polyphonic pieces
def i₂ : Interp := ⟨2⟩  -- Medium: mostly polyphonic
def i₃ : Interp := ⟨3⟩  -- Loose: includes monophonic pieces

/-- Three possible worlds. -/
def w₁ : World := ⟨1⟩  -- Madrigals generally popular
def w₂ : World := ⟨2⟩  -- Madrigals generally popular
def w₃ : World := ⟨3⟩  -- Madrigals not popular

/-- Initial common ground: all interpretations, all worlds. -/
def cg₀ : CommonGround :=
  { interps := [i₁, i₂, i₃]
  , worlds := [w₁, w₂, w₃] }

/-- "Madrigals are popular" — a descriptive claim.
    True in w₁ and w₂ under all interpretations, false in w₃. -/
def madrigalsPopular : Denotation := λ _i w =>
  match w.id with
  | 1 | 2 => true
  | _ => false

/-- "Madrigals are polyphonic" — true under i₁ and i₂ (in all worlds),
    false under i₃. -/
def madrigalsPolyphonic : Denotation := λ i _w =>
  match i.id with
  | 1 | 2 => true
  | _ => false

-- Descriptive update: "Madrigals are popular" restricts worlds

/-- After DES("Madrigals are popular"), w₃ is eliminated. -/
theorem des_popular_eliminates_w3 :
    (des cg₀ madrigalsPopular).worlds = [w₁, w₂] := by native_decide

/-- DES preserves all three interpretations. -/
theorem des_popular_keeps_interps :
    (des cg₀ madrigalsPopular).interps = [i₁, i₂, i₃] := rfl

-- Definitional update: "Madrigals are polyphonic" restricts interpretations

/-- After DEF("Madrigals are polyphonic"), i₃ is eliminated. -/
theorem def_polyphonic_eliminates_i3 :
    (def_ cg₀ madrigalsPolyphonic).interps = [i₁, i₂] := by native_decide

/-- DEF preserves all three worlds. -/
theorem def_polyphonic_keeps_worlds :
    (def_ cg₀ madrigalsPolyphonic).worlds = [w₁, w₂, w₃] := rfl

-- The Key Distinction: DES and DEF are independent operations

/-- DES and DEF affect orthogonal components of the common ground. -/
theorem des_def_orthogonal :
    let cg1 := des cg₀ madrigalsPopular
    let cg2 := def_ cg1 madrigalsPolyphonic
    -- After both updates: 2 interpretations, 2 worlds
    cg2.interps = [i₁, i₂] ∧ cg2.worlds = [w₁, w₂] := by
  constructor <;> native_decide

-- Connection to GEN eliminability

/-- Definitional generics cannot be reduced to prevalence thresholds because
    they operate on interpretations, not worlds. A prevalence measure counts
    situations/worlds where the property holds, but a definitional generic
    restricts which interpretations are admissible — a categorically different
    operation. -/
theorem def_not_world_reducible :
    -- DEF doesn't change worlds at all
    (def_ cg₀ madrigalsPolyphonic).worlds = cg₀.worlds ∧
    -- But it does change interpretations
    (def_ cg₀ madrigalsPolyphonic).interps ≠ cg₀.interps := by
  constructor
  · rfl
  · native_decide

-- DEF-escapes-threshold bridge

/-- Any function of worlds alone is invariant under DEF, because DEF only
    changes interpretations. Since threshold semantics measures world-prevalence,
    it cannot capture definitional generics that change truth value through DEF. -/
theorem def_invariant_world_measure {α : Type} (cg : CommonGround) (φ : Denotation)
    (f : List World → α) :
    f (def_ cg φ).worlds = f cg.worlds := by
  rw [def_preserves_worlds]

-- IS-Generic vs BP-Generic Correlation

open Core.Genericity (GenericForm GenericReading)

/-- Krifka's observation: IS-generics have a clear tendency toward
    definitional interpretation. -/
structure GenericDatum where
  sentence : String
  subjectForm : GenericForm
  preferredReading : GenericReading
  ruleType : Option RuleType
  notes : String := ""
  deriving Repr

def madrigalPolyphonicIS : GenericDatum :=
  { sentence := "A madrigal is polyphonic"
  , subjectForm := .indefiniteSingular
  , preferredReading := .definitional
  , ruleType := some .linguistic
  , notes := "Restricts the interpretation of 'madrigal'" }

def madrigalPopularBP : GenericDatum :=
  { sentence := "Madrigals are popular"
  , subjectForm := .barePlural
  , preferredReading := .descriptive
  , ruleType := none
  , notes := "Empirical generalization about madrigals in the world" }

def electronChargeIS : GenericDatum :=
  { sentence := "An electron has a negative electric charge"
  , subjectForm := .indefiniteSingular
  , preferredReading := .definitional
  , ruleType := some .physical }

def gentlemanDoorsIS : GenericDatum :=
  { sentence := "A gentleman opens doors for ladies"
  , subjectForm := .indefiniteSingular
  , preferredReading := .definitional
  , ruleType := some .moral }

def bishopDiagonalIS : GenericDatum :=
  { sentence := "A bishop moves diagonally"
  , subjectForm := .indefiniteSingular
  , preferredReading := .definitional
  , ruleType := some .legal
  , notes := "Legal rule in chess" }

def donkeyChromosomesIS : GenericDatum :=
  { sentence := "A donkey has 62 chromosomes"
  , subjectForm := .indefiniteSingular
  , preferredReading := .definitional
  , ruleType := some .physical
  , notes := "Empirical discovery becomes a defining property of the kind" }

def dogsBarkBP : GenericDatum :=
  { sentence := "Dogs bark"
  , subjectForm := .barePlural
  , preferredReading := .descriptive
  , ruleType := none }

def exampleData : List GenericDatum :=
  [ madrigalPolyphonicIS, madrigalPopularBP, electronChargeIS
  , gentlemanDoorsIS, bishopDiagonalIS, donkeyChromosomesIS, dogsBarkBP ]

end Phenomena.Generics.Studies.Krifka2013
