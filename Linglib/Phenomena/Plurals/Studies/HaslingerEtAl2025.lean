/-
# @cite{haslinger-etal-2025}: Distributivity ≠ Maximality

Empirical data from "On the relation between distributivity and maximality"
(Semantics & Pragmatics 18, Article 1, doi:10.3765/sp.18.1).

## Main Finding

German *jeweils* is obligatorily distributive but permits non-maximal
interpretations for some speakers, while *jeder* requires maximality.
This demonstrates that distributivity and maximality are independent.

## Theoretical Connection

The theory in `Theories/Semantics/Lexical/Plural/Distributivity.lean` predicts:
- *jeder* uses `distMaximal` (identity tolerance)
- *jeweils* uses `distTolerant` (context-sensitive tolerance)
- *alle* universally binds the tolerance parameter (`allViaForallH`)

The atom-vacuity theorem (`distMaximal_singleton`) explains WHY `each`/`jeder`
forces maximality: when P is distributed to atoms, there's no plurality for
tolerance to weaken.

## Connection to Imprecision

@cite{haslinger-2025-diss} argues that non-maximality (= imprecision in the plural
domain) is an "unmarked default" that functional items like `all`/`each` can remove.
The tolerance relation ≤ is the formal locus: predicates introduce it by default,
`all` binds it universally, `each` renders it vacuous on atoms, and `jeweils`
preserves it at the operator level. See `Phenomena/Imprecision/Basic.lean`.

-/

import Linglib.Theories.Semantics.Lexical.Plural.Distributivity
import Linglib.Theories.Semantics.Lexical.Plural.CandidateInterpretation

namespace HaslingerEtAl2025

open Semantics.Lexical.Plural.Distributivity

-- German Distributive Lexical Items

/-- Syntactic distribution of a distributive element -/
inductive SyntacticUse where
  | dpInternal   -- "jeder Hund" (every dog)
  | distance     -- "Die Hunde haben jeweils/jeder..."
  deriving DecidableEq, Repr

/-- A German distributive item with its properties -/
structure LexicalItem where
  form : String
  gloss : String
  uses : List SyntacticUse
  semanticClass : DistMaxClass
  deriving Repr

/-- jeder (DP-internal and distance): +distributive, +maximal -/
def jeder : LexicalItem :=
  { form := "jeder"
  , gloss := "every/each"
  , uses := [.dpInternal, .distance]
  , semanticClass := .distMax }

/-- jeweils (distance only): +distributive, -maximal -/
def jeweils : LexicalItem :=
  { form := "jeweils"
  , gloss := "each/respectively"
  , uses := [.distance]  -- No DP-internal use!
  , semanticClass := .distNonMax }

/-- alle (DP-internal): -distributive, +maximal -/
def alle : LexicalItem :=
  { form := "alle"
  , gloss := "all"
  , uses := [.dpInternal]
  , semanticClass := .nonDistMax }

/-- Definite plurals: -distributive, -maximal -/
def definitePlural : LexicalItem :=
  { form := "die NPs"
  , gloss := "the NPs"
  , uses := [.dpInternal]
  , semanticClass := .nonDistNonMax }

-- Experimental Data (Section 3)

/-- Context for testing non-maximality (QUD makes exceptions irrelevant) -/
structure NonMaxContext where
  description : String
  totalItems : Nat
  exceptions : Nat
  implicitQUD : String
  deriving Repr

/-- Magnets scenario (example 23): 5 boxes, 4 have 2 magnets, 1 has 1 -/
def magnetsContext : NonMaxContext :=
  { description := "Magnets that shouldn't be stored together"
  , totalItems := 5
  , exceptions := 1
  , implicitQUD := "Is there explosion risk?" }

/-- Volunteers scenario (example 24): 5 volunteers, 4 have 2 dogs, 1 has 1 -/
def volunteersContext : NonMaxContext :=
  { description := "Attack dogs that shouldn't be walked together"
  , totalItems := 5
  , exceptions := 1
  , implicitQUD := "Is there a dog fight risk?" }

/-- Experimental observation -/
structure Observation where
  item : LexicalItem
  context : NonMaxContext
  /-- Qualitative acceptance pattern from Figures 1-2 -/
  pattern : String
  deriving Repr

/-- DP-jeder overwhelmingly rejected in non-maximal contexts (Figure 1) -/
def dpJederInNonMax : Observation :=
  { item := jeder
  , context := magnetsContext
  , pattern := "overwhelmingly rejected (modal rating 1)" }

/-- jeweils shows mixed judgments across speakers (Figure 1) -/
def jeweilsInNonMax : Observation :=
  { item := jeweils
  , context := magnetsContext
  , pattern := "mixed: some speakers accept, some reject (bimodal distribution)" }

/-- Distance jeder mostly rejected, less categorically than DP-jeder (Figure 2) -/
def distanceJederInNonMax : Observation :=
  { item := { jeder with uses := [.distance] }
  , context := volunteersContext
  , pattern := "mostly rejected but less categorically than DP-jeder" }

-- Key Empirical Generalizations

/-- The independence claim: same distributivity, different maximality -/
theorem independence_attested :
    jeder.semanticClass.isDistributive = jeweils.semanticClass.isDistributive ∧
    jeder.semanticClass ≠ jeweils.semanticClass := by
  constructor <;> native_decide

/-- Correlation (Section 4): No DP use ↔ permits non-maximality? -/
def hasDPUse (item : LexicalItem) : Bool :=
  item.uses.contains .dpInternal

-- jeder has DP use and requires maximality
example : hasDPUse jeder = true := rfl
example : jeder.semanticClass = .distMax := rfl

-- jeweils lacks DP use and permits non-maximality
example : hasDPUse jeweils = false := rfl
example : jeweils.semanticClass = .distNonMax := rfl

/-- The typological table (5) from the paper, extended with jeweils -/
def typologyTable : List (String × DistMaxClass) :=
  [ ("definite DP",      .nonDistNonMax)
  , ("alle",             .nonDistMax)
  , ("numeral indef",    .nonDistMax)
  , ("jeder (DP)",       .distMax)
  , ("jeder (distance)", .distMax)
  , ("jeweils",          .distNonMax)   -- KEY: +dist, -max
  ]

/-- All four cells of the 2×2 are populated -/
theorem all_four_cells_populated :
    (∃ e ∈ typologyTable, e.2 = .distMax) ∧
    (∃ e ∈ typologyTable, e.2 = .distNonMax) ∧
    (∃ e ∈ typologyTable, e.2 = .nonDistMax) ∧
    (∃ e ∈ typologyTable, e.2 = .nonDistNonMax) :=
  ⟨⟨("jeder (DP)", .distMax), by simp [typologyTable], rfl⟩,
   ⟨("jeweils", .distNonMax), by simp [typologyTable], rfl⟩,
   ⟨("alle", .nonDistMax), by simp [typologyTable], rfl⟩,
   ⟨("definite DP", .nonDistNonMax), by simp [typologyTable], rfl⟩⟩

-- ============================================================================
-- Finite Model: Magnets Scenario (Section 3, example 23)
-- ============================================================================

/-! Demonstrate the jeder/jeweils contrast on a concrete model.

5 boxes, predicate "contains two magnets":
- Boxes 1-4: contain 2 magnets (satisfy P)
- Box 5: contains 1 magnet (exception)

QUD: "Is there explosion risk?" — any box with 2 magnets is dangerous,
so the exception in box 5 is irrelevant.

- `distMaximal` rejects: not all boxes have 2 magnets
- `distTolerant` with a tolerance that accepts 4/5 sub-plurality: accepts -/

section MagnetsModel

inductive Box where | b1 | b2 | b3 | b4 | b5
  deriving DecidableEq, Repr

instance : Fintype Box where
  elems := {.b1, .b2, .b3, .b4, .b5}
  complete := by intro x; cases x <;> simp

/-- World with 4 of 5 boxes containing 2 magnets -/
inductive MWorld where | actual
  deriving DecidableEq, Repr

instance : Fintype MWorld where
  elems := {.actual}
  complete := by intro x; cases x; simp

/-- "This box contains two magnets" -/
def hasTwoMagnets : Box → MWorld → Bool
  | .b1, _ => true
  | .b2, _ => true
  | .b3, _ => true
  | .b4, _ => true
  | .b5, _ => false  -- exception: only 1 magnet

def allBoxes : Finset Box := Finset.univ

/-- jeder rejects: not all boxes have 2 magnets -/
theorem jeder_rejects_magnets :
    distMaximal hasTwoMagnets allBoxes .actual = false := by native_decide

/-- jeweils accepts: there exists a sub-plurality where all boxes have 2 magnets.
    We use full tolerance (any subset is tolerant) — the 4-box subset {b1,b2,b3,b4}
    witnesses truth because all four satisfy `hasTwoMagnets`. -/
theorem jeweils_accepts_magnets :
    distTolerant hasTwoMagnets Tolerance.full allBoxes .actual = true := by
  native_decide

/-- The atom-vacuity principle in action: distributing to individual boxes,
    maximality follows because each singleton has no room for tolerance. -/
theorem each_box_maximal (b : Box) :
    distMaximal hasTwoMagnets {b} .actual = hasTwoMagnets b .actual :=
  distMaximal_singleton hasTwoMagnets b .actual

end MagnetsModel

end HaslingerEtAl2025
