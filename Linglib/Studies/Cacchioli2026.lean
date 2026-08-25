import Linglib.Fragments.Tigrinya.Complementizers
import Linglib.Data.Examples.Cacchioli2026

/-!
# [cacchioli-2026] — The Syntax of Clausal Prefixes in Tigrinya

[cacchioli-2026] argues that Tigrinya's clause-initial prefixes owe their
position to syntax, not to a morphological property of prefixes in a
head-final language. *zɨ-* is a reflex of successive-cyclic Ā-movement —
Spec-Head agreement in a phasal aspectual projection — rather than a
complementizer head (the zɨP heads of [cacchioli-2023] are withdrawn).
*kɛmzɨ-* is *kɛm* + *zɨ-*, so its complement clauses are relative clauses
with a null nominal Ā-moved. *kɨ-* is a subjunctive marker heading a MoodP
below TP in reduced, temporally dependent clauses. *ʔaj-…-(ɨ)n* is split
negation: *ʔaj-* heads NegP below TP and *-(ɨ)n* heads PolP above it,
which is why the suffix is missing wherever the clause lacks the higher
layer.

Two of the thesis's descriptive generalizations are checked against its
own examples (`Cacchioli2026.Examples`): the selection table (which verb
classes take *kɛmzɨ-*, *kɨ-* and *ʔɨlu*) and the distribution of the
negative suffix across clause types.

## TODO

* State the head placements — PolP above TP above NegP, MoodP below TP —
  against the extended-projection substrate once `fValue` separates Pol,
  T, Neg and Mod (all F2 today).
* Record *ʔɨlu*'s agreement with the matrix subject once `Complementizer`
  carries an agreement axis; the former `agrees` field meant
  clause-internal agreement and had no correct setter.
-/

namespace Cacchioli2026

open Data.Examples Tigrinya.Complementizers

/-! ### Selection -/

/-- The verb classes of the thesis's selection table (ch. 6). -/
inductive VerbClass where
  | factive | cognitiveNonFactive | fiction | utterance | perception
  | directive | desire | modal | emotiveFactive | control | ecm
  deriving DecidableEq, Fintype, Repr

/-- The clause-typers a class's complement may take. -/
def selects : VerbClass → List Complementizer
  | .factive => [kemzi]
  | .cognitiveNonFactive | .utterance => [kemzi, ilu]
  | .fiction => [kemzi, ki, ilu]
  | .perception => [kemzi, ki]
  | .directive | .desire | .modal | .emotiveFactive | .control | .ecm => [ki]

/-- Every class takes one of the two prefixal typers. -/
theorem kemzi_or_ki (c : VerbClass) : kemzi ∈ selects c ∨ ki ∈ selects c := by
  cases c <;> decide

/-- *ʔɨlu* occurs only where *kɛmzɨ-* does. -/
theorem kemzi_of_ilu {c : VerbClass} (h : ilu ∈ selects c) : kemzi ∈ selects c := by
  revert h; cases c <;> decide

/-- The two prefixes overlap exactly on fiction and perception verbs. -/
theorem kemzi_and_ki_iff (c : VerbClass) :
    kemzi ∈ selects c ∧ ki ∈ selects c ↔ c = .fiction ∨ c = .perception := by
  cases c <;> decide

def parseVerbClass : String → Option VerbClass
  | "factive" => some .factive
  | "cognitive_non_factive" => some .cognitiveNonFactive
  | "fiction" => some .fiction
  | "utterance" => some .utterance
  | "perception" => some .perception
  | "directive" => some .directive
  | "desire" => some .desire
  | "modal" => some .modal
  | "emotive_factive" => some .emotiveFactive
  | "control" => some .control
  | "ecm" => some .ecm
  | _ => none

def parseTyper : String → Option Complementizer
  | "kemzi" => some kemzi
  | "ki" => some ki
  | "ilu" => some ilu
  | _ => none

/-- A matrix verb of a given class attested with a given clause-typer. -/
structure SelectionDatum where
  verbClass : VerbClass
  typer : Complementizer
  deriving DecidableEq, Repr

def selectionDatum (e : LinguisticExample) : Option SelectionDatum := do
  let c ← parseVerbClass (← e.paperFeatures.lookup "verb_class")
  let t ← parseTyper (← e.paperFeatures.lookup "typer")
  some ⟨c, t⟩

/-- The attested (verb class, typer) pairs of the thesis's examples. -/
def selectionData : List SelectionDatum := Examples.all.filterMap selectionDatum

/-- The selection table admits every attested pairing. -/
theorem selects_covers_data : ∀ d ∈ selectionData, d.typer ∈ selects d.verbClass := by
  decide

/-! ### Sentential negation -/

/-- The clause types in which the thesis negates a verb (ch. 5). -/
inductive ClauseKind where
  | root | ilu | future | relative | seem | conditional | complement | subjunctive | purpose
  deriving DecidableEq, Repr

/-- Clauses carrying the PolP layer that hosts *-(ɨ)n*: root declaratives,
*ʔɨlu*-complements and the negative future. -/
def HasPolP : ClauseKind → Prop
  | .root | .ilu | .future => True
  | _ => False

instance : DecidablePred HasPolP
  | .root | .ilu | .future => isTrue trivial
  | .relative | .seem | .conditional | .complement | .subjunctive | .purpose => isFalse id

def parseClauseKind : String → Option ClauseKind
  | "root" => some .root
  | "ilu" => some .ilu
  | "future" => some .future
  | "relative" => some .relative
  | "seem" => some .seem
  | "conditional" => some .conditional
  | "complement" => some .complement
  | "subjunctive" => some .subjunctive
  | "purpose" => some .purpose
  | _ => none

def parseSuffix : String → Option Bool
  | "present" => some true
  | "absent" => some false
  | _ => none

/-- A negated clause: its kind and whether the suffix *-(ɨ)n* appears. -/
structure NegationDatum where
  clause : ClauseKind
  suffix : Bool
  deriving DecidableEq, Repr

def negationDatum (e : LinguisticExample) : Option NegationDatum := do
  let c ← parseClauseKind (← e.paperFeatures.lookup "clause")
  let s ← parseSuffix (← e.paperFeatures.lookup "neg_suffix")
  some ⟨c, s⟩

/-- The negated clauses of the thesis's examples. -/
def negationData : List NegationDatum := Examples.all.filterMap negationDatum

/-- The suffix appears exactly in the clauses that carry PolP. -/
theorem suffix_iff_polP : ∀ d ∈ negationData, d.suffix = true ↔ HasPolP d.clause := by
  decide

end Cacchioli2026
