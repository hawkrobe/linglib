import Linglib.Fragments.Tigrinya.Complementizers
import Linglib.Data.Examples.Cacchioli2026

/-!
# Cacchioli 2026: the clausal prefixes of Tigrinya

Tigrinya is head-final and yet marks its subordinate clauses with prefixes. This file formalizes
the two descriptive generalizations of a thesis arguing that the position is syntactic rather than
a morphological quirk: *zɨ-* is a reflex of successive-cyclic Ā-movement rather than a
complementizer head, *kɛmzɨ-* is *kɛm* plus that reflex, so its complement clauses are relative
clauses with a null nominal moved, *kɨ-* is a subjunctive marker heading a projection below tense,
and *ʔaj-…-(ɨ)n* is split negation whose prefix sits below tense and whose suffix heads a polarity
projection above it.

The first generalization is which verb classes take which clause-typer, the thesis's own summary
table. The second is the distribution of the negative suffix, which appears exactly in the clauses
whose structure reaches the polarity projection — root declaratives, *ʔɨlu*-complements and the
negative future — and is missing wherever the clause is reduced. Both are checked against the
thesis's own examples, and both are attested on each side, so neither check is vacuous.

## Main definitions

* `VerbClass`, `selects` — the verb classes and the clause-typers each admits
* `ClauseKind`, `HasPolP` — the clause types and which of them carry the polarity projection

## Main results

* `kemzi_or_ki`, `kemzi_of_ilu`, `kemzi_and_ki_iff` — the shape of the selection table: every class
  takes one of the two prefixes, *ʔɨlu* occurs only where *kɛmzɨ-* does, and the two prefixes
  overlap on the fiction and perception verbs alone
* `selects_covers_data`, `each_typer_attested` — the table admits every attested pairing, and each
  typer is attested
* `suffix_iff_polP`, `polP_clauses_attested` — the suffix appears exactly in the clauses carrying
  the polarity projection, and every such clause type is attested with it

## References

* [cacchioli-2026]
* [cacchioli-2023]
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

/-- The thesis's verb-class labels. -/
private def parseVerbClass : String → Option VerbClass
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

/-- The thesis's clause-typer labels. -/
private def parseTyper : String → Option Complementizer
  | "kemzi" => some kemzi
  | "ki" => some ki
  | "ilu" => some ilu
  | _ => none

/-- A matrix verb of a given class attested with a given clause-typer. -/
structure SelectionDatum where
  verbClass : VerbClass
  typer : Complementizer
  deriving DecidableEq, Repr

/-- The selection pairing an example records, where it records one. -/
private def selectionDatum (e : LinguisticExample) : Option SelectionDatum := do
  let c ← parseVerbClass (← e.paperFeatures.lookup "verb_class")
  let t ← parseTyper (← e.paperFeatures.lookup "typer")
  some ⟨c, t⟩

/-- The attested (verb class, typer) pairs of the thesis's examples. -/
def selectionData : List SelectionDatum := Examples.all.filterMap selectionDatum

/-- The selection table admits every attested pairing. -/
theorem selects_covers_data : ∀ d ∈ selectionData, d.typer ∈ selects d.verbClass := by
  decide

/-- All three typers are attested, so the coverage check has something to check. -/
theorem each_typer_attested :
    (∃ d ∈ selectionData, d.typer = kemzi) ∧ (∃ d ∈ selectionData, d.typer = ki) ∧
      (∃ d ∈ selectionData, d.typer = ilu) := by decide

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

/-- The thesis's clause-type labels. -/
private def parseClauseKind : String → Option ClauseKind
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

/-- Whether an example is coded as carrying the negative suffix. -/
private def parseSuffix : String → Option Bool
  | "present" => some true
  | "absent" => some false
  | _ => none

/-- A negated clause: its kind and whether the suffix *-(ɨ)n* appears. -/
structure NegationDatum where
  clause : ClauseKind
  suffix : Bool
  deriving DecidableEq, Repr

/-- The negated clause an example records, where it records one. -/
private def negationDatum (e : LinguisticExample) : Option NegationDatum := do
  let c ← parseClauseKind (← e.paperFeatures.lookup "clause")
  let s ← parseSuffix (← e.paperFeatures.lookup "neg_suffix")
  some ⟨c, s⟩

/-- The negated clauses of the thesis's examples. -/
def negationData : List NegationDatum := Examples.all.filterMap negationDatum

/-- The suffix appears exactly in the clauses that carry PolP. -/
theorem suffix_iff_polP : ∀ d ∈ negationData, d.suffix = true ↔ HasPolP d.clause := by
  decide

/-- Every clause type the analysis gives a polarity projection is attested with the suffix, so the
generalization is confirmed on both sides rather than by the absence of counterexamples. -/
theorem polP_clauses_attested :
    ⟨.root, true⟩ ∈ negationData ∧ ⟨.ilu, true⟩ ∈ negationData ∧
      ⟨.future, true⟩ ∈ negationData := by decide

end Cacchioli2026
