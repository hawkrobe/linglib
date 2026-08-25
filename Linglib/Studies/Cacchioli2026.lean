import Linglib.Fragments.Tigrinya.Complementizers
import Linglib.Fragments.Tigrinya.Negation
import Linglib.Morphology.Word.Tree

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

Two of the thesis's descriptive generalizations are checked against the
fragment entries: the selection table (which verb classes take *kɛmzɨ-*,
*kɨ-* and *ʔɨlu*), and the distribution of the negative suffix across
clause types, read off the thesis's own negated words built from the
fragment morphs.

## TODO

* State the head placements — PolP above TP above NegP, MoodP below TP —
  against the extended-projection substrate once `fValue` separates Pol,
  T, Neg and Mod (all F2 today).
* Record *ʔɨlu*'s agreement with the matrix subject once `Complementizer`
  carries an agreement axis; the former `agrees` field meant
  clause-internal agreement and had no correct setter.
-/

namespace Cacchioli2026

open Morphology Tigrinya.Complementizers Tigrinya.Negation

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

/-- *ʔɨlu* occurs only where *kɛmzɨ-* does (§3.2.3). -/
theorem kemzi_of_ilu {c : VerbClass} (h : ilu ∈ selects c) : kemzi ∈ selects c := by
  revert h; cases c <;> decide

/-- The two prefixes overlap exactly on fiction and perception verbs. -/
theorem kemzi_and_ki_iff (c : VerbClass) :
    kemzi ∈ selects c ∧ ki ∈ selects c ↔ c = .fiction ∨ c = .perception := by
  cases c <;> decide

/-! ### Sentential negation

The thesis's negated verbs (ch. 5), as word trees over the fragment
morphs. -/

/-- (5b) *ʔaj-ts'awɛt-ɨn* 'I do not play': a root declarative. -/
def rootNegative : Word.Tree Morph := .circumfixed aj (.root (.free "ts'awɛt")) n

/-- (25) *ʔaj-nɨfɨr-ɨn* '(that a chicken) does not fly': an *ʔɨlu*-complement. -/
def iluNegative : Word.Tree Morph := .circumfixed aj (.root (.free "nɨfɨr")) n

/-- (24) *ʔaj-kɨ-bɛlʔɨ-n* 'will not eat': the negative future keeps the
suffix, with *ʔaj-* outside *kɨ-*. -/
def futureNegative : Word.Tree Morph :=
  .circumfixed aj (.prefixed ki.morph (.root (.free "bɛlʔ"))) n

/-- (12a) *z-ɛj-nbɨb* '(the books) that I do not read': a relative clause
takes the prefix alone. -/
def relativeNegative : Word.Tree Morph :=
  .prefixed zi.morph (.prefixed ej (.root (.free "nbɨb")))

/-- (16) *kɛm-z-ɛj-fɛttu* '(what) I do not like': a *kɛmzɨ-*-complement. -/
def complementNegative : Word.Tree Morph :=
  .prefixed kem (.prefixed zi.morph (.prefixed ej (.root (.free "fɛttu"))))

/-- (20) *k-ɛj-bɛki* 'not to cry': a *kɨ-*-clause. -/
def subjunctiveNegative : Word.Tree Morph :=
  .prefixed ki.morph (.prefixed ej (.root (.free "bɛki")))

/-- The suffix *-(ɨ)n* appears in root declaratives, *ʔɨlu*-complements
and the negative future, and in no *zɨ-* or other *kɨ-* clause. -/
theorem suffix_distribution :
    n ∈ rootNegative.toList ∧ n ∈ iluNegative.toList ∧ n ∈ futureNegative.toList ∧
      n ∉ relativeNegative.toList ∧ n ∉ complementNegative.toList ∧
      n ∉ subjunctiveNegative.toList := by
  decide

/-- Only the circumfixed words are non-concatenative; the prefix-only
negatives segment as their morph lists. -/
theorem concatenative_iff_no_suffix :
    ¬ rootNegative.IsConcatenative ∧ ¬ futureNegative.IsConcatenative ∧
      relativeNegative.IsConcatenative ∧ complementNegative.IsConcatenative ∧
      subjunctiveNegative.IsConcatenative :=
  ⟨id, id, trivial, trivial, trivial⟩

example : relativeNegative.toList.map Morph.form = ["zɨ", "ɛj", "nbɨb"] := rfl

example : rootNegative.IsKindCoherent ∧ futureNegative.IsKindCoherent ∧
    relativeNegative.IsKindCoherent ∧ complementNegative.IsKindCoherent ∧
    subjunctiveNegative.IsKindCoherent := by
  decide

end Cacchioli2026
