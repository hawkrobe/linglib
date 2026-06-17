import Linglib.Data.Examples.Schema
import Linglib.Semantics.Tense.Reichenbach
import Linglib.Semantics.Tense.Finset Ordering
import Linglib.Semantics.Tense.Basic
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Data.Examples.Wurmbrand2014

/-!
# [wurmbrand-2014]: Tense and aspect in English infinitives
[wurmbrand-2014]

Wurmbrand (Linguistic Inquiry 45(3), 2014) classifies English infinitival
complements into three types based on tense-aspect behavior:

1. **Future irrealis** (`decide`, `want`, `plan`, `hope`): no independent
   tense; future orientation comes from a woll-like operator selected by
   the matrix verb. Example: "Leo decided to read a book" — reading is
   future of deciding.
2. **Propositional** (`believe`, `claim`): NOW-anchored tense. The
   embedded event is simultaneous with the matrix attitude. Example: "Leo
   believes Julia to be a princess" — princess-status at believing time.
3. **Restructuring** (`try`, `begin`): dependent on matrix tense; embedded
   event in the same temporal domain as the matrix.

## Empirical anchors

- (1a) "Leo decided to read a book." — future irrealis
- (1b) "Leo believes Julia to be a princess." — propositional
- (2a) "Leo decided to bring the toys tomorrow." — future-irrealis +
  episodic adverbial OK
- (2b) "*Leo believed Julia to bring the toys right then." — propositional
  + episodic adverbial blocks bare infinitive (needs progressive)

## Lean encoding

The `InfinitivalTenseClass` type is substrate (`Minimalist.ExtendedProjection`),
shared with `Studies/Ostrove2026`. Wurmbrand's apparatus — temporal orientation,
woll decomposition, episodic predictions, and the verb classification table — is
study-local below; the empirical examples are generated from
`Data/Examples/Wurmbrand2014.json`.

-/

namespace Wurmbrand2014

open Tense
open Tense
open Data.Examples (LinguisticExample)
open Minimalist (InfinitivalTenseClass ComplementSize)

/-! ### Temporal orientation by class -/

/-- The temporal orientation of a complement relative to the matrix event. -/
inductive TemporalOrientation where
  /-- Complement event after the matrix event. -/
  | futureOriented
  /-- Complement event simultaneous with the matrix event. -/
  | simultaneous
  /-- Complement event's temporal location depends entirely on the matrix. -/
  | dependent
  deriving DecidableEq, Repr

/-- Each infinitival class's predicted temporal orientation. -/
def classOrientation : InfinitivalTenseClass → TemporalOrientation
  | .futureIrrealis => .futureOriented
  | .propositional => .simultaneous
  | .restructuring => .dependent

/-! ### Woll decomposition -/

/-- *will* = PRES + *woll*; *would* = PAST + *woll* (§2). The tense component
    undergoes SOT; *woll* supplies the future orientation. -/
structure WollDecomposition where
  /-- The tense component. -/
  tense : Finset Ordering
  /-- Whether *woll* is present (future orientation). -/
  hasWoll : Bool
  deriving DecidableEq, Repr

/-- *will* = present + woll. -/
def will_ : WollDecomposition where
  tense := .present
  hasWoll := true

/-- *would* = past + woll. -/
def would_ : WollDecomposition where
  tense := .past
  hasWoll := true

/-- Plain present (no woll). -/
def plainPresent : WollDecomposition where
  tense := .present
  hasWoll := false

/-- *will* and *would* share the woll component. -/
theorem will_would_share_woll : will_.hasWoll = would_.hasWoll := rfl

/-- *will* and *would* differ only in tense. -/
theorem will_would_tense_differs : will_.tense ≠ would_.tense := nofun

/-- Only future-irrealis infinitives contain the future modal *woll*. -/
def classHasWoll : InfinitivalTenseClass → Bool
  | .futureIrrealis => true
  | .propositional => false
  | .restructuring => false

theorem futureIrrealis_has_woll : classHasWoll .futureIrrealis = true := rfl
theorem propositional_no_woll : classHasWoll .propositional = false := rfl
theorem restructuring_no_woll : classHasWoll .restructuring = false := rfl

/-! ### Episodic interpretation predictions (Table 3) -/

/-- Availability of bare (nonprogressive) episodic interpretations (§4). -/
inductive EpisodicAvailability where
  /-- Possible: *woll* supplies an unrestricted future reference time. -/
  | possible
  /-- Impossible: the attitude holder's NOW is too short for perfective. -/
  | impossible
  /-- Matrix-dependent: possible iff the matrix reference time is large enough. -/
  | matrixDependent
  deriving DecidableEq, Repr

/-- Each class's episodic prediction. -/
def classEpisodicPrediction : InfinitivalTenseClass → EpisodicAvailability
  | .futureIrrealis => .possible
  | .propositional => .impossible
  | .restructuring => .matrixDependent

theorem propositional_no_episodic :
    classEpisodicPrediction .propositional = .impossible := rfl
theorem restructuring_episodic_matrix_dependent :
    classEpisodicPrediction .restructuring = .matrixDependent := rfl
theorem futureIrrealis_episodic_possible :
    classEpisodicPrediction .futureIrrealis = .possible := rfl

/-! ### Verb classification -/

/-- A verb classified by its infinitival tense class (Table 4). -/
structure InfinitivalVerb where
  /-- The verb lemma. -/
  lemma_ : String
  /-- Its tense class. -/
  tenseClass : InfinitivalTenseClass
  deriving Repr

def want : InfinitivalVerb := ⟨"want", .futureIrrealis⟩
def decide : InfinitivalVerb := ⟨"decide", .futureIrrealis⟩
def plan : InfinitivalVerb := ⟨"plan", .futureIrrealis⟩
def promise : InfinitivalVerb := ⟨"promise", .futureIrrealis⟩
def believe : InfinitivalVerb := ⟨"believe", .propositional⟩
def claim : InfinitivalVerb := ⟨"claim", .propositional⟩
def try_ : InfinitivalVerb := ⟨"try", .restructuring⟩
def begin_ : InfinitivalVerb := ⟨"begin", .restructuring⟩
def manage : InfinitivalVerb := ⟨"manage", .restructuring⟩

/-- A verb ambiguous between two infinitival tense classes. -/
structure AmbiguousVerb where
  lemma_ : String
  readings : List InfinitivalTenseClass
  deriving Repr

/-- *expect* is ambiguous between future-irrealis and propositional (§3, §4.3). -/
def expect : AmbiguousVerb := ⟨"expect", [.futureIrrealis, .propositional]⟩

/-- *seem* is restructuring, but propositional with an experiencer (§4.4). -/
def seem : AmbiguousVerb := ⟨"seem", [.restructuring, .propositional]⟩

theorem expect_is_ambiguous : expect.readings.length > 1 := by decide
theorem seem_is_ambiguous : seem.readings.length > 1 := by decide

/-! ### Per-class classification theorems -/

/-- `want` is future-irrealis → future-oriented complement. -/
theorem wurmbrandClassifiesWant :
    want.tenseClass = .futureIrrealis ∧
    classOrientation .futureIrrealis = .futureOriented := ⟨rfl, rfl⟩

/-- `believe` is propositional → simultaneous complement. -/
theorem wurmbrandClassifiesBelieve :
    believe.tenseClass = .propositional ∧
    classOrientation .propositional = .simultaneous := ⟨rfl, rfl⟩

/-- `try` is restructuring → dependent on matrix temporal domain. -/
theorem wurmbrandClassifiesTry :
    try_.tenseClass = .restructuring ∧
    classOrientation .restructuring = .dependent := ⟨rfl, rfl⟩

/-! ### Derivation theorems -/

theorem futureIrrealis_is_future_oriented :
    classOrientation .futureIrrealis = .futureOriented := rfl
theorem propositional_now_anchored :
    classOrientation .propositional = .simultaneous := rfl
theorem restructuring_dependent :
    classOrientation .restructuring = .dependent := rfl

/-- Propositional NOW-anchoring connects to the attitude eval-time shift:
    `standardShift` sets the embedded eval time to the matrix event time. -/
theorem propositional_uses_attitude_eval_time :
    classOrientation .propositional = .simultaneous ∧
    (standardShift (Time := ℕ)).shiftEvalTime
      { speechTime := 0, perspectiveTime := 0, referenceTime := 0, eventTime := 5 } = 5 :=
  ⟨rfl, rfl⟩

/-- Restructuring infinitives lack independent tense: `dependent` orientation,
    the smallest complement size (`vP`), and no woll. -/
theorem restructuring_minimal_structure :
    classOrientation .restructuring = .dependent ∧
    InfinitivalTenseClass.toComplementSize .restructuring = .vP ∧
    classHasWoll .restructuring = false :=
  ⟨rfl, rfl, rfl⟩

/-- Future-oriented complements have woll and project a modal (wollP ≈ ModP). -/
theorem futureIrrealis_structural_future :
    classHasWoll .futureIrrealis = true ∧
    InfinitivalTenseClass.toComplementSize .futureIrrealis = .modP ∧
    classOrientation .futureIrrealis = .futureOriented :=
  ⟨rfl, rfl, rfl⟩

/-- Woll presence correlates exactly with future orientation. -/
theorem woll_iff_future :
    ∀ c : InfinitivalTenseClass,
      classHasWoll c = true ↔ classOrientation c = .futureOriented := by
  intro c; cases c <;> simp [classHasWoll, classOrientation]

/-! ### Complement-size hierarchy

Wurmbrand's theory-internal sizing is `wollP > TP > vP/AspP`. The substrate
`InfinitivalTenseClass.toComplementSize` maps future-irrealis and propositional
to the same fseq tier (ModP/TP), so the strict ordering is recorded here via a
study-local rank. -/

/-- Wurmbrand's complement-size rank: future-irrealis > propositional > restructuring. -/
def sizeRank : InfinitivalTenseClass → Nat
  | .futureIrrealis => 3
  | .propositional => 2
  | .restructuring => 1

theorem complement_size_hierarchy :
    sizeRank .futureIrrealis > sizeRank .propositional ∧
    sizeRank .propositional > sizeRank .restructuring := by decide

/-- Episodic availability tracks complement size: complements with their own
    temporal elements allow episodic readings; smaller ones are matrix-dependent. -/
theorem episodic_correlates_with_size :
    classEpisodicPrediction .futureIrrealis = .possible ∧
    InfinitivalTenseClass.toComplementSize .futureIrrealis = .modP ∧
    classEpisodicPrediction .propositional = .impossible ∧
    InfinitivalTenseClass.toComplementSize .propositional = .tP ∧
    classEpisodicPrediction .restructuring = .matrixDependent ∧
    InfinitivalTenseClass.toComplementSize .restructuring = .vP :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Wurmbrand2014
