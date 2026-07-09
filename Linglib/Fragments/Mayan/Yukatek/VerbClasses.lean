import Linglib.Semantics.Aspect.Basic
import Linglib.Semantics.ArgumentStructure.EventStructure
import Linglib.Semantics.Verb.Root.SalienceClass
import Linglib.Fragments.Mayan.Params
import Linglib.Features.Case.Basic
import Linglib.Syntax.Case.Alignment
/-!
# Yukatek Maya Verb Classes and Status System

Yukatek Maya has a typologically rare split-intransitive pattern of
argument marking controlled by overt aspect-mood marking
([bohnemeyer-2004]; [lucy-1994]). The system comprises five verb stem
classes distinguished by status inflection patterns (allomorphy of
aspect-mood suffixes) and four status categories encoding viewpoint aspect
and modal assertiveness. The split in argument marking tracks the aspectual
value: perfective status marks S like U (ergative), imperfective status
marks S like A (accusative).

## Main declarations

* `Yukatek.VerbStemClass`: the five stem classes, with `eventType`,
  `isIntransitive`, `toTemplate` (R&H templates), and `toSalienceClass`
  ([lucy-1994]'s 4-way cut).
* `Yukatek.StatusCategory`: the four status categories, with
  `viewpointAspect` and `isAssertive`.
* `Yukatek.sArgumentMarker`: which marker set cross-references the
  intransitive subject, given the status category.
* `Yukatek.yukatekSplit`: the aspect-conditioned split as an
  `Alignment.SplitErgativity`, shared with Hindi and Georgian.

## Implementation notes

Verb stem classes ([bohnemeyer-2004] Table 3; [lucy-1994]):

| Class | Event type | Examples |
|-------|-----------|----------|
| active | process | walk, sing, dance, sneeze |
| inactive | state change | die, burst, enter, exit |
| inchoative | state change (stative root + *-tal*) | blacken, shrink, sink |
| positional | state change (spatial config.) | sit, stand, hang, be round |
| transitive active | transitive | hit, chip, eat |

Status marking encodes both viewpoint aspect and modal assertiveness
([bohnemeyer-2004] Table 2):

- **completive**: +perfective, +assertive → ergative (S = U)
- **subjunctive**: +perfective, −assertive → ergative (S = U)
- **incompletive**: −perfective, +assertive → accusative (S = A)
- **imperative**: directive mood
-/

namespace Yukatek

open Verb
open Semantics.Aspect (ViewpointAspectB)
open ArgumentStructure.EventStructure (EventType InternalExternalCause)
open Mayan (MarkerSet)

/-! ### Verb stem classes -/

/-- The five verb stem classes of Yukatek Maya, distinguished by
    status inflection patterns ([bohnemeyer-2004] Table 3;
    [lucy-1994]). -/
inductive VerbStemClass where
  | active           -- activity roots: walk, sing, dance, sneeze
  | inactive         -- state-change roots: die, burst, enter, exit
  | inchoative       -- stative root + *-tal*: blacken, shrink, sink
  | positional       -- spatial configurations: sit, stand, hang
  | transitiveActive -- transitive roots: hit, chip, eat
  deriving DecidableEq, Repr

/-- Event type per verb stem class: active stems encode processes, all
    others state changes. Per [bohnemeyer-2004] §5, atelic degree
    achievements still fall in the inactive and inchoative classes — class
    membership tracks the process vs state-change distinction, not
    telicity. -/
def VerbStemClass.eventType : VerbStemClass → EventType
  | .active => .process
  | .inactive => .stateChange
  | .inchoative => .stateChange
  | .positional => .stateChange
  | .transitiveActive => .stateChange

/-- Whether a verb stem class is intransitive. -/
def VerbStemClass.isIntransitive : VerbStemClass → Bool
  | .transitiveActive => false
  | _ => true

/-! ### Status categories -/

/-- The four status categories of Yukatek Maya, encoding viewpoint
    aspect and modal assertiveness ([bohnemeyer-2004] Table 2). -/
inductive StatusCategory where
  | completive    -- +assertive, +perfective
  | subjunctive   -- −assertive, +perfective
  | incompletive  -- +assertive, −perfective
  | imperative    -- directive mood
  deriving DecidableEq, Repr

/-- Aspectual value of a status category (the imperative has none). -/
def StatusCategory.viewpointAspect : StatusCategory → Option ViewpointAspectB
  | .completive => some .perfective
  | .subjunctive => some .perfective
  | .incompletive => some .imperfective
  | .imperative => none

/-- Whether the status category is assertive (modal component). -/
def StatusCategory.isAssertive : StatusCategory → Bool
  | .completive => true
  | .incompletive => true
  | _ => false

/-! ### Argument marking pattern -/

/-- Which marker set cross-references the sole argument (S) of an
    intransitive verb, given the status category ([bohnemeyer-2004]
    Table 2). Perfective status gives set-B (ergative, S = U), imperfective
    set-A (accusative, S = A); the imperative is omitted from Table 2's
    split analysis. -/
def sArgumentMarker : StatusCategory → Option MarkerSet
  | .completive => some .setB    -- ergative: S patterns with U
  | .subjunctive => some .setB   -- ergative: S patterns with U
  | .incompletive => some .setA  -- accusative: S patterns with A
  | .imperative => none          -- not part of the aspect-governed split

/-- The split: perfective → set-B (ergative), imperfective → set-A (accusative). -/
theorem perfective_ergative :
    sArgumentMarker .completive = some .setB ∧
    sArgumentMarker .subjunctive = some .setB := ⟨rfl, rfl⟩

theorem imperfective_accusative :
    sArgumentMarker .incompletive = some .setA := rfl

/-! ### Representative verb entries -/

/-- A Yukatek verb entry for the split-intransitivity analysis: stem class
    and causation type of the intransitive base. -/
structure YukatekVerb where
  gloss : String
  stemClass : VerbStemClass
  causationType : InternalExternalCause
  deriving BEq, Repr

-- Active verbs (internally caused processes)
def meyah : YukatekVerb := ⟨"work", .active, .internal⟩
def baaxal : YukatekVerb := ⟨"play", .active, .internal⟩

-- Active verbs (externally caused processes — manner of motion / emission)
def balak : YukatekVerb := ⟨"roll", .active, .external⟩
def peek : YukatekVerb := ⟨"move/wiggle", .active, .external⟩
def tsiirin : YukatekVerb := ⟨"buzz", .active, .external⟩

-- Inactive verbs (state changes, externally caused)
def kim : YukatekVerb := ⟨"die", .inactive, .external⟩
def luub : YukatekVerb := ⟨"fall", .inactive, .external⟩

-- Inchoative verbs (state changes from stative roots)
def booxTal : YukatekVerb := ⟨"blacken", .inchoative, .external⟩
def chichanTal : YukatekVerb := ⟨"shrink", .inchoative, .external⟩

-- Degree achievements — inactive/inchoative class despite atelic behavior
def kaan : YukatekVerb := ⟨"get tired", .inactive, .external⟩
def naak : YukatekVerb := ⟨"ascend", .inactive, .external⟩

-- Positional verbs (externally caused spatial configurations)
def kulTal : YukatekVerb := ⟨"sit down", .positional, .external⟩
def waalTal : YukatekVerb := ⟨"stand up", .positional, .external⟩

-- Key exception: inactive stem class but internally caused → applicative
-- [bohnemeyer-2004] ex. (9): hàan-t-ik (applicative -t, not causative -s).
-- Low-tone `hàan` "eat" — distinct from high-tone `háan` "stop, cease,
-- heal" in `Roots.haanCease`, which is patient-salient (Lucy's diagnostic).
def haanEat : YukatekVerb := ⟨"eat", .inactive, .internal⟩

-- Active verbs (externally caused: manner of motion)
def chiik : YukatekVerb := ⟨"shake", .active, .external⟩
def haarax : YukatekVerb := ⟨"slide", .active, .external⟩
def huuy : YukatekVerb := ⟨"stir", .active, .external⟩
def mosoon : YukatekVerb := ⟨"whirl", .active, .external⟩
def pirik : YukatekVerb := ⟨"flick", .active, .external⟩
def walak : YukatekVerb := ⟨"turn/revolve", .active, .external⟩

-- Active verbs (externally caused: sound emission)
def nikich : YukatekVerb := ⟨"squeak", .active, .external⟩

-- Positional verbs (additional)
def chilTal : YukatekVerb := ⟨"lie down", .positional, .external⟩
def xolTal : YukatekVerb := ⟨"kneel", .positional, .external⟩

-- Degree achievements (additional, inactive class but atelic)
def lab : YukatekVerb := ⟨"deteriorate", .inactive, .external⟩
def tiil : YukatekVerb := ⟨"last/drag on", .inactive, .external⟩
def tsuuk : YukatekVerb := ⟨"rot", .inactive, .external⟩

-- Transitive active
def haats : YukatekVerb := ⟨"hit", .transitiveActive, .internal⟩

/-! ### Event-structure templates -/

open ArgumentStructure.EventStructure (Template)

/-- Yukatek verb stem classes to R&H event-structure templates
    (`EventStructure.lean`): active → activity [x ACT], inactive and
    inchoative → achievement [BECOME [x ⟨STATE⟩]], positional → achievement
    (externally-caused spatial config.), transitive active →
    accomplishment [[x ACT] CAUSE [BECOME [y ⟨STATE⟩]]]. -/
def VerbStemClass.toTemplate : VerbStemClass → Template
  | .active => .activity
  | .inactive => .achievement
  | .inchoative => .achievement
  | .positional => .achievement
  | .transitiveActive => .accomplishment

/-- The stem class → template mapping preserves event type:
    `VerbStemClass.eventType` agrees with `Template.eventType ∘ toTemplate`. -/
theorem eventType_consistent (c : VerbStemClass) :
    c.eventType = c.toTemplate.eventType := by
  cases c <;> rfl

/-! ### Salience classes ([lucy-1994]) -/

/-- Map [bohnemeyer-2004]'s 5-way Yukatek stem classification to
    [lucy-1994]'s 4-way salience cut. The 5-way is a refinement:
    `inchoative` and `positional` both pattern as Lucy's `positional`
    (both derive via `-tal` from a stative root); `active`/`inactive`/
    `transitiveActive` map straightforwardly to `agent`/`patient`/
    `agentPatient`. -/
def VerbStemClass.toSalienceClass : VerbStemClass → SalienceClass
  | .active           => .agent
  | .inactive         => .patient
  | .inchoative       => .positional
  | .positional       => .positional
  | .transitiveActive => .agentPatient

/-- Bohnemeyer's 5-way stem classes refining Lucy's positional class:
    `inchoative` and `positional` both reduce to the same Lucy class. -/
theorem inchoative_positional_collapse_under_lucy :
    VerbStemClass.toSalienceClass .inchoative =
      VerbStemClass.toSalienceClass .positional := rfl

/-- The other three Bohnemeyer classes are mutually distinct under
    Lucy's salience cut (they map to three different `SalienceClass`
    values). -/
theorem active_inactive_transitive_distinct :
    VerbStemClass.toSalienceClass .active ≠
      VerbStemClass.toSalienceClass .inactive ∧
    VerbStemClass.toSalienceClass .active ≠
      VerbStemClass.toSalienceClass .transitiveActive ∧
    VerbStemClass.toSalienceClass .inactive ≠
      VerbStemClass.toSalienceClass .transitiveActive := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- `toSalienceClass` is surjective: every Lucy class is in the image of
    Bohnemeyer's 5-way refinement. -/
theorem toSalienceClass_surjective :
    ∀ c : SalienceClass, ∃ s : VerbStemClass, s.toSalienceClass = c
  | .agent        => ⟨.active,           rfl⟩
  | .agentPatient => ⟨.transitiveActive, rfl⟩
  | .patient      => ⟨.inactive,         rfl⟩
  | .positional   => ⟨.positional,       rfl⟩

/-- The fibre of `toSalienceClass` over `.positional` is exactly
    `{.inchoative, .positional}` — these are the two Bohnemeyer classes
    that collapse under [lucy-1994]'s 4-way cut. The other three
    fibres are singletons (`active ↦ agent`, `inactive ↦ patient`,
    `transitiveActive ↦ agentPatient`). -/
theorem toSalienceClass_fiber_positional (s : VerbStemClass) :
    s.toSalienceClass = .positional ↔ s = .inchoative ∨ s = .positional := by
  cases s <;> simp [VerbStemClass.toSalienceClass]

/-- The other three fibres are singletons. -/
theorem toSalienceClass_fiber_agent (s : VerbStemClass) :
    s.toSalienceClass = .agent ↔ s = .active := by
  cases s <;> simp [VerbStemClass.toSalienceClass]

theorem toSalienceClass_fiber_patient (s : VerbStemClass) :
    s.toSalienceClass = .patient ↔ s = .inactive := by
  cases s <;> simp [VerbStemClass.toSalienceClass]

theorem toSalienceClass_fiber_agentPatient (s : VerbStemClass) :
    s.toSalienceClass = .agentPatient ↔ s = .transitiveActive := by
  cases s <;> simp [VerbStemClass.toSalienceClass]

/-! ### Split-ergative system -/

/-- Yukatek split-ergative system, parameterized by status category:
    perfective status (completive/subjunctive) triggers ergative alignment,
    imperfective (incompletive) accusative; the imperative defaults to
    ergative. Instantiates the same `Alignment.SplitErgativity` used by
    Hindi and Georgian. -/
def yukatekSplit : Alignment.SplitErgativity StatusCategory :=
  { ergCondition := λ s => match s.viewpointAspect with
      | some .perfective => true
      | some .imperfective => false
      | none => true }  -- imperative: ergative-like default

theorem yukatek_completive_erg :
    yukatekSplit.alignment .completive = .ergative := rfl

theorem yukatek_subjunctive_erg :
    yukatekSplit.alignment .subjunctive = .ergative := rfl

theorem yukatek_incompletive_acc :
    yukatekSplit.alignment .incompletive = .accusative := rfl

/-- Yukatek and Hindi share the same split conditioning: perfective → ergative,
    imperfective → accusative. This is [bohnemeyer-2004]'s core insight
    that a single linking-by-viewpoint mechanism underlies both systems. -/
theorem yukatek_hindi_same_split :
    yukatekSplit.alignment .completive = Alignment.hindiSplit.alignment .perfective ∧
    yukatekSplit.alignment .incompletive = Alignment.hindiSplit.alignment .imperfective :=
  ⟨rfl, rfl⟩

end Yukatek
