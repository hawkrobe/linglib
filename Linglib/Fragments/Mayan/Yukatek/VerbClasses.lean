module

public import Linglib.Semantics.Aspect.Defs
public import Linglib.Semantics.ArgumentStructure.EventStructure
public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Case.Alignment
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
  `isIntransitive`, and `toTemplate` (R&H templates).
* `Yukatek.StatusCategory`: the four status categories, with
  `viewpointAspect` and `isAssertive`.
* `Yukatek.sArgumentMarker`: which marker set cross-references the
  intransitive subject, given the status category.
* `Yukatek.alignment`: the alignment each status category imposes.

## Implementation notes

Verb stem classes ([bohnemeyer-2004] Table 3):

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

@[expose] public section

namespace Yukatek

open Aspect (Perfectivity)
open ArgumentStructure.EventStructure (EventType InternalExternalCause)
open Mayan (MarkerSet)

/-! ### Verb stem classes -/

/-- The five verb stem classes of Yukatek Maya, distinguished by
    status inflection patterns ([bohnemeyer-2004] Table 3). -/
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
def StatusCategory.viewpointAspect : StatusCategory → Option Perfectivity
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

/-! ### Split-ergative system -/

/-- The alignment a status category imposes: ergative under perfective status, the
completive and the subjunctive, accusative under the imperfective incompletive, and ergative
by default in the imperative ([bohnemeyer-2004]). -/
def alignment (s : StatusCategory) : Alignment.AlignmentType :=
  match s.viewpointAspect with
  | some .imperfective => .accusative
  | some .perfective | none => .ergative

end Yukatek
