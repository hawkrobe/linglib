import Linglib.Theories.Semantics.Tense.Aspect.Core
import Linglib.Theories.Semantics.Lexical.Verb.EventStructure
import Linglib.Phenomena.Ergativity.Basic

/-!
# Yukatek Maya Verb Classes and Status System

@cite{bohnemeyer-2004} @cite{lucy-1994}

Yukatek Maya has a typologically rare split-intransitive pattern of
argument marking controlled by overt aspect-mood marking. The system
comprises five verb stem classes distinguished by their status
inflection patterns (allomorphy of aspect-mood suffixes).

## Verb Stem Classes

| Class | Event type | Examples |
|-------|-----------|----------|
| active | process | walk, sing, dance, sneeze |
| inactive | state change | die, burst, enter, exit |
| inchoative | state change (stative root + *-tal*) | blacken, shrink, sink |
| positional | state change (spatial config.) | sit, stand, hang, be round |
| transitive active | transitive | hit, chip, eat |

## Status Categories

Status marking encodes both viewpoint aspect and modal assertiveness
(@cite{bohnemeyer-2004} Table 2):

- **completive**: +perfective, +assertive → ergative (S = U)
- **subjunctive**: +perfective, −assertive → ergative (S = U)
- **incompletive**: −perfective, +assertive → accusative (S = A)
- **imperative**: directive mood

The split in argument marking is associated with the aspectual value:
perfective status → S marked like U (ergative); imperfective status →
S marked like A (accusative).
-/

namespace Fragments.Mayan.Yukatek

open Semantics.Tense.Aspect.Core (ViewpointAspectB)
open Semantics.Lexical.Verb.EventStructure (EventType CausationType)
open Phenomena.Ergativity (MarkerSet)

-- ════════════════════════════════════════════════════
-- § 1. Verb Stem Classes
-- ════════════════════════════════════════════════════

/-- The five verb stem classes of Yukatek Maya, distinguished by
    status inflection patterns (@cite{bohnemeyer-2004} Table 3;
    @cite{lucy-1994}). -/
inductive VerbStemClass where
  | active           -- activity roots: walk, sing, dance, sneeze
  | inactive         -- state-change roots: die, burst, enter, exit
  | inchoative       -- stative root + *-tal*: blacken, shrink, sink
  | positional       -- spatial configurations: sit, stand, hang
  | transitiveActive -- transitive roots: hit, chip, eat
  deriving DecidableEq, BEq, Repr

/-- Event type encoded by each verb stem class.
    Active stems encode processes; all others encode state changes.

    @cite{bohnemeyer-2004} §5: degree achievement verbs regularly appear
    in the inactive and inchoative classes despite being atelic. Their
    event structure encodes state change — the process/state-change
    distinction, not telicity, motivates class membership. -/
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

-- ════════════════════════════════════════════════════
-- § 2. Status Categories
-- ════════════════════════════════════════════════════

/-- The four status categories of Yukatek Maya, encoding viewpoint
    aspect and modal assertiveness (@cite{bohnemeyer-2004} Table 2). -/
inductive StatusCategory where
  | completive    -- +assertive, +perfective
  | subjunctive   -- −assertive, +perfective
  | incompletive  -- +assertive, −perfective
  | imperative    -- directive mood
  deriving DecidableEq, BEq, Repr

/-- Aspectual value of a status category.
    Completive and subjunctive are perfective; incompletive is
    imperfective. Imperative has no clear aspectual value. -/
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

-- ════════════════════════════════════════════════════
-- § 3. Argument Marking Pattern
-- ════════════════════════════════════════════════════

/-- Which marker set cross-references the sole argument (S) of an
    intransitive verb, given the status category.

    @cite{bohnemeyer-2004} Table 2:
    - Perfective status (completive/subjunctive): S = U → set-B (ergative)
    - Imperfective status (incompletive): S = A → set-A (accusative)
    - Imperative: not discussed in the split analysis (Table 2 omits it) -/
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

-- ════════════════════════════════════════════════════
-- § 4. Representative Verb Entries
-- ════════════════════════════════════════════════════

/-- A Yukatek verb entry for the split intransitivity analysis.
    Records stem class and causation type of the intransitive base. -/
structure YukatekVerb where
  gloss : String
  stemClass : VerbStemClass
  causationType : CausationType
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
-- @cite{bohnemeyer-2004} ex. (9): hàan-t-ik (applicative -t, not causative -s)
def haan : YukatekVerb := ⟨"eat", .inactive, .internal⟩

-- Transitive active
def haats : YukatekVerb := ⟨"hit", .transitiveActive, .internal⟩

-- ════════════════════════════════════════════════════
-- § 5. Bridge to Event Structure Templates
-- ════════════════════════════════════════════════════

open Semantics.Lexical.Verb.EventStructure (Template)

/-- Map Yukatek verb stem classes to R&H event structure templates.
    This connects the language-specific classification to the
    theory-level decomposition in `EventStructure.lean`.

    - Active → activity [x ACT]
    - Inactive/inchoative → achievement [BECOME [x ⟨STATE⟩]]
    - Positional → achievement (externally-caused spatial config.)
    - Transitive active → accomplishment [[x ACT] CAUSE [BECOME [y ⟨STATE⟩]]] -/
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

end Fragments.Mayan.Yukatek
