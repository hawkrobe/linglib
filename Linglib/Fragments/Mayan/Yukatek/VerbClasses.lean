import Linglib.Theories.Semantics.Tense.Aspect.Core
import Linglib.Theories.Semantics.Verb.EventStructure
import Linglib.Theories.Semantics.Verb.Roots.SalienceClass
import Linglib.Fragments.Mayan.Params
import Linglib.Core.Case

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
open Semantics.Verb.EventStructure (EventType CausationType)
open Fragments.Mayan (MarkerSet)

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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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
-- @cite{bohnemeyer-2004} ex. (9): hàan-t-ik (applicative -t, not causative -s).
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

-- ════════════════════════════════════════════════════
-- § 5. Bridge to Event Structure Templates
-- ════════════════════════════════════════════════════

open Semantics.Verb.EventStructure (Template)

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

-- ════════════════════════════════════════════════════
-- § 5.5. Bridge to @cite{lucy-1994} Salience Classes
-- ════════════════════════════════════════════════════

open Semantics.Verb.Roots (SalienceClass)

/-- Map @cite{bohnemeyer-2004}'s 5-way Yukatek stem classification to
    @cite{lucy-1994}'s 4-way salience cut. The 5-way is a refinement:
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
    that collapse under @cite{lucy-1994}'s 4-way cut. The other three
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

-- ════════════════════════════════════════════════════
-- § 6. Split-Ergative System
-- ════════════════════════════════════════════════════

/-- Yukatek split-ergative system, parameterized by status category.
    Perfective status (completive/subjunctive) triggers ergative alignment;
    imperfective status (incompletive) triggers accusative alignment.
    Imperative is treated as ergative (completive-like default).

    This instantiates the same `Core.SplitErgativity` type used by Hindi
    and Georgian, enabling cross-linguistic comparison. -/
def yukatekSplit : Core.SplitErgativity StatusCategory :=
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
    imperfective → accusative. This is @cite{bohnemeyer-2004}'s core insight
    that a single linking-by-viewpoint mechanism underlies both systems. -/
theorem yukatek_hindi_same_split :
    yukatekSplit.alignment .completive = Core.hindiSplit.alignment .perfective ∧
    yukatekSplit.alignment .incompletive = Core.hindiSplit.alignment .imperfective :=
  ⟨rfl, rfl⟩

end Fragments.Mayan.Yukatek
