import Linglib.Theories.Semantics.Reference.Kaplan

/-!
# Shifted Indexicals

Cross-linguistic variation in indexical interpretation via tower depth:
English "I" reads from the origin (`.origin`), Amharic "I" reads from the
innermost context (`.local`), and Nez Perce exhibits mixed shifting where
person shifts but time does not.

## Key Definitions

- `amharic_pronI`: Amharic first person — `⟨.local, KContext.agent⟩`
- `UniformShiftParam`: Anand & Nevins (2004) constraint — all shifted
  indexicals in a language read from the same depth
- `MixedShiftLexicon`: Deal (2020) — person shifts but time doesn't (Nez Perce)
- `schlenker_counterexample`: English "I" and Amharic "I" diverge in the
  same tower configuration

## References

- Schlenker, P. (2003). A Plea for Monsters. *Linguistics & Philosophy*.
- Anand, P. & Nevins, A. (2004). Shifty Operators in Changing Contexts. SALT XIV.
- Deal, A. R. (2020). A Theory of Indexical Shift. MIT Press.
-/

namespace Semantics.Reference.ShiftedIndexicals

open Core.Context
open Semantics.Reference.Kaplan

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*}

-- ════════════════════════════════════════════════════════════════
-- § Amharic Shifted Indexicals (Schlenker 2003)
-- ════════════════════════════════════════════════════════════════

/-- Amharic first person pronoun: reads the agent from the innermost
    (most deeply embedded) context.

    "John yä-nä Ïnä dässïtäñ alä" ≈ "John said that I am happy"
    where "I" refers to John (the shifted agent), not the actual speaker.

    Schlenker (2003): Amharic attitude verbs are context-shifting operators
    (monsters). Under the tower analysis, the monster pushes an attitude
    shift, and the shifted "I" reads from `.local` rather than `.origin`. -/
def amharic_pronI : AccessPattern (KContext W E P T) E :=
  ⟨.local, KContext.agent⟩

/-- Amharic "here": reads position from the local (shifted) context.
    Under attitude shift, this yields the location of the attitude holder's
    reported speech act, not the actual speaker's location. -/
def amharic_opHere : AccessPattern (KContext W E P T) P :=
  ⟨.local, KContext.position⟩

@[simp] theorem amharic_pronI_depth :
    (amharic_pronI (W := W) (E := E) (P := P) (T := T)).depth = .local := rfl

-- ════════════════════════════════════════════════════════════════
-- § Schlenker Counterexample: English vs Amharic in Same Tower
-- ════════════════════════════════════════════════════════════════

/-- English "I" and Amharic "I" diverge when an attitude shift is pushed
    onto the tower. English "I" reads from the origin (unaffected), while
    Amharic "I" reads from the innermost context (shifted to the attitude
    holder).

    This is the formal content of Schlenker's (2003) counterexample to
    Kaplan's thesis: the SAME lexical item ("I") receives different
    interpretations cross-linguistically because of a depth parameter. -/
theorem schlenker_counterexample
    (c : KContext W E P T) (holder : E) (attWorld : W)
    (hDistinct : c.agent ≠ holder) :
    let t := ContextTower.root c
    let σ := attitudeShift holder attWorld
    pronI_access.resolve (t.push σ) ≠ amharic_pronI.resolve (t.push σ) := by
  simp only [pronI_access, amharic_pronI, AccessPattern.resolve,
    DepthSpec.resolve, ContextTower.push, ContextTower.root,
    ContextTower.contextAt, ContextTower.depth,
    List.take, List.foldl, attitudeShift]
  exact hDistinct

/-- In a root tower (no embedding), English and Amharic "I" agree:
    both return the context's agent. -/
theorem no_shift_agreement (c : KContext W E P T) :
    pronI_access.resolve (ContextTower.root c) =
    amharic_pronI.resolve (ContextTower.root c) := by
  simp only [pronI_access, amharic_pronI, AccessPattern.resolve,
    DepthSpec.resolve, ContextTower.root, ContextTower.contextAt,
    ContextTower.depth, List.length_nil, List.take, List.foldl]

-- ════════════════════════════════════════════════════════════════
-- § Uniform Shift Parameter (Anand & Nevins 2004)
-- ════════════════════════════════════════════════════════════════

/-- Anand & Nevins (2004) Uniform Shift: in languages with indexical
    shift, ALL shifted indexicals must shift to the same depth.

    In Zazaki, if "I" shifts under an attitude verb, then "you" must
    also shift. You cannot have "I" shifted but "you" unshifted in the
    same embedded clause.

    The parameter records the shared depth that all person indexicals use. -/
structure UniformShiftParam where
  /-- The shared depth for all person indexicals in this language -/
  personDepth : DepthSpec
  /-- The language exhibiting this pattern -/
  language : String

/-- Zazaki: both first and second person shift uniformly to `.local`. -/
def zazaki : UniformShiftParam :=
  { personDepth := .local
  , language := "Zazaki" }

/-- English: both first and second person uniformly read from `.origin`. -/
def english : UniformShiftParam :=
  { personDepth := .origin
  , language := "English" }

/-- Generate the first person access pattern from a uniform shift parameter. -/
def UniformShiftParam.pronI (u : UniformShiftParam) :
    AccessPattern (KContext W E P T) E :=
  ⟨u.personDepth, KContext.agent⟩

/-- Generate the second person access pattern from a uniform shift parameter. -/
def UniformShiftParam.pronYou (u : UniformShiftParam) :
    AccessPattern (KContext W E P T) E :=
  ⟨u.personDepth, KContext.addressee⟩

/-- Uniformity: first and second person share the same depth. -/
theorem uniform_depth (u : UniformShiftParam) :
    (u.pronI (W := W) (E := E) (P := P) (T := T)).depth =
    (u.pronYou (W := W) (E := E) (P := P) (T := T)).depth := rfl

-- ════════════════════════════════════════════════════════════════
-- § Mixed Shift Lexicon (Deal 2020)
-- ════════════════════════════════════════════════════════════════

/-- Deal (2020): Nez Perce exhibits MIXED shifting — person indexicals
    shift under attitude verbs but temporal indexicals do not.

    "Hii-pe-n'wi-ye kuhet hi-ppeew-n-e"
    ≈ "She_i said that she_i/*the speaker was going to arrive"
    Person shifts, but tense is evaluated relative to the actual speech time.

    A `MixedShiftLexicon` records per-coordinate depth specifications,
    allowing person and time to diverge. -/
structure MixedShiftLexicon where
  /-- Depth for person indexicals (first/second) -/
  personDepth : DepthSpec
  /-- Depth for temporal indexicals ("now", tense) -/
  temporalDepth : DepthSpec
  /-- Depth for spatial indexicals ("here") -/
  spatialDepth : DepthSpec
  /-- The language exhibiting this pattern -/
  language : String

/-- Nez Perce: person shifts to local, time stays at origin. -/
def nezPerce : MixedShiftLexicon :=
  { personDepth := .local
  , temporalDepth := .origin
  , spatialDepth := .origin
  , language := "Nez Perce" }

/-- Generate the first person access pattern from a mixed shift lexicon. -/
def MixedShiftLexicon.pronI (m : MixedShiftLexicon) :
    AccessPattern (KContext W E P T) E :=
  ⟨m.personDepth, KContext.agent⟩

/-- Generate the temporal indexical from a mixed shift lexicon. -/
def MixedShiftLexicon.opNow (m : MixedShiftLexicon) :
    AccessPattern (KContext W E P T) T :=
  ⟨m.temporalDepth, KContext.time⟩

/-- In Nez Perce, person and time have different depths. -/
theorem nezPerce_mixed :
    nezPerce.personDepth ≠ nezPerce.temporalDepth := nofun

/-- English is uniformly origin-reading: all coordinates share depth. -/
def englishMixed : MixedShiftLexicon :=
  { personDepth := .origin
  , temporalDepth := .origin
  , spatialDepth := .origin
  , language := "English" }

theorem english_not_mixed :
    englishMixed.personDepth = englishMixed.temporalDepth := rfl

end Semantics.Reference.ShiftedIndexicals
