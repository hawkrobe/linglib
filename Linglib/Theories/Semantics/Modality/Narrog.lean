import Linglib.Core.Modality.DeonticNecessity
import Linglib.Core.Modality.ModalTypes
import Linglib.Core.Subjectivity

/-!
# Narrog's Semantic Map of Modality and Mood
@cite{narrog-2010} @cite{narrog-2012} @cite{heine-1995}

@cite{narrog-2010}'s two-dimensional semantic map classifies modal meanings along
two orthogonal axes:

1. **Volitivity** (horizontal): whether a modal meaning involves the speaker's
   or subject's will. Deontic obligation/permission and boulomaic wish/desire
   are *volitive*; epistemic possibility, ability, and evidentiality are
   *non-volitive*.

2. **Speaker-orientation** (vertical): the degree to which the modal meaning is
   anchored in the speech situation. Event-oriented modality (ability,
   circumstantial) is at the bottom; speaker-oriented modality (epistemic
   assessment, deontic imposition) is in the middle; mood and illocutionary
   force modulation (imperative, hortative) are at the top.

The central diachronic claim: modal meanings always shift **upward** — toward
increased speaker-orientation — independently of the volitive/non-volitive
dimension. The well-known deontic → epistemic shift is just one instance.

@cite{narrog-2012} adds a third dimension: **performativity** — whether the
utterance constitutes the modal act or merely describes it. This dimension
is orthogonal to speaker-orientation and is precisely what Traugott's
subjectivity cline fails to distinguish (§2.4, ch. 3).

## Bridges

- `toVolitivity` classifies `ModalFlavor` into Narrog's volitivity dimension:
  deontic = volitive; epistemic, circumstantial = non-volitive.
- `NarrogRegion` → `ModalFlavor`: reverse bridge from the 2D map back to
  Kratzer's flavor classification (partial — mood regions have no Kratzer analog).
- `SpeakerOrientationLevel` → `SubjectivityLevel`: event-oriented = nonSubjective;
  speaker-oriented = subjective; mood = intersubjective. Note: @cite{narrog-2012}
  argues this bridge is an oversimplification — see `performativity_invisible_to_traugott`.
- `Core.Modality.DeonticNecessity`: cross-linguistic data on obligation markers from
  the same 200-language sample.
-/

namespace Semantics.Modality.Narrog

open Core.Modality (ModalFlavor)
open Core.Subjectivity (SubjectivityLevel Performativity)

-- ============================================================================
-- §1. Volitivity
-- ============================================================================

/-- Whether a modal meaning involves the will of the speaker or subject.

    @cite{narrog-2010} §3.1, building on Jespersen ([1924] 1992) and
    @cite{heine-1995}: "the element of will" is the most fundamental
    distinguishing element between different kinds of mood. -/
inductive Volitivity where
  | volitive     -- involves will/desire (deontic, boulomaic)
  | nonVolitive  -- independent of will (epistemic, ability, evidential)
  deriving DecidableEq, Repr, Inhabited

/-- Classify `ModalFlavor` into Narrog's volitivity dimension.

    Deontic modality (obligation, permission) is volitive because it involves
    the speaker's or some authority's will. Epistemic and circumstantial
    modality are non-volitive — they describe the world independently of
    anyone's will. -/
def toVolitivity : ModalFlavor → Volitivity
  | .deontic => .volitive
  | .bouletic => .volitive
  | .epistemic => .nonVolitive
  | .circumstantial => .nonVolitive

-- ============================================================================
-- §2. Speaker-Orientation
-- ============================================================================

/-- Degree of anchoring to the speech situation.

    @cite{narrog-2010} Figure 1: the vertical axis ranges from event-oriented
    (bottom) through speaker-oriented modality (middle) to mood / illocutionary
    force modulation (top). -/
inductive SpeakerOrientationLevel where
  | eventOriented    -- modality describes event/situation properties (ability)
  | speakerOriented  -- modality reflects speaker's assessment (epistemic, deontic)
  | mood             -- illocutionary force: imperative, hortative, admonitive
  deriving DecidableEq, Repr, Inhabited

def SpeakerOrientationLevel.toNat : SpeakerOrientationLevel → Nat
  | .eventOriented => 0
  | .speakerOriented => 1
  | .mood => 2

instance : LinearOrder SpeakerOrientationLevel :=
  LinearOrder.lift' SpeakerOrientationLevel.toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [SpeakerOrientationLevel.toNat])

/-- Bridge to Traugott's subjectivity cline.

    The vertical axis of Narrog's map aligns with Traugott's cline:
    event-oriented = nonSubjective, speaker-oriented = subjective,
    mood = intersubjective (imperatives direct the addressee).

    **Caveat**: @cite{narrog-2012} ch. 3 argues this bridge is an
    oversimplification. Traugott's cline conflates speaker-orientation with
    performativity: deontic obligation (performative, face-threatening) and
    epistemic assessment (descriptive, not face-threatening) both map to
    `subjective`, but they differ fundamentally in their pragmatic effects.
    See `performativity_invisible_to_traugott`. -/
def SpeakerOrientationLevel.toSubjectivityLevel : SpeakerOrientationLevel → SubjectivityLevel
  | .eventOriented => .nonSubjective
  | .speakerOriented => .subjective
  | .mood => .intersubjective

/-- The bridge preserves ordering. -/
theorem speakerOrientation_toSubjectivity_monotone
    (a b : SpeakerOrientationLevel) (h : a ≤ b) :
    a.toSubjectivityLevel ≤ b.toSubjectivityLevel := by
  cases a <;> cases b <;> first | exact Nat.le_refl _ | exact h

-- ============================================================================
-- §3. Positions in the Semantic Map
-- ============================================================================

/-- A region in Narrog's 2D semantic map of modality and mood. -/
structure NarrogRegion where
  volitivity : Volitivity
  orientation : SpeakerOrientationLevel
  deriving Repr, DecidableEq

/-- A position in Narrog's full 3D space: volitivity × orientation × performativity.

    @cite{narrog-2012} §2.4: "subjectivity" decomposes into speaker-orientation
    (who is the modal source) and performativity (whether the utterance
    constitutes the modal act). The 2D map captures the first two dimensions;
    the full 3D space adds the third. -/
structure NarrogPosition where
  volitivity : Volitivity
  orientation : SpeakerOrientationLevel
  performativity : Performativity
  deriving Repr, DecidableEq

/-- Project to the 2D semantic map (dropping performativity). -/
def NarrogPosition.toRegion (r : NarrogPosition) : NarrogRegion :=
  ⟨r.volitivity, r.orientation⟩

-- ============================================================================
-- §4. Bridges to Kratzer's Framework
-- ============================================================================

/-- Map Narrog's 2D region to Kratzer's modal flavor classification.

    Mood-level regions (imperative, hortative) are illocutionary rather
    than truth-conditional, so they have no clean Kratzer flavor.

    @cite{narrog-2012} §2.4: this bridge makes explicit Narrog's claim that
    his 2D map *classifies* the Kratzer parameterization space — the
    combination of volitivity and orientation determines whether the
    conversational background is epistemic, deontic, or circumstantial. -/
def NarrogRegion.toModalFlavor : NarrogRegion → Option ModalFlavor
  | ⟨.volitive, .eventOriented⟩ => some .deontic       -- boulomaic desire
  | ⟨.volitive, .speakerOriented⟩ => some .deontic     -- obligation, permission
  | ⟨.nonVolitive, .eventOriented⟩ => some .circumstantial  -- ability, root possibility
  | ⟨.nonVolitive, .speakerOriented⟩ => some .epistemic     -- epistemic assessment
  | ⟨_, .mood⟩ => none                                  -- illocutionary (no Kratzer analog)

/-- The flavor bridge is consistent with the volitivity bridge:
    if a region maps to a flavor, that flavor's volitivity matches. -/
theorem toModalFlavor_consistent_volitivity (r : NarrogRegion) (f : ModalFlavor)
    (h : r.toModalFlavor = some f) : toVolitivity f = r.volitivity := by
  cases r with | mk v o => cases v <;> cases o <;>
    simp [NarrogRegion.toModalFlavor] at h <;> subst h <;> rfl

/-- Every non-mood `ModalFlavor` round-trips through the Narrog map:
    flavor → (volitivity, canonical orientation) → flavor. -/
theorem modalFlavor_roundtrip (f : ModalFlavor) (hf : f ≠ .bouletic) :
    NarrogRegion.toModalFlavor ⟨toVolitivity f,
      match f with
      | .deontic => .speakerOriented
      | .bouletic => .speakerOriented  -- bouletic collapses with deontic in Narrog's 2D space
      | .epistemic => .speakerOriented
      | .circumstantial => .eventOriented⟩ = some f := by
  cases f with
  | epistemic | deontic | circumstantial => rfl
  | bouletic => exact absurd rfl hf

-- ============================================================================
-- §5. Performativity and Traugott's Cline
-- ============================================================================

/-- Performativity is invisible to the Traugott bridge: deontic obligation
    (volitive, speaker-oriented, performative) and epistemic assessment
    (non-volitive, speaker-oriented, descriptive) both map to the same
    `SubjectivityLevel.subjective`, even though they differ radically in
    face-threatening potential and pragmatic effects.

    This is @cite{narrog-2012}'s central critique of Traugott's
    unidirectional subjectification: the cline conflates two independent
    dimensions (speaker-orientation and performativity), collapsing
    distinctions that matter for understanding both synchronic typology
    and diachronic change. -/
theorem performativity_invisible_to_traugott :
    (NarrogRegion.mk .volitive .speakerOriented).orientation.toSubjectivityLevel =
    (NarrogRegion.mk .nonVolitive .speakerOriented).orientation.toSubjectivityLevel := rfl

/-- Derive face-threatening potential from the 3D position.

    An utterance is face-threatening when it is performative (creates rather
    than describes the modal state), volitive (involves the will), and
    speaker-oriented or higher (directed at the addressee).

    @cite{narrog-2010} §4.2: strong obligation is cross-linguistically
    avoided with 2nd-person subjects precisely because it occupies this
    region — performative + volitive + speaker-oriented. -/
def NarrogPosition.isFaceThreatening (r : NarrogPosition) : Bool :=
  r.performativity == .performative &&
  r.volitivity == .volitive &&
  r.orientation != .eventOriented

/-- Canonical positions for major modal types. -/
def strongObligation : NarrogPosition :=
  ⟨.volitive, .speakerOriented, .performative⟩

def weakObligation : NarrogPosition :=
  ⟨.volitive, .speakerOriented, .descriptive⟩

def epistemicAssessment : NarrogPosition :=
  ⟨.nonVolitive, .speakerOriented, .descriptive⟩

def dynamicAbility : NarrogPosition :=
  ⟨.nonVolitive, .eventOriented, .descriptive⟩

def imperative : NarrogPosition :=
  ⟨.volitive, .mood, .performative⟩

/-- Strong obligation is face-threatening. -/
theorem strong_obligation_face_threatening :
    strongObligation.isFaceThreatening = true := rfl

/-- Weak obligation is NOT face-threatening (descriptive, not performative). -/
theorem weak_obligation_not_face_threatening :
    weakObligation.isFaceThreatening = false := rfl

/-- Epistemic assessment is NOT face-threatening. -/
theorem epistemic_not_face_threatening :
    epistemicAssessment.isFaceThreatening = false := rfl

/-- Imperatives are face-threatening (performative + volitive + mood > eventOriented). -/
theorem imperative_face_threatening :
    imperative.isFaceThreatening = true := rfl

/-- Strong and weak obligation differ ONLY in performativity — they share
    volitivity and orientation. The Traugott bridge cannot distinguish them
    because it drops performativity. -/
theorem strong_weak_differ_only_in_performativity :
    strongObligation.toRegion = weakObligation.toRegion := rfl

/-! ## §6. Cross-Linguistic Modal Changes

Diachronic modal change data and directionality theorems are now in
`Theories.Diachronic.ModalChange`, which imports this file and uses
`NarrogRegion` and `SpeakerOrientationLevel` to formalize the claim
that modal meanings always shift upward in the semantic map. -/

end Semantics.Modality.Narrog
