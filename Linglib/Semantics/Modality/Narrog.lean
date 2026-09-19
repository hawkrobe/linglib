import Linglib.Semantics.Modality.Basic

/-!
# Narrog's Semantic Map of Modality and Mood
[narrog-2010] [narrog-2012] [heine-1995]

[narrog-2010]'s two-dimensional semantic map classifies modal meanings along
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

[narrog-2012] takes performativity, the use of a form to qualify a proposition with respect
to the current speech situation, as the core criterion of subjectivity in modality.

## Bridges

- `toVolitivity` classifies `ModalFlavor` into Narrog's volitivity dimension:
  deontic = volitive; epistemic, circumstantial = non-volitive.
- `NarrogRegion` → `ModalFlavor`: reverse bridge from the 2D map back to
  Kratzer's flavor classification (partial — mood regions have no Kratzer analog).
- The 200-language sample's NEC/POT cross-linguistic data lives with
  the formalised study at `Studies/Narrog2010.lean`.

## TODO

[narrog-2012] treats performativity as a gradient property of uses that defines speaker
orientation, and [narrog-2010] says that speaker orientation subsumes both subjectivity and
intersubjectivity in Traugott's sense. `NarrogPosition` instead stores performativity as a binary
coordinate independent of orientation, and the canonical positions below are stipulated.
-/

namespace Modality.Narrog

open Modality (ModalFlavor)

-- ============================================================================
-- §1. Volitivity
-- ============================================================================

/-- Whether a modal meaning involves the will of the speaker or subject.

    [narrog-2010] §3.1, building on Jespersen ([1924] 1992) and
    [heine-1995]: "the element of will" is the most fundamental
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

    [narrog-2010] Figure 1: the vertical axis ranges from event-oriented
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

-- ============================================================================
-- §3. Positions in the Semantic Map
-- ============================================================================

/-- A region in Narrog's 2D semantic map of modality and mood. -/
structure NarrogRegion where
  volitivity : Volitivity
  orientation : SpeakerOrientationLevel
  deriving Repr, DecidableEq

/-- A form is used performatively to the extent that it qualifies a proposition with respect to
the current speech situation, and descriptively to the extent that it does not. -/
inductive Performativity where
  /-- The form qualifies the proposition with respect to the current speech situation. -/
  | performative
  /-- The form reports a qualification without tying it to the current speech situation. -/
  | descriptive
  deriving DecidableEq, Repr, Inhabited

/-- A position pairs a region of the semantic map with a performative or descriptive use. -/
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

    [narrog-2012] §2.4: this bridge makes explicit Narrog's claim that
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
-- §5. Performativity and face threat
-- ============================================================================

/-- Derive face-threatening potential from the 3D position.

    An utterance is face-threatening when it is performative (creates rather
    than describes the modal state), volitive (involves the will), and
    speaker-oriented or higher (directed at the addressee).

    [narrog-2010] §4.2: strong obligation is cross-linguistically
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

/-- Strong and weak obligation share volitivity and orientation and differ in performativity
    alone. -/
theorem strong_weak_differ_only_in_performativity :
    strongObligation.toRegion = weakObligation.toRegion := rfl

/-! ## §6. Cross-Linguistic Modal Changes

Diachronic modal change data and directionality theorems are now in
`Studies/Narrog2010.lean`, which imports this file and uses
`NarrogRegion` and `SpeakerOrientationLevel` to formalize the claim
that modal meanings always shift upward in the semantic map. -/

end Modality.Narrog
