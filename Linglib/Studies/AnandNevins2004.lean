import Linglib.Semantics.Reference.FreeIndirectDiscourse
import Linglib.Semantics.Reference.Context.Tower
import Linglib.Semantics.Reference.Context.Shifts
import Linglib.Semantics.Tense.DeRe
import Linglib.Data.Examples.Schema
import Linglib.Data.Examples.AnandNevins2004

/-!
# Reference: ContextTower
[anand-nevins-2004] [banfield-1982] [kaplan-1989] [schlenker-2003]

End-to-end derivation chain connecting the ContextTower infrastructure
to the Zazaki indexical-shift data in `Data.Examples.AnandNevins2004`.

## Derivation Chain

```
Semantics.Context.Tower (ContextTower, push, origin, innermost)
    ↓
Semantics.Context.Shifts (attitudeShift, perspectiveShift, identityShift)
    ↓
Semantics.Reference.FreeIndirectDiscourse (FIDProfile)
    ↓
This file: tower operations model Kaplan's thesis and its violations
    ↓
Data.Examples.AnandNevins2004 (Zazaki rows (4) and (7))
```

## Key Results

1. **Kaplan's thesis = identityShift**: English attitude verbs push identity
   shifts, so embedded indexicals read from origin (speaker's context)
2. **Indexical shift = perspectiveShift**: shift languages (Amharic, Zazaki)
   push perspective shifts, so embedded "I" reads from local (attitude
   holder's context)
3. **FID = mixed access**: Classic FID reads agent from origin (narrator)
   but time/world from local (character) — the hallmark mixed perspective
4. **Direct speech = full local access**: All coordinates from the embedded
   context (full perspective shift)

-/

namespace AnandNevins2004

open Semantics.Context
open Semantics.Reference.FreeIndirectDiscourse

-- ============================================================================
-- § Concrete Context Type
-- ============================================================================

/-- A context with distinguishable agents (for testing identity). -/
inductive Agent where | narrator | character
  deriving DecidableEq, Repr

abbrev RefCtx := KContext Unit Agent Unit ℤ

/-- Speech-act context: narrator speaking at time 0. -/
def speechCtx : RefCtx :=
  { world := (), agent := .narrator, addressee := .character, time := 0, position := () }

/-- Root tower at the speech-act context. -/
def rootTower : ContextTower RefCtx := ContextTower.root speechCtx

-- ============================================================================
-- § Kaplan's Thesis: English = Identity Shift
-- ============================================================================

/-- English attitude verbs push identity shifts (Kaplan's thesis).
    "John said that I am here now" — "I", "here", "now" all refer to
    the speaker, not to John. -/
def englishAttitudeTower : ContextTower RefCtx :=
  rootTower.push identityShift

/-- Under an identity shift, the embedded agent is still the narrator.
    This is Kaplan's thesis: English indexicals are not shifted. -/
theorem english_I_is_narrator :
    englishAttitudeTower.innermost.agent = .narrator := rfl

/-- Under an identity shift, the embedded time is still 0.
    "Now" refers to the speech time, not the attitude time. -/
theorem english_now_is_speech_time :
    englishAttitudeTower.innermost.time = 0 := rfl

-- ============================================================================
-- § Shift Languages: perspectiveShift
-- ============================================================================

/-- Shift languages (Amharic, Zazaki, etc.) push perspective shifts.
    The attitude verb shifts the agent to the attitude holder and the
    time to the attitude time. -/
def shiftLanguageTower : ContextTower RefCtx :=
  rootTower.push (perspectiveShift .character (-3) ())

/-- Under a perspective shift, the embedded agent is the character.
    "I" in Amharic under an attitude verb refers to the attitude holder. -/
theorem shifted_I_is_character :
    shiftLanguageTower.innermost.agent = .character := rfl

/-- Under a perspective shift, the embedded time is the attitude time.
    "Now" in a shifted language refers to the attitude time, not speech time. -/
theorem shifted_now_is_attitude_time :
    shiftLanguageTower.innermost.time = -3 := rfl

/-- Monsters exist: [anand-nevins-2004]'s (4) records the shifted reading
    of Zazaki embedded `ɛz` as acceptable — the witness against Kaplan's
    prohibition that `shiftLanguageTower` models. -/
theorem monsters_exist :
    Examples.ex4.readings[1]? = some ("shifted (ɛz = Hesen)", .acceptable) := rfl

/-- [anand-nevins-2004]'s (7): the temporal indexical shifts obligatorily —
    only the attitude-anchored reading of embedded `vizeri` is acceptable,
    the utterance-anchored one is not. This is the row that
    `shifted_now_is_attitude_time` models on the time coordinate. -/
theorem temporal_shift_obligatory :
    Examples.ex7.readings.map Prod.snd = [.acceptable, .unacceptable] := rfl

-- ============================================================================
-- § FID: Mixed Access (Narrator Agent + Character Time/World)
-- ============================================================================

/-- Classic FID pushes a perspective shift (character's time/world) but
    reads the agent from origin (narrator). The FIDProfile encodes this
    per-coordinate depth specification. -/
def fidTower : ContextTower RefCtx :=
  rootTower.push (perspectiveShift .character (-5) ())

/-- Classic FID profile: agent from origin, everything else from local. -/
def classicFIDProfile : FIDProfile := classicFID

/-- In FID, the agent is the narrator (read from origin). -/
theorem fid_agent_is_narrator :
    classicFIDProfile.resolveAgent fidTower = .narrator := rfl

/-- In FID, the time is the character's (read from local). -/
theorem fid_time_is_character :
    classicFIDProfile.resolveTime fidTower = -5 := rfl

/-- FID is genuinely mixed: agent ≠ what perspectiveShift gives. -/
theorem fid_is_mixed_perspective :
    classicFIDProfile.resolveAgent fidTower ≠
    fidTower.innermost.agent := by decide

-- ============================================================================
-- § Direct vs Indirect Speech Comparison
-- ============================================================================

/-- Indirect speech: all coordinates from origin (Kaplan-compliant). -/
def indirectProfile : FIDProfile := indirectSpeech

/-- Direct speech: all coordinates from local (full shift). -/
def directProfile : FIDProfile := directSpeech

/-- In indirect speech, agent is narrator (from origin). -/
theorem indirect_agent_narrator :
    indirectProfile.resolveAgent fidTower = .narrator := rfl

/-- In direct speech, agent is character (from local). -/
theorem direct_agent_character :
    directProfile.resolveAgent fidTower = .character := rfl

/-- FID agent agrees with indirect speech (both from origin). -/
theorem fid_agent_eq_indirect :
    classicFIDProfile.resolveAgent fidTower =
    indirectProfile.resolveAgent fidTower := rfl

/-- FID time agrees with direct speech (both from local). -/
theorem fid_time_eq_direct :
    classicFIDProfile.resolveTime fidTower =
    directProfile.resolveTime fidTower := rfl

-- ============================================================================
-- § Entity-Concept Bridge: Anand-Nevins 2004 in the centered-world substrate
-- ============================================================================

/-! Bridge from [anand-nevins-2004]'s shifty-operator framework to
    `Tense.DeRe.EntityConcept` — the substrate's
    individual-side de re intension. The existing FIDProfile-based
    formalization above and the substrate's `EntityConcept`-based
    formalization are two perspectives on the same phenomenon; the
    substrate's `Intension.IsRigid` predicate distinguishes
    Kaplan-compliant from shifty indexicals at the type level.

    The architectural payoff: this is **exactly parallel** to how
    `Intension.IsRigid` distinguishes Abusch-style wide-scope rigid
    time-references from de dicto descriptive time-concepts in
    `Studies/Abusch1997.lean` (`TimeConcept`).
    The polymorphism in `Intension W τ` is non-trivial: individual
    de re (this file) and temporal de re (Abusch) are *the same
    machinery* at different `Res` types. The
    `entityConcept_and_timeConcept_share_isRigid_substrate` theorem
    below makes that claim kernel-checked. -/

open Tense.DeRe (EntityConcept TimeConcept)

/-- **Kaplan-compliant "I"** as a rigid `EntityConcept`.

    The substrate's `EntityConcept` `Intension (KContext) E` is at
    Kaplan's *content* level — the result of applying his *character*
    to a context. Kaplan's `I` is technically a character (function
    from context to content) that returns `c.author` for any context;
    the **content** at a fixed actual context IS rigid. The substrate
    captures this content rigidity by modeling `kaplanI` as a constant
    intension at the speaker (here `.narrator`); the character-level
    structure is elided. This matches [anand-nevins-2004]'s
    framing of English `I` as `AUTH(c*)` (sticky to actual context),
    contrasted with shifty languages where the operator can override
    the context parameter (yielding non-rigid agent-projection — see
    `shiftedI`). -/
def kaplanI : EntityConcept Unit Agent Unit ℤ :=
  Intensional.Intension.rigid .narrator

/-- **Anand-Nevins (2004 §1, eq. 2a) shifted "I"** (Zazaki under
    `OP_V`): the operator overwrites the context parameter with the
    index parameter (`[[OP_V[α]]]^{c,i} = [[α]]^{i,i}`), so an
    embedded `I` reads the AUTHOR of whichever centered context is
    locally supplied. As an `EntityConcept`, this is the
    agent-projection function — non-rigid: it varies with whatever
    `KContext` is plugged in. -/
def shiftedI : EntityConcept Unit Agent Unit ℤ :=
  fun c => c.agent

/-- **Kaplan's "I" is rigid** (entity-side analog of Abusch's "rigid
    time-concept" being the de re reading). -/
theorem kaplanI_isRigid : Intensional.Intension.IsRigid kaplanI :=
  Intensional.Intension.rigid_isRigid _

/-- **[anand-nevins-2004]'s shifted "I" is non-rigid** —
    discriminating witness from contexts with different agents.
    Entity-side analog of Abusch's "descriptive time-concept" being
    the de dicto reading. -/
theorem shiftedI_not_isRigid : ¬ Intensional.Intension.IsRigid shiftedI := by
  intro h
  have hContradiction : (Agent.narrator) = .character :=
    h speechCtx { speechCtx with agent := .character }
  exact absurd hContradiction (by decide)

/-- **Bridge to FIDProfile**: the shifted `I` entity-concept evaluated
    at the embedded layer of `shiftLanguageTower` (perspective-shifted
    to `.character`) equals `directProfile.resolveAgent shiftLanguageTower`.
    Both formalize the "shifted indexical reads from local context"
    claim; the substrate exposes it as concept non-rigidity, the
    FIDProfile mechanism exposes it as `.local` depth access. -/
theorem shiftedI_at_shiftLanguageTower :
    shiftedI shiftLanguageTower.innermost =
    directProfile.resolveAgent shiftLanguageTower := rfl

/-- **Bridge to FIDProfile**: Kaplan's `I` evaluated at any context
    equals `indirectProfile.resolveAgent englishAttitudeTower`. Both
    formalize the "Kaplan-compliant indexical reads from origin"
    claim; the substrate exposes it as concept rigidity, the
    FIDProfile mechanism exposes it as `.origin` depth access. -/
theorem kaplanI_at_englishAttitudeTower (c : RefCtx) :
    kaplanI c = indirectProfile.resolveAgent englishAttitudeTower := rfl

/-- Concrete witnesses (4 points in the rigid/non-rigid × Agent/ℤ
    matrix) — kept as a verifiable example. The deep structural
    statement of why the parallel holds is
    `kaplanI_lifts_rigidly_to_timeConcept` below — functoriality of
    `Intension.IsRigid` does the work. -/
example :
    -- Res = Agent (this file)
    Intensional.Intension.IsRigid kaplanI ∧
    ¬ Intensional.Intension.IsRigid shiftedI ∧
    -- Res = ℤ (Abusch's TimeConcept domain)
    Intensional.Intension.IsRigid (Intensional.Intension.rigid (W := RefCtx) (50 : ℤ)) ∧
    ¬ Intensional.Intension.IsRigid (fun c : RefCtx => c.time) := by
  refine ⟨kaplanI_isRigid, shiftedI_not_isRigid,
          Intensional.Intension.rigid_isRigid _, ?_⟩
  intro h
  have hContradiction : (0 : ℤ) = 999 :=
    h speechCtx { speechCtx with time := 999 }
  exact absurd hContradiction (by decide)

/-- **Architectural payoff via `Intension` functoriality** (the deep
    structural claim). Rigidity transfers across `Res` types via
    post-composition with ANY function — by the general
    `Intension.IsRigid.map` lemma in `Semantics/Intensional/Rigidity.lean`.

    Concretely: [anand-nevins-2004]'s Kaplan-compliant `kaplanI`
    (rigid at `Res = Agent`) yields, for any `f : Agent → ℤ` (e.g.
    "birth year of the speaker"), a rigid `TimeConcept` `f ∘ kaplanI`
    at `Res = ℤ` — proved by `kaplanI_isRigid.map f`. The parallel
    between individual de re (this file) and temporal de re
    (`Studies/Abusch1997.lean`) is *the covariant action of
    `Intension RefCtx` on its target type*: a one-line corollary of
    `Intension.IsRigid.map`, not a list of two facts.

    [abusch-1997]'s prose claim at p. 6 ("To apply the same
    machinery to de re belief, a further constraint is required...
    the same parallel as for tenses") is now functorially true:
    [lewis-1979-attitudes] + [cresswell-vonstechow-1982]'s
    centered-world reduction is formalized once and applies uniformly
    across all `Res` types via the same closure lemma. -/
theorem kaplanI_lifts_rigidly_to_timeConcept (f : Agent → ℤ) :
    Intensional.Intension.IsRigid (fun c : RefCtx => f (kaplanI c)) :=
  kaplanI_isRigid.map f

/-- **Bidirectional structural equivalence under injective lifting**:
    when `f : Agent → ℤ` is injective (e.g., a unique-birth-year
    function), rigidity of the lifted time-concept `f ∘ c` is
    EQUIVALENT to rigidity of the underlying entity-concept `c`.
    Both directions are corollaries of substrate-level functoriality:
    `Intension.IsRigid.map` (forward) and `Intension.IsRigid.of_map_injective`
    (reverse).

    This establishes that the parallel between Anand-Nevins
    entity-concepts and Abusch time-concepts is not just a one-way
    mapping but a structural equivalence under any injective `f` —
    rigidity-classifying entity-concepts and their image
    time-concepts are *the same problem* up to the choice of
    injective lifting. -/
theorem entityConcept_rigid_iff_image_rigid_under_injective
    {f : Agent → ℤ} (hf : Function.Injective f)
    (c : EntityConcept Unit Agent Unit ℤ) :
    Intensional.Intension.IsRigid c ↔
    Intensional.Intension.IsRigid (fun ctx : RefCtx => f (c ctx)) :=
  ⟨fun h => h.map f, fun h => h.of_map_injective hf⟩

end AnandNevins2004
