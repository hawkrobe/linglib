import Linglib.Phenomena.Reference.DirectReference
import Linglib.Theories.Semantics.Reference.FreeIndirectDiscourse
import Linglib.Core.Context.Tower
import Linglib.Core.Context.Shifts
import Linglib.Theories.Semantics.Tense.DeRe
import Linglib.Data.Examples.Schema

/-!
# Reference: ContextTower
@cite{anand-nevins-2004} @cite{banfield-1982} @cite{kaplan-1989} @cite{schlenker-2003}

End-to-end derivation chain connecting the ContextTower infrastructure
to the direct reference and indexical shift data in
`Phenomena.Reference.DirectReference`.

## Derivation Chain

```
Core.Context.Tower (ContextTower, push, origin, innermost)
    ↓
Core.Context.Shifts (attitudeShift, perspectiveShift, identityShift)
    ↓
Theories.Semantics.Reference.FreeIndirectDiscourse (FIDProfile)
    ↓
This file: tower operations model Kaplan's thesis and its violations
    ↓
Phenomena.Reference.DirectReference (MonsterThesis, shift languages)
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

open Phenomena.Reference

namespace AnandNevins2004

open Core.Context
open Semantics.Reference.FreeIndirectDiscourse
open Data.Examples (LinguisticExample)

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/AnandNevins2004.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def ex4 : LinguisticExample :=
  { id := "anandnevins2004_ex4"
    source := ⟨"anand-nevins-2004", "(4)"⟩
    reportedIn := none
    language := "diml1235"
    primaryText := "Hɛseni (mık-ra) va kɛ ɛz dɛwlɛtia."
    discourseSegments := []
    glossedTokens := [("Hɛseni", "Hesen.OBL"), ("(mık-ra)", "(I.OBL-to)"), ("va", "said"), ("kɛ", "that"), ("ɛz", "I"), ("dɛwlɛtia", "rich.be-PRES")]
    translation := "Hesen said that {I am, Hesen is} rich."
    context := "Zazaki: the embedded 1st-person `ɛz` can refer either to the utterance speaker OR to the attitude holder Hesen. Indexical shift is OPTIONAL under `vano` ('say'). Cornerstone first-person example."
    judgment := .acceptable
    alternatives := []
    readings := [("indexical (ɛz = utterance speaker)", .acceptable), ("shifted (ɛz = Hesen)", .acceptable)]
    paperFeatures := []
    comment := "Anand & Nevins 2004 ex (4), SALT XIV p. 20. First of four examples (4)-(7) demonstrating that all four Zazaki indexicals (I, you, here, yesterday) can shift under `vano`. The pronominal-shift facts motivate the context-shifting operator OPv."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex7 : LinguisticExample :=
  { id := "anandnevins2004_ex7"
    source := ⟨"anand-nevins-2004", "(7)"⟩
    reportedIn := none
    language := "diml1235"
    primaryText := "Hefte nayeraraver, H. mı-ra va kɛ o vizeri Rojda paci kɛrd."
    discourseSegments := []
    glossedTokens := [("Hefte", "week"), ("nayeraraver", "ago"), (",", ","), ("H.", "Hesen"), ("mı-ra", "me-at"), ("va", "said"), ("kɛ", "that"), ("o", "he"), ("vizeri", "yesterday"), ("Rojda", "Rojda"), ("paci", "kiss"), ("kɛrd", "did")]
    translation := "A week ago, H. told me that he kissed Rojda {8 days ago, #yesterday}."
    context := "Zazaki temporal-indexical shift. `vizeri` ('yesterday') in the embedded clause can shift to the attitude-context's now (= the day before the saying, i.e. 8 days before utterance), but NOT remain anchored to utterance-yesterday. The unavailable utterance-anchored reading is the diagnostic — English allows only that reading."
    judgment := .acceptable
    alternatives := []
    readings := [("shifted (yesterday = day-before-saying ≈ 8 days ago)", .acceptable), ("indexical (yesterday = utterance-yesterday)", .unacceptable)]
    paperFeatures := []
    comment := "Anand & Nevins 2004 ex (7), p. 20. Fourth of four indexical-shift examples (4)-(7). Together with (4)-(6), motivates that ALL indexicals (I, you, here, yesterday) shift in Zazaki — not just pronouns. A&N analyze (7) as an *adverbial* shift (`vizeri` is a temporal adverbial), not a tense-pronoun shift — this distinguishes A&N's indexical-shift account from tense-pronoun analyses of cross-linguistic embedded-past."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [ex4, ex7]

end Examples
-- END GENERATED EXAMPLES

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

/-- Kaplan's thesis holds for English — consistent with `monsterThesis.holdsForEnglish`. -/
theorem kaplan_holds_english :
    DirectReference.monsterThesis.holdsForEnglish = true := rfl

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

/-- The monster thesis IS challenged cross-linguistically — consistent with
    `monsterThesis.challengedCrossLinguistically`. -/
theorem monsters_exist :
    DirectReference.monsterThesis.challengedCrossLinguistically = true := rfl

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

/-! Bridge from @cite{anand-nevins-2004}'s shifty-operator framework to
    `Semantics.Tense.DeRe.EntityConcept` — the substrate's
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

open Semantics.Tense.DeRe (EntityConcept TimeConcept)

/-- **Kaplan-compliant "I"** as a rigid `EntityConcept`.

    The substrate's `EntityConcept` `Intension (KContext) E` is at
    Kaplan's *content* level — the result of applying his *character*
    to a context. Kaplan's `I` is technically a character (function
    from context to content) that returns `c.author` for any context;
    the **content** at a fixed actual context IS rigid. The substrate
    captures this content rigidity by modeling `kaplanI` as a constant
    intension at the speaker (here `.narrator`); the character-level
    structure is elided. This matches @cite{anand-nevins-2004}'s
    framing of English `I` as `AUTH(c*)` (sticky to actual context),
    contrasted with shifty languages where the operator can override
    the context parameter (yielding non-rigid agent-projection — see
    `shiftedI`). -/
def kaplanI : EntityConcept Unit Agent Unit ℤ :=
  Core.Intension.rigid .narrator

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
theorem kaplanI_isRigid : Core.Intension.IsRigid kaplanI :=
  Core.Intension.rigid_isRigid _

/-- **@cite{anand-nevins-2004}'s shifted "I" is non-rigid** —
    discriminating witness from contexts with different agents.
    Entity-side analog of Abusch's "descriptive time-concept" being
    the de dicto reading. -/
theorem shiftedI_not_isRigid : ¬ Core.Intension.IsRigid shiftedI := by
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
    Core.Intension.IsRigid kaplanI ∧
    ¬ Core.Intension.IsRigid shiftedI ∧
    -- Res = ℤ (Abusch's TimeConcept domain)
    Core.Intension.IsRigid (Core.Intension.rigid (W := RefCtx) (50 : ℤ)) ∧
    ¬ Core.Intension.IsRigid (fun c : RefCtx => c.time) := by
  refine ⟨kaplanI_isRigid, shiftedI_not_isRigid,
          Core.Intension.rigid_isRigid _, ?_⟩
  intro h
  have hContradiction : (0 : ℤ) = 999 :=
    h speechCtx { speechCtx with time := 999 }
  exact absurd hContradiction (by decide)

/-- **Architectural payoff via `Intension` functoriality** (the deep
    structural claim). Rigidity transfers across `Res` types via
    post-composition with ANY function — by the general
    `Intension.IsRigid.map` lemma in `Core/Logic/Intensional/Rigidity.lean`.

    Concretely: @cite{anand-nevins-2004}'s Kaplan-compliant `kaplanI`
    (rigid at `Res = Agent`) yields, for any `f : Agent → ℤ` (e.g.
    "birth year of the speaker"), a rigid `TimeConcept` `f ∘ kaplanI`
    at `Res = ℤ` — proved by `kaplanI_isRigid.map f`. The parallel
    between individual de re (this file) and temporal de re
    (`Studies/Abusch1997.lean`) is *the covariant action of
    `Intension RefCtx` on its target type*: a one-line corollary of
    `Intension.IsRigid.map`, not a list of two facts.

    @cite{abusch-1997}'s prose claim at p. 6 ("To apply the same
    machinery to de re belief, a further constraint is required...
    the same parallel as for tenses") is now functorially true:
    @cite{lewis-1979-attitudes} + @cite{cresswell-vonstechow-1982}'s
    centered-world reduction is formalized once and applies uniformly
    across all `Res` types via the same closure lemma. -/
theorem kaplanI_lifts_rigidly_to_timeConcept (f : Agent → ℤ) :
    Core.Intension.IsRigid (fun c : RefCtx => f (kaplanI c)) :=
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
    Core.Intension.IsRigid c ↔
    Core.Intension.IsRigid (fun ctx : RefCtx => f (c ctx)) :=
  ⟨fun h => h.map f, fun h => h.of_map_injective hf⟩

end AnandNevins2004
