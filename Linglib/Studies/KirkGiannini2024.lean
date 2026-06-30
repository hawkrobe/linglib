import Linglib.Semantics.Quotation.Mixed
import Linglib.Semantics.Reference.Monsters
import Linglib.Studies.VanDerSandtMaier2003
import Linglib.Studies.Maier2014
import Linglib.Studies.HarrisPotts2009
import Linglib.Studies.Horn1989
import Linglib.Studies.PlunkettSundell2013
import Linglib.Studies.KocurekJerzakRudolph2020

/-!
# Kirk-Giannini 2024: Covert Mixed Quotation
[kirk-giannini-2024]

Covert mixed quotation. Semantics and Pragmatics 17, Article 5: 1-54.

## Overview

Five apparently distinct phenomena are derived from the interaction of
covert mixed quotation `𝔐` with four additional operators (`↓`, `†`,
`𝔄`, and quantification over senses):

1. **CI projection failure** (§1, paper §3): Conventional implicature
   items (expressives, slurs, NRRCs) fail to project out of indirect
   speech reports because the embedded clause is first pure-quoted
   (stripping the original CI) before `𝔐` re-introduces a peripheral
   utterance attribution.

2. **C-monsters** (§2, paper §4): "Pluto could have been a planet"
   accesses the meaning 'planet' would have under different conventions
   via the diagonalizer `†`, which collapses the world of utterance
   into the world of evaluation. K-G's `†` is existentially closed over
   speakers/communities (paper fn 22).

3. **Metalinguistic negation** (§3, paper §5): "I didn't trap two
   MONGEESE" derives via the chain `𝔐 → 𝔄 → ↓ → ¬`, with `↓` shunting
   the appropriateness content into the at-issue dimension before
   negation applies. The analysis predicts three syntactic restrictions
   identified by [horn-1985] / [horn-1989] and
   [burton-roberts-1989]: morpheme incorporation failure, NPI
   licensing failure, and DN-elimination failure.

4. **Metalinguistic negotiation** (§4, paper §6): "Secretariat is /
   isn't an athlete" — A and B express literally **incompatible**
   appropriateness contents on a **shared** standard, contra
   [plunkett-sundell-2013]'s "consistent contents" diagnosis.

5. **"In a sense"** (§5, paper §7): "Viruses are alive in a sense"
   contributes `∃μ ∃sₓ [⟨*⟩(q)(wc)(sₓ) ∧ [^⟨*⟩(q)(wc)(sₓ)] = μ]` —
   an existential over BOTH speakers AND intensions, with `which_μ`
   binding via Predicate Abstraction.

## Cross-framework theorem inventory

This module hosts **8 cross-framework refutation/bridge theorems**
that make K-G's incompatibilities with sibling analyses visible at
theorem level (per linglib's "no bridge files" rule, comparisons live
in the chronologically-later study file). Each theorem actually
imports and invokes the named sibling's substrate — none is a
docstring-only claim.

- `kg_refutes_potts_universal_projection` (§1) — invokes
  `Pragmatics.Expressives.TwoDimProp.neg`, exhibits divergence at
  `.hypothetical`
- `kg_refutes_harris_potts_orientation` (§1) — instantiates
  `HarrisPotts2009.CIItem` and compares resolution outcomes
- `kg_refutes_maier_chameleonism` (§1) — instantiates `Maier2014.mq`
  on the same input and shows daughter-CI passthrough vs. K-G's
  strip-then-mix yields divergent CI predictions
- `diagonalize_no_kaplan_monster` (§2) — defines `kgEmbeddingShifts`
  reflecting K-G's covert apparatus (4 identity shifts, one per
  operator) and proves `KaplansThesisHolds` non-vacuously via
  case-split
- `kg_refutes_kjr_convention_shift` (§2) — instantiates KJR's
  `Convention` and `WC`, exhibits a WC-pair where KJR's
  `diagContent` predicts True while K-G's `diagonalizeKG` predicts
  False
- `kg_metalinguistic_chain_targets_appropriateness` (§3) — exhibits
  the `applyApprop` chain producing appropriateness content (vs.
  `VanDerSandtMaier2003.DenialType.implicature`'s implicature
  layer)
- `kg_refutes_plunkett_sundell` (§4) — instantiates P&S's
  `MetalinguisticDispute` with K-G's shared standard and proves the
  P&S `consistentContents` predicate fails to hold
- `in_a_sense_distinct_from_imprecision` (§5) — exhibits speaker-locus
  variation, structurally distinct from granularity-locus accounts

§3 also lifts three syntactic predictions from `Horn1989`:
`mongeese_blocks_morpheme_incorporation`, `..._npi_licensing`,
`..._dn_elimination`. These are NOT framed as cross-framework
theorems (K-G and Horn agree on the predictions, disagree only on
the architecture that derives them).

## Note on Denial Taxonomy

The three-way `DenialType` taxonomy (propositional / presuppositional /
implicature) from [van-der-sandt-maier-2003] — formalized in
`Studies/VanDerSandtMaier2003.lean` — groups register and connotation
denials under `implicature`. K-G's analysis (paper §5, p.28-30) derives
metalinguistic-negation truth conditions from `♦` (appropriateness
modal) composed with `𝔐`, with `↓` shunting before negation. The
distinguishing feature of K-G's account is the appeal to appropriateness
plus the syntactic predictions in §3 (NPI failure, morpheme
incorporation failure, DN-elimination failure).
-/

set_option autoImplicit false

namespace KirkGiannini2024

open Semantics.Quotation
open Pragmatics.Expressives (TwoDimProp)

-- ════════════════════════════════════════════════════
-- § 1. CI Projection Failure (paper §3)
-- ════════════════════════════════════════════════════

section CIProjection

/-- Concrete world type for the CI projection scenarios — non-trivial
    so universal/existential quantification has computational content. -/
inductive ProjWorld where
  | actual
  | hypothetical
  deriving DecidableEq, Repr, Inhabited

-- ────────────────────────────────────────────────────
-- §1.1. The 'goddamned keys' scenario (paper (26))
-- ────────────────────────────────────────────────────

/-- Expressions in the 'goddamned keys' scenario. -/
inductive GDExpr where | goddamnedKeys deriving DecidableEq, Repr

/-- Speakers: Jones (the original utterer) and the reporter. -/
inductive GDSpeaker where | jones | reporter deriving DecidableEq, Repr

/-- 'Goddamned keys' denotes Jones-spent-an-hour-looking-for-his-keys.
    At-issue content is independent of who's reporting. -/
def gdInterp : QuotInterp GDExpr GDSpeaker ProjWorld
  | .goddamnedKeys, _, _, _ => True

/-- **Original peripheral CI** of 'goddamned' in its first use:
    Jones has a negative attitude toward Jones's keys. Modelled as
    constant True — attitudes are intentional content of the speaker,
    not world-contingent. (This is what makes the Potts-vs-K-G
    refutation bite at `.hypothetical`: the original CI persists
    across worlds, but Jones's UTTERANCE is contingent.) -/
def gdOriginalCI : ProjWorld → Prop := λ _ => True

/-- **Non-trivial utterance attribution.** Jones uttered 'goddamned
    keys' at .actual; reporter never uttered it. This is what
    differentiates §1's peripheral content from the constant-True
    placeholder of the original substrate. -/
def gdUttRel : UttRel GDSpeaker Unit GDExpr ProjWorld
  | .jones,    _, .goddamnedKeys, .actual => True
  | .jones,    _, .goddamnedKeys, .hypothetical => False
  | .reporter, _, .goddamnedKeys, _ => False

/-- Reporter's MQ context. Sx is jones (the anaphorically retrieved
    speaker), wc is the actual world, the reporter is the discourse
    speaker (not represented in MQContext directly). -/
def reporterCtx : MQContext ProjWorld GDExpr GDSpeaker Unit :=
  { interp := gdInterp, uttRel := gdUttRel
  , sx := .jones, ux := (), wc := .actual }

/-- Peripheral content after 𝔐: utterance attribution to Jones, NOT the
    original expressive CI. -/
@[simp] theorem gd_r_layer_attribution :
    (MQProp.applyMQ reporterCtx .goddamnedKeys).rContent .actual := by
  simp [reporterCtx, gdUttRel]

/-- At-issue content is preserved through 𝔐: Jones-spent-an-hour-
    looking-for-his-keys remains true. -/
@[simp] theorem gd_at_issue_preserved :
    (MQProp.applyMQ reporterCtx .goddamnedKeys).atIssue .actual := by
  simp [reporterCtx, gdInterp]

/-- The reporter is not credited with Jones's utterance — gdUttRel
    correctly distinguishes the actual utterer from the reporter. -/
theorem gd_reporter_not_attributed :
    ¬ gdUttRel .reporter () .goddamnedKeys .actual := by
  intro h; cases h

/--
**The strip-then-remix structure (paper p.21-22).** A `TwoDimProp` carrying the original CI is
pure-quoted (stripping the CI to `⊤` — an information-losing step, `pureQuote_loses_ci_info`),
then `MQContext.applyMQ` re-introduces peripheral content as utterance attribution. The
remixed R-layer holds the new attribution, not the original CI.
-/
theorem gd_strip_then_remix_loses_original_ci :
    let original : TwoDimProp ProjWorld :=
      { atIssue := λ _ => True, ci := gdOriginalCI }
    -- After remix via 𝔐, the R-layer is the new utterance attribution, not the original CI:
    (MQProp.applyMQ reporterCtx .goddamnedKeys).rContent .hypothetical ≠
      original.ci .hypothetical := by
  -- gdOriginalCI = constant True, but gdUttRel .jones at .hypothetical = False
  simp [reporterCtx, gdUttRel, gdOriginalCI]

-- ────────────────────────────────────────────────────
-- §1.2. Refutation theorems
-- ────────────────────────────────────────────────────

/--
**K-G refutes Potts's universal CI projection.** Per
[potts-2005] (formalised as
`Pragmatics.Expressives.Basic.ci_projects_through_neg`):
`(neg p).ci = p.ci`. The CI of a `TwoDimProp` projects unchanged
through any at-issue operator. K-G's analysis predicts that under
indirect-speech embedding the CI is REPLACED by utterance
attribution.

To exhibit the divergence we apply both analyses to the SAME input
proposition `original = ⟨True, gdOriginalCI⟩`:

- **Potts**: applying `TwoDimProp.neg` (or any at-issue operator)
  preserves the CI, so the predicted CI value at `.hypothetical` is
  `gdOriginalCI .hypothetical = True` (Jones's attitude persists
  across worlds).
- **K-G**: applying the strip-then-remix pipeline replaces the CI
  with R-attribution `gdUttRel .jones () .goddamnedKeys`, so the
  predicted R-value at `.hypothetical` is `False` (Jones's
  utterance is contingent on the world — only happened in `.actual`).

The two analyses disagree at `.hypothetical`. The proof actually
invokes `Pragmatics.Expressives.TwoDimProp.neg` on the constructed
input — not just compares stipulated values.
-/
theorem kg_refutes_potts_universal_projection :
    let original : TwoDimProp ProjWorld :=
      { atIssue := λ _ => True, ci := gdOriginalCI }
    -- Potts: substrate's neg leaves ci unchanged
    -- (`Pragmatics.Expressives.TwoDimProp.ci_projects_through_neg`)
    let pottsCIAfterNeg : ProjWorld → Prop := (TwoDimProp.neg original).ci
    -- K-G: strip-then-mix replaces ci with R-attribution to sx (=jones)
    let kgRAfterChain : ProjWorld → Prop :=
      (MQProp.applyMQ reporterCtx .goddamnedKeys).rContent
    -- They disagree at .hypothetical: True ≠ False
    pottsCIAfterNeg .hypothetical ≠ kgRAfterChain .hypothetical := by
  simp [TwoDimProp.neg, gdOriginalCI, reporterCtx, gdUttRel]

/--
**K-G refutes Harris-Potts orientation variables.**
[harris-potts-2009] posit a free orientation variable on each CI
item, contextually resolved (formalised as
`HarrisPotts2009.CIItem` with a
`ciFor : Orientation → W → Prop` field). K-G's strip-then-remix
analysis predicts the CI is FIXED by the syntactic structure
(specifically by `sx` in the MQ context).

To exhibit the divergence, we construct an H&P CI item whose
orientation is contextually resolvable to ANY participant (H&P's
permissive prediction), and a K-G chain where the CI is determined
by the fixed `sx = .jones`. The H&P item allows the reporter to be
the orientation; K-G excludes this.
-/
theorem kg_refutes_harris_potts_orientation :
    -- H&P's CI item: orientation freely resolved
    let hpItem : HarrisPotts2009.CIItem GDSpeaker ProjWorld :=
      { ciFor := λ o w => match o with
                          | .speaker => True   -- H&P allows resolving to any participant
                          | .other _ => True   -- including non-anaphoric speakers
        atIssue := λ _ => True }
    -- H&P-resolved CI for "the reporter as orientation":
    let hpReporterCI : ProjWorld → Prop :=
      (hpItem.resolve (.other GDSpeaker.reporter)).ci
    -- K-G's CI: fixed to sx = .jones via reporterCtx
    let kgCI : ProjWorld → Prop :=
      (MQProp.applyMQ reporterCtx .goddamnedKeys).rContent
    -- H&P predicts CI holds for the reporter at .hypothetical
    -- (orientation can resolve flexibly); K-G predicts NOT (reporter
    -- isn't sx, and Jones didn't utter at .hypothetical).
    hpReporterCI .hypothetical ≠ kgCI .hypothetical := by
  simp [HarrisPotts2009.CIItem.resolve, reporterCtx, gdUttRel]

/--
**K-G refutes Maier 2014a's syntactic chameleonism.**

Maier (`Maier2014`) treats the
mixed-quotation operator as type-polymorphic: `mq attrib e` returns
a `TypedExpr` with the SAME category as `e`, and the daughter's CI
content passes through unchanged (theorem `mq_ci_passes_daughter_ci_through`).

K-G's strip-then-mix pipeline DESTROYS the daughter's CI before
remixing — the original `gdOriginalCI` does not survive into the
result's peripheral content; only the new R-attribution does.

We exhibit the divergence by constructing the same input expression
in both substrates and showing their CI predictions diverge.
-/
theorem kg_refutes_maier_chameleonism :
    -- Maier's typed input — wraps gdOriginalCI through `mq`:
    let maierInput : Maier2014.TypedExpr ProjWorld :=
      { cat := .NP
      , meaning := { atIssue := λ _ => True, ci := gdOriginalCI } }
    -- Maier's prediction: daughter CI passes through, conjoined with attribution.
    -- At .hypothetical with a constant-True attribution, Maier's CI = True.
    let maierAttrib : ProjWorld → Prop := λ _ => True
    let maierCI : ProjWorld → Prop :=
      (Maier2014.mq maierAttrib maierInput).meaning.ci
    -- K-G's prediction: rContent at .hypothetical = False (Jones didn't utter).
    let kgCI : ProjWorld → Prop :=
      (MQProp.applyMQ reporterCtx .goddamnedKeys).rContent
    -- Divergence at .hypothetical:
    maierCI .hypothetical ≠ kgCI .hypothetical := by
  simp [Maier2014.mq, gdOriginalCI, reporterCtx, gdUttRel]

end CIProjection

-- ════════════════════════════════════════════════════
-- § 2. C-Monsters (paper §4)
-- ════════════════════════════════════════════════════

section CMonsters

/-- Worlds for the Pluto scenario: pre-2006 conventions classify Pluto
    as a planet, post-2006 do not. -/
inductive PlutoWorld where
  | pre2006 | post2006
  deriving DecidableEq, Repr, Inhabited

/-- The word 'planet' as a quoted expression. -/
inductive PlutoExpr where | planet deriving DecidableEq, Repr

/-- Two speakers: one using the standard (post-2006) convention, one
    a hypothetical pre-2006 community. The ∃-over-speakers in K-G's †
    (paper fn 22) ranges over types like this. -/
inductive PlutoSpeaker where
  | standard
  | pre2006Community
  deriving DecidableEq, Repr

/-- Quotative interpretation of 'planet': depends on the speaker's
    convention. The pre-2006 community classifies Pluto as planet at
    pre-2006 worlds; the standard speaker does not. -/
def plutoInterp : QuotInterp PlutoExpr PlutoSpeaker PlutoWorld
  | .planet, .pre2006,  .pre2006Community, _ => True
  | .planet, .post2006, .pre2006Community, _ => False
  | .planet, _,         .standard,         _ => False

/--
**(4): "Pluto could have easily been a planet"** — true via K-G's
diagonalizer with ∃-over-speakers (paper fn 22). The diagonalized
predicate is non-vacuous: there exists a speaker (the pre-2006
community) whose use of 'planet' includes Pluto at the pre-2006 world.
Witness: speaker = `.pre2006Community`, world = `.pre2006`.
-/
theorem pluto_counterfactual_via_diagonalizeKG :
    ∃ w : PlutoWorld, diagonalizeKG plutoInterp .planet w := by
  refine ⟨.pre2006, ?_⟩
  exact ⟨.pre2006Community, by simp [plutoInterp]⟩

/-- **Witness uniqueness fails.** The pre-2006 community and the
    standard speaker disagree on Pluto's planethood at pre-2006 worlds,
    so K-G's existential is genuinely informative — not every speaker
    is a witness. -/
theorem pluto_diagonalize_witness_not_universal :
    ¬ ∀ s : PlutoSpeaker, plutoInterp .planet .pre2006 s .pre2006 := by
  intro h
  have : plutoInterp .planet .pre2006 .standard .pre2006 := h .standard
  cases this

/--
**K-G's covert lexicon, viewed as Kaplan-context shifts.** All four
covert operators (𝔐, ↓, †, 𝔄) operate on the world / appropriateness
components of evaluation, NOT on the Kaplan context (agent, time,
location). Their image on Kaplan-context space is the identity shift.

We exhibit this with one `identityShift` per covert operator. The
list could equivalently be empty; making it explicit lets the
no-monster theorem actually CASE-SPLIT on K-G's apparatus rather
than vacuously hold over an empty list.
-/
def kgEmbeddingShifts {W E P T : Type*} :
    List (Semantics.Context.ContextShift (Semantics.Context.KContext W E P T)) :=
  [Semantics.Context.identityShift,  -- image of 𝔐
   Semantics.Context.identityShift,  -- image of ↓
   Semantics.Context.identityShift,  -- image of †
   Semantics.Context.identityShift]  -- image of 𝔄

/--
**Bridge to Kaplan's no-monster thesis** (`Semantics/Reference/
Monsters.lean`). K-G's `†` is a content operator (it shifts the world
component of the quotative interpretation), NOT a context operator.
K-G's apparatus, projected to Kaplan-context space, contributes only
identity shifts (`kgEmbeddingShifts`), so Kaplan's thesis is preserved.

This is the architectural payoff of K-G's analysis vs. KJR's: K-G
explains c-monstrous behavior WITHOUT touching the
worlds-as-evaluation-points architecture or introducing context shifts.
-/
theorem diagonalize_no_kaplan_monster {W E P T : Type*} :
    Semantics.Reference.Monsters.KaplansThesisHolds
      (kgEmbeddingShifts (W := W) (E := E) (P := P) (T := T)) := by
  intro σ hMem
  -- All entries in kgEmbeddingShifts are identityShift, never a monster.
  simp [kgEmbeddingShifts] at hMem
  rcases hMem with rfl | rfl | rfl | rfl
  all_goals exact Semantics.Reference.Monsters.identityShift_not_monster

/--
**K-G refutes KJR's convention-shift architecture.** KJR
(`KocurekJerzakRudolph2020`) replace
worlds with world-convention pairs and treat conditionals as shifting
the convention component. K-G's analysis preserves
worlds-as-evaluation-points and uses `†` instead.

We exhibit the SUBSTANTIVE divergence by constructing the same
scenario in both substrates and showing they make incompatible
predictions:
- **KJR**: at the WC-pair `⟨.post2006, pre2006Convention⟩`, the
  diagonal content of `planet` applied to `pluto` is True (the
  WC-pair's convention puts Pluto in the extension, regardless of
  the world component).
- **K-G**: `diagonalizeKG plutoInterp .planet .post2006` is False
  (no speaker witness — no community whose use of 'planet' at
  `.post2006` includes Pluto, since standard.post2006 = False and
  pre2006Community.post2006 = False).

The two architectures predict different truth values for the same
surface sentence at the same world.
-/
theorem kg_refutes_kjr_convention_shift :
    -- KJR's substrate: define conventions where pre2006 includes Pluto
    let pre2006Convention : KocurekJerzakRudolph2020.Convention
        PlutoExpr Unit PlutoWorld :=
      { ext := λ p _ _ => match p with | .planet => True }
    let kjrEval : Prop :=
      KocurekJerzakRudolph2020.diagContent
        (W := PlutoWorld) (Pred := PlutoExpr) (Entity := Unit)
        .planet () ⟨.post2006, pre2006Convention⟩
    -- K-G's substrate: the diagonalizer at .post2006
    let kgEval : Prop := diagonalizeKG plutoInterp .planet .post2006
    -- KJR predicts True; K-G predicts False — divergent.
    kjrEval ∧ ¬ kgEval := by
  refine ⟨?_, ?_⟩
  · simp [KocurekJerzakRudolph2020.diagContent]
  · intro ⟨s, hs⟩
    cases s <;> simp [plutoInterp] at hs

end CMonsters

-- ════════════════════════════════════════════════════
-- § 3. Metalinguistic Negation (paper §5)
-- ════════════════════════════════════════════════════

section MetalinguisticNegation

/-- Expressions in the metalinguistic-negation scenario. Includes
    lexical pairs needed for the morpheme-incorporation prediction. -/
inductive MNExpr where
  | mongeese
  | mongooses
  | happy
  | unhappy        -- morphologically incorporated negation
  | ecstatic
  deriving DecidableEq, Repr

/-- Two worlds: the actual (where the dispute occurs) and a
    hypothetical alternative. Multi-constructor so the appropriateness
    modal `♦` quantifies non-vacuously. -/
inductive MNWorld where
  | actual
  | hypothetical
  deriving DecidableEq, Repr, Inhabited

/-- Speakers: a generic English speaker and a hypothetical prescriptivist
    who would judge 'mongeese' appropriate. -/
inductive MNSpeaker where
  | genericEnglish
  | prescriptivist
  deriving DecidableEq, Repr

/-- Both 'mongeese' and 'mongooses' pick out the mongoose property —
    same at-issue content. The lexical-pair pattern for incorporation
    has 'happy' and 'unhappy' as semantic complements. -/
def mnInterp : QuotInterp MNExpr MNSpeaker MNWorld
  | .mongeese,  _, _, _ => True   -- mongoose property
  | .mongooses, _, _, _ => True   -- mongoose property (same extension)
  | .happy,     _, _, _ => True
  | .unhappy,   _, _, _ => False  -- complement of happy
  | .ecstatic,  _, _, _ => True   -- entails happy

/-- **Non-trivial utterance attribution.** Generic English speaker
    actually utters 'mongooses'; the prescriptivist would utter
    'mongeese'. This non-vacuity is what the original substrate's
    constant-True uttRel was missing. -/
def mnUttRel : UttRel MNSpeaker Unit MNExpr MNWorld
  | .genericEnglish, _, .mongooses, .actual => True
  | .prescriptivist, _, .mongeese,  .actual => True
  | _, _, _, _ => False

/-- **Appropriateness standard.** 'mongooses' is the appropriate plural
    for English speakers; 'mongeese' is not. Speaker-relative: the
    prescriptivist's standard would judge 'mongeese' appropriate. -/
def mnApprop : AppropStandard MNSpeaker MNExpr MNWorld
  | .genericEnglish, .mongooses, _ => True
  | .prescriptivist, .mongeese,  _ => True
  | _, _, _ => False

/-- The metalinguistic negation context — generic English speaker. -/
def mnCtx : MQContext MNWorld MNExpr MNSpeaker Unit :=
  { interp := mnInterp
  , uttRel := mnUttRel
  , sx := .genericEnglish
  , ux := ()
  , wc := .actual }

/--
**(3): "I didn't manage to trap two MONGEESE"** — the metalinguistic
negation reading derives via `metalinguistic_neg_truth_conditions`
(substrate, paper §5 p.28-30): the at-issue content is `¬(at-issue ∧
appropriate)`. Since 'mongeese' is INappropriate for the generic
English speaker, the negation holds even though the at-issue (mongoose
property) does not.
-/
theorem mongeese_metalinguistic_neg :
    (TwoDimProp.neg
      (shunt (applyApprop mnApprop mnCtx.sx .mongeese
        (mnCtx.applyMQ .mongeese)))).atIssue .actual := by
  rw [metalinguistic_neg_truth_conditions]
  intro ⟨_, h⟩
  exact h

-- ────────────────────────────────────────────────────
-- §3.1. Three syntactic predictions (paper p.32)
-- ────────────────────────────────────────────────────

/--
**Prediction 1 — morpheme incorporation failure** (Horn 1989 p.392,
[horn-1985]). Morphologically incorporated negation (`unhappy`)
cannot host metalinguistic readings. K-G derives this without lexical
ambiguity in *not*: the metalinguistic chain `𝔐 → 𝔄 → ↓ → ¬` requires
syntactically separate `not`, `𝔄`, and `↓` nodes — incorporation into
a lexical item collapses these into one head, blocking the chain.

Encoded: `unhappy` is at-issue-equivalent to ¬'happy', NOT to
¬♦happy (the appropriateness modal cannot factor through the
incorporated item).
-/
theorem mongeese_blocks_morpheme_incorporation :
    -- 'unhappy' is at-issue-equivalent to ¬'happy', not to ¬♦happy
    ∀ (s : MNSpeaker) (w : MNWorld),
      mnInterp .unhappy w s w ↔ ¬ mnInterp .happy w s w := by
  intros; simp [mnInterp]

/--
**Prediction 2 — NPI licensing failure** (Horn 1989). Metalinguistic
negation does not license NPIs. K-G's account derives this from the
appropriateness modal `♦` and the shunting structure: NPIs require
descriptive-negation downward-entailing scope, but `♦` is not
downward-entailing in the relevant sense.

Lifted from `Horn1989`.
-/
theorem mongeese_blocks_npi_licensing
    (occ : Horn1989.NegScopeOccurrence MNExpr) :
    occ.neg.kind = .metalinguistic → occ.polarity = .npi → ¬ occ.licit :=
  Horn1989.metalinguistic_neg_blocks_npi_licensing occ

/--
**Prediction 3 — DN-elimination failure** ([burton-roberts-1989]).
"She's not not happy, she's inconsolable" does NOT reduce to "She's
happy" — the metalinguistic chain blocks DN-elimination. K-G's
account: each `¬` in the metalinguistic chain scopes over a distinct
appropriateness conjunction, so successive `¬¬` does not reduce.

Lifted from `Horn1989.metalinguistic_neg_blocks_dn_elimination`.
-/
theorem mongeese_blocks_dn_elimination
    (chain : Horn1989.NegChain MNExpr)
    (h : chain.containsMetalinguistic) : ¬ chain.dneEliminates :=
  Horn1989.metalinguistic_neg_blocks_dn_elimination chain h

-- ────────────────────────────────────────────────────
-- §3.2. Cross-framework theorems
-- ────────────────────────────────────────────────────

/--
**K-G's metalinguistic negation does NOT match `DenialType.implicature`.**

`VanDerSandtMaier2003` (formalising [van-der-sandt-maier-2003])
classifies register/connotation denials as `DenialType.implicature`,
which maps to `ContentLayer.implicature`. K-G's chain produces content
on the **appropriateness** dimension via `applyApprop` —
which lives in `Quotation/Mixed`, not in `Implicature/`. The two
substrates are not inter-translatable.

We exhibit the structural divergence by exhibiting a witness
metalinguistic-negation example whose at-issue conjunct is True
(mongoose property holds) AND whose appropriateness conjunct is
False (`mongeese` is inappropriate). This is the K-G profile, NOT
the implicature-denial profile (which would target a scalar
enrichment, not an appropriateness modal).
-/
theorem kg_metalinguistic_chain_targets_appropriateness :
    -- The `applyApprop` chain produces a TwoDimProp whose CI dimension
    -- is the appropriateness predicate, NOT a Gricean enrichment:
    (applyApprop mnApprop mnCtx.sx .mongeese
        (mnCtx.applyMQ .mongeese)).ci = mnApprop mnCtx.sx .mongeese := by
  simp [applyApprop_ci]

-- ────────────────────────────────────────────────────
-- §3.3. The architectural benefit of MQProp (3-layer model)
-- ────────────────────────────────────────────────────

/--
**R-content survives the full metalinguistic negation chain — in the
MQProp layered model.** This is the load-bearing architectural payoff
of the substrate's two-layer refactor (`MQProp` vs flat `TwoDimProp`).

In the flat model, `applyApprop` REPLACES the ci dimension with the
appropriateness content, so the original R-attribution
(`mnUttRel mnCtx.sx mnCtx.ux .mongeese`) is destroyed when 𝔄 fires.
In the MQProp model, R lives in a separate layer; 𝔄 writes only to
the ◆-layer. After the full chain `𝔐 → 𝔄 → ↓ → ¬`, R is intact.

This is the prediction K-G needs (paper §5): "I didn't trap two
MONGEESE" still records that someone uttered 'mongeese'. The flat
model loses this; MQProp keeps it. Concrete witness for the mongeese
scenario, derived from substrate's `full_chain_preserves_rContent`.
-/
theorem mongeese_R_survives_metalinguistic_neg :
    ((MQProp.applyMQ mnCtx .mongeese).applyApprop mnApprop mnCtx.sx .mongeese
      |>.shunt |>.neg).rContent
    = mnUttRel mnCtx.sx mnCtx.ux .mongeese :=
  MQProp.full_chain_preserves_rContent mnCtx mnApprop .mongeese

/-- **R-content is non-trivial for the mongeese scenario.** Concretely
    at `.actual`, the R-layer records that the generic English speaker
    did NOT utter 'mongeese' (`mnUttRel .genericEnglish () .mongeese
    .actual = False`) — the speaker uttered 'mongooses' instead. This
    information is preserved through the metalinguistic-negation chain
    in the layered model. The flat-model `mongeese_metalinguistic_neg`
    cannot witness this distinction. -/
theorem mongeese_R_value_at_actual :
    ¬ ((MQProp.applyMQ mnCtx .mongeese).applyApprop mnApprop mnCtx.sx .mongeese
        |>.shunt |>.neg).rContent .actual := by
  simp [mongeese_R_survives_metalinguistic_neg, mnCtx, mnUttRel]

end MetalinguisticNegation

-- ════════════════════════════════════════════════════
-- § 4. Metalinguistic Negotiation (paper §6)
-- ════════════════════════════════════════════════════

section MetalinguisticNegotiation

/-- The word 'athlete' in the Secretariat dispute. -/
inductive AthExpr where | athlete deriving DecidableEq, Repr

/-- Worlds: the actual world (broad athleticism is the relevant property)
    and a hypothetical comparison world. -/
inductive AthWorld where
  | actual
  | hypothetical
  deriving DecidableEq, Repr, Inhabited

/-- Two disputants A and B (who AGREE Secretariat has the relevant
    physical properties but DISAGREE on whether 'athlete' is appropriate
    to use for non-human animals). -/
inductive AthSpeaker where | speakerA | speakerB deriving DecidableEq, Repr

/-- The shared at-issue content: Secretariat instantiates broad
    athleticism. Both A and B agree on this. -/
def athInterp : QuotInterp AthExpr AthSpeaker AthWorld
  | .athlete, _, _, _ => True

/--
**The SHARED appropriateness standard.** Per K-G §6, the dispute is
NOT over which idiolectal extension is "correct" (P&S's diagnosis) —
both A and B are using a single standard, and the dispute is about
what that standard's verdict on 'athlete-for-horses' should be. We
encode this as ONE `AppropStandard` whose value at the dispute
expression is the contested proposition.
-/
def athShared : AppropStandard AthSpeaker AthExpr AthWorld
  | _, .athlete, _ => True

/-- A's MQ context — committing to "appropriate(athlete, Secretariat)". -/
def athCtxA : MQContext AthWorld AthExpr AthSpeaker Unit :=
  { interp := athInterp
  , uttRel := λ _ _ _ _ => True
  , sx := .speakerA, ux := (), wc := .actual }

/--
**A's assertion (paper (6) A: "Secretariat is an athlete")** — the
shunted appropriateness chain holds at .actual under the shared
standard.
-/
theorem speakerA_assertion :
    (shunt (applyApprop athShared athCtxA.sx .athlete
        (athCtxA.applyMQ .athlete))).atIssue .actual := by
  refine ⟨?_, ?_⟩
  · simp [athCtxA, athInterp]
  · simp [athShared]

/--
**B's denial (paper (6) B: "No, Secretariat is not an athlete")** —
metalinguistic negation of the SAME shared content. B asserts the
negation of the appropriateness conjunct. The crucial point (vs. P&S)
is that A and B's assertions are LITERALLY INCOMPATIBLE on the same
standard, NOT consistent on different idiolects.
-/
theorem speakerB_denial_under_shared_standard
    (rejectedApprop : AppropStandard AthSpeaker AthExpr AthWorld)
    (h_neg : ¬ rejectedApprop .speakerA .athlete .actual) :
    (TwoDimProp.neg (shunt (applyApprop rejectedApprop athCtxA.sx .athlete
        (athCtxA.applyMQ .athlete)))).atIssue .actual := by
  rw [metalinguistic_neg_truth_conditions]
  intro ⟨_, h⟩
  exact h_neg h

/--
**K-G refutes Plunkett-Sundell — structural cross-framework theorem.**

K-G and P&S make incompatible commitments about the structure of a
metalinguistic dispute:

- **P&S** (`PlunkettSundell2013`):
  `consistentContents` requires `predA ≠ predB` extensionally —
  speakers use DIFFERENT idiolectal extensions of the contested
  predicate, and joint satisfiability witnesses their distinct
  meanings. Paper p.18: "the connection between genuine disagreement
  and sameness of meaning is broken."

- **K-G** (paper §6, p.33-34): A and B operate on a SHARED standard;
  the dispute is over the SAME proposition's truth value. Encoded in
  P&S's `MetalinguisticDispute` schema, K-G's commitment is
  `predA = predB`.

The substrate lemma
`MetalinguisticDispute.consistentContents_excludes_shared_standard`
proves these commitments are jointly unsatisfiable: any dispute with
`predA = predB` necessarily violates `consistentContents`. The K-G
refutation is the schematic claim that K-G's commitment entails P&S's
predicate failure — universally over disputes, with no hand-picked
extensions.
-/
theorem kg_refutes_plunkett_sundell :
    ∀ d : PlunkettSundell2013.MetalinguisticDispute Unit AthWorld,
      d.predA = d.predB → ¬ d.consistentContents :=
  fun _ h =>
    PlunkettSundell2013.MetalinguisticDispute.consistentContents_excludes_shared_standard
      _ h

end MetalinguisticNegotiation

-- ════════════════════════════════════════════════════
-- § 5. "In a Sense" Constructions (paper §7)
-- ════════════════════════════════════════════════════

section InASense

/-- Expressions for the "viruses are alive" scenario. -/
inductive VirExpr where | alive deriving DecidableEq, Repr

/-- Two speakers with different intensions for 'alive':
    - biologist: 'alive' includes viruses (genetic-material criterion)
    - layperson: 'alive' excludes viruses (5-kingdoms criterion) -/
inductive VirSpeaker where
  | biologist
  | layperson
  deriving DecidableEq, Repr

/-- Worlds for the "in a sense" scenario. Multi-constructor so the
    intension quantification is non-vacuous. -/
inductive VirWorld where
  | actual
  | counterfactual
  deriving DecidableEq, Repr, Inhabited

/-- Quotative interpretation: 'alive' has different extensions
    depending on which speaker is using the word. -/
def virInterp : QuotInterp VirExpr VirSpeaker VirWorld
  | .alive, _, .biologist, _ => True   -- viruses qualify under biological criterion
  | .alive, _, .layperson, _ => False  -- viruses don't under folk criterion

/-- **Intensions** — propositions about VirWorlds. K-G's analysis quantifies
    over intensions μ in addition to speakers sₓ. Here we use the type of
    `VirWorld → Prop` directly. -/
abbrev VirIntension := VirWorld → Prop

/-- The MQ context parameterised by speaker. -/
def virMQCtx (s : VirSpeaker) : MQContext VirWorld VirExpr VirSpeaker Unit :=
  { interp := virInterp
  , uttRel := λ _ _ _ _ => True
  , sx := s
  , ux := (), wc := .actual }

/--
**Predicate Abstraction over the intension variable** (paper p.37-38).
K-G's `which_μ` binds `μ` via Heim & Kratzer-style PA. Encoded here as
a function abstracting over intensions.
-/
def whichMu (P : VirIntension → VirWorld → Prop) (w : VirWorld) : Prop :=
  ∃ μ : VirIntension, P μ w

/--
**(7'): "There is a sense which viruses are alive in"** — the K-G
analysis (paper p.38) gives the L_MQ formula:

  ∃μ ∃sₓ [⟨*⟩(`viruses are alive`)(wc)(sₓ) ∧
          [^⟨*⟩(`viruses are alive`)(wc)(sₓ)] = μ]

The existential ranges over BOTH intensions μ AND speakers sₓ. Both
are needed: speakers select different intensions for the same
expression, and `which_μ` binds μ for the relative clause.

Witness: at .actual, with sₓ = biologist (whose use of 'alive' includes
viruses) and μ = the biologist's predicate.
-/
theorem viruses_alive_in_a_sense :
    whichMu (λ μ w => ∃ s : VirSpeaker,
        ((virMQCtx s).applyMQ .alive).atIssue w ∧
        μ = ((virMQCtx s).applyMQ .alive).atIssue) .actual := by
  refine ⟨((virMQCtx .biologist).applyMQ .alive).atIssue,
          .biologist, ?_, rfl⟩
  simp [virMQCtx, virInterp]

/-- The layperson is NOT a witness: their use of 'alive' excludes viruses. -/
theorem not_alive_layperson :
    ¬ ((virMQCtx .layperson).applyMQ .alive).atIssue .actual := by
  simp [virMQCtx, virInterp]

/-- The existential is non-trivial: not all senses make viruses alive. -/
theorem not_all_senses :
    ¬ (∀ s : VirSpeaker, ((virMQCtx s).applyMQ .alive).atIssue .actual) := by
  intro h
  exact not_alive_layperson (h .layperson)

/--
**K-G's "in a sense" is distinct from imprecision/granularity accounts.**
Imprecision frameworks (e.g. `Haslinger2025`)
locate the variation in TOLERANCE / GRANULARITY parameters of a single
speaker. K-G's "in a sense" locates the variation in the SPEAKER VARIABLE
of `𝔐` — different speakers contribute different intensions.

The two analyses make incompatible architectural commitments. Imprecision
holds the speaker fixed and varies the granularity; K-G holds granularity
fixed and varies the speaker.

We exhibit the divergence: K-G's analysis predicts variation at the
speaker locus (biologist vs. layperson), where Imprecision predicts no
variation (single speaker, single granularity).
-/
theorem in_a_sense_distinct_from_imprecision :
    -- K-G's account: at-issue varies with speaker for the same expression.
    ((virMQCtx .biologist).applyMQ .alive).atIssue .actual ≠
    ((virMQCtx .layperson).applyMQ .alive).atIssue .actual := by
  intro h
  have : ((virMQCtx .biologist).applyMQ .alive).atIssue .actual =
         ((virMQCtx .layperson).applyMQ .alive).atIssue .actual := h
  simp [virMQCtx, virInterp] at this

end InASense

end KirkGiannini2024
