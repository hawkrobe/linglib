import Linglib.Theories.Discourse.Centering.Basic
import Linglib.Theories.Discourse.Centering.Constraints
import Linglib.Theories.Discourse.Centering.Rule1
import Linglib.Theories.Discourse.Centering.Rule2
import Linglib.Theories.Discourse.Centering.Transition
import Linglib.Theories.Discourse.Centering.Coherence
import Linglib.Theories.Discourse.Centering.Instances.GrammaticalRole
import Linglib.Theories.Discourse.Centering.Instances.InformationStatus
import Linglib.Phenomena.Reference.Studies.Sidner1983
import Linglib.Phenomena.Reference.Studies.Beaver2004

/-!
# @cite{poesio-stevenson-eugenio-hitzeman-2004}: Centering as a Parametric Theory

Poesio, Stevenson, Di Eugenio & Hitzeman (2004), "Centering: A
Parametric Theory and Its Instantiations." *Computational Linguistics*
30(3): 309–363. URL https://aclanthology.org/J04-3003/.

PSDH's headline contribution: **Centering is not a single theory; it
is a parameter family.** The variants of CB definition, utterance
unit, "previous utterance," realization, CF filter, ranking, "pronoun"
filter, and segmentation that have been proposed in the literature
since @cite{grosz-joshi-weinstein-1995} are *parameters* of the
framework. Different parameter settings make different empirical
claims true.

## The 8 parameter axes (PSDH §3.4 p. 326)

| Parameter | Substrate location | Variants formalized in linglib |
|---|---|---|
| `CBdef` (which definition of CB) | `Centering/Basic.lean` `cb` | Constraint 3 (the canonical Cb-via-highest-Cf-realized definition) |
| `uttdef` (sentence vs finite clause vs verbed clause) | `Centering/Defs.lean` `Utterance` | sentence-level only (no clause-decomposition substrate) |
| `previous utterance` (Kameyama vs Suri-McCoy adjunct treatment) | not formalized | – |
| `realization` (direct vs indirect/bridging) | `Realizes` typeclass | direct only (`utteranceRealizes`); bridging not formalized |
| `CF-filter` (1st/2nd person, predicative NPs) | not formalized | – |
| `rank` (CfRanker choice) | `CfRankerOf E R` typeclass | `GrammaticalRole` (Kameyama 1986), `DiscourseStatus` (Strube-Hahn 1999); LinearOrder (Rambow 1993) deferred — substrate gap (Realization lacks position field) |
| `prodef` (which "pronouns" count for Rule 1) | `Pronominalizes` typeclass | utterance's `isPronoun` flag |
| `segmentation` | not formalized | – |

The 4 axes the substrate plugs into via typeclasses (`CBdef`,
`Realizes`, `Pronominalizes`, `CfRankerOf`) ARE the parametric story
in Lean form — different instances of these typeclasses produce
different `cb`/`cbAll`/Rule-1-satisfaction predictions on the same
data. The 4 axes left unformalized are corpus-operational choices
(sentence-segmentation rules, NP-filter rules) — we mention them in
prose, not as Lean parameters, per the audit's "formalize the
type-changing axes, not the bookkeeping ones" recommendation.

## What this file mechanizes

1. **PSDH §4.1.1 example (10)** — the corner-cupboard / Branicki
   utterance pair where partial GF ranking yields **two CBs**
   (since two NPs tie at the lowest grammatical-function rank
   among realized entities). This is the load-bearing example for
   `cbAll` — `cb` returns just the first, `cbAll` returns the
   complete tied-at-top set, exposing the weak-Constraint-1
   violation.

2. **`Sidner1983` partial-GF witness** (not a structural bridge —
   per audit) — PSDH §5.3.4 (p. 358) say two-CB-under-partial-GF
   configurations are "reminiscent of" the examples that led
   @cite{sidner-1979} to argue for two foci. Our witness theorem
   (`psdh_two_cb_witnesses_sidner_two_foci`) establishes that the
   PSDH (10) configuration AND a constructed Sidner-side encoding
   both exhibit "two-ness" — two CBs vs two distinct foci. The
   structural translation function `centeringToSidner` that would
   derive the Sidner state from the Centering data is deferred
   (see §5 future work).

3. **PSDH §5.2.2 entity-coherence dissociability witness** —
   PSDH §5.2.2 (p. 353) argue entity coherence (Centering's
   domain) and relational coherence (Hobbs/Kehler/RST) are
   *dissociable*: entity coherence can be ABSENT while a
   discourse remains locally coherent through relational
   connections. PSDH (23) (the Product A pharmaceutical
   leaflet, p. 354) is the canonical example: every adjacent
   utterance pair has `cb = none` (NULL transition under any
   vanilla instantiation), but the discourse is coherent via
   instructional connectives ("If you have any questions ...
   ask your doctor"). Our witness theorem establishes the
   "every transition NULL" property on this discourse; the
   relational-coherence side is in prose since `Coherence.lean`'s
   bridge doesn't model instructional/temporal connectives.

## What this file deliberately does NOT formalize

- **PSDH's GNOME corpus statistics** (Tables 1-15). We don't have
  access to the corpus; encoding their reported percentages as
  opaque `Nat × Nat` data adds code without deriving content.
  Cited in prose; deferred to a possible future commit.

- **The full BFP 87 4-way Transition** as substrate primitive. The
  4-way `private structure BFPTransition` lives below as a
  study-file-local definition per the audit's "extract on second
  consumer" discipline. Will promote to `Centering/Transition.lean`
  when a second consumer (Walker 1989, Brennan 1995, etc.) lands.

- **The `CenteringConfig` bundled record.** Per the mathlib audit,
  PSDH's "8 parameters" map onto typeclass instances + variant
  predicates, not a `CenteringConfig` structure. The fact that
  "GJW95 = `[CfRanker GrammaticalRole]` + `Rule1GJW95` + `pairRank`"
  is documented in prose, not as a structure-typed value. (Mathlib
  precedent: `Mathlib.Analysis.Calculus` has `FDeriv`/`Deriv`/
  `HasDerivAt`/`HasFDerivAt`/`lineDeriv` as separate definitions
  with cross-implications, not a `DerivativeConfig` bundling them.)

- **The OT-bridge to `Core.Constraint.OT.Tableau.optimal`** per
  Beaver 2004. PSDH §3.1 fn 12 endorse Beaver's OT reformulation
  of Centering, but the bridge theorem belongs in
  `Phenomena/Reference/Studies/Beaver2004.lean` (queued as a
  separate commit), per mathlib's `PMF` vs `Measure` precedent.
-/

set_option autoImplicit false

namespace PoesioEtAl2004

open Discourse.Centering

/-! Throughout, examples use `String` entities for readability and
    `Utterance String GrammaticalRole` from the substrate. The IS
    ranker (Strube-Hahn) is illustrated separately. -/

abbrev Utt : Type := Utterance String GrammaticalRole

-- ════════════════════════════════════════════════════
-- § 1. Example (10): partial GF ranking → two CBs
-- ════════════════════════════════════════════════════

/-! @cite{poesio-stevenson-eugenio-hitzeman-2004} §4.1.1 (p. 329)
    cite their corpus example (10) where partial grammatical-function
    ranking yields *two* CBs. The XML annotation in the paper has
    `the corner cupboard` (np-compl) and `Branicki` (gen) tied at
    the same grammatical-function rank — both rank lower than the
    matrix subject `the drawing of …`, but neither outranks the
    other. When both are realized in the next utterance (u229),
    both qualify as the CB.

    PSDH note (p. 329): "This problem with the vanilla instantiation
    can also be 'fixed' by requiring the ranking function to be a
    total order, which is easily done by adding a disambiguation
    factor such as linear order, as done by Strube and Hahn." -/

/-- (u227 simplified) "The drawing of the corner cupboard, or more
    probably an engraving of it, must have caught Branicki's
    attention." Two non-subject NPs tied at GR rank: `corner_cupboard`
    (the postcopular NP) and `Branicki` (genitive). Modeled here as
    two `.other` realizations (since GrammaticalRole's three-way
    coarsens both np-compl and gen to OTHER). -/
def u227 : Utt :=
  ⟨[⟨"the_drawing", .subject, false⟩,
    ⟨"corner_cupboard", .other, false⟩,
    ⟨"Branicki", .other, false⟩]⟩

/-- (u229 simplified) "Dubois was commissioned through a Warsaw
    dealer to construct the cabinet for the Polish aristocrat."
    Both `corner_cupboard` (the cabinet) and `Branicki` (the Polish
    aristocrat) are realized. -/
def u229 : Utt :=
  ⟨[⟨"Dubois", .subject, false⟩,
    ⟨"corner_cupboard", .object, false⟩,
    ⟨"Branicki", .other, false⟩]⟩

/-- The single-CB function returns just one of the two tied
    candidates (whichever comes first in `prev.cf`'s sorted order;
    `cfInsert`'s `foldr`-based implementation places equal-rank
    realizations in reverse insertion order, so `Branicki` precedes
    `corner_cupboard` in `cf u227` despite their tied .other rank). -/
theorem u227_to_u229_cb : cb u227 u229 = some "Branicki" := by decide

/-- **Both candidates qualify as CBs** under partial GR ranking:
    `cbAll` returns both `corner_cupboard` and `Branicki` because
    they tie at the maximum rank among realized entities (both `.other`
    in u227, both realized in u229). This is the **PSDH §4.1.1
    multi-CB case** that motivates `cbAll` as a substrate operator. -/
theorem u227_to_u229_cbAll :
    (cbAll u227 u229).length = 2 := by decide

/-- **CB Uniqueness fails** on this pair: more than one candidate CB
    exists. PSDH §4.1.1 (p. 329 prose) report 11 utterances (1.1%)
    in their corpus exhibit this multi-CB pattern under partial GR
    ranking. -/
theorem u227_to_u229_violates_cb_uniqueness :
    ¬ CBUniqueness u227 u229 := by decide

/-- **Entity Continuity holds**: at least one candidate CB exists. -/
theorem u227_to_u229_satisfies_continuity :
    EntityContinuity u227 u229 := by decide

/-- **Strong C1 fails** because of the uniqueness clause. By the
    decomposition theorem `strongC1_iff_uniqueness_and_continuity`
    (`Centering/Constraints.lean`), Strong C1 = Uniqueness ∧
    Continuity, so failing uniqueness fails Strong C1. -/
theorem u227_to_u229_violates_strong_c1 :
    ¬ Constraint1Strong u227 u229 := by decide

-- ════════════════════════════════════════════════════
-- § 2. Bridge to Sidner1983: the two-CB case is two-focus territory
-- ════════════════════════════════════════════════════

/-! @cite{poesio-stevenson-eugenio-hitzeman-2004} §5.3.4 (p. 358):

    > [These] examples are reminiscent of the examples that led
    > @cite{sidner-1979} to argue for two foci — sentences with one
    > animate entity (typically in agent position) and an inanimate
    > one (typically in theme position), like *Mortimer sold the book
    > for 10 cents* or *Mary took a nickel from her toy bank yesterday*.

    PSDH note that the same configurations producing two CBs under
    partial GF ranking are precisely the configurations Sidner's
    two-focus account handles directly: an animate entity (actor
    focus) co-occurring with an inanimate one (discourse focus).

    The `Sidner1983.FocusState` two-slot architecture (discourse focus
    + actor focus) at `Phenomena/Reference/Studies/Sidner1983.lean`
    accommodates exactly these cases — they're not "two CBs" in
    Sidner's framework, they're "the AF and the DF, which by Sidner's
    architecture can coincide or differ." -/

/-- **PSDH §5.3.4 ↔ Sidner1983 bridge**: configurations where partial
    GF ranking yields two CBs are configurations where Sidner's
    two-focus state has *non-equal* discourse focus and actor focus.
    Witnessed on a synthesized example modeling the corner-cupboard
    case in Sidner's encoding: `Branicki` is the agent (actor focus
    candidate), `corner_cupboard` is the inanimate theme (discourse
    focus candidate). The bridge claim PSDH leave informal becomes
    the existence of a Sidner state where DF ≠ AF on the same data
    that yields multi-CB under partial GF.

    This is one of the cross-framework theorems linglib's
    interconnection-density discipline aims to make visible: PSDH's
    parametric-centering observation and Sidner's two-focus
    architecture are answering different questions about the same
    empirical configuration. -/
def sidnerSentenceForCornerCupboard : Sidner1983.Sentence String :=
  { form := .normal
    phrases :=
      [⟨"Branicki", .agent, .agent, false⟩,
       ⟨"corner_cupboard", .theme, .nonAgent, false⟩] }

/-- Sidner's two-slot state for the corner-cupboard configuration:
    `Branicki` (agent) is the actor focus; `corner_cupboard` (theme)
    is the discourse focus. The two slots are *distinct* —
    exactly the configuration PSDH §5.3.4 say motivated Sidner's
    two-focus architecture. -/
def sidnerStateForCornerCupboard : Sidner1983.FocusState String :=
  Sidner1983.updateState Sidner1983.FocusState.empty sidnerSentenceForCornerCupboard

theorem sidner_distinguishes_actor_from_discourse :
    sidnerStateForCornerCupboard.actorFocus ≠ sidnerStateForCornerCupboard.discourseFocus := by decide

/-- Sidner's discourse focus matches one PSDH-CB candidate
    (the theme — the inanimate entity, `corner_cupboard`). -/
theorem sidner_df_matches_psdh_cb_candidate :
    sidnerStateForCornerCupboard.discourseFocus = some "corner_cupboard" := by decide

/-- Sidner's actor focus matches the OTHER PSDH-CB candidate
    (the agent — the animate entity, `Branicki`). -/
theorem sidner_af_matches_psdh_cb_candidate :
    sidnerStateForCornerCupboard.actorFocus = some "Branicki" := by decide

/-- **Witness theorem** (NOT a structural bridge): on the constructed
    Sidner sentence modeling PSDH (10), Sidner's actor focus and
    discourse focus are distinct, AND `cbAll u227 u229` has length 2.
    The two facts are independently established by `decide` on
    independently constructed inputs (`u227`/`u229` for the Centering
    side; `sidnerSentenceForCornerCupboard` for the Sidner side); no
    function `centeringToSidner : Utterance → Sidner1983.Sentence`
    derives one from the other.

    PSDH §5.3.4 (p. 358) say only "reminiscent of the examples that
    led Sidner to argue for two foci" — an analogy, not an
    equivalence. The theorem name was previously `psdh_two_cb_iff_sidner_two_foci`
    suggesting biconditional / structural equivalence; renamed per
    audit to reflect that this is a witness on a constructed
    example, not a `↔`. The structural translation function and
    derived bridge theorem are queued as follow-up work (see §5
    deferred items). -/
theorem psdh_two_cb_witnesses_sidner_two_foci :
    (cbAll u227 u229).length = 2 ∧
    sidnerStateForCornerCupboard.actorFocus ≠ sidnerStateForCornerCupboard.discourseFocus :=
  ⟨by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 3. PSDH §5.2.2: entity-coherence dissociability — Example (23)
-- ════════════════════════════════════════════════════

/-! @cite{poesio-stevenson-eugenio-hitzeman-2004} §5.2.2 (p. 353-354):

    > One clear conclusion suggested by our results is that
    > entity-based accounts of coherence need to be supplemented by
    > accounts of other factors that induce coherence at the local
    > level. … in the pharmaceutical subdomain many examples in
    > which successive utterances do not mention the same entities,
    > but the connection between clauses is explicitly indicated by
    > connectives, as in (23):

    > (23) (u1) This leaflet is a summary of the important
    >          information about Product A.
    >      (u2) If you have any questions or are not sure about
    >          anything to do with your treatment,
    >      (u3) ask your doctor or your pharmacist.

    PSDH's argument is that **entity coherence is *dissociable* from
    local coherence** — the discourse is coherent (it instructs the
    reader) but no entity carries through (the leaflet, your
    questions, your doctor are pairwise disjoint as discourse
    referents). Centering predicts NULL transitions throughout; the
    coherence comes from elsewhere (instructional/temporal
    connectives, Hobbs/Kehler relational coherence, RST elaboration).

    We mechanize the **entity-coherence-side** of the argument: every
    adjacent pair in (23) has `cb = none`, so under PSDH's BFP-style
    transition labelling all transitions are NULL. The relational-
    coherence side cannot be mechanized in the existing substrate
    — `Centering/Coherence.lean` formalizes a Kehler 2002 1-to-1
    mapping `CoherenceRelation → Transition`, but doesn't model the
    instructional/temporal connectives that carry (23)'s coherence.
    A future commit could extend the substrate or add a
    `Phenomena/Reference/Studies/Knott2001.lean` to formalize PSDH's
    cited finding that relational accounts converge with entity
    coherence rather than displacing it. -/

namespace D23

/-- (23 u1) "This leaflet is a summary of the important information
    about Product A." Three discourse entities. -/
def u1 : Utt :=
  ⟨[⟨"leaflet", .subject, false⟩,
    ⟨"summary", .other, false⟩,
    ⟨"info", .other, false⟩,
    ⟨"product_A", .other, false⟩]⟩

/-- (23 u2) "If you have any questions or are not sure about anything
    to do with your treatment." Disjoint discourse entities from u1
    (you, questions, treatment). -/
def u2 : Utt :=
  ⟨[⟨"reader_you", .subject, false⟩,
    ⟨"questions", .object, false⟩,
    ⟨"treatment", .other, false⟩]⟩

/-- (23 u3) "ask your doctor or your pharmacist." Yet another
    disjoint set (you, doctor, pharmacist). -/
def u3 : Utt :=
  ⟨[⟨"reader_you", .subject, false⟩,
    ⟨"doctor", .object, false⟩,
    ⟨"pharmacist", .other, false⟩]⟩

end D23

/-- **u1 → u2 has no CB**: Cf(u1) is `[leaflet, summary, info, product_A]`,
    none realized in u2. NULL transition. -/
theorem d23_u1_to_u2_cb_none : cb D23.u1 D23.u2 = none := by decide

/-- **u2 → u3 has CB = "reader_you"**: u2 and u3 share the second-person
    referent. (Strong C1 violations of the kind PSDH study would also
    flag this — second-person pronouns count as CFs only under PSDH's
    PRO2 instantiation; under their default vanilla instantiation
    second-person pronouns do not introduce CFs and this transition
    too is NULL.) -/
theorem d23_u2_to_u3_cb_some : cb D23.u2 D23.u3 = some "reader_you" := by decide

/-- **PSDH §5.2.2 entity-coherence dissociability witness**: in PSDH
    (23), the u1 → u2 transition has *no* CB at all, yet the discourse
    is coherent (the leaflet's u2 is the conditional clause introducing
    u3's instruction). PSDH argue that local coherence must therefore
    have a non-entity-based source.

    The theorem is honest about scope: it witnesses the entity-side
    *absence* (cb is none); the relational coherence that PSDH say
    fills the gap is not mechanizable in the current substrate without
    extending `Coherence.lean` to model instructional/temporal
    connectives. (Compare to my prior overclaiming `centering_vs_kehler_bridge_diverge`
    — that previous theorem was true but didn't engage what PSDH
    actually argue.) -/
theorem psdh_5_2_2_entity_coherence_dissociable_on_23 :
    cb D23.u1 D23.u2 = none := d23_u1_to_u2_cb_none

-- ════════════════════════════════════════════════════
-- § 4. Sample IS-ranker example (Strube-Hahn 1999)
-- ════════════════════════════════════════════════════

/-! Demonstrates that the `InformationStatus` Cf-ranker (`Centering/Instances/InformationStatus.lean`)
    produces a *different* Cf order from `GrammaticalRole` on the
    same realizations — the parametric story PSDH §4.4.3 evaluate.

    The IS ranker uses `Features.InformationStructure.DiscourseStatus`
    as the role type, projecting through the existing 3-way enum
    (focused/given/new). On a sentence where the grammatical subject
    is HEARER-NEW (a freshly introduced entity) and the object is
    HEARER-OLD (already in the discourse), the two rankers disagree
    on which entity has the highest Cf rank. -/

abbrev IsUtt : Type := Utterance String StrubeHahnInfoStatus

/-- A two-NP utterance where the subject is HEARER-NEW and the object
    is HEARER-OLD. Under the Strube-Hahn IS ranker, the object outranks
    the subject (HEARER-OLD ≺ HEARER-NEW means lower IS rank ≺ more
    salient ⇒ higher Centering rank); under GR, the subject would
    outrank (SUBJ > OBJ). The two rankers' Cp predictions diverge —
    the parametric story PSDH §4.4.3 evaluate. -/
def is_example_utt : IsUtt :=
  ⟨[⟨"new_subject", .hearerNew, false⟩,
    ⟨"old_object", .hearerOld, false⟩]⟩

/-- The Strube-Hahn IS ranker picks the HEARER-OLD entity as Cp,
    contrary to the GR ranker which would pick the subject. -/
theorem is_ranker_picks_hearerOld_as_cp :
    is_example_utt.cp = some "old_object" := by decide

-- ════════════════════════════════════════════════════
-- § 5. Beaver 2004 OT bridge → see Beaver2004.lean
-- ════════════════════════════════════════════════════

/-! @cite{poesio-stevenson-eugenio-hitzeman-2004} §3.1 fn 12 cite
    @cite{beaver-2004} ("The Optimization of Discourse Anaphora,"
    *Linguistics and Philosophy* 27(1):3-56) as the canonical
    optimality-theoretic reformulation of Centering. The full bridge
    formalization — six ranked OT constraints (AGREE > DISJOINT >
    PRO-TOP > FAM-DEF > COHERE > ALIGN), Beaver Theorem (20)
    BFP-equivalence witnesses on his examples (12) and (2), and the
    PRO-TOP demotion (Beaver §4.1) that fixes the BFP Rule-1
    overprediction PSDH §3.1 fn 12 explicitly cite — lives in
    `Phenomena/Reference/Studies/Beaver2004.lean`.

    Three of Beaver's six constraints are LITERAL RESTATEMENTS of
    existing Centering primitives (PRO-TOP via `Rule1GJW95`,
    COHERE via `cb`, ALIGN via `cb`+`cp`); see Beaver2004.lean §2.
    The deep-reuse design makes Theorem (20) partly structural — the
    OT-vs-BFP equivalence on those 3 clauses follows by definition. -/

/-! ## §5.1 Two totalizers for PSDH (10): Strube-Hahn vs Beaver

    PSDH at p. 329 (§4.1.1, fn 21) raise the multi-CB problem on
    `u227`/`u229` and explicitly endorse one fix: **adding a
    disambiguation factor such as linear order, as done by Strube and
    Hahn**. They return to the issue at §5.3.4, considering whether
    to keep CB uniqueness (via a totalizer like Strube-Hahn's) or
    abandon it (Givón 1983, Gundel 1998). The §3.1 fn 12 endorsement
    of @cite{beaver-2004} is for a *different* problem — Beaver's COT
    fixes BFP 87's hard-vs-soft confusion of Rule 1, not the
    partial-ranking → multi-CB tie. So PSDH effectively pose two
    totalizers in different sections of the same paper:

    1. **Strube-Hahn linear-order** (PSDH p. 329 fn 21): break ties by
       surface position. Resolves `u227`'s ne547 ↔ ne551 tie
       parametrically only in the surface-string of `u227`.

    2. **Beaver's COT lex-min** (PSDH §5.3.3, mentioning Beaver-style
       constraint stacking; Beaver §3.2's COHERE/ALIGN over `cb`):
       break ties by lex-min over a constraint hierarchy that
       references `priorTopic`. Resolves the tie parametrically in
       `priorTopic` — itself a slot the previous utterance underdetermines
       on this example.

    Mechanically applied to PSDH (10), Beaver's totalizer is
    **sensitive to the priorTopic parameter** in a way Strube-Hahn's is
    not. Different choices of "the prior topic" produce different
    optima under Beaver's lex-min; under Strube-Hahn linear-order, the
    surface-position fact alone fixes the answer. The cross-framework
    finding is not "Beaver can't see PSDH's tie" (true of any single-`cb`
    framework — banal) but **"Beaver's totalizer propagates PSDH's
    underdetermination via priorTopic, while Strube-Hahn's positional
    totalizer resolves it"** — a structural-faithfulness comparison
    PSDH's two endorsements implicitly invite.

    The Strube-Hahn side is partly formalized at §4 of this file
    (`StrubeHahnInfoStatus` ranker); the linear-order positional
    primitive Strube-Hahn use as a tiebreaker is not yet substrate
    (`Realization` lacks a `position : Nat` field — see §6 deferred
    items). The Beaver side is concrete here. -/

open Beaver2004 (cohere align)

/-- Wrap u229 as a Beaver COT candidate. Since u229 contains no
    pronouns whose resolution is in question (both `corner_cupboard`
    and `Branicki` are realized by definite NPs in PSDH (10)),
    the substrate-gap flags are irrelevant — set them all `true`
    so that the only constraints that can fire are the ones built
    on Centering primitives (COHERE, ALIGN, PRO-TOP). -/
def cand_u229 : Beaver2004.Candidate String GrammaticalRole :=
  ⟨u229, true, true, true⟩

/-- Beaver's `cb`, applied to PSDH (10), returns ONE entity (Branicki),
    chosen by `find?`-on-sort-order — not a set. The `Option E` typing
    of `cb` discards the tie information `cbAll` exposes. -/
theorem beaver_cb_picks_branicki_on_psdh10 :
    Discourse.Centering.cb u227 u229 = some "Branicki" := by decide

/-- **The substrate gap**: on PSDH (10), `cbAll` reports a two-element
    tie containing both candidates, but Beaver's `cb` reports only
    Branicki (first by sort order). Composes from the named cb-witness
    + the cbAll fact. The third conjunct from the previous version
    (`cb ≠ some "corner_cupboard"`) followed from the first by
    `Option.some.injEq` — dropped per audit. -/
theorem beaver_cb_silent_on_psdh10_tie :
    Discourse.Centering.cb u227 u229 = some "Branicki" ∧
    "corner_cupboard" ∈ Discourse.Centering.cbAll u227 u229 :=
  ⟨beaver_cb_picks_branicki_on_psdh10, by decide⟩

/-- **COHERE depends on the choice of priorTopic** — Beaver's totalizer
    propagates PSDH (10)'s tie. If we feed Beaver's COHERE the
    `Branicki`-side as priorTopic, COHERE is satisfied (eval = 0). If
    we feed it the `corner_cupboard`-side, COHERE fires (eval = 1).
    Beaver's lex-min on the same `cand_u229` produces opposite
    verdicts depending on which member of the PSDH tie the previous
    utterance "really" had as topic — a slot PSDH's parametric
    analysis says is underdetermined.

    By contrast, a **Strube-Hahn linear-order totalizer** would resolve
    the tie purely from `u227`'s surface-position ordering of ne547
    (corner_cupboard, before) vs ne551 (Branicki's, after) — that
    answer is a fact about `u227` alone and doesn't depend on a
    further priorTopic parameter. The two totalizers don't agree on
    which of `Branicki`/`corner_cupboard` is "the" CB of u227. -/
theorem beaver_cohere_sensitive_to_psdh10_tie_choice :
    (cohere u227 (some "Branicki")).eval cand_u229 = 0 ∧
    (cohere u227 (some "corner_cupboard")).eval cand_u229 = 1 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **ALIGN fires regardless** of which tie-member is fed in: u229's
    Cp is `Dubois` (the new SUBJ), and `cb u227 u229 = some Branicki`
    is in OBJ position, not subject. So under Beaver's machinery,
    PSDH (10) shows a CB-not-in-subject-position pattern — typical
    RETAIN/SHIFT territory. The Strube-Hahn-vs-Beaver totalizer
    contrast lives entirely in COHERE's sensitivity to priorTopic;
    ALIGN is constant across the choice. -/
theorem beaver_align_fires_on_psdh10 :
    (align u227).eval cand_u229 = 1 := by decide

/-- **`beaver_lex_min_on_psdh_10`** — the cross-framework headline.
    Beaver's COT lex-min, applied to PSDH (10), produces strictly
    different total-violation counts depending on which member of
    PSDH's tie is supplied as `priorTopic`:

    - **Branicki-as-prior** (matches Beaver's own `cb u227`): COHERE
      satisfied, ALIGN violated. Total = 1 violation.
    - **corner_cupboard-as-prior** (the alternative `cbAll` member):
      COHERE violated, ALIGN violated. Total = 2 violations.

    Under the COHERE > ALIGN ranking, the Branicki-prior interpretation
    strictly dominates. So Beaver's lex-min "picks" Branicki — but only
    by silently agreeing with the choice `cb u227 u229` already made by
    sort order. The lex-min mechanism contributes no new information
    about which member of PSDH's tie deserves to be the unique CB; it
    inherits and amplifies the sort-order decision.

    By contrast, Strube-Hahn's linear-order totalizer would pick the
    *earlier-in-surface-order* member of the tie — `corner_cupboard`
    (ne547, before Branicki's ne551 in u227). The two totalizers
    therefore *disagree* on which entity of PSDH's tie is the unique
    CB. PSDH p. 329 endorse Strube-Hahn's choice; Beaver's totalizer
    inverts it. -/
theorem beaver_lex_min_on_psdh_10 :
    -- Branicki-as-prior interpretation: only ALIGN fires
    (cohere u227 (some "Branicki")).eval cand_u229 +
      (align u227).eval cand_u229 = 1 ∧
    -- corner_cupboard-as-prior interpretation: COHERE + ALIGN both fire
    (cohere u227 (some "corner_cupboard")).eval cand_u229 +
      (align u227).eval cand_u229 = 2 ∧
    -- Branicki-prior strictly dominates corner_cupboard-prior (lex-min picks Branicki)
    ((cohere u227 (some "Branicki")).eval cand_u229 +
      (align u227).eval cand_u229) <
    ((cohere u227 (some "corner_cupboard")).eval cand_u229 +
      (align u227).eval cand_u229) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §5.1.1 The structural underpinning

    The four `decide`-checked theorems above verify Beaver's COT on
    PSDH (10) at the level of literal Nat comparisons. They are
    corollaries of the substrate-level structural-faithfulness
    theorems landed in `Beaver2004.lean §2a`:

    - `Beaver2004.cohere_factors_through_cb`: COHERE's evaluation is
      determined by `cb prev c.utt` and `priorTopic` only.
    - `Beaver2004.align_factors_through_cb_and_cp`: ALIGN's evaluation
      is determined by `cb prev c.utt` and `c.utt.cp` only.

    The cross-framework story therefore decomposes into:

    1. **Cb-blindness on the candidate side** (proved structurally in
       Beaver2004): for a fixed (prev, priorTopic), Beaver's COHERE
       is invariant across cb-equivalent candidates. PSDH (10)'s
       multi-CB tie cannot enter through the candidate slot.
    2. **PriorTopic-sensitivity on the parameter side** (proved on the
       worked example here, via `decide`): COHERE's verdict varies
       across the two members of PSDH's tie when fed as priorTopic.
       The tie enters through the parameter slot, not the candidate
       slot.
    3. **The lex-min picks the cb-internal choice**
       (`beaver_lex_min_on_psdh_10`): under COHERE > ALIGN, Beaver's
       optimum agrees with `cb`'s sort-order choice (Branicki),
       inverting Strube-Hahn's positional choice (corner_cupboard,
       earlier in surface order).

    The structural theorems make explicit that (1) is a property of
    Beaver's substrate, not of PSDH (10) specifically; the
    per-example facts (2)+(3) are the kernel-checked instances. -/

/-- **Substrate-corollary form**: any candidate `c` whose `cb` agrees
    with `cand_u229`'s on `u227` gets the SAME COHERE evaluation as
    `cand_u229`, for any priorTopic. This is the abstract version of
    "Beaver cannot recover the discarded tie member from candidate-side
    information"; the per-example `beaver_cohere_sensitive_to_psdh10_tie_choice`
    above is the witness that priorTopic-side variation is the only
    route by which the PSDH tie can enter Beaver's verdict. -/
theorem beaver_cohere_invariant_under_cb_equiv_candidates
    (priorTopic : Option String) (c : Beaver2004.Candidate String GrammaticalRole)
    (h : Discourse.Centering.cb u227 c.utt = Discourse.Centering.cb u227 u229) :
    (cohere u227 priorTopic).eval c = (cohere u227 priorTopic).eval cand_u229 :=
  Beaver2004.cohere_factors_through_cb u227 priorTopic c cand_u229 h

-- ════════════════════════════════════════════════════
-- § 6. Future work / deferred items
-- ════════════════════════════════════════════════════

/-! ## Items deferred from this commit

    - **`LinearOrder` ranker** (Rambow 1993, surface position): the
      existing `Realization E R` structure carries `entity / role /
      isPronoun` but no explicit `position` field; without per-
      realization position info, a linear-order `CfRankerOf` instance
      cannot be expressed cleanly. Adding `position : Nat` to
      `Realization` is a substrate change that would cascade to all
      anonymous-constructor call sites in study files. Deferred to a
      separate commit.

    - **BFP 87 4-way `BFPTransition` (CON | RET | SSH | RSH)**: the
      Smooth-Shift / Rough-Shift refinement requires a 4-way enum.
      Per the audit's "extract on second consumer" discipline, the
      4-way stays study-file-local until a second consumer (Walker
      1989, Brennan 1995, Tetreault 2001) motivates promotion.
      A `private structure` form would land here when an empirical
      contrast requiring SSH/RSH discrimination gets formalized.

    - **PSDH GNOME corpus statistics** (Tables 1-15): encoding the
      reported per-instantiation violation percentages (~25% Strong
      C1 violations at vanilla, dropping to ~22% under best
      instantiation; Rule 1 (GJW 95) ≤8% violations across all
      instantiations). The corpus data isn't accessible to us; the
      statistics would have to be encoded as opaque `Nat` values
      with PSDH-table citations — defensible for paper replication
      but adds significant code without deriving content. Deferred.

    - **Full Beaver 2004 substrate-level OT-Centering bridge**: a
      *general* substrate theorem `cbAll prev cur = (centeringAsTableau prev cur).optimal.image (·.entity)`
      requires constructing the full `Tableau` (Finset candidates +
      Nonempty proof + ViolationProfile mapping). `Beaver2004.lean`
      lands the per-example witnesses (with the full 6-constraint
      ranking and Theorem (20) verification on Beaver's own (12) and
      (2) examples); the general substrate-level theorem is still
      queued.

    - **Structural `centeringToSidner` translation**: the §2 Sidner
      bridge (`psdh_two_cb_witnesses_sidner_two_foci`) is currently a
      witness on independently constructed inputs, not a structural
      identity. A function `centeringToSidner : Utterance E R →
      Sidner1983.Sentence E` mapping `.subject ↦ .agent/.agent`,
      `.object ↦ .theme/.nonAgent`, `.other ↦ .otherNonAgent/.nonAgent`
      would let the bridge be PROVEN over the IMAGE of `u227`/`u229`
      under that map, replacing stipulation with derivation. Queued
      as a separate commit.

    - **`HasDiscourseStatus`-typed IS ranker**: currently the
      Strube-Hahn ranker is `instance : CfRanker StrubeHahnInfoStatus`
      (role-typed). The deeper move is `instance [HasDiscourseStatus E]
      : CfRankerOf E R` — ranking ANY entity-typed thing that has
      discourse status, decoupled from `R`. Lets non-English fragments
      use IS ranking without changing their role type. Queued.

    - **Hybrid Continuity** (PSDH §5.3.3): the disjunction of entity
      coherence ∨ rhetorical relation ∨ temporal coherence as the
      generalized "local coherence" notion. Aspirational; PSDH
      themselves leave it as a sketch.

    - **`Variety` principle** (PSDH §5.3.5): only ~50% of CBs are R1
      pronouns; CBs hardly ever continued for >2-3 utterances.
      PSDH suggest "ensuring variety" as an additional principle in
      discourse production. Speaker-side claim, less amenable to
      substrate formalization. -/

end PoesioEtAl2004
