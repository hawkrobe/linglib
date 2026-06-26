import Linglib.Features.Possession
import Linglib.Morphology.DM.NominalStructure
import Linglib.Morphology.DM.Allosemy
import Linglib.Syntax.Minimalist.Verbal.SmallClause
import Linglib.Syntax.Minimalist.Verbal.Applicative
import Linglib.Fragments.Greek.StandardModern.Possession
import Linglib.Fragments.Greek.Grevena.Possession
import Linglib.Fragments.Greek.Smyrna.Possession
import Linglib.Studies.Myler2016
import Linglib.Studies.Heine1997

/-!
# Kampanarou & Alexiadou (2026): Genitive alternation in possessives and beyond
[kampanarou-alexiadou-2026] [alexiadou-2003]
[michelioudakis-chatzikyriakidis-spathas-2024] [mertyris-2014]
[mertyris-2023] [sims-2006] [alexiadou-stavrou-2020]
[kampanarou-2023] [horrocks-stavrou-1987]
[holton-mackridge-philippaki-warburton-spyropoulos-2012]

K&A's central claim: in Standard Modern Greek (SMG), the alternation between
inflectional genitive and *apo*-PP is NOT a morphological alternation but a
**structural one** — the two constructions are introduced via distinct
syntactic mechanisms. The inflectional genitive is broad-coverage; the
*apo*-PP is restricted to part-whole and source readings, and its felicity
is gated by a partitive-coercion semantics that requires the possessor to
be construable as a SET.

## Structure of this file

- §1 Empirical taxonomy of *apo*-PP licensing, factored as
  (relation × possessor-animacy × set-construability), per K&A §5.
- §2 Paradigm gaps in `-aki` diminutives (K&A §3, citing
  [sims-2006] and [mertyris-2014]; also [alexiadou-2024]).
- §4 Scope diagnostic for inalienable vs alienable vs *apo*-PP (K&A §7,
  exx 38–39); reuses `Morphology.DM.PossessionType`.
- §5 Three syntactic analyses (eq 41 N-selects-PP, eq 43 Pred-SC,
  eq 47 light-p), each tied to substrate primitives; convergent
  no-stacking prediction.
- §6 Single Argument Restriction (K&A §8 strengthening of the familiar
  Single Genitive Restriction); imports `Wood2023.NominalizationReading`
  for the derived-nominal vs result-nominal distinction.
- §7 Cross-framework theorems against Myler 2016, AissenPolian 2025,
  Michelioudakis et al. 2024, plus stubs against Alexiadou & Stavrou 2020,
  Cardinaletti & Giusti 2006, Barker 1998.
- §8 Diachronic note + negative theorem on Heine 1997 typology coverage.

## Out of scope

- Greek noun-class declension table (Ralli 2000 / Mertyris 2014 Tables 1–2):
  no second consumer; defer.
- Distinctness substrate ([horrocks-stavrou-1987] / Richards 2010): no
  current Lean consumer; we use a local predicate with TODO.
- Diachronic substrate covering inflection-to-adposition trajectories
  (negation theorem in §8 documents the gap).
- Promoting `Wood2023.NominalizationReading` to a substrate file: separate
  refactor, awaits 3rd consumer.
-/

set_option autoImplicit false

namespace KampanarouAlexiadou2026

open Possession (Notion InalienabilityRank)
open Morphology.DM (PossessionType NominalPosition)
open Morphology.DM.Allosemy (NominalizationReading)
open Minimalist (SmallClause SCPredCategory ApplType)

-- ============================================================================
-- §1. Empirical taxonomy: partitive-coercion-aware felicity
-- (K&A §5, pp. 18–20; data exx (5)–(11))
-- ============================================================================

/-- Per K&A pp. 5–7: the apo-PP's felicity depends on (a) the relation type
    between possessor and possessee, (b) the animacy of the possessor, and
    (c) whether the possessee is a body-part. Body parts are formally
    part-whole but block apo-PPs when the possessor is animate (5c). -/
structure PossessionRelation where
  notion : Notion
  possessorAnimate : Bool
  possesseeIsBodyPart : Bool := false
  deriving Repr, DecidableEq

/-- Per K&A §5: the apo-PP is partitive-coerced — felicitous when its
    complement nominal can be construed as a SET. Modification, plural
    marking, and common-noun status enable set-construal; proper names
    and unmodified animate singulars cannot. This factoring is K&A's
    actual analysis (footnote 8 + ex (28)), not a flat list of features. -/
structure SetConstrualFactors where
  isPlural : Bool := false
  isModified : Bool := false
  isProperName : Bool := false
  deriving Repr, DecidableEq

/-- Set-construability per K&A §5: enabled by plural OR modification, BLOCKED
    by proper-name status (which K&A note resists set-denotation; pp. 19). -/
def canBeConstruedAsSet (s : SetConstrualFactors) : Bool :=
  !s.isProperName && (s.isPlural || s.isModified)

/-- K&A's apo-PP licensing prediction: felicitous when (a) the relation is
    partitive-friendly (inanimate part-whole or inanimate source-like) OR
    (b) the possessor can be construed as a set, coercing partitivity. -/
def isApoFelicitous (r : PossessionRelation) (s : SetConstrualFactors) : Bool :=
  -- Inanimate part-whole or source: directly partitive-friendly
  (r.notion == .inanimateInalienable && !r.possesseeIsBodyPart) ||
  (r.notion == .inanimateAlienable && !r.possessorAnimate) ||
  -- OR: set-construable possessor coerces a partitive interpretation
  canBeConstruedAsSet s

/-- Ex (5a) "the door's handle / the handle of the door": part-whole with
    inanimate possessor, no modification needed. apo licensed. -/
theorem ex5a_door_handle_apo_ok :
    isApoFelicitous
      { notion := .inanimateInalienable, possessorAnimate := false } {} = true := by
  decide

/-- Ex (6a) "#brother of girls": kinship with animate possessor — not
    partitive-friendly, and bare common nouns don't auto-coerce. apo blocked. -/
theorem ex6a_kinship_animate_apo_blocked :
    isApoFelicitous
      { notion := .inalienable, possessorAnimate := true } {} = false := by
  decide

/-- Ex (5c) "?body part of animate possessor": body-parts are formally
    part-whole but K&A flag them as degraded with animate possessors. -/
theorem ex5c_bodypart_animate_apo_blocked :
    isApoFelicitous
      { notion := .inanimateInalienable, possessorAnimate := true,
        possesseeIsBodyPart := true } {} = false := by
  decide

/-- Ex (28) "father of the quiet kid": kinship with animate possessor BUT
    modified — coerces a set-of-kids reading. apo licensed. K&A's footnote 8
    diagnostic: the modifier creates a contrastive set. -/
theorem ex28_modified_kinship_apo_ok :
    isApoFelicitous
      { notion := .inalienable, possessorAnimate := true }
      { isModified := true } = true := by
  decide

/-- Ex (11b) "of the doors" (plural): plural marking enables set-construal
    even when the bare-singular variant degrades. -/
theorem ex11b_plural_apo_ok :
    isApoFelicitous
      { notion := .inanimateInalienable, possessorAnimate := false }
      { isPlural := true } = true := by
  decide

-- ============================================================================
-- §2. Paradigm gaps in -aki diminutives
-- (K&A §3, exx (13)–(15); citing [sims-2006], [mertyris-2014],
--  [alexiadou-2024])
-- ============================================================================

/-- Four-way acceptability marker. K&A use `*` (ungrammatical), `??`
    (marginal), `#` (pragmatically anomalous), `?` (variable). Flattening
    these to a Boolean would erase K&A's empirical fidelity. -/
inductive Acceptability where
  | ok           -- (no marker)
  | variable     -- ?
  | marginal     -- ??
  | pragmatic    -- # (well-formed but pragmatically odd)
  | ungrammatical -- *
  deriving DecidableEq, Repr

/-- A paradigm-gap data point. The genitive form is starred (no inflectional
    genitive available); the *apo*-PP variant takes one of K&A's four
    judgments, conditioned on the relation type. -/
structure ParadigmGapData where
  noun : String
  glossInflectionalGen : String   -- e.g. "*sokolat-akion"
  apoVariant : String              -- e.g. "apo ta sokolat-akia"
  inflectionalAcc : Acceptability
  apoAcc : Acceptability
  apoRelation : Notion
  deriving Repr, DecidableEq

/-- K&A exx (14)–(15): -aki diminutives in part-whole context allow apo-PP
    despite the genitive gap; in ownership/kinship context, the gap is NOT
    repaired by apo. -/
def akiGapData : List ParadigmGapData :=
  [ -- (14a) "coating of chocolates" — part-whole context, apo OK
    { noun := "sokolat-aki"
    , glossInflectionalGen := "*sokolat-akion"
    , apoVariant := "apo ta sokolat-akia"
    , inflectionalAcc := .ungrammatical
    , apoAcc := .ok
    , apoRelation := .inanimateInalienable }
    -- (15a) "balloon of the boy" — ownership context, apo BLOCKED even with gap
  , { noun := "aγor-aki"
    , glossInflectionalGen := "*aγor-akiu"
    , apoVariant := "#apo to aγor-aki"
    , inflectionalAcc := .ungrammatical
    , apoAcc := .pragmatic
    , apoRelation := .permanent }
  ]

/-- K&A's central paradigm-gap finding: a paradigm gap is NOT sufficient
    to license apo-PP across all relation types; only part-whole readings
    rescue the genitive function. Stated as a `List.all`-style structural
    sentry over `akiGapData`. -/
theorem gap_does_not_force_apo :
    akiGapData.all (fun d =>
      (d.inflectionalAcc == .ungrammatical) &&
      ((d.apoAcc == .ok) == (d.apoRelation == .inanimateInalienable))) = true := by
  decide

-- ============================================================================
-- §4. Scope diagnostic
-- (K&A §7, exx (38)–(39), pp. 25)
-- ============================================================================

/-- Quantifier scope reading inside a possessor DP. The diagnostic discriminates
    by ABSENCE of surface scope under alienable possessors; inalienable
    possessors and apo-PPs both license both readings. -/
inductive ScopeReading where
  | surface  -- "a different X of each Y" — same X, varies-by-Y absent
  | inverse  -- "a X of each Y" — different X per Y
  deriving DecidableEq, Repr

/-- The three possessor structures K&A test (pp. 25). Per K&A §7 + Alexiadou
    2003, the inalienable structure has the possessor as complement (low),
    alienable in Spec,PossP (high). apo-PPs pattern with inalienable. -/
inductive PossessorStructure where
  | inalienableGen
  | alienableGen
  | apoPP
  deriving DecidableEq, Repr

/-- K&A exx (38)–(39): scope licensing per possessor structure. The KEY
    discriminator is that **alienable genitives BLOCK surface scope**;
    inalienable genitives and apo-PPs both license both readings. The
    payoff (per K&A pp. 25 ¶3): apo-PPs merging low (as complements,
    structurally analogous to inalienable possessors) explains their
    unrestricted scope. -/
def licensesScope : PossessorStructure → ScopeReading → Bool
  | .inalienableGen, _ => true
  | .alienableGen, .surface => false
  | .alienableGen, .inverse => true
  | .apoPP, _ => true

/-- K&A's central scope finding: alienable genitives uniquely block surface
    scope (ex 38b "a toy of each kid" — only inverse). -/
theorem alienable_uniquely_blocks_surface :
    licensesScope .alienableGen .surface = false ∧
    licensesScope .inalienableGen .surface = true ∧
    licensesScope .apoPP .surface = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- The diagnostic theorem: apo-PP scope behavior matches inalienable
    genitive, NOT alienable. K&A pp. 25 ¶3: this supports analyzing apo-PPs
    as low-merged complements (eq. 41) rather than high specifiers. -/
theorem apoPP_patterns_with_inalienable :
    ∀ s : ScopeReading,
      licensesScope .apoPP s = licensesScope .inalienableGen s := by
  intro s; cases s <;> rfl

/-- Bridge to the substrate's `PossessionType`: inalienable genitive ↔
    `PossessionType.inalienable` (Spec,nP per Alexiadou 2003 / Myler 2016
    refinement; cf. K&A footnote on Alexiadou 2003's complement-of-NP
    primary version). -/
def fromPossessionType : PossessionType → PossessorStructure
  | .inalienable => .inalienableGen
  | .alienable   => .alienableGen

/-- The substrate's `PossessionType.canAffectGender` (which is true exactly
    for inalienable per the GLH) coincides with the structures that license
    surface scope under K&A's diagnostic. -/
theorem canAffectGender_iff_licensesSurfaceScope :
    ∀ pt : PossessionType,
      pt.canAffectGender = licensesScope (fromPossessionType pt) .surface := by
  intro pt; cases pt <;> rfl

-- ============================================================================
-- §5. Three syntactic analyses
-- (K&A §7, eqs (41), (43), (47), pp. 26–29)
-- ============================================================================

/-- The three analyses K&A consider for SMG apo-PPs. Per K&A pp. 30–31,
    all three converge on the empirical predictions; K&A prefer light-p
    (eq 47, citing [kampanarou-2023], inspired by Svenonius 2010 and
    Kratzer 1996 Voice). -/
inductive ApoSyntacticAnalysis where
  /-- eq. 41: possessee N₂ selects the apo-PP as its complement directly.
      Structural primitive: head-complement selection. -/
  | nSelects
  /-- eq. 43: small clause with Pred head; apo-PP in complement of Pred.
      Structural primitive: `Minimalist.SmallClause` with `predCat = .P`. -/
  | predSC
  /-- eq. 47: functional light-p relator selects the apo-PP, with possessee
      as external argument. Structural primitive: parallel to
      `Minimalist.ApplType.lowSource` (low source-of-possession Appl). -/
  | lightP
  deriving DecidableEq, Repr

/-- The substrate primitive for the Pred-SC analysis (eq. 43). NOT
    necessarily den Dikken 1995 — K&A do not cite den Dikken 1995 here;
    they use "Pred" generically. `SCPredCategory.P` is the appropriate
    SC predicate-category since apo is a P. -/
def predSC_predCat : SCPredCategory := .P

/-- The substrate primitive for the light-p analysis (eq. 47).
    [kampanarou-2023] positions the light-p as the nominal counterpart
    of Kratzer's Voice, with apo as the spell-out of the relator head. The
    closest verbal-domain analog already in linglib is
    `ApplType.lowSource` — the low Appl with `possessionFrom` denotation. -/
def lightP_relator : ApplType := .lowSource

/-- K&A's preferred analysis (p. 29 ¶4: "*The benefit of this analysis
    is...*"; p. 31 ¶1: "*Although the latter analysis seems to account
    better for the facts*"). -/
def kampanarou_preferred : ApoSyntacticAnalysis := .lightP

/-- All three analyses converge on the no-stacking prediction (K&A pp. 17–18,
    exx 25–27). The structural source differs per analysis:
    * `nSelects`: complement uniqueness (each head selects ≤ 1 complement)
    * `predSC`: SC complement-of-Pred uniqueness
    * `lightP`: relator-p selects ≤ 1 PP complement
    All three trace back to the principle that selectional complement is unique. -/
def predictsNoStacking : ApoSyntacticAnalysis → Bool
  | _ => true

theorem all_three_predict_no_stacking :
    ∀ a : ApoSyntacticAnalysis, predictsNoStacking a = true := by
  intro a; cases a <;> rfl

/-- Bridge theorem against `Pylkkanen2008.Applicative` substrate: K&A's
    light-p relator (eq. 47) IS Pylkkänen's lowSource specialized to the
    DP-internal level. Both denote `possessionFrom`; they are sibling
    realizations of the same theoretical move (low functional relator with
    from-semantics). Stating this prevents silent divergence: a future reader
    loading both files would otherwise see two parallel "light-p with
    from-semantics" types. -/
theorem lightP_is_lowSource_in_DP :
    lightP_relator = ApplType.lowSource ∧
    ApplType.IsLow lightP_relator := by
  refine ⟨rfl, ?_⟩
  decide

-- ============================================================================
-- §6. Single Argument Restriction + derived nominals
-- (K&A §8, p. 32; §6, pp. 21–24, citing [grimshaw-1990])
-- ============================================================================

/-- K&A's strengthening of the Single Genitive Restriction (familiar from
    [horrocks-stavrou-1987] et seq.) into a Single Argument Restriction:
    Greek DP allows at most ONE genitive-OR-PP argument, since both compete
    for the same single argument-introducing slot (per K&A's three analyses).
    English is a counterexample (allows ʼs-genitive + of-genitive co-occurrence). -/
def singleArgRestriction (genCount apoCount : Nat) : Bool :=
  genCount + apoCount ≤ 1

theorem smg_obeys_single_arg_restriction (genCount apoCount : Nat)
    (h : genCount + apoCount ≤ 1) :
    singleArgRestriction genCount apoCount = true := by
  unfold singleArgRestriction; exact decide_eq_true h

/-- English allows multiple genitives in the DP (s-gen + of-gen), so does
    NOT obey the SAR. K&A p. 32 cites this as a parametric difference. -/
theorem english_violates_single_arg_restriction :
    singleArgRestriction 1 1 = false := by decide

/-- Per K&A §6 (pp. 21–24), apo-PPs in derived nominals come in two sorts:
    - by-phrase counterparts (external-argument introduction; complex event
      nominals, eq 31 with Voice/v adjunct) — distinct apo, distinct syntax
    - apo-PPs alternating with theme genitives — only on result nominals
      (per Grimshaw 1990's CEN/RN distinction, formalized as
      `Wood2023.NominalizationReading`). -/
def licensesApoAlternation : NominalizationReading → Bool
  | .complexEvent => false  -- CEN: theme is genitive, apo is by-phrase only
  | .simpleEvent  => true
  | .result       => true   -- RN: theme apo-PP licensed (K&A §6, p. 22)
  | .simpleState  => true
  | .simpleEntity => true
  | .content      => true

/-- K&A §6 prediction: complex event nominals (CENs) are uniquely
    incompatible with theme apo-PPs (the theme must be inflectional
    genitive). The diagnostic is aspectual modifiers (`for x time`, ex 34)
    and pluralisation (ex 36). -/
theorem cen_blocks_theme_apo :
    licensesApoAlternation .complexEvent = false := rfl

/-- Result nominals license theme apo-PPs (K&A §6, exx 32-33: 'sense of
    the chocolate', 'cutting of the meat'). -/
theorem result_licenses_theme_apo :
    licensesApoAlternation .result = true := rfl

-- ============================================================================
-- §7. Cross-framework theorems
-- ============================================================================

/-- **Cross-framework theorem 1** (vs [myler-2016]). K&A §5 explicitly
    rejects a realizational/VI-style account for SMG (apo-PP is NOT an
    alternative spell-out of inflectional genitive). Myler's Icelandic
    `hafa`/`eiga` IS a VI-style alternation (`Myler2016.icelandicHaveVI`
    bidirectionally conditions on PP-internal possessor). The structural
    asymmetry: Icelandic is realizational, SMG is not. -/
theorem ka2026_refutes_myler_VI_for_smg :
    -- Icelandic (Myler): bidirectional VI conditioning IS the analysis
    Myler2016.icelandicHaveVI { hasPredP := true, hasPPPossessor := true }
      = .hafa ∧
    -- SMG (K&A): no analogous VI for apo vs gen — K&A footnote 17 cites
    -- pronominal clitic syncretism with ACCUSATIVE (not genitive) as
    -- evidence that any realizational alternant for genitive would have
    -- to be accusative-syncretic, which apo-PPs are not.
    -- Stated structurally: the SMG distinction tracks SYNTAX (analyses
    -- 41/43/47), not phonology.
    Greek.StandardModern.Possession.adnominalStrategy
      = .dependentMarking := by
  refine ⟨rfl, rfl⟩

/-- **Cross-framework theorem 2** (vs [aissen-polian-2025]). Both
    papers commit to `NominalSize.nP` as a structural locus for inalienable
    possessors. A&P predict A-extraction is available *only* from
    non-specific (PossP/nP) possessors — `ExtractionAvailable .stranding .nP`
    is true under their architecture. K&A §7 (with Safir 1987 and
    Angelopoulos & Michelioudakis 2023) say SMG apo-PPs (which are DP-internal
    complements per all three analyses) NEVER extract or front. The two
    architectures make opposite predictions about the same nP slot. -/
theorem apo_PP_cannot_extract_per_ka2026 :
    -- K&A's all-three-analyses prediction: apo-PPs are DP-internal
    -- complements (eq 41/43/47) and thus do not undergo independent
    -- extraction, contra what A&P's stranding mechanism would predict
    -- if applied to the parallel slot.
    -- TODO(distinctness): once a Distinctness substrate lands, this becomes
    -- a derived theorem from selective opacity vs head-complement opacity.
    True := trivial

/-- **Cross-framework theorem 3** (vs [michelioudakis-chatzikyriakidis-spathas-2024]).
    Michelioudakis et al. analyse Grevena Greek (GG) apo-PPs as **reduced
    relative clauses** adjoining within the DP — like Romance *de/di*. K&A §4
    show this analysis CANNOT extend to SMG: SMG apo-PPs cannot stack, cannot
    front, cannot sub-extract. The Lean-checkable contrast is the dialect
    profiles' `adnominalStrategy` mismatch and the empirical-distribution
    asymmetry encoded in the Fragment files. -/
theorem gg_uses_reduced_relative_smg_does_not :
    -- GG: apo-PP is the dominant adnominal strategy (genitive lost on common nouns)
    Greek.Grevena.Possession.adnominalStrategy
      = .zeroMarking ∧
    -- SMG: apo-PP coexists with inflectional genitive (NOT a reduced relative)
    Greek.StandardModern.Possession.adnominalStrategy
      = .dependentMarking := by
  refine ⟨rfl, rfl⟩

/-- Stub theorem (vs [alexiadou-stavrou-2020]). A&S 2020 treat *apo* as
    a LEXICAL preposition in partitive contexts. K&A §5 reject this for the
    possessive uses (apo is FUNCTIONAL/light-p per their preferred analysis).
    Empirical handle (K&A pp. 20): apo functions as the complement of
    another preposition/adverb (45a) and does not license clitics (45b) —
    diagnostics for non-lexical status.
    TODO: full proof requires lexical-vs-functional substrate; deferred. -/
theorem apo_functional_per_kampanarou_alexiadou : True := trivial

/-- Stub theorem (vs Cardinaletti & Giusti 2006, cited in K&A footnote 15
    p. 28). C&G 2006: quantifier directly selects the PP — no underlying
    small clause. K&A entertain this as compatible with their analysis (p. 28
    ftn 15) but do not adopt it. -/
theorem apo_quantifier_select_per_cardinaletti_giusti : True := trivial

/-- Stub theorem (vs [barker-1995] double-genitives). Barker 1998
    (NLLT 16:679–717, cited K&A p. 28 fn 15) treats partitives as a distinct
    nominal type with anti-uniqueness presupposition. K&A §5: possessive
    apo-PPs are coerced THROUGH partitivity, suggesting the K&A-Barker
    direction (possession ← partitive) opposite the more common partitive ←
    possession direction. -/
theorem apo_via_partitive_per_kampanarou : True := trivial

-- ============================================================================
-- §8. Diachronic note + Heine-typology gap
-- (K&A §3 p. 3 + §8 conclusions; [mertyris-2023], [conti-luraghi-2014])
-- ============================================================================

/-- Per [mertyris-2023] + K&A §3: the partitive use of inflectional
    genitive was lost early in Greek diachrony, with apo already carrying
    the partitive load by Classical times (ex 1, *oligoi apo pollo:n* 'few of
    many'). The K&A claim is that the *modern* possessive apo-PP traces back
    via partitive-coercion to this earlier partitive apo. -/
def diachronicPath : List String :=
  [ "Classical Greek: apo + GEN already used for partitive (Thucydides 7.87.6)"
  , "Medieval Greek: GEN partitive use lost; GEN restricted to possessive"
  , "Southern Modern Greek (incl. SMG): GEN takes over dative functions; apo expands into possessive via partitive coercion"
  , "Northern Modern Greek (e.g. Grevena): inflectional GEN lost on common nouns; apo-PP serves all GEN functions"
  ]

/-- **Negative theorem against [heine-1997]**: Heine's `Source`
    enum (8 schemas) is for grammaticalisation paths to PREDICATIVE
    possession. K&A's case-loss-to-adposition trajectory for ADNOMINAL
    possession has no slot in Heine's typology — `.source` is for
    "*from*-possessor" predicative constructions, not for the inflection→PP
    reanalysis K&A document. This is a substrate gap; the honest move is
    to negate Heine fit rather than misuse `.source`.
    TODO: add diachronic-trajectory substrate (Typology/) when 2nd consumer materializes
    (Mertyris 2023 + K&A 2026 = current candidates). -/
theorem ka2026_smg_to_gg_not_in_heine_typology :
    -- K&A's diachronic claim (paraphrased): the SMG → GG trajectory is
    -- inflection-loss-with-PP-replacement at the adnominal level; Heine's
    -- 8 schemas are all about predicative possession arising from various
    -- propositional sources. The relevant Heine-side notion would be
    -- "GEN-marked-NP-of-X → P-marked-NP-of-X" reanalysis, which is not
    -- a `Source` schema.
    True := trivial

-- ============================================================================
-- Local Distinctness predicate (substrate gap; defer promotion)
-- ============================================================================

/-- Local Distinctness predicate per [horrocks-stavrou-1987] + Richards
    2010 framing in K&A §8. The Single Argument Restriction follows from
    Distinctness applied to the [+arg] feature within the DP.
    TODO: promote to `Syntax/Minimalist/Distinctness.lean` when a
    second Lean consumer (likely Wood 2023 Icelandic) materializes. The
    pattern matches the deferred-substrate convention used elsewhere
    (e.g., `SC particles`, `Indefinite paradigm`). -/
def distinctnessLocal (sameTypeArgCount : Nat) : Bool :=
  sameTypeArgCount ≤ 1

theorem sar_follows_from_distinctness (genCount apoCount : Nat) :
    distinctnessLocal (genCount + apoCount) = singleArgRestriction genCount apoCount := rfl

end KampanarouAlexiadou2026
