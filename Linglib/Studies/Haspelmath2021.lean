import Linglib.Features.Prominence
import Linglib.Features.Givenness
import Linglib.Studies.Aissen2003
import Linglib.Studies.DeHoopMalchukov2008
import Linglib.Studies.Marantz1991
import Linglib.Syntax.Case.Alignment

/-!
# [haspelmath-2021]: Role-reference associations and the explanation of argument coding splits

[haspelmath-2021], *Linguistics* 59(1): 123–174.
DOI: 10.1515/ling-2020-0252.

## Overview

Haspelmath proposes a single meta-universal — the **Role-Reference
Association Universal** (Universal 1) — that subsumes differential object
marking, split ergativity, ditransitive splits, and person-scenario splits
under one generalization: deviations from the usual associations of role
rank and referential prominence tend to be coded by longer grammatical forms.

Universal 1 in turn is "evidently a special case of" the broader
**form-frequency correspondence universal** (Universal 68 in §11.2): the
"usual" associations ARE the frequent ones, and frequent expressions get
shorter forms (Zipf).

## The Paper's Numbered Universals

The paper states the following numbered universals (Figure 1, §11.1):

### Meta-universals (§2)
- **Universal 1** (statement (5)): Role-Reference Association Universal
- **Universal 2** (statement (6)): usual role-reference associations

### Single-argument coding splits (§3–5)
- **Universal 3** (statement (13), §3): Single-argument flagging universal
- **Universal 4** (statement (14), §4.1): Split P flagging (DOM)
- **Universal 5** (statement (16), §3, restated §6): Scenario coding universal
- **Universal 6** (statement (21), §4.2): Split A flagging (DSM)
- **Universal 7** (statement (26), §5): Split R flagging
- **Universal 8** (statement (27), §5): Split T flagging

### Ditransitive scenario splits (§7)
- **Universal 9a** (statement (41), §7.1): Ditransitive Person-Role Constraint
- **Universal 9b** (statement (42), §7.1): Ditransitive person-role universal

### Relative scenario / inverse / alternations (§8–§10)
- **Universal 10** (statement (54), §8): Relative scenario universal
- **Universal 11** (statement (57), §9): Inverse universal
- **Universal 12** (statement (61), §10.1): Alternation universal
- **Universal 13** (statement (62), §10.1): Passive universal
- **Universal 14** (statement (63), §10.1): Dative alternation universal

### The reductive claim
- **Universal 68** (statement (68), §11.2): Grammatical form-frequency
  correspondence universal — Universal 1 is "evidently a special case of"
  this broader universal.

## What This File Formalizes

Universals 1–14, with U4 and U6 re-expressing model predictions from
[aissen-2003] and [de-hoop-malchukov-2008] respectively, and a
final §18 contrastive section showing how [marantz-1991]'s dependent
case algorithm partitions the empirical territory of "split case marking"
with Haspelmath's framework: structural-condition splits (Marantz) vs.
prominence-condition splits (Haspelmath).

## What This File Does NOT Formalize

The paper's frequency claims are tendency-claims based on corpus regularities.
Haspelmath himself: "I do not focus on documenting the discourse frequencies
in this paper... testing this claim more thoroughly is a topic for future
comparative corpus research" (p. 126). Lean theorems committing the
frequency-class function to specific Nat values would over-reify a
tendency-claim. We use `Scenario.frequencyClass` from the substrate as a
discrete proxy and clearly mark its theorems as proxy-checks, not empirical
claims about token frequencies.

-/

namespace Haspelmath2021

open Features.Prominence
open Core.Optimization.Evaluation
open Constraints Pragmatics.Bidirectional
open Aissen2003
open DeHoopMalchukov2008
open Alignment

-- ============================================================================
-- § 0: Form-Frequency Apparatus (paper-specific substrate, co-located)
-- ============================================================================

/-! Haspelmath 2021's deeper explanation of argument-coding splits: the
    Role-Reference Association Universal (Universal 1) reduces to the
    general cognitive tendency for frequent expressions to be short.

    Three-step chain:

    1. **Frequency asymmetry**: some role-reference combinations are more
       frequent than others ("I saw him" > "He saw me"; animate agents >
       inanimate agents).
    2. **Form-frequency correspondence**: more frequent expressions tend
       to get shorter forms (diachronic erosion + analogical extension).
    3. **Coding asymmetry**: "usual" role-reference associations (= the
       frequent ones) get shorter (often zero) coding; "unusual" ones get
       longer (overt) coding.

    Previously housed in `Core/FormFrequency.lean` — demoted to this study
    file at 0.230.551 when the consumer count was 1 (only Haspelmath2021
    used any of the primitives) and four primitives in the substrate file
    (`respectsFormFrequency`, `argumentCodingRespectsFrequency`,
    `VoiceDirection`, `DitransitiveFrame`) were completely unused. -/

/-- Relative coding length of an argument expression. Haspelmath's claim
    is about *relative* length, not absolute morpheme counts. -/
inductive CodingLength where
  /-- Zero coding (no overt marker) -/
  | zero
  /-- Short overt coding (e.g., clitic, monosyllabic affix) -/
  | short
  /-- Long overt coding (e.g., full adposition, bisyllabic affix) -/
  | long
  deriving DecidableEq, Repr

/-- Numeric rank: zero (0) < short (1) < long (2). -/
def CodingLength.rank : CodingLength → Nat
  | .zero  => 0
  | .short => 1
  | .long  => 2

/-- Frequency proxy from prominence + role: Haspelmath's bridge claim.
    For P/T arguments, prominence correlates positively with unusualness
    (and so with coding length); for A/R, frequency is directly related
    to prominence rank. S is neutral. -/
def frequencyProxy (role : ArgumentRole)
    (a : AnimacyLevel) (d : DefinitenessLevel) : Nat :=
  match role with
  | .A | .R => prominenceRank a d        -- high prominence = high freq
  | .P | .T => 6 - prominenceRank a d    -- high prominence = LOW freq
  | .S      => 3                          -- neutral

/-- The frequency proxy predicts that usual associations are more frequent:
    every default-zone cell has at least the median proxy value. -/
theorem frequency_proxy_matches_default (role : ArgumentRole)
    (a : AnimacyLevel) (d : DefinitenessLevel) :
    (isDefaultZone role a d = true) →
    (frequencyProxy role a d ≥ 3) := by
  intro h
  cases role <;>
    simp only [isDefaultZone, frequencyProxy, prominenceRank,
               decide_eq_true_eq] at h ⊢ <;> omega

/-- Scenario-level form-frequency correspondence: higher frequency-class
    scenarios should get shorter-or-equal coding. -/
def scenarioRespectsFormFrequency
    (scenarios : List Scenario) (coding : Scenario → CodingLength) : Bool :=
  scenarios.all λ s1 =>
    scenarios.all λ s2 =>
      if s1.frequencyClass > s2.frequencyClass
      then (coding s1).rank ≤ (coding s2).rank
      else true

-- ============================================================================
-- § 1: Universal 1 — The Role-Reference Association Universal
-- ============================================================================

/-! **Universal 1** ([haspelmath-2021], §2, statement (5), p. 125):

    > Deviations from usual associations of role rank and referential
    > prominence tend to be coded by longer grammatical forms if the
    > coding is asymmetric.

    The paper's central meta-universal. Universal 1 is a claim about
    **coding length**, not about which prominence end gets a flag — that
    specialization is Universal 3.

    Formalized as: for each argument role `r`, the "deviation zone" is
    the negation of `r`'s default zone (`isDefaultZone r a d = false`),
    and the meta-universal predicts non-default cells get longer coding.
    The cell-level corollary is captured by `frequency_proxy_matches_default`
    (co-located in §0): default cells have `frequencyProxy ≥ 3`, non-default
    cells have `frequencyProxy ≤ 3`.
    Form-frequency correspondence (U68) then maps this to coding length. -/

/-- Universal 1 (cell form): default-zone cells have at least the median
    frequency proxy. Substrate lemma re-exported with the U1 framing. -/
theorem universal1_role_reference_association
    (role : ArgumentRole) (a : AnimacyLevel) (d : DefinitenessLevel) :
    (isDefaultZone role a d = true) →
    (frequencyProxy role a d ≥ 3) :=
  frequency_proxy_matches_default role a d

-- ============================================================================
-- § 2: Universal 2 — Usual Role-Reference Associations
-- ============================================================================

/-! **Universal 2** ([haspelmath-2021], §2, statement (6), p. 126):

    > Arguments with higher-ranked roles tend to be more referentially
    > prominent, and vice versa.

    Defines the *baseline* for Universal 1: A/R arguments (higher role
    rank) tend to be human, definite, topical. P/T arguments (lower role
    rank) tend to be inanimate, indefinite, new-information.

    Formalized via the substrate's `highDefault` (A, R) / `lowDefault`
    (P, T) predicates. -/

/-- Universal 2 (default-side): A and R have high-default-prominence
    expectations; P and T have low-default-prominence expectations.
    S is the alignment reference point and has no strong default
    (Haspelmath fn. 15, p. 138 explicitly excludes intransitives from
    the analysis). -/
theorem universal2_usual_associations :
    ArgumentRole.A.highDefault = true ∧
    ArgumentRole.R.highDefault = true ∧
    ArgumentRole.P.lowDefault = true ∧
    ArgumentRole.T.lowDefault = true := ⟨rfl, rfl, rfl, rfl⟩

/-! Haspelmath on role rank, p. 127: "the notion of role rank is not
    crucial. (Since some readers will be curious, I will make a few
    remarks below in Section 11.2, but it should be kept in mind that
    these considerations are not essential for this paper.)"

    The only role-rank claims the paper commits to are the
    monotransitive A > P (statement (7), p. 127) and the ditransitive
    R > T. We do *not* state a total ordering A > R > S > T > P; that
    would over-formalize. -/

/-- Universal 2 (role-rank fragment): A > P (monotransitive) and R > T
    (ditransitive). These are the only role-rank orderings the paper
    commits to. -/
theorem universal2_role_rank_committed_orderings :
    ArgumentRole.A.roleRank > ArgumentRole.P.roleRank ∧
    ArgumentRole.R.roleRank > ArgumentRole.T.roleRank := by decide

-- ============================================================================
-- § 3: Universal 3 — Single-Argument Flagging Universal
-- ============================================================================

/-! **Universal 3** ([haspelmath-2021], §3, statement (13), p. 131):

    > The single-argument flagging universal: If a language has an
    > asymmetric single-argument flagging split depending on some
    > prominence scale, then the coding is longer for prominent
    > P/T-arguments or for non-prominent A/R-arguments.

    The general single-argument form from which Universals 4, 6, 7, 8
    follow as specific cases for each argument role. It applies to both
    flagging and indexing (statement (15)).

    **Derived from U1 + U2.** Substrate-level: for any role `r`,
    `differentialTargetsProminent r = lowDefault r` (the prominent end
    is the "deviation" for low-default roles, and the non-prominent end
    is the deviation for high-default roles). U3 asserts this equality
    over the four core roles. -/

/-- Universal 3 derives from U1 + U2: for any argument role, the
    differential-flagging direction is determined by whether the role is
    low-default (prominent end = deviation) or high-default (non-prominent
    end = deviation). Strictly stronger than the four-conjunct over
    {A, P, R, T} since it ranges over all five roles, including S.

    `rfl` because substrate `differentialTargetsProminent r := r.lowDefault`
    is the alias — the equality holds by construction, not by enumeration. -/
theorem universal3_single_argument_flagging (r : ArgumentRole) :
    differentialTargetsProminent r = r.lowDefault := rfl

-- ============================================================================
-- § 4: Universal 4 — Split P Flagging (DOM)
-- ============================================================================

/-! **Universal 4** ([haspelmath-2021], §4.1, statement (14), p. 131):

    > Split P flagging: If a language has an asymmetric split in P
    > flagging depending on some prominence scale, then the special
    > flag is used on the prominent P-argument.

    Re-exported from [aissen-2003]'s OT factorial typology, which
    *predicts* this universal: the typology generates only monotone DOM
    patterns. -/

/-- [aissen-2003]'s OT factorial typology *predicts* Universal 4:
    every animacy DOM pattern in `animOptima` is monotone (the prominent
    end gets the marker first). Renamed from `universal4_split_P_flagging`
    to clarify that this is a *model prediction* of U4, not the universal
    itself: a model-internal lemma can support a typological universal
    without being identical to it. -/
theorem universal4_aissen_predicts : animOptima.all (λ opts =>
    opts.checkAll (λ c =>
      (if c.an then c.hu else true) &&
      (if c.inan then c.an else true))) = true :=
  animacy_all_monotone

-- ============================================================================
-- § 5: Universal 5 — Scenario Coding Universal
-- ============================================================================

/-! **Universal 5** ([haspelmath-2021], §3, statement (16), p. 132,
    restated §6, p. 144):

    > If a language has an asymmetric scenario split, then the coding is
    > longest for upstream scenarios, shortest for downstream scenarios,
    > and intermediate for balanced scenarios.

    The second major branch under Universal 1 (alongside Universal 3).
    Universal 3 conditions coding on the prominence of a single argument;
    Universal 5 conditions it on the *combination* of A-person and P-person.

    "Upstream" / "downstream" / "balanced" is Haspelmath's trichotomy
    (statement (11), p. 130). The paper does NOT introduce a "local"
    sub-case for SAP↔SAP scenarios — that classification was a formaliser
    invention and has been removed. -/

/-- Canonical witnesses for the trichotomy (statement (11)). -/
def downstreamScenario : Scenario := ⟨.first, .third⟩
def upstreamScenario : Scenario := ⟨.third, .first⟩
def balancedScenario : Scenario := ⟨.third, .third⟩

/-- Universal 5: the downstream/upstream/balanced trichotomy is exhaustive
    for *every* `Scenario`, not just the 9 in `Scenario.all`. Strictly
    stronger than the list-anchored form (which silently passes if
    `Scenario.all` ever loses an inhabitant). -/
theorem universal5_trichotomy_exhaustive (s : Scenario) :
    (s.isDownstream || s.isUpstream || s.isBalanced) = true := by
  obtain ⟨a, p⟩ := s; cases a <;> cases p <;> rfl

/-- Universal 5: the frequency-class proxy is monotone in the "usualness"
    of the scenario — downstream > balanced > upstream. This is a
    *substrate-level proxy*, not an empirical claim about discourse
    frequencies (cf. Haspelmath p. 126: corpus testing is "a topic for
    future comparative research"). -/
theorem universal5_frequency_class_monotone :
    downstreamScenario.frequencyClass > balancedScenario.frequencyClass ∧
    balancedScenario.frequencyClass > upstreamScenario.frequencyClass := by decide

-- ============================================================================
-- § 6: Universal 6 — Split A Flagging (DSM)
-- ============================================================================

/-! **Universal 6** ([haspelmath-2021], §4.2, statement (21), p. 136):

    > Split A flagging: If a language has an asymmetric split in A
    > flagging depending on some prominence scale, then the special
    > flag is used on the non-prominent A-argument.

    The mirror image of Universal 4. Re-expressed via [de-hoop-malchukov-2008]'s
    Distinguish constraint, which *predicts* this directionality: weak
    (non-prominent) subjects get overt ergative marking. -/

/-- [de-hoop-malchukov-2008]'s Distinguish-ranking *predicts* Universal 6:
    weak subjects are marked (Fore pattern). Renamed from
    `universal6_split_A_flagging` for the same reason as U4. -/
theorem universal6_dehoopmalchukov_predicts :
    superoptimal allPairs (profileFor [distinguishSubj, economy])
    = winnerDistinguishSubj :=
  dsm_distinguish

-- ============================================================================
-- § 7: Universals 7–8 — Ditransitive Splits (R and T flagging)
-- ============================================================================

/-! **Universal 7** ([haspelmath-2021], §5, statement (26), p. 139):

    > Split R flagging: If a language has an asymmetric split in R
    > flagging depending on some prominence scale, then the special
    > flag is used on the non-prominent R-argument.

    R behaves like A: both are high-rank roles whose differential marking
    targets the non-prominent end.

    **Universal 8** ([haspelmath-2021], §5, statement (27), p. 139):

    > Split T flagging: If a language has an asymmetric split in T
    > flagging depending on some prominence scale, then the special
    > flag is used on the prominent T-argument.

    T behaves like P: both are low-rank roles whose differential marking
    targets the prominent end.

    Haspelmath, p. 136: "Universal 6 in (21) is completely parallel to
    Universal 4 in (14)" and similarly for U7/U8 ("completely parallel
    to those about split A and P flagging seen earlier"). The parallelism
    IS Haspelmath's. -/

/-- Universal 7: R targets the non-prominent end (like A). -/
theorem universal7_R_like_A :
    differentialTargetsProminent .R = differentialTargetsProminent .A := rfl

/-- Universal 8: T targets the prominent end (like P). -/
theorem universal8_T_like_P :
    differentialTargetsProminent .T = differentialTargetsProminent .P := rfl

-- ============================================================================
-- § 8: Universals 9a/9b — Ditransitive Person-Role
-- ============================================================================

/-! **Universal 9a** ([haspelmath-2021], §7.1, statement (41), p. 147):

    > Ditransitive Person-Role Constraint: Combinations of bound person
    > forms (indexes) with the roles R and T are disfavoured if the T
    > index is first or second person and the R index is third person.

    Originally formulated as the "Person-Case Constraint" (Bonet 1994).
    Haspelmath fn. 19 (p. 147) reformulates this *empirically testable*
    version as 9b in coding-length terms.

    **Universal 9b** ([haspelmath-2021], §7.1, statement (42), p. 147):

    > Ditransitive person-role universal: If T is locuphoric and R is
    > aliophoric (i.e., if T is higher on the person scale than R), a
    > language may require a longer construction (not involving person
    > indexes), while (short) person indexes are always allowed when
    > the R is locuphoric and the T is aliophoric.

    Haspelmath, p. 147: "Universals 9a and 9b are thus merely special
    cases of Universal 5 in (16)." -/

/-- Universal 9b (proxy): the "unusual" R×T scenario (T locuphoric, R
    aliophoric) has lower frequency class than the "usual" one (R
    locuphoric, T aliophoric). The R-person/T-person convention reuses
    `Scenario`'s aPerson/pPerson slots: aPerson ↦ R-person, pPerson ↦
    T-person. Under that mapping, the upstream/downstream witnesses
    coincide with U5's, per Haspelmath's "merely special cases of U5"
    remark (p. 147). -/
theorem universal9b_unusual_lower_frequency :
    upstreamScenario.frequencyClass < downstreamScenario.frequencyClass := by decide

-- ============================================================================
-- § 9: Universal 10 — Relative Scenario Splits
-- ============================================================================

/-! **Universal 10** ([haspelmath-2021], §8, statement (54), p. 151):

    > The relative scenario universal: If a language has an asymmetric
    > relative scenario split, then the coding tends to be longest for
    > upstream scenarios, shortest for downstream scenarios, and
    > intermediate for balanced scenarios.

    Haspelmath: "merely a special case of the scenario universal that we
    saw earlier, and in fact the prediction is exactly the same" (p. 151).
    Frequency class is monotone: downstream > balanced > upstream. -/

theorem universal10_relative_scenario :
    downstreamScenario.frequencyClass > balancedScenario.frequencyClass ∧
    balancedScenario.frequencyClass > upstreamScenario.frequencyClass :=
  universal5_frequency_class_monotone

-- ============================================================================
-- § 10: Universal 11 — Inverse
-- ============================================================================

/-! **Universal 11** ([haspelmath-2021], §9, statement (57), p. 153):

    > The inverse universal: If a language uses different verb forms for
    > downstream and upstream scenarios, i.e., an inverse form and a
    > direct form, and the verb coding is asymmetric, then the inverse
    > form tends to be longer than the direct form.

    Upstream = unusual = lower frequency class = predicted longer by FFC.
    The direct/inverse distinction is captured at the scenario level via
    `Scenario.isDownstream`/`isUpstream` (substrate `Features/Prominence.lean`);
    a dedicated `VoiceDirection` enum was carried in `Core/FormFrequency.lean`
    until 0.230.551 but never used and was demoted out. -/

theorem universal11_inverse :
    upstreamScenario.frequencyClass < downstreamScenario.frequencyClass := by decide

-- ============================================================================
-- § 11: Universal 12 — Alternation Universal
-- ============================================================================

/-! **Universal 12** ([haspelmath-2021], §10.1, statement (61), p. 154):

    > The alternation universal: In an asymmetric argument coding
    > alternation, the longer alternant tends to be used in situations
    > that deviate from the usual associations of roles and referential
    > prominence.

    The parent universal that subsumes both U13 (passive) and U14
    (dative alternation). Haspelmath, p. 155: "both 13 and 14 are special
    cases of Universal 12, so I would like to claim that it is indeed a
    universal generalization. Universal 12, in turn, is evidently a
    special case of Universal 1, the general role-reference association
    universal."

    Formalized as a predicate `deviatesFromUsual` over a generic
    role/discourse-status pairing; U13 and U14 instantiate it for
    A/P (passive) and R/T (dative). -/

open Features (BinaryGivenness)

/-- Usual discourse-status association for the four core argument roles.
    A/R (high-rank) tend to be given (topical); P/T (low-rank) tend to
    be new (focal). S is excluded (Haspelmath fn. 15, p. 138 — the paper
    does not analyze intransitive constructions); querying S is therefore
    not defined. -/
def usualGivenness : ArgumentRole → Option BinaryGivenness
  | .A | .R => some .given
  | .P | .T => some .new
  | .S      => none

/-- An argument's discourse status deviates from the usual association
    if the role has a defined "usual" status and the actual status
    differs from it. S returns `false` (not analyzed). -/
def deviatesFromUsual (role : ArgumentRole) (status : BinaryGivenness) : Bool :=
  match usualGivenness role with
  | some usual => status != usual
  | none       => false

/-- Universal 12 (general form): the longer alternant is preferred when
    a role-pair has at least one role-discourse-status deviation from
    the usual association. Parameterized by the role pair (A,P for
    passive; R,T for dative) so U13 and U14 are pure instantiations. -/
def alternantPreferredLong
    (sensitiveToGivenness : Bool)
    (highRole lowRole : ArgumentRole)
    (highStatus lowStatus : BinaryGivenness) : Bool :=
  sensitiveToGivenness &&
    (deviatesFromUsual highRole highStatus || deviatesFromUsual lowRole lowStatus)

/-- Universal 12: under sensitivity, the longer alternant is preferred
    in deviation cases and dispreferred in usual cases. Parameterized
    over the role pair so U13 (A,P) and U14 (R,T) instantiate it. -/
theorem universal12_alternation
    (highRole lowRole : ArgumentRole)
    (h_high_given : usualGivenness highRole = some .given)
    (h_low_new   : usualGivenness lowRole  = some .new) :
    -- Deviant: high is new, low is given → longer alternant preferred
    alternantPreferredLong true highRole lowRole .new .given = true ∧
    -- Usual: high is given, low is new → longer alternant dispreferred
    alternantPreferredLong true highRole lowRole .given .new = false := by
  refine ⟨?_, ?_⟩ <;>
    · unfold alternantPreferredLong deviatesFromUsual
      rw [h_high_given, h_low_new]
      decide

-- ============================================================================
-- § 12: Universal 13 — Passive
-- ============================================================================

/-! **Universal 13** ([haspelmath-2021], §10.1, statement (62), p. 155):

    > The passive universal: If a passive alternation is sensitive to
    > givenness, then the passive alternant tends to be used when the
    > original A is not given information and/or the original P is not
    > new information.

    Note the conditional **"If a passive alternation is sensitive to
    givenness"**. This is a typological universal about languages whose
    passive is givenness-conditioned, not a fact about every language.
    Earlier formalisations dropped the conditional. -/

/-- Universal 13 = Universal 12 instantiated for the (A, P) role pair.
    Under the antecedent that the alternation IS sensitive to givenness,
    passive is preferred when A's or P's discourse status deviates from
    the usual association. `abbrev` (not `def`) so U13 is *literally*
    `alternantPreferredLong _ .A .P _ _` — no bridge or readout theorems
    needed; U12 instantiated at `(.A, .P)` carries the content. -/
abbrev passivePreferredGivenSensitive
    (sensitiveToGivenness : Bool) (statusA statusP : BinaryGivenness) : Bool :=
  alternantPreferredLong sensitiveToGivenness .A .P statusA statusP

-- ============================================================================
-- § 13: Universal 14 — Dative Alternation
-- ============================================================================

/-! **Universal 14** ([haspelmath-2021], §10.1, statement (63), p. 155):

    > The dative alternation universal: If a dative alternation is
    > sensitive to givenness, then the dative alternant tends to be
    > used when the R is not given information and/or the T is not
    > new information.

    Same conditional shape as U13. The "dative alternant" is the longer
    PP-dative form (cf. statement (60)); the alternative is the
    double-object construction. -/

/-- Universal 14 = Universal 12 instantiated for the (R, T) role pair.
    `abbrev` for the same reason as `passivePreferredGivenSensitive`: U14
    is *literally* `alternantPreferredLong _ .R .T _ _`. -/
abbrev ppDativePreferredGivenSensitive
    (sensitiveToGivenness : Bool) (statusR statusT : BinaryGivenness) : Bool :=
  alternantPreferredLong sensitiveToGivenness .R .T statusR statusT

-- ============================================================================
-- § 14: Ditransitive Alignment Parallels
-- ============================================================================

/-! The parallel between monotransitive and ditransitive alignment is a
    structural consequence of the role-rank hierarchy (Universal 2):

    - Indirective (R marked, T = P) parallels accusative (P marked, A = S)
    - Secundative (T marked, R = P) parallels ergative (A marked, P = S)

    This follows from Universals 7–8: R behaves like A, T behaves like P. -/

/-- Ditransitive alignment parallels monotransitive alignment:
    indirective marks R (the high-rank role), secundative marks T
    (the low-rank role). -/
theorem ditransitive_parallels_monotransitive :
    DitransitiveAlignment.indirective.marksR = true ∧
    DitransitiveAlignment.indirective.marksT = false ∧
    DitransitiveAlignment.secundative.marksT = true ∧
    DitransitiveAlignment.secundative.marksR = false := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 15: DOM ↔ Accusative, DSM ↔ Ergative ([de-hoop-malchukov-2008])
-- ============================================================================

/-! The correlation between DOM and accusative alignment, and between DSM
    and ergative alignment, is independently derived in [de-hoop-malchukov-2008] via the PaIP (Primary Actant Immunity Principle). [haspelmath-2021]
    discusses this as background but does NOT number it as one of his 14
    universals — included here for cross-reference only. -/

/-- Differential marking patterns ([de-hoop-malchukov-2008], not a
    numbered Haspelmath universal). -/
theorem alignment_correlation_deHoopMalchukov :
    markingPattern [identify, economy] = ⟨.overt, .zero⟩ ∧
    markingPattern [distinguishSubj, economy] = ⟨.zero, .overt⟩ ∧
    markingPattern [distinguishObj, economy] = ⟨.overt, .zero⟩ :=
  alignment_correlation

-- ============================================================================
-- § 16: Universal 68 — Form-Frequency Reduction
-- ============================================================================

/-! **Universal 68** ([haspelmath-2021], §11.2, statement (68), p. 158):

    > The grammatical form-frequency correspondence universal.

    Haspelmath, p. 155: "Universal 12, in turn, is evidently a special
    case of Universal 1, the general role-reference association
    universal." And the broader claim of §11.2 is that **Universal 1
    itself reduces to Universal 68**. The reduction in Figure 1 (§11.1)
    runs U3..U14 → U1 → U68; we do NOT claim that all 14 universals
    "reduce to U68" directly (that conflation was an error in earlier
    revisions of this file).

    `scenarioRespectsFormFrequency` (defined in §0) is the predicate
    "more frequent → shorter (or equal) coding". The scenario-level
    theorem below shows that `Scenario.frequencyClass` coheres with the
    form-frequency correspondence over the 9 scenarios. -/

/-- A coding function that assigns shortest coding to downstream
    scenarios, longest to upstream — exactly the gradient U10/U11
    predict. -/
def usualnessCoding (s : Scenario) : CodingLength :=
  if s.isDownstream then .zero
  else if s.isBalanced then .short
  else .long

/-- The `usualnessCoding` proxy respects the form-frequency correspondence
    over `Scenario.all` (substrate's `scenarioRespectsFormFrequency`).
    This factors through the substrate predicate rather than rolling its
    own consistency check — earlier revisions used `native_decide` over
    a hand-rolled all-pairs sweep. -/
theorem universal68_scenario_form_frequency :
    scenarioRespectsFormFrequency Scenario.all usualnessCoding = true := by decide

-- ============================================================================
-- § 17: Form-Frequency Grounding (re-export)
-- ============================================================================

/-- The cell-level form-frequency claim under U1: default cells have
    `frequencyProxy ≥ 3`. Re-exported from substrate for direct citation
    under the U1 framing. -/
theorem universal1_frequency_grounding (role : ArgumentRole)
    (a : AnimacyLevel) (d : DefinitenessLevel) :
    (isDefaultZone role a d = true) →
    (frequencyProxy role a d ≥ 3) :=
  frequency_proxy_matches_default role a d

-- ============================================================================
-- § 18: Contrast with [marantz-1991] — Configurational Case
-- ============================================================================

/-! [haspelmath-2021]'s reductive claim — that a wide range of
    "split case marking" phenomena reduce to form-frequency — competes
    with the configurational tradition of [marantz-1991] and
    [baker-2015], which derives split case from STRUCTURAL parameters
    (aspect, voice, derived-subject status) without reference to
    referential prominence.

    The two frameworks address overlapping but distinct empirical
    territory:

    - **Marantz**: structural-condition splits — Hindi aspect ERG
      (perfective vs imperfective), Georgian tense series, Burzio's
      generalization (no ACC on derived subjects), the Ergative
      generalization (no ERG on derived subjects).
    - **Haspelmath**: prominence-condition splits — Fore DSM (only
      non-prominent A gets ERG), Cashinahua, Yidiɲ DOM,
      Bulgarian/Shambala ditransitive person-role splits.

    Each is silent on the other's territory at the level of its core
    algorithm. Haspelmath's §11.2 reduction to form-frequency does NOT
    engage Marantz's structural account of Hindi aspect splits;
    Marantz's `assignCases` algorithm cannot generate Fore-style
    prominence-conditioned ERG without an additional prominence
    parameter not present in the formalization.

    This section makes the partition Lean-checkable, following the
    contrastive-theorem pattern from [bruening-2021]. -/

/-- [marantz-1991]: Hindi's aspect-conditioned ERG split is derived
    structurally — the *same* `[⟨"agent", none⟩, ⟨"theme", none⟩]` NP
    list produces ERG-marking under perfective and NOM-ACC under
    imperfective, driven by the `CaseLanguageType` parameter alone.
    No prominence input enters the algorithm. -/
theorem marantz_hindi_split_is_structural :
    Marantz1991.hindiTransitive .perfective ≠
    Marantz1991.hindiTransitive .imperfective :=
  Marantz1991.hindi_split_is_algorithmic

/-- [marantz-1991]: in ergative mode, the *higher* of two caseless
    NPs gets ERG, regardless of any "prominence" attribute. The function
    signature `assignCases : CaseLanguageType → List NPInDomain → List CasedNP`
    has no prominence input — `NPInDomain` carries only `label : String`
    and `lex : Option Case`. The two-NP transitive case witnesses this
    uniformity. -/
theorem marantz_ergative_uniform_on_higher :
    Syntax.Case.getCaseOf "agent"
      (Syntax.Case.assignCases .ergative
        [⟨"agent", none⟩, ⟨"theme", none⟩]) = some .erg := by
  decide

/-- [marantz-1991]: a sole NP in ergative mode gets unmarked case
    (no competitor for dependent ERG). This is the "Ergative
    generalization" (Marantz 1991, statement (6), p. 13): no ERG on
    derived subjects. The empirical witness is Hindi unaccusatives
    (*siitta (\*ne) aayii*). -/
theorem marantz_ergative_no_marking_on_sole_np :
    Syntax.Case.getCaseOf "theme"
      (Syntax.Case.assignCases .ergative [⟨"theme", none⟩]) = some .abs := by
  decide

/-- The two frameworks partition the empirical territory of split case
    marking. Marantz's algorithm cannot generate the *partial* marking
    Haspelmath U6 covers (Fore: *only* non-prominent A gets ERG);
    Haspelmath's reduction to form-frequency does not derive
    Marantz-style aspect splits.

    The structural witness: for ANY two label choices `l₁, l₂, l₁', l₂'`
    and ANY language type, `assignCases` produces the same case sequence
    (up to label relabeling). The labels are uninterpreted strings — the
    function cannot read them as proxies for prominence. There is no
    prominence input to `assignCases : CaseLanguageType → List NPInDomain
    → List CasedNP`; `NPInDomain` carries only `label : String` and
    `lex : Option Case`. A Fore-style prominence-conditioned ERG would
    require an extra parameter not present in the algorithm. -/
theorem marantz_haspelmath_partition_witness
    (lang : Syntax.Case.CaseLanguageType) (l₁ l₂ l₁' l₂' : String) :
    (Syntax.Case.assignCases lang
        [⟨l₁, none⟩, ⟨l₂, none⟩]).map (·.case) =
    (Syntax.Case.assignCases lang
        [⟨l₁', none⟩, ⟨l₂', none⟩]).map (·.case) := by
  cases lang <;> rfl

end Haspelmath2021
