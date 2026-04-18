import Linglib.Theories.Syntax.Minimalism.Core.DependentCase

/-!
# Sakha Two-Modality Case Assignment @cite{baker-vinokurova-2010}

@cite{baker-vinokurova-2010} argue that Sakha (Turkic) requires
**both** of the case-assignment mechanisms that linguistic theory has
on offer: configurational dependent case (Marantz; @cite{marantz-1991})
for ACC and DAT, and Agree with a functional head (Chomsky;
@cite{chomsky-2000}) for NOM and GEN. The two modalities are not in
competition — they coexist in a single grammar:

- **DAT rule (paper (4a)/(85)):** if NP1 c-commands NP2 in the same
  VP-phase and NP2 is unmarked, value NP1 as DAT.
- **ACC rule (paper (4b)/(85)):** if NP1 c-commands NP2 in any phase
  and NP1 is unmarked, value NP2 as ACC. (4a) bleeds (4b) on the VP
  cycle by Elsewhere ordering.
- **NOM rule (paper (5)/(86)):** finite T Agrees with the highest
  unvalued NP visible on the CP cycle and values it NOM.
- **GEN rule (paper (5)/(86)):** D Agrees with the possessor inside DP
  and values it GEN. (DP-internal; not modeled by the clausal
  algorithm here, but parameterized via `genMode := .agreeD`.)

The library's `CaseSystemConfig` (in `DependentCase.lean`) is
parameterized so each of the four structural cases gets an independent
mechanism slot. Sakha is the configuration where ACC and DAT are
dependent while NOM and GEN are Agree-based — exactly the
@cite{baker-vinokurova-2010} grammar.

## Phase visibility and DOM

NPs carry both a `basePhase` (where they were merged) and a
`shifted` flag (did they move to a higher phase before evaluation).
This captures the Phase Impenetrability Condition: an unshifted NP
inside VP is invisible on the CP cycle, so it cannot be a competitor
for the ACC rule on that cycle.

Differential Object Marking falls out: specific objects shift to the
edge of VP (or beyond) and become visible on the CP cycle, where they
form a competitor pair with the subject and receive ACC. Nonspecific
objects stay inside VP, are invisible to T, and surface unmarked.

This file states the central derivations for monotransitives,
ditransitives, unaccusatives, and DOM. ECM and DP-level GEN are
acknowledged but not formalized; the clausal algorithm covers them
in principle but the present `PhasedNP` representation does not yet
distinguish embedded vs matrix domains.
-/

namespace Phenomena.Case.Studies.BakerVinokurova2010

open Minimalism

-- ============================================================================
-- § 1: The Sakha Case System Configuration
-- ============================================================================

/-- Sakha's case system: accusative alignment with the
    @cite{baker-vinokurova-2010} two-modality split. ACC and DAT are
    dependent (Marantz); NOM and GEN are Agree-based (Chomsky). -/
def sakhaConfig : CaseSystemConfig where
  langType := .accusative
  nomMode  := .agreeT
  datMode  := .dependent
  accMode  := .dependent
  genMode  := .agreeD

theorem sakha_acc_dependent : sakhaConfig.accMode = .dependent := rfl
theorem sakha_dat_dependent : sakhaConfig.datMode = .dependent := rfl
theorem sakha_nom_agree     : sakhaConfig.nomMode = .agreeT    := rfl
theorem sakha_gen_agree     : sakhaConfig.genMode = .agreeD    := rfl

/-- The two-modality thesis stated as a structural property of the
    config: at least one case is configurational, at least one is
    Agree-based. Mongolian shares the configurational ACC but uses
    a nonstructural DAT, so Sakha is the strictest exemplar. -/
theorem two_modalities_present :
    (sakhaConfig.accMode = .dependent ∨ sakhaConfig.datMode = .dependent) ∧
    (sakhaConfig.nomMode = .agreeT ∨ sakhaConfig.genMode = .agreeD) :=
  ⟨Or.inl rfl, Or.inl rfl⟩

-- ============================================================================
-- § 2: NP Position Constructors
-- ============================================================================

/-- A subject NP merged at the vP edge / SpecTP — visible on the CP cycle. -/
def subj (label : String) : PhasedNP :=
  { label := label, lexicalCase := none, basePhase := .cp, shifted := false }

/-- A VP-internal NP that has shifted (specific object, raised theme). -/
def shiftedVP (label : String) : PhasedNP :=
  { label := label, lexicalCase := none, basePhase := .vp, shifted := true }

/-- A VP-internal NP that has not shifted (nonspecific object). -/
def lowVP (label : String) : PhasedNP :=
  { label := label, lexicalCase := none, basePhase := .vp, shifted := false }

-- ============================================================================
-- § 3: Monotransitive — Specific (= Shifted) Object
-- ============================================================================

/-- "Masha cake-ACC ate" with a specific object: the object shifts,
    competes with the subject on the CP cycle, and is valued ACC. -/
def transSpecific : List PhasedNP := [subj "subj", shiftedVP "obj"]

def transSpecificResult : List CasedNP := assignCasesPhased sakhaConfig transSpecific

/-- Specific object surfaces with ACC, by the (4b)/(86) ACC rule on
    the CP cycle. -/
theorem trans_specific_obj_acc :
    getCaseOf "obj" transSpecificResult = some .acc := by decide

/-- The ACC on the specific object is dependent case, not lexical or
    Agree-based — verifying the Marantz modality is doing the work. -/
theorem trans_specific_obj_dependent :
    getSourceOf "obj" transSpecificResult = some .dependent := by decide

/-- Subject is valued NOM by T-Agree (paper (5)/(86)). -/
theorem trans_specific_subj_nom :
    getCaseOf "subj" transSpecificResult = some .nom := by decide

/-- The NOM on the subject is the Chomskyan Agree modality, not the
    Marantzian unmarked default — the central contrast with
    Mongolian and the structural payoff of `nomMode := .agreeT`. -/
theorem trans_specific_subj_agree :
    getSourceOf "subj" transSpecificResult = some .agree := by decide

-- ============================================================================
-- § 4: Monotransitive — Nonspecific (= Unshifted) Object
-- ============================================================================

/-- "Masha cake ate" with a nonspecific object: the object stays in
    VP and is invisible to T on the CP cycle, so the ACC rule never
    fires (no competitor pair). The object surfaces unmarked. -/
def transNonspecific : List PhasedNP := [subj "subj", lowVP "obj"]

def transNonspecificResult : List CasedNP :=
  assignCasesPhased sakhaConfig transNonspecific

/-- Nonspecific object: no ACC, surfaces unmarked. PIC-driven DOM. -/
theorem trans_nonspecific_obj_unmarked :
    getSourceOf "obj" transNonspecificResult = some .unmarked := by decide

/-- Subject still gets NOM by T-Agree — the Agree probe always finds
    the highest CP-visible unvalued NP, which is the subject in both
    DOM variants. -/
theorem trans_nonspecific_subj_nom :
    getCaseOf "subj" transNonspecificResult = some .nom ∧
    getSourceOf "subj" transNonspecificResult = some .agree := by decide

-- ============================================================================
-- § 5: DOM Contrast — The Algorithmic Source of Differential ACC
-- ============================================================================

/-- The DOM alternation: object case differs purely by whether the
    object has shifted out of VP, with no change to the subject. The
    grammar does not stipulate "specificity → ACC"; it is derived
    from phase visibility + the (4b) ACC rule. -/
theorem dom_alternation_in_object :
    getCaseOf "obj" transSpecificResult ≠ getCaseOf "obj" transNonspecificResult := by
  decide

/-- The subject case is invariant across the DOM contrast — the same
    NOM-by-Agree applies whether the object is specific or not. -/
theorem dom_subject_invariant :
    getCaseOf "subj" transSpecificResult = getCaseOf "subj" transNonspecificResult := by
  decide

-- ============================================================================
-- § 6: Ditransitive — Goal Gets DAT, Theme Gets ACC
-- ============================================================================

/-- Ditransitive with a specific theme. Three NPs:
    subj (CP), goal (VP), theme (VP, shifted). The DAT rule fires on
    the VP cycle for the goal (highest of two unmarked VP-internals),
    bleeding ACC at that cycle by Elsewhere. The theme then competes
    with the subject on the CP cycle and is valued ACC. -/
def ditransitive : List PhasedNP :=
  [subj "subj", lowVP "goal", shiftedVP "theme"]

def ditransitiveResult : List CasedNP := assignCasesPhased sakhaConfig ditransitive

/-- Goal NP receives DAT by the (4a)/(85) DAT rule on the VP cycle. -/
theorem ditrans_goal_dat :
    getCaseOf "goal" ditransitiveResult = some .dat ∧
    getSourceOf "goal" ditransitiveResult = some .dependent := by decide

/-- Specific theme receives ACC on the CP cycle (after the goal has
    been valued DAT and removed from competition). -/
theorem ditrans_theme_acc :
    getCaseOf "theme" ditransitiveResult = some .acc ∧
    getSourceOf "theme" ditransitiveResult = some .dependent := by decide

/-- Subject receives NOM by T-Agree. -/
theorem ditrans_subj_nom :
    getCaseOf "subj" ditransitiveResult = some .nom ∧
    getSourceOf "subj" ditransitiveResult = some .agree := by decide

/-- The full NOM/DAT/ACC ditransitive pattern derived in one step from
    `assignCasesPhased`: this is the central empirical signature of
    @cite{baker-vinokurova-2010}'s analysis, and it follows from the
    interaction of the two modalities, not from a stipulated
    case-assignment template. -/
theorem ditrans_full_pattern :
    getCaseOf "subj" ditransitiveResult = some .nom ∧
    getCaseOf "goal" ditransitiveResult = some .dat ∧
    getCaseOf "theme" ditransitiveResult = some .acc := by decide

/-- Elsewhere ordering: in the ditransitive, only ONE NP gets ACC
    despite there being two VP-internal NPs. The (4a) DAT rule bleeds
    (4b) at the VP cycle.

    This is the per-datum verification. The structural reason — that
    `applyAccRule` cannot overwrite *any* marked NP, regardless of the
    input — is `applyAccRule_preserves_marked_at` in
    `DependentCase.lean`, and the full pipeline analogue is
    `dat_persists_through_assignCasesPhased`. -/
theorem dat_bleeds_acc_on_vp_cycle :
    (ditransitiveResult.filter (·.case == .acc)).length = 1 ∧
    (ditransitiveResult.filter (·.case == .dat)).length = 1 := by decide

-- ============================================================================
-- § 7: Unaccusative — Sole NP Gets NOM, Not ACC
-- ============================================================================

/-- Unaccusative: theme raises to SpecTP (modeled with `basePhase :=
    .cp`). With a single visible NP on the CP cycle, no ACC competitor
    exists; T-Agree values the theme NOM. -/
def unaccusative : List PhasedNP := [subj "theme"]

def unaccResult : List CasedNP := assignCasesPhased sakhaConfig unaccusative

theorem unacc_theme_nom :
    getCaseOf "theme" unaccResult = some .nom ∧
    getSourceOf "theme" unaccResult = some .agree := by decide

/-- No NP receives ACC in the unaccusative — the dependent ACC rule
    requires two unmarked competitors and there is only one NP. -/
theorem unacc_no_acc :
    unaccResult.all (·.case ≠ .acc) := by decide

-- ============================================================================
-- § 8: Two-Modality Cross-Comparison
-- ============================================================================

/-! These derivations exhibit *both* modalities firing within a single
sentence: dependent case for one NP, Agree for another. This is what
forces a hybrid grammar — neither pure Marantz nor pure Chomsky covers
the full Sakha pattern. -/

/-- In the specific-object monotransitive, subject and object receive
    case from *different* mechanisms: NOM by Agree, ACC by dependent
    case. -/
theorem trans_specific_uses_both_modalities :
    getSourceOf "subj" transSpecificResult = some .agree ∧
    getSourceOf "obj"  transSpecificResult = some .dependent := by decide

/-- In the ditransitive, all three modal sources are attested: Agree
    (subject NOM), and two dependent cases (goal DAT, theme ACC). The
    .lexical and .unmarked sources are absent from this derivation —
    they would arise for quirky-DAT subjects and for nonspecific
    themes respectively. -/
theorem ditrans_three_sources :
    getSourceOf "subj"  ditransitiveResult = some .agree ∧
    getSourceOf "goal"  ditransitiveResult = some .dependent ∧
    getSourceOf "theme" ditransitiveResult = some .dependent := by decide

-- ============================================================================
-- § 9: Mongolian Contrast (cf. Fragments/Mongolian/Case.lean)
-- ============================================================================

/-! @cite{gong-2022} adopts the Sakha framework for Mongolian but
swaps `datMode` from `.dependent` to `.nonstructural`: Mongolian DAT
is inherent. Holding ACC, NOM, GEN modes constant and varying only
DAT, the algorithm correctly predicts that Mongolian ditransitives
have no DAT-from-the-algorithm — DAT must come pre-loaded as
`lexicalCase`. -/

/-- The Mongolian config differs from Sakha only in `datMode`. -/
def mongolianLikeConfig : CaseSystemConfig :=
  { sakhaConfig with datMode := .nonstructural }

/-- Same ditransitive input, Mongolian config: the goal is no longer
    valued DAT by the algorithm — it becomes an unmarked VP-internal
    NP, which then competes with the theme on the VP cycle for ACC. -/
def ditransMongolian : List CasedNP :=
  assignCasesPhased mongolianLikeConfig ditransitive

/-- Without dependent DAT, no NP gets DAT from the algorithm. The DAT
    on Mongolian goals must be supplied as inherent/lexical case at
    the lexicon level — exactly @cite{gong-2022}'s claim. -/
theorem mongolian_no_algorithmic_dat :
    ditransMongolian.all (·.case ≠ .dat) := by decide

/-- The Sakha vs. Mongolian contrast localizes to a single config
    parameter — `datMode` — exactly as predicted by the parameterized
    `CaseSystemConfig` design. -/
theorem sakha_mongolian_diff_in_dat :
    getCaseOf "goal" ditransitiveResult ≠ getCaseOf "goal" ditransMongolian := by
  decide

-- ============================================================================
-- § 10: Structural Property — Agree-NOM is Not Unmarked
-- ============================================================================

/-! A structural payoff of distinguishing `.agree` from `.unmarked`:
the same surface case (NOM) can have two distinct sources, and the
source matters for downstream computations (visibility to higher
probes, raising-to-object, etc.). Sakha NOM is always `.agree`; a
default-NOM language (pure Marantz) would have it as `.unmarked`. -/

/-- Every NOM in Sakha derivations comes from T-Agree, never from
    the unmarked default. This holds across all derivations in this
    file by construction (because `nomMode := .agreeT`), and is the
    structural fingerprint of the Chomsky modality. -/
theorem all_nom_is_agree_in_sakha :
    transSpecificResult.all (fun cn => cn.case ≠ .nom ∨ cn.source = .agree) ∧
    ditransitiveResult.all (fun cn => cn.case ≠ .nom ∨ cn.source = .agree) ∧
    unaccResult.all       (fun cn => cn.case ≠ .nom ∨ cn.source = .agree) := by
  decide

-- ============================================================================
-- § 11: Causative Cascade — The Cleanest Test of Dependent Case
-- ============================================================================

/-! @cite{baker-vinokurova-2010} (23)–(24): morphological causatives in
Sakha exhibit a striking cascade. The causee surfaces with ACC if the
base verb is intransitive (one argumental NP in max VP, no DAT competitor)
but with DAT if the base verb is transitive (two argumental NPs in max
VP, (4a) fires marking the causee as DAT).

This is the cleanest test of the dependent-case modality: *adding* an
NP (the lower theme) *changes* the case on a different NP (the causee),
which is impossible under any version of head-driven Agree case. The
algorithmic Mechanism — (4a) bleeding (4b) on the VP cycle — predicts
the cascade without any additional stipulation. -/

/-- (23a) "Sardaana made Aisen cry" — base verb 'cry' is intransitive.
    Max VP contains only the causee (Aisen). With only one argumental
    NP visible on the VP cycle, neither (4a) nor (4b) fires. The causee
    shifts to the CP phase, becomes a competitor for the causer
    (Sardaana), and is valued ACC by (4b) on the CP cycle. -/
def causativeOfIntransitive : List PhasedNP :=
  [subj "causer", shiftedVP "causee"]

def causIntransResult : List CasedNP :=
  assignCasesPhased sakhaConfig causativeOfIntransitive

theorem caus_intrans_causee_acc :
    getCaseOf "causee" causIntransResult = some .acc ∧
    getSourceOf "causee" causIntransResult = some .dependent := by decide

theorem caus_intrans_causer_nom :
    getCaseOf "causer" causIntransResult = some .nom ∧
    getSourceOf "causer" causIntransResult = some .agree := by decide

/-- (23b) "Misha made Masha eat soup" — base verb 'eat' is transitive.
    Max VP contains the causee (Masha) and theme (soup), both argumental.
    On the VP cycle, (4a) fires: Masha (the higher of the two unmarked
    NPs) is valued DAT, bleeding (4b). The theme then shifts to the CP
    phase, competes with the causer (Misha), and is valued ACC. -/
def causativeOfTransitive : List PhasedNP :=
  [subj "causer", lowVP "causee", shiftedVP "theme"]

def causTransResult : List CasedNP :=
  assignCasesPhased sakhaConfig causativeOfTransitive

theorem caus_trans_causee_dat :
    getCaseOf "causee" causTransResult = some .dat ∧
    getSourceOf "causee" causTransResult = some .dependent := by decide

theorem caus_trans_theme_acc :
    getCaseOf "theme" causTransResult = some .acc ∧
    getSourceOf "theme" causTransResult = some .dependent := by decide

theorem caus_trans_causer_nom :
    getCaseOf "causer" causTransResult = some .nom ∧
    getSourceOf "causer" causTransResult = some .agree := by decide

/-- The causative cascade: the *same* causative morpheme produces ACC
    on the causee in (23a) and DAT on the causee in (23b). The only
    difference is the transitivity of the base verb — i.e., the
    *number of argumental NPs in max VP*. This is the structural
    signature of dependent case. -/
theorem causee_case_depends_on_base_transitivity :
    getCaseOf "causee" causIntransResult = some .acc ∧
    getCaseOf "causee" causTransResult = some .dat := by decide

-- ============================================================================
-- § 12: Bare-NP Adverb Test — The Argumental Filter
-- ============================================================================

/-! @cite{baker-vinokurova-2010} (8)–(9): rules (4a)/(4b) only apply
between *argumental* NPs (those bearing a θ-role w.r.t. some case-
assigning head). Bare-NP adverbs like *sajyn* 'summer' do not count
as case competitors, even when c-commanded by another caseless NP.

The PhasedNP `isArgumental` field captures this: when set to false,
the NP is filtered out of `unmarkedVisible` and so cannot trigger or
receive dependent case. The very same noun that surfaces as ACC when
functioning as the object of a transitive verb (8c) surfaces unmarked
when functioning as a temporal adverb (8a)/(8b). -/

/-- Adverbial NP — bears no θ-role w.r.t. a case-assigning head. -/
def adverb (label : String) : PhasedNP :=
  { label := label, lexicalCase := none, basePhase := .cp,
    shifted := false, isArgumental := false }

/-- (8a) "Bihigi beqehee ystan-nybyt" 'we yesterday jumped'. Two NPs:
    'we' (subject, argumental) and 'yesterday' (adverb, non-argumental).
    The adverb is filtered from case competition; only one argumental
    NP is visible to T-Agree on the CP cycle. -/
def intransitiveWithAdverb : List PhasedNP :=
  [subj "subj", adverb "yesterday"]

def intrAdvResult : List CasedNP :=
  assignCasesPhased sakhaConfig intransitiveWithAdverb

/-- The adverb is *not* marked ACC: rule (4b) does not see it as a
    case competitor. The subject is valued NOM by T-Agree, and the
    adverb falls through to the default sweep with unmarked NOM. -/
theorem adverb_does_not_get_acc :
    getCaseOf "yesterday" intrAdvResult = some .nom ∧
    getSourceOf "yesterday" intrAdvResult = some .unmarked := by decide

theorem subj_with_adverb_nom_agree :
    getCaseOf "subj" intrAdvResult = some .nom ∧
    getSourceOf "subj" intrAdvResult = some .agree := by decide

/-- (8c) "Masha sajyn-y axt-ar" 'Masha summer-ACC misses'. Same noun
    'summer', now functioning as the *object* of transitive 'miss' —
    it bears a θ-role and so counts as argumental. Now (4b) applies
    and the object is marked ACC, exactly the contrast (8a/b vs 8c). -/
def transitiveSummerObject : List PhasedNP :=
  [subj "masha", shiftedVP "summer"]

def transSummerResult : List CasedNP :=
  assignCasesPhased sakhaConfig transitiveSummerObject

theorem summer_as_object_gets_acc :
    getCaseOf "summer" transSummerResult = some .acc ∧
    getSourceOf "summer" transSummerResult = some .dependent := by decide

/-- The argumental contrast: the very same lexical noun receives ACC
    when argumental and unmarked NOM when adverbial. The grammar does
    not stipulate that 'summer' is ambiguous between an argumental
    and an adverbial entry; both readings reduce to a single algorithm
    parameterized by the `isArgumental` feature. -/
theorem argumental_status_drives_case :
    getCaseOf "summer" transSummerResult ≠ getCaseOf "yesterday" intrAdvResult ∨
    getSourceOf "summer" transSummerResult ≠ getSourceOf "yesterday" intrAdvResult := by
  decide

-- ============================================================================
-- § 13: Substantive Two-Modality Theorem
-- ============================================================================

/-! Replacing the trivial `two_modalities_present` (which only restated
the config) with a theorem that *no single modality* — pure Marantz
or pure Chomsky — can produce the Sakha derivational pattern. The
two-modality grammar is empirically required, not just stipulated. -/

/-- Pure Marantz (Sakha pattern with NOM as unmarked default and no
    Agree-based case): all structural cases are configurational. -/
def pureMarantz : CaseSystemConfig where
  langType := .accusative
  nomMode  := .unmarkedDefault
  datMode  := .dependent
  accMode  := .dependent
  genMode  := .nonstructural

/-- Pure Chomsky: every structural case assigned by Agree with a
    functional head. v-Agree marks the lowest CP-visible argumental
    NP as ACC; T-Agree marks the highest as NOM; D-Agree marks DP-
    internals as GEN; DAT is purely lexical/inherent
    (`.nonstructural`). This is the standard
    @cite{chomsky-2000}/@cite{chomsky-2001} configuration. -/
def pureChomsky : CaseSystemConfig where
  langType := .accusative
  nomMode  := .agreeT
  datMode  := .nonstructural
  accMode  := .agreeV
  genMode  := .agreeD

/-- Pure Marantz produces the same surface NOM on the subject as Sakha
    — but with `source := .unmarked`, not `.agree`. The structural
    fingerprint of the modality differs even when the morphology
    coincides. -/
theorem pure_marantz_subj_unmarked :
    getSourceOf "subj" (assignCasesPhased pureMarantz ditransitive) = some .unmarked := by
  decide

theorem sakha_subj_distinct_from_pure_marantz :
    getSourceOf "subj" (assignCasesPhased pureMarantz ditransitive) ≠
    getSourceOf "subj" ditransitiveResult := by decide

/-- Pure Chomsky has `datMode := .nonstructural`, so the algorithm
    never derives DAT — Mongolian-style, every DAT must be lexical.
    This contradicts the Sakha pattern where DAT is productive on
    structural goals. -/
theorem pure_chomsky_no_algorithmic_dat :
    (assignCasesPhased pureChomsky ditransitive).all (·.case ≠ .dat) := by decide

/-- Pure Chomsky's v-Agree fires under `accMode := .agreeV` and marks
    the theme ACC via Agree (not via the dependent rule). This makes
    the source-distinction operative, not just the case-distinction:
    Sakha derives ACC via `.dependent`, pure Chomsky via `.agree`. -/
theorem pure_chomsky_acc_via_agree :
    getCaseOf "theme" (assignCasesPhased pureChomsky ditransitive) = some .acc ∧
    getSourceOf "theme" (assignCasesPhased pureChomsky ditransitive) = some .agree := by
  decide

/-- The causative cascade is the canonical wedge against any
    pure-Agree theory of structural case. Adding the lower theme to
    a transitive-base causative *changes* the case on the causee
    (ACC → DAT) — but no head's Agree relation has been altered,
    only the count of NPs in max VP. Pure Chomsky predicts the
    causee in (23b) surfaces with NOM-by-default, exactly because
    its v-Agree probe targets the theme; the (4a)/dependent-DAT
    rule cannot apply without `datMode := .dependent`. -/
theorem pure_chomsky_misses_causative_cascade :
    getCaseOf "causee" (assignCasesPhased pureChomsky causativeOfTransitive) ≠
      some .dat ∧
    getCaseOf "causee" causTransResult = some .dat := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The strong two-modality theorem: neither pure modality derives
    the Sakha pattern. Pure Marantz fails the NOM-as-Agree fingerprint
    (subject NOM source = `.unmarked`). Pure Chomsky fails on DAT —
    not just on the ditransitive but, more sharply, on the causative
    cascade where adding an NP changes another NP's case in a way no
    Agree relation can mediate. The two-modality grammar is
    *required*, not stipulated. -/
theorem two_modalities_required :
    -- Pure Marantz fails on the NOM source fingerprint
    (getSourceOf "subj" (assignCasesPhased pureMarantz ditransitive) ≠ some .agree) ∧
    -- Pure Chomsky fails on DAT in the ditransitive
    (¬ ∃ cn ∈ assignCasesPhased pureChomsky ditransitive, cn.case = .dat) ∧
    -- Pure Chomsky additionally fails on the causative cascade
    (getCaseOf "causee" (assignCasesPhased pureChomsky causativeOfTransitive) ≠
       some .dat) ∧
    -- Sakha succeeds on all three
    (getSourceOf "subj" ditransitiveResult = some .agree) ∧
    (∃ cn ∈ ditransitiveResult, cn.case = .dat) ∧
    (getCaseOf "causee" causTransResult = some .dat) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- § 14: D-Agree GEN — DP-Internal Possessors (paper (5)/(86))
-- ============================================================================

/-! @cite{baker-vinokurova-2010} (5)/(86): D Agrees with the
possessor inside DP and values it GEN. The clausal cycles see the DP
as opaque — its possessor is filtered out of `unmarkedVisible` by
the `inDP` flag — and `applyGenAgree` runs as the DP-internal
counterpart to T-Agree. This is the second Agree-modality slot
(`genMode := .agreeD`) that distinguishes the Sakha grammar from a
purely Marantzian one. -/

/-- A DP-internal possessor: opaque to clause-level case competition
    but valued GEN by D-Agree. -/
def possessor (label : String) : PhasedNP :=
  { label := label, lexicalCase := none, basePhase := .cp,
    shifted := false, isArgumental := true, inDP := true }

/-- "Aisen's house [is in town]" — the matrix subject is a DP whose
    possessor `aisen` is valued GEN by D-Agree. The possessor is
    invisible to clausal probes; the head noun (`house`) is the
    subject of T-Agree and surfaces NOM. -/
def possessedSubject : List PhasedNP := [subj "house", possessor "aisen"]

def possessedResult : List CasedNP :=
  assignCasesPhased sakhaConfig possessedSubject

theorem possessor_gets_gen_via_agree :
    getCaseOf "aisen" possessedResult = some .gen ∧
    getSourceOf "aisen" possessedResult = some .agree := by decide

theorem possessed_head_gets_nom :
    getCaseOf "house" possessedResult = some .nom ∧
    getSourceOf "house" possessedResult = some .agree := by decide

/-- The GEN possessor is invisible to (4b)/ACC: in a transitive with
    a possessed object, the head noun is what receives ACC, not the
    possessor (which is busy being valued GEN inside its DP). -/
def transWithPossessedObj : List PhasedNP :=
  [subj "subj", shiftedVP "book", possessor "aisen"]

def transPossResult : List CasedNP :=
  assignCasesPhased sakhaConfig transWithPossessedObj

theorem possessor_is_opaque_to_clausal_acc :
    getCaseOf "aisen" transPossResult = some .gen ∧
    getCaseOf "book"  transPossResult = some .acc := by decide

/-- The two Agree modalities (T → NOM, D → GEN) coexist with the
    two dependent modalities (DAT, ACC) in a single derivation —
    the strongest empirical demonstration of the four-slot
    parameterization at work. -/
theorem all_four_modalities_in_one_clause :
    let cl : List PhasedNP :=
      [subj "subj", lowVP "goal", shiftedVP "theme", possessor "aisen"]
    let r := assignCasesPhased sakhaConfig cl
    getSourceOf "subj"  r = some .agree     ∧  -- T-Agree
    getSourceOf "aisen" r = some .agree     ∧  -- D-Agree
    getSourceOf "goal"  r = some .dependent ∧  -- (4a)
    getSourceOf "theme" r = some .dependent := by decide

-- ============================================================================
-- § 15: Soundness — One Case per NP (Re-export from DependentCase)
-- ============================================================================

/-- The phased algorithm is total on every Sakha derivation in this
    file: each input NP appears in the output with exactly one case.
    Follows from `assignCasesPhased_length` in `DependentCase.lean`. -/
theorem all_sakha_derivations_total :
    transSpecificResult.length = transSpecific.length ∧
    transNonspecificResult.length = transNonspecific.length ∧
    ditransitiveResult.length = ditransitive.length ∧
    unaccResult.length = unaccusative.length ∧
    causIntransResult.length = causativeOfIntransitive.length ∧
    causTransResult.length = causativeOfTransitive.length ∧
    intrAdvResult.length = intransitiveWithAdverb.length ∧
    transSummerResult.length = transitiveSummerObject.length ∧
    possessedResult.length = possessedSubject.length ∧
    transPossResult.length = transWithPossessedObj.length := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply assignCasesPhased_length

end Phenomena.Case.Studies.BakerVinokurova2010
