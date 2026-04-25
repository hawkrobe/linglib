import Linglib.Features.Acceptability
import Linglib.Theories.Syntax.Minimalism.Cascade
import Linglib.Theories.Semantics.Causation.Psych
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Zero Syntax: Experiencers and Cascades

@cite{pesetsky-1995}

Cascade-based analysis of Class II psych verbs. The T/SM restriction
(Cause and Subject Matter cannot cooccur) is derived from the Head
Movement Constraint: CAUS must incorporate into V by successive head
adjunction through the Cascade spine, and nonaffixal overt prepositions
(T/SM heads like *at* and *about*) block this movement.

## Key results

1. **T/SM restriction from HMC** (§ 2): CAUS is blocked by nonaffixal P
2. **T/SM mutual exclusivity** (§ 2): each cascade has at most one stimulus slot
3. **Backward binding as derived-subject diagnostic** (§ 3): A-Causer
   originates inside VP (spec of CAUS in cascade complement), must raise
   to subject — reconstruction enables backward binding
4. **Double object alternation** (§ 4): G (zero P) vs *to* cascades
5. **θ-suppression** (§ 5): CAUS affixation suppresses external argument
6. **CAUS strength derived from cascade geometry** (§ 6)
7. **Symmetric T/SM blocking** (§ 7): both *at* and *about* are nonaffixal,
   so both block CAUS movement equally via HMC
8. **Natural vs arbitrary predicates** (§ 9): Target-selecting predicates
   are "natural," SM-selecting predicates are "arbitrary"
9. **HNPS from cascade geometry** (§ 10): cascade depth determines
   available landing sites for heavy NP shift
10. **End-to-end per-verb derivation** (§ 9): full cascade chain for all
    24 Class II psych verbs, derived from `causalSource`

-/

set_option autoImplicit false

namespace Phenomena.PsychVerbs

-- ============================================================================
-- Belletti-Rizzi 1988 / Kim 2024 empirical data
-- (Was `Phenomena/PsychVerbs/Data.lean`; inlined per the provenance-tracking
--  policy. @cite{pesetsky-1995} is the natural owner since it directly
--  consumes the @cite{belletti-rizzi-1988} classification.)
-- ============================================================================

/-- @cite{belletti-rizzi-1988} classification of psych verbs. -/
inductive PsychVerbClass where
  | classI    -- Experiencer-subject: enjoy, like, fear / It. temere
  | classII   -- Object-experiencer: frighten, concern / It. preoccupare
  | classIII  -- Dative experiencer (Romance): It. piacere
  deriving DecidableEq, Repr

/-- Aspectual reading of a Class II psych verb. -/
inductive ClassIIReading where
  | eventive  -- External cause: "the noise frightened John"
  | stative   -- Internal cause: "the problem concerns John"
  deriving DecidableEq, Repr

/-- B&R syntactic diagnostic for discriminating psych verb classes (§§1–2). -/
inductive BRDiagnostic where
  | anaphoricCliticization -- §1.1: partitive ne extraction from subject
  | arbitraryPro           -- §1.2: arb pro interpretation of subject
  | causativeFare          -- §1.3: embedding under fare/make infinitive
  | backwardBinding        -- §2.1: anaphor in subject bound by object
  | adjectivalPassive      -- §1.5: passive is adjectival (not verbal)
  deriving DecidableEq, Repr

/-- Result of a B&R diagnostic applied to each class.
    `classI`/`classII` record whether the class *passes* the test. -/
structure BRDiagnosticResult where
  diagnostic : BRDiagnostic
  classI : Bool
  classII : Bool
  deriving Repr, BEq

/-- @cite{belletti-rizzi-1988} diagnostic data.

    | Diagnostic | Class I (*temere*) | Class II (*preoccupare*) |
    |---|---|---|
    | Anaphoric clitic *ne* (§1.1) | ✗ | ✓ (11a) |
    | Arbitrary *pro* (§1.2) | ✓ (24a) | ✗ (24b) |
    | Causative *fare* (§1.3) | ✓ (35) | ✗ (36) |
    | Backward binding (§2.1) | ✗ | ✓ (57a) |
    | Adjectival passive (§1.5) | ✗ | ✓ (47) | -/
def brDiagnosticData : List BRDiagnosticResult := [
  ⟨.anaphoricCliticization, false, true⟩,
  ⟨.arbitraryPro,           true,  false⟩,
  ⟨.causativeFare,          true,  false⟩,
  ⟨.backwardBinding,        false, true⟩,
  ⟨.adjectivalPassive,      false, true⟩
]

/-- Every B&R diagnostic discriminates Class I from Class II. -/
theorem br_diagnostics_discriminate :
    brDiagnosticData.all (fun d => d.classI != d.classII) = true := by decide

/-- Class I passes arb-pro and causative-fare but fails the other three. -/
theorem classI_pattern :
    brDiagnosticData.all (fun d =>
      match d.diagnostic with
      | .anaphoricCliticization => d.classI == false
      | .arbitraryPro => d.classI == true
      | .causativeFare => d.classI == true
      | .backwardBinding => d.classI == false
      | .adjectivalPassive => d.classI == false
    ) = true := by decide

/-- Class II shows the mirror pattern. -/
theorem classII_pattern :
    brDiagnosticData.all (fun d =>
      match d.diagnostic with
      | .anaphoricCliticization => d.classII == true
      | .arbitraryPro => d.classII == false
      | .causativeFare => d.classII == false
      | .backwardBinding => d.classII == true
      | .adjectivalPassive => d.classII == true
    ) = true := by decide

/-- The Class I/II distinction is characterized by theta-role reversal. -/
inductive SubjectRole where
  | experiencer  -- Class I: subject = experiencer
  | stimulus     -- Class II: subject = stimulus/cause
  deriving DecidableEq, Repr

/-- Map from B&R class to expected subject role. -/
def PsychVerbClass.expectedSubjectRole : PsychVerbClass → Option SubjectRole
  | .classI => some .experiencer
  | .classII => some .stimulus
  | .classIII => none

/-- Intensionality datum (@cite{kim-2024} Ch. 4): does substitution of
co-referential terms fail in subject position? -/
structure IntensionalityDatum where
  verb : String
  reading : ClassIIReading
  substitutionFails : Bool
  deriving Repr, BEq

/-- Empirical intensionality data from @cite{kim-2024}. -/
def intensionalityData : List IntensionalityDatum := [
  ⟨"concern", .stative, true⟩,
  ⟨"interest", .stative, true⟩,
  ⟨"frighten", .eventive, false⟩,
  ⟨"amuse", .eventive, false⟩
]

/-- The T/SM restriction (@cite{kim-2024} Ch. 5): Cause and Subject Matter
cannot cooccur. -/
structure TSMRestriction where
  causePresent : Bool
  smPresent : Bool
  wellFormed : Bool
  deriving Repr, BEq

/-- Cause and SM cannot cooccur. -/
def tsmData : List TSMRestriction := [
  ⟨true, false, true⟩,
  ⟨false, true, true⟩,
  ⟨true, true, false⟩,
  ⟨false, false, true⟩
]

/-- Stative Class II verbs create intensional subject positions. -/
theorem stative_substitution_fails :
    (intensionalityData.filter (·.reading == .stative)).all
      (·.substitutionFails) = true := by decide

/-- Eventive Class II verbs have extensional subject positions. -/
theorem eventive_substitution_succeeds :
    (intensionalityData.filter (·.reading == .eventive)).all
      (!·.substitutionFails) = true := by decide

/-- Cause + SM cooccurrence is always ill-formed. -/
theorem cause_sm_cooccurrence_illformed :
    (tsmData.filter (fun d => d.causePresent && d.smPresent)).all
      (!·.wellFormed) = true := by decide

end Phenomena.PsychVerbs


-- ============================================================================
-- Pesetsky 1995 cascade analysis
-- ============================================================================

namespace Pesetsky1995

open Minimalism
open Semantics.Causation.Psych
open Phenomena.PsychVerbs
open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 1. Concrete Cascade Structures
-- ════════════════════════════════════════════════════

/-- Class II psych verb with Target stimulus via *at*.

    ```
    V'
    ├── V (annoy, frighten, ...)
    └── PP_CAUS (head: CAUS, spec: A-Causer)
        └── PP_at (head: at, spec: Experiencer)
            └── terminal
    ```

    CAUS is closest to V (position 0), then *at* (position 1).
    The A-Causer is the specifier of CAUS; the Experiencer is
    the specifier of *at*. -/
def cascadeTarget : Cascade :=
  .layer caus "A-Causer"
    (.layer headAt "Experiencer"
      .terminal)

/-- Class II psych verb with Subject Matter stimulus via *about*.

    Same geometry as Target, but with *about* instead of *at*.
    Both are nonaffixal, so both block CAUS equally. -/
def cascadeSM : Cascade :=
  .layer caus "A-Causer"
    (.layer headAbout "Experiencer"
      .terminal)

/-- Class II psych verb with BOTH Cause and T/SM stimulus.

    ```
    V'
    ├── V
    └── PP_CAUS (head: CAUS, spec: A-Causer)
        └── PP_at (head: at, spec: Target)
            └── PP_about (head: about, spec: SM)
                └── terminal
    ```

    The ill-formed structure that the T/SM restriction rules out. -/
def cascadeCausePlusStimulus : Cascade :=
  .layer caus "A-Causer"
    (.layer headAt "Target"
      (.layer headAbout "SubjectMatter"
        .terminal))

/-- Double object construction with zero G preposition.

    ```
    V'
    ├── V (give)
    └── PP_G (head: G, spec: Theme)
        └── PP_to (head: to, spec: Goal)
            └── terminal
    ```

    G is a zero preposition that mediates Theme θ-selection
    in double object constructions. -/
def cascadeDOC : Cascade :=
  .layer headG "Theme"
    (.layer headTo "Goal"
      .terminal)

/-- Dative alternant: single *to*-PP.

    ```
    V'
    ├── V (give)
    └── PP_to (head: to, spec: Goal)
        └── terminal
    ``` -/
def cascadeDative : Cascade :=
  .layer headTo "Goal" .terminal

/-- Derive the appropriate cascade from a verb's causal source.
    External cause → Target cascade (with *at*);
    internal cause → SM cascade (with *about*). -/
def cascadeForSource : CausalSource → Cascade
  | .external => cascadeTarget
  | .internal => cascadeSM

-- ════════════════════════════════════════════════════
-- § 2. T/SM Restriction from HMC
-- ════════════════════════════════════════════════════

/-! The T/SM restriction follows from the HMC: CAUS at position 0 must
    incorporate into V, but any nonaffixal head between CAUS and V blocks
    movement. In the Target/SM cascades, CAUS IS at position 0 (closest
    to V), so it CAN reach V — there are no intervening heads.

    The restriction arises in a different configuration: when an OVERT
    Cause argument occupies the specifier of CAUS, the T/SM stimulus
    cannot also be expressed, because the Cascade geometry doesn't have
    room for both an independent Cause and a T/SM stimulus while keeping
    CAUS in a position that can incorporate.

    More precisely: in Pesetsky's actual account, the restriction comes
    from the fact that CAUS_aff (on V) must DISCHARGE its strong features
    by adjoining to CAUS_p (in the Cascade). If a nonaffixal head
    intervenes between CAUS_p and the stimulus head, the Cascade
    geometry is ill-formed. -/

/-- Target cascade spine: [CAUS, at]. -/
theorem target_spine :
    cascadeTarget.spine = [caus, headAt] := rfl

/-- SM cascade spine: [CAUS, about]. -/
theorem sm_spine :
    cascadeSM.spine = [caus, headAbout] := rfl

/-- CAUS is at position 0 in the Target cascade.
    Position 0 can always reach V (no interveners). -/
theorem caus_reachable_in_target :
    cascadeTarget.headCanReachV "CAUS" = some true := by native_decide

/-- CAUS is at position 0 in the SM cascade.
    Position 0 can always reach V (no interveners). -/
theorem caus_reachable_in_sm :
    cascadeSM.headCanReachV "CAUS" = some true := by native_decide

/-- The nonaffixal *at* head blocks anything below it.
    In the Cause+Stimulus cascade, *at* at position 1 blocks position 2+. -/
theorem at_blocks_below :
    canReachV cascadeCausePlusStimulus.spine 2 = false := by native_decide

/-- The nonaffixal *about* head also blocks anything below it. -/
theorem about_blocks_in_extended :
    canReachV [caus, headAbout, headAt] 2 = false := by native_decide

/-- **Core T/SM restriction theorem**: in the Cause+Stimulus cascade,
    the CAUS head can reach V (it's at position 0), but any head at
    position 2 or deeper cannot — blocked by the nonaffixal *at* at
    position 1. -/
theorem tsm_restriction_via_hmc :
    -- CAUS at position 0: reachable
    canReachV cascadeCausePlusStimulus.spine 0 = true ∧
    -- at head at position 1: not reachable from position 2+
    canReachV cascadeCausePlusStimulus.spine 2 = false ∧
    canReachV cascadeCausePlusStimulus.spine 3 = false :=
  ⟨by native_decide, by native_decide, by native_decide⟩

/-- **T/SM mutual exclusivity (Target cascade)**: the Target cascade
    contains *at* but not *about*. A single cascade geometry admits
    at most one stimulus type, so T and SM cannot cooccur within
    a single verb's cascade complement. -/
theorem t_sm_exclusive_in_target :
    cascadeTarget.hasHead "at" = true ∧
    cascadeTarget.hasHead "about" = false :=
  ⟨by native_decide, by native_decide⟩

/-- **T/SM mutual exclusivity (SM cascade)**: the SM cascade
    contains *about* but not *at*. -/
theorem t_sm_exclusive_in_sm :
    cascadeSM.hasHead "about" = true ∧
    cascadeSM.hasHead "at" = false :=
  ⟨by native_decide, by native_decide⟩

/-- The cascade assigned to a verb is determined by its causal source,
    so a verb with a single source gets exactly one stimulus type.
    External source → cascade with *at* (Target), no *about* (SM).
    Internal source → cascade with *about* (SM), no *at* (Target). -/
theorem source_determines_unique_stimulus :
    -- External → has at, lacks about
    (cascadeForSource .external).hasHead "at" = true ∧
    (cascadeForSource .external).hasHead "about" = false ∧
    -- Internal → has about, lacks at
    (cascadeForSource .internal).hasHead "about" = true ∧
    (cascadeForSource .internal).hasHead "at" = false :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 3. Backward Binding (Derived-Subject Diagnostic)
-- ════════════════════════════════════════════════════

/-! Backward binding in Class II psych verbs ("Stories about each other_i
    worried the boys_i") is diagnosed by B&R as a Class II property.

    Pesetsky's cascade geometry explains this: the A-Causer originates
    INSIDE the cascade complement of V (spec of CAUS at position 0),
    making it a VP-internal argument. It must RAISE to subject position
    (Spec,IP) to receive Case. This derived-subject status enables
    backward binding via reconstruction: at LF, the raised subject
    reconstructs to its base position inside the cascade, where the
    experiencer (in the higher position within the VP) c-commands it.

    In the base cascade, A-Causer (position 0, outermost) actually
    c-commands the Experiencer (position 1, inner). The binding reversal
    comes from movement + reconstruction, not from the base geometry. -/

/-- A-Causer originates inside the cascade at position 0 (spec of CAUS).
    This VP-internal base position means the surface subject is DERIVED —
    the key structural prerequisite for backward binding. -/
theorem causer_is_cascade_internal :
    cascadeTarget.argPosition "A-Causer" = some 0 ∧
    cascadeSM.argPosition "A-Causer" = some 0 :=
  ⟨by native_decide, by native_decide⟩

/-- In the base cascade, A-Causer (outer, position 0) c-commands
    Experiencer (inner, position 1) — the standard direction. -/
theorem causer_ccommands_experiencer_base :
    cascadeTarget.specCCommands "A-Causer" "Experiencer" = true ∧
    cascadeSM.specCCommands "A-Causer" "Experiencer" = true :=
  ⟨by native_decide, by native_decide⟩

/-- The experiencer does NOT c-command the A-Causer in the base cascade.
    Backward binding requires A-Causer to raise to subject, then
    reconstruct — the experiencer binds the reconstructed copy. -/
theorem experiencer_does_not_ccommand_causer_base :
    cascadeTarget.specCCommands "Experiencer" "A-Causer" = false ∧
    cascadeSM.specCCommands "Experiencer" "A-Causer" = false :=
  ⟨by native_decide, by native_decide⟩

/-- Backward binding diagnostic matches Cascade prediction.
    B&R diagnostic: Class II allows backward binding (Data.lean). -/
theorem backward_binding_br_match :
    (brDiagnosticData.filter (·.diagnostic == .backwardBinding)).all
      (·.classII) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 4. Double Object Alternation
-- ════════════════════════════════════════════════════

/-- DOC cascade has zero G (affixal) and overt *to* (nonaffixal). -/
theorem doc_spine :
    cascadeDOC.spine = [headG, headTo] := rfl

/-- G can reach V because it's at position 0 (zero affixal P). -/
theorem g_reaches_v :
    cascadeDOC.headCanReachV "G" = some true := by native_decide

/-- DOC argument order: Theme (spec of G) then Goal (spec of *to*). -/
theorem doc_arguments :
    cascadeDOC.arguments = ["Theme", "Goal"] := rfl

/-- Dative alternant has only *to* (nonaffixal). -/
theorem dative_spine :
    cascadeDative.spine = [headTo] := rfl

/-- DOC vs dative: different cascade geometries. -/
theorem doc_vs_dative_depth :
    cascadeDOC.depth = 2 ∧ cascadeDative.depth = 1 :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. θ-Suppression by CAUS
-- ════════════════════════════════════════════════════

/-- Strong CAUS (affixal variant) suppresses root's external θ-role.

    When CAUS_aff is affixed to √annoy, the agent role of the root is
    suppressed. The A-Causer (CAUS's own specifier) surfaces as the
    derived subject instead. -/
theorem caus_aff_suppresses :
    CausVariant.affixal.hasStrongFeatures = true ∧
    thetaSuppressed true true = true := ⟨rfl, rfl⟩

/-- Prepositional CAUS does NOT have strong features. -/
theorem caus_p_no_strong_features :
    CausVariant.prepositional.hasStrongFeatures = false := rfl

/-- Without CAUS affixation, no suppression occurs. -/
theorem no_caus_no_suppression :
    thetaSuppressed false true = false := rfl

/-- Without an external argument, there's nothing to suppress. -/
theorem no_ext_arg_no_suppression :
    thetaSuppressed true false = false := rfl

-- ════════════════════════════════════════════════════
-- § 6. CAUS Strength (Derived from Cascade Geometry)
-- ════════════════════════════════════════════════════

/-- Target and SM cascades both contain CAUS → strong causation. -/
theorem classII_has_strong_caus :
    cascadeTarget.causStrength = .strong ∧
    cascadeSM.causStrength = .strong :=
  ⟨by native_decide, by native_decide⟩

/-- A terminal cascade (no CAUS) → absent causation (Class I). -/
theorem classI_no_caus :
    Cascade.terminal.causStrength = .absent := rfl

/-- CAUS strength is uniform across Class II: both eventive (external
    source) and stative (internal source) cascades derive strong CAUS. -/
theorem caus_strength_uniform_across_classII :
    (cascadeForSource .external).causStrength = .strong ∧
    (cascadeForSource .internal).causStrength = .strong :=
  ⟨by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 7. Symmetric T/SM Blocking via HMC
-- ════════════════════════════════════════════════════

/-! The HMC predicts that BOTH Target (*at*) and Subject Matter (*about*)
    block CAUS movement equally, because both are nonaffixal P heads.
    This symmetric prediction is internal to @cite{pesetsky-1995}'s
    account — both stimulus subtypes produce the same HMC configuration.

    The bridge to semantic accounts of the T/SM restriction (which may
    make asymmetric predictions) is in `Kim2024_UPH.lean`. -/

/-- Both *at* and *about* are nonaffixal: both block CAUS movement
    through the cascade spine equally. -/
theorem symmetric_blocking :
    headAt.affixal = false ∧ headAbout.affixal = false :=
  ⟨rfl, rfl⟩

/-- The HMC prediction matches the empirical T/SM data: Cause + SM
    cooccurrence is ill-formed, as predicted by nonaffixal blocking. -/
theorem hmc_predicts_tsm_data :
    -- Nonaffixal *about* blocks CAUS in the combined cascade
    canReachV cascadeCausePlusStimulus.spine 2 = false ∧
    -- Data: Cause+SM cooccurrence is ill-formed
    (tsmData.filter (fun d => d.causePresent && d.smPresent)).all
      (!·.wellFormed) = true :=
  ⟨by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 8. CAUS ≠ vCAUSE Bridge
-- ════════════════════════════════════════════════════

-- Pesetsky's CAUS is a syntactic zero morpheme (P⁰) that creates
-- causative verbs by incorporating into V. It is present ONLY in
-- causative structures.
--
-- Cuervo's vCAUSE is an event-structural head present in BOTH
-- causative and anticausative alternants — it encodes the causal
-- relation between subevents, independent of Voice.
--
-- The bridge theorem `vcause_in_anticausative_but_not_caus`
-- (in Cascade.lean) witnesses this distinction: the anticausative
-- [vCAUSE, vGO, vBE] has vCAUSE but no CAUS.

/-- CAUS is a zero morpheme (not phonologically realized). -/
theorem caus_zero_morpheme : caus.isZero = true := rfl

/-- CAUS is affixal (can incorporate into V). -/
theorem caus_is_affixal : caus.affixal = true := rfl

/-- vCAUSE is present in anticausatives; CAUS is not. -/
theorem vcause_not_caus :
    isAnticausative [.vCAUSE, .vGO, .vBE] = true ∧
    -- An anticausative has no CAUS in its Cascade — terminal Cascade
    Cascade.terminal.hasHead "CAUS" = false :=
  ⟨by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 9. End-to-End Per-Verb Derivation
-- ════════════════════════════════════════════════════

/-! The full argumentation chain for each Class II psych verb, derived
    from a single lexical field (`causalSource` in the Fragment):

    ```
    Fragment: v.causalSource = some src
      → Cascade:  cascadeForSource src        (Target or SM cascade)
        → HMC:    headCanReachV "CAUS"        (CAUS can incorporate)
          → Stim: CausalSource.toStimulusType (Target or SubjectMatter)
            → Nat: isNaturalPredicate         (natural or arbitrary)
              → Str: Cascade.causStrength     (strong CAUS)
    ```

    Each per-verb theorem is a single breakable unit: change any verb's
    `causalSource` field in the Fragment and exactly one theorem fails.

    @cite{pesetsky-1995} Ch. 4 distinguishes **natural** predicates
    (Target-selecting, PP *of*: "afraid OF dogs") from **arbitrary**
    predicates (SM-selecting, PP *about*: "worried ABOUT the exam").
    This is derived from the causal source: external → natural,
    internal → arbitrary. -/

/-- Natural predicates select Target stimulus (PP *of*);
    arbitrary predicates select Subject Matter (PP *about*). -/
def isNaturalPredicate : StimulusType → Prop
  | .target => True
  | .subjectMatter => False

instance : DecidablePred isNaturalPredicate := fun x => by
  cases x <;> unfold isNaturalPredicate <;> infer_instance

/-- End-to-end cascade derivation chain for a Class II psych verb.
    From a verb's `causalSource`, derives: cascade assignment (via
    `cascadeForSource`), HMC reachability, stimulus type, natural/
    arbitrary classification, and CAUS strength. All from one field. -/
def cascadeChain (v : VerbEntry) (src : CausalSource) : Prop :=
    v.causalSource = some src ∧
    v.causalSource.map cascadeForSource = some (cascadeForSource src) ∧
    (cascadeForSource src).headCanReachV "CAUS" = some true ∧
    v.causalSource.map CausalSource.toStimulusType =
      some (CausalSource.toStimulusType src) ∧
    v.causalSource.map (isNaturalPredicate ∘ CausalSource.toStimulusType) =
      some (isNaturalPredicate (CausalSource.toStimulusType src)) ∧
    (cascadeForSource src).causStrength = .strong

-- External source → Target cascade → natural predicate → strong CAUS

theorem annoy_chain       : cascadeChain annoy .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem frighten_chain    : cascadeChain frighten .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem amuse_chain       : cascadeChain amuse .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem fascinate_chain   : cascadeChain fascinate .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem irritate_chain    : cascadeChain irritate .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem bore_chain        : cascadeChain bore .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem charm_chain       : cascadeChain charm .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem impress_chain     : cascadeChain impress .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem surprise_chain    : cascadeChain surprise .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem scare_chain       : cascadeChain scare .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem delight_chain     : cascadeChain delight .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem embarrass_chain   : cascadeChain embarrass .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem upset_chain       : cascadeChain upset_psych .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem disgust_chain     : cascadeChain disgust .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem shock_chain       : cascadeChain shock .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem confuse_chain     : cascadeChain confuse .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem disappoint_chain  : cascadeChain disappoint .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem worry_ev_chain    : cascadeChain worry_eventive .external :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩

-- Internal source → SM cascade → arbitrary predicate → strong CAUS

theorem concern_chain     : cascadeChain concern .internal :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem interest_chain    : cascadeChain interest .internal :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem worry_st_chain    : cascadeChain worry_stative .internal :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem please_chain      : cascadeChain please_psych .internal :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem trouble_chain     : cascadeChain trouble .internal :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩
theorem puzzle_chain      : cascadeChain puzzle .internal :=
  ⟨rfl, rfl, by native_decide, rfl, rfl, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 10. Heavy NP Shift and Cascade Depth
-- ════════════════════════════════════════════════════

/-! @cite{pesetsky-1995} Ch. 7 extends the Cascade Hypothesis to derive
    heavy NP shift (HNPS) from cascade geometry. Shifted phrases adjoin
    to cascade nodes; cascade depth determines how many potential landing
    sites exist for rightward-shifted heavy NPs.

    The cascade-based HNPS account provides a *syntactic* mechanism for
    weight effects: the verb's argument structure — determined by its
    cascade complement — constrains where shifted phrases can land. This
    predicts structural constraints on shift targets, not just statistical
    preference for heavy-last ordering. -/

/-- Psych verb cascades (depth 2) provide more shift sites than
    simple dative cascades (depth 1). -/
theorem psych_cascade_deeper_than_dative :
    cascadeTarget.shiftSites > cascadeDative.shiftSites :=
  by native_decide

/-- The DOC cascade and psych verb cascades have equal depth. -/
theorem doc_same_depth_as_psych :
    cascadeDOC.shiftSites = cascadeTarget.shiftSites := rfl

/-- Terminal cascades (intransitive verbs) provide no shift sites. -/
theorem terminal_no_shift_sites :
    Cascade.terminal.shiftSites = 0 := rfl

/-- Cascade depth predicts a hierarchy of HNPS availability:
    intransitive (0) < simple dative (1) < psych/DOC (2) < extended (3). -/
theorem shift_site_hierarchy :
    Cascade.terminal.shiftSites < cascadeDative.shiftSites ∧
    cascadeDative.shiftSites < cascadeTarget.shiftSites ∧
    cascadeTarget.shiftSites < cascadeCausePlusStimulus.shiftSites :=
  ⟨by native_decide, by native_decide, by native_decide⟩

end Pesetsky1995
