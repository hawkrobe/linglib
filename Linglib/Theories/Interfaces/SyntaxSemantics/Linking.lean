import Linglib.Theories.Semantics.Verb.EntailmentProfile

/-!
# Linking Theory Interface

@cite{beavers-koontz-garboden-2020} @cite{dowty-1991} @cite{goldberg-1995} @cite{kratzer-1996} @cite{levin-2004} @cite{levin-hovav-1995} @cite{pesetsky-1995} @cite{pylkknen-2008} @cite{rappaport-hovav-levin-1998}

General interface for theories of argument realization — how verbs'
arguments get their thematic roles.

## Theta Roles

Theta roles are **derived convenience labels** that name clusters in
entailment-profile space (`EntailmentProfile.lean`). They are NOT
primitives: the authoritative representation of argument semantics is
the entailment profile, and role labels are computed from it via
`EntailmentProfile.toRole`.

The field consensus (@cite{levin-2019}) is that discrete thematic roles
have been superseded by entailment-based representations. Role labels
remain useful as a **shared interface vocabulary** for linking theories,
neo-Davidsonian logical forms, and cross-framework comparison.

## Linking Theories

Theories in the literature differ along three dimensions:

1. **What the verb contributes** (lexical semantics, meaning components,
   event structure templates, root meaning, entailment profiles)
2. **What the structure contributes** (Voice flavor, applicative type,
   sub-event decomposition, construction type, causal chain position)
3. **Which direction the mapping goes** (verb → role, structure → role,
   or both jointly)

The `LinkingTheory` structure captures this variation by parameterizing
over BOTH the verb representation type (`Verb`) and the structural
context type (`Ctx`). Theories that ignore structure use `Unit` for
`Ctx`; theories that care about Voice use `VoiceFlavor`; theories
with richer decompositions bring their own types.

The role output is always `ThetaRole` — the shared vocabulary that
makes theories comparable against fragment data.

The `compatible` field captures gradient verb–construction pairing: a verb may be compatible with multiple structural
contexts (causative alternation verbs appear with both agentive and
non-thematic Voice). Singleton lists express categorical predictions;
multi-element lists express gradient compatibility.

## Coverage

Accounts expressible via this interface (non-exhaustive):

| Account | Ctx | compatible | predict uses verb? |
|---------|-----|------------|-------------------|
| Severing | VoiceFlavor | verb-constrained | no |
| Lexicalist | Unit | always [] | yes |
| Zero morphology | (custom) | verb-constrained | yes |
| First Phase Syntax | (custom) | verb-constrained | yes |
| CxG | (custom) | broad | no |
| Proto-roles | Unit | always [] | yes (via ASP) |
| Applicatives | (custom) | verb-constrained | no |

-/

open Semantics.Verb.EntailmentProfile

-- ════════════════════════════════════════════════════════════════════════
-- § 1. Theta Role Labels (derived convenience names)
-- ════════════════════════════════════════════════════════════════════════

/-- Theta roles — derived convenience labels that name clusters in
    entailment-profile space. These are NOT primitives: the authoritative
    representation is the `EntailmentProfile`, and role labels are computed
    from it via `EntailmentProfile.toRole`.

    The field consensus (@cite{levin-2019}) is that discrete thematic roles
    have been superseded by entailment-based representations. Role labels
    remain useful as shared interface vocabulary for linking theories,
    neo-Davidsonian logical forms, and cross-framework comparison. -/
inductive ThetaRole where
  | agent       -- Volitional causer (John kicked the ball)
  | patient     -- Affected entity (John kicked the ball)
  | theme       -- Entity in a state/location (The book is on the table)
  | experiencer -- Perceiver/cognizer (John knows that p)
  | goal        -- Recipient/target (John gave Mary a book)
  | source      -- Origin (John came from Paris)
  | instrument  -- Means (John opened the door with a key)
  | stimulus    -- Cause of experience (The noise frightened John)
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════════════
-- § 2. EntailmentProfile → ThetaRole (canonical direction)
-- ════════════════════════════════════════════════════════════════════════

namespace Semantics.Verb.EntailmentProfile

/-- Derive a convenience theta-role label from an entailment profile.

    This is the **canonical direction**: profiles are authoritative,
    labels are derived. The function uses feature-based heuristics
    to assign the most natural label:

    - Volition → agent
    - Sentience without causation → experiencer
    - Causation without sentience → stimulus
    - P-Patient features without P-Agent → patient (if CoS) or theme
    - IE only → goal (ambiguous with source)
    - No distinguishing features → none

    Note: instrument and stimulus have identical canonical profiles
    ({causation, IE}), as do goal and source ({IE}). The function
    defaults to stimulus and goal respectively. Disambiguation requires
    external context (e.g., `VerbCore.causalSource`). -/
def EntailmentProfile.toRole (p : EntailmentProfile) : Option ThetaRole :=
  if p.volition then some .agent
  else if p.sentience && !p.causation then some .experiencer
  else if p.causation && !p.sentience then some .stimulus
  else if !p.volition && !p.sentience && !p.causation && !p.movement then
    -- No core P-Agent features (at most IE). Disambiguate by P-Patient.
    if p.pPatientScore > 0 then
      if p.changeOfState || p.causallyAffected then some .patient
      else some .theme
    else if p.independentExistence then some .goal
    else none
  else none

end Semantics.Verb.EntailmentProfile

-- ════════════════════════════════════════════════════════════════════════
-- § 3. ThetaRole → Canonical Profile (inverse direction)
-- ════════════════════════════════════════════════════════════════════════

/-- Map each ThetaRole label back to its canonical entailment profile.

    This is the **inverse direction** — from convenience labels to the
    underlying entailment structure. Each label names a prototypical
    combination of entailments.

    Round-trip: `toRole (canonicalProfile θ) = some θ'` where `θ'` is
    the canonical representative. Note that instrument→stimulus and
    source→goal collapse because their canonical profiles are identical. -/
def ThetaRole.canonicalProfile : ThetaRole → EntailmentProfile
  | .agent       => ⟨true, true, true, true, true,     false, false, false, false, false⟩
  | .patient     => ⟨false, false, false, false, false, true, false, true, true, false⟩
  | .theme       => ⟨false, false, false, false, true,  false, false, false, true, false⟩
  | .experiencer => ⟨false, true, false, false, true,   false, false, false, false, false⟩
  | .instrument  => ⟨false, false, true, false, true,   false, false, false, false, false⟩
  | .stimulus    => ⟨false, false, true, false, true,   false, false, false, false, false⟩
  | .goal        => ⟨false, false, false, false, true,  false, false, false, false, false⟩
  | .source      => ⟨false, false, false, false, true,  false, false, false, false, false⟩

-- Round-trip: toRole ∘ canonicalProfile

/-- Instrument and stimulus have identical canonical profiles — both are
    {causation, independentExistence}. `toRole` cannot distinguish them. -/
theorem instrument_stimulus_same_profile :
    ThetaRole.canonicalProfile .instrument = ThetaRole.canonicalProfile .stimulus := rfl

/-- Goal and source have identical canonical profiles — both are
    {independentExistence} only. `toRole` cannot distinguish them. -/
theorem goal_source_same_profile :
    ThetaRole.canonicalProfile .goal = ThetaRole.canonicalProfile .source := rfl

/-- `toRole ∘ canonicalProfile` is a retraction: it recovers a role whose
    canonical profile matches the input's. This partitions ThetaRole into
    equivalence classes under profile identity:

    - Singletons: agent, patient, theme, experiencer (recoverable)
    - {instrument, stimulus} — both map to stimulus
    - {goal, source} — both map to goal

    The proof is uniform: `cases r` splits into 8 constructors, and for each,
    both `toRole` and profile equality reduce by `rfl`. -/
theorem toRole_canonicalProfile_roundtrip (r : ThetaRole) :
    ∃ r', (r.canonicalProfile).toRole = some r' ∧
          r'.canonicalProfile = r.canonicalProfile := by
  cases r <;> exact ⟨_, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════════
-- § 4. toRole on Canonical Verb Profiles
-- ════════════════════════════════════════════════════════════════════════

/-- "kick" subject profile → agent. -/
theorem kick_subject_toRole : kickSubjectProfile.toRole = some .agent := by rfl

/-- "kick" object profile → patient. -/
theorem kick_object_toRole : kickObjectProfile.toRole = some .patient := by rfl

/-- "see" subject profile → experiencer. -/
theorem see_subject_toRole : seeSubjectProfile.toRole = some .experiencer := by rfl

/-- "arrive" subject profile → none (mixed P-Agent + P-Patient: movement disqualifies). -/
theorem arrive_subject_toRole : arriveSubjectProfile.toRole = none := by rfl

/-- "die" subject profile → patient (pure P-Patient). -/
theorem die_subject_toRole : dieSubjectProfile.toRole = some .patient := by rfl

-- ════════════════════════════════════════════════════════════════════════
-- § 5. ASP Verification with Canonical Profiles
-- ════════════════════════════════════════════════════════════════════════

-- Between-argument ASP

/-- Agent outranks patient for subjecthood (lattice: {V,S,C,M,IE} ⊃ {}). -/
theorem agent_outranks_patient :
    OutranksForSubject
      (ThetaRole.canonicalProfile .agent)
      (ThetaRole.canonicalProfile .patient) := by decide

/-- Agent outranks instrument (lattice: {V,S,C,M,IE} ⊃ {C,IE}). -/
theorem agent_outranks_instrument :
    OutranksForSubject
      (ThetaRole.canonicalProfile .agent)
      (ThetaRole.canonicalProfile .instrument) := by decide

/-- Agent outranks experiencer (lattice: {V,S,C,M,IE} ⊃ {S,IE}). -/
theorem agent_outranks_experiencer :
    OutranksForSubject
      (ThetaRole.canonicalProfile .agent)
      (ThetaRole.canonicalProfile .experiencer) := by decide

/-- Experiencer and instrument have incomparable P-Agent sets ({S,IE} ⊥ {C,IE}),
    but also equal P-Patient (both 0) → alternation predicted. -/
theorem experiencer_instrument_alternation :
    AllowsAlternation
      (ThetaRole.canonicalProfile .experiencer)
      (ThetaRole.canonicalProfile .instrument) := by decide

/-- Experiencer and stimulus have equal profiles → alternation (like/please). -/
theorem experiencer_stimulus_alternation :
    AllowsAlternation
      (ThetaRole.canonicalProfile .experiencer)
      (ThetaRole.canonicalProfile .stimulus) := by decide

/-- Agent is maximally proto-agentive and minimally proto-patientive —
    the archetype at one end of Dowty's continuum. -/
theorem agent_maximal_pAgent :
    (ThetaRole.canonicalProfile .agent).pAgentScore = 5 ∧
    (ThetaRole.canonicalProfile .agent).pPatientScore = 0 := ⟨rfl, rfl⟩

/-- Patient is maximally proto-patientive and minimally proto-agentive —
    the archetype at the opposite end. -/
theorem patient_maximal_pPatient :
    (ThetaRole.canonicalProfile .patient).pAgentScore = 0 ∧
    (ThetaRole.canonicalProfile .patient).pPatientScore = 3 := ⟨rfl, rfl⟩

/-- All canonical profiles satisfy the well-formedness constraint:
    volition entails sentience. -/
theorem canonical_profiles_wellformed (r : ThetaRole) :
    (r.canonicalProfile).WellFormedInternal := by
  cases r <;> decide

-- ════════════════════════════════════════════════════════════════════════
-- § 6. Argument position
-- ════════════════════════════════════════════════════════════════════════

namespace Interfaces.SyntaxSemantics

/-- Which argument position in the clause we're asking about.
    Theory-neutral: expressed as grammatical functions, not structural
    positions (Spec-vP, Comp-VP, etc.), so that theories with different
    structural vocabularies can all target the same output. -/
inductive ArgPosition where
  | subject         -- Grammatical subject (external or raised)
  | directObject    -- Direct object
  | indirectObject  -- Indirect object / dative
  | oblique         -- Oblique / PP complement
  | applied         -- Applied argument (@cite{pylkknen-2008})
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════════════
-- § 7. LinkingTheory
-- ════════════════════════════════════════════════════════════════════════

/-- A linking theory, parameterized by verb representation and structural
    context type.

    - `Verb`: what the theory needs to know about the verb. Typically
      `VerbCore`, but could be `EntailmentProfile` (Dowty) or
      `EventTemplate` (Rappaport Hovav & Levin).
    - `Ctx`: what the theory considers relevant about the syntactic
      structure beyond the verb itself:
      - `Unit` for theories that derive everything from the verb
      - `VoiceFlavor` for the severing account
      - A richer type for Ramchand, Goldberg, Pylkkänen, etc.

    The theory provides two functions:
    - `compatible`: which structural contexts can this verb appear in?
    - `predict`: in a given context, what theta role does each position get?

    This separation captures the key theoretical distinction:
    - **Pure constructional** (Borer, strong Goldberg): `compatible` is
      broad — the verb is promiscuous; structure determines roles
    - **Pure lexicalist** (Levin): `compatible` always returns `[]` —
      there is nothing structural to vary
    - **Hybrid**: `compatible` returns a
      verb-constrained subset — gradient compatibility -/
structure LinkingTheory (Verb Ctx : Type) where
  /-- Which structural contexts this verb is compatible with.
      Singleton = categorical. Multiple = gradient (alternation). -/
  compatible : Verb → List Ctx
  /-- Predict each argument's theta role in a given context.
      Returns `none` for positions the theory is silent about. -/
  predict : Verb → Ctx → ArgPosition → Option ThetaRole

-- ════════════════════════════════════════════════════════════════════════
-- § 8. Testing predictions against fragment data
-- ════════════════════════════════════════════════════════════════════════

/-- Does the theory's prediction match the observed role at a given
    position, for at least one compatible structural context?

    For alternation verbs (multiple compatible contexts), the test passes
    if ANY context produces the correct prediction — the fragment entry
    records one use of the verb, not all possible uses. -/
def LinkingTheory.matchesAt {Verb Ctx : Type} [BEq Ctx]
    (th : LinkingTheory Verb Ctx) (v : Verb) (pos : ArgPosition)
    (actual : Option ThetaRole) : Bool :=
  (th.compatible v).any fun ctx => th.predict v ctx pos == actual

end Interfaces.SyntaxSemantics
