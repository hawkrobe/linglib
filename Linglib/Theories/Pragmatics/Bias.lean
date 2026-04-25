import Linglib.Phenomena.Negation.ExpletiveNegation
import Linglib.Core.Mood.IllocutionaryMood

/-!
# Bias-Conditioned Negation: A Shared Licensing Predicate

@cite{napoli-nespor-1976} @cite{romero-han-2004} @cite{repp-2013}
@cite{farkas-bruce-2010} @cite{hohle-1992}
@cite{romero-2024}

Bias-conditioned negation is the cluster of phenomena where a negation
marker appears not to negate truth-conditionally but to mark the speaker's
presupposition that their assertion contradicts a prior belief — their own
or one attributed to the addressee.

@cite{napoli-nespor-1976} first identified the cluster for Italian *non₂*
in comparative clauses and indirect questions. The same licensing
predicate has been independently rediscovered for biased English polar
questions (@cite{romero-han-2004}, @cite{romero-2024}), VERUM focus
(@cite{hohle-1992}, @cite{repp-2013}), and discourse rejection moves
(@cite{farkas-bruce-2010}). This module provides the framework-neutral
licensing predicate; specific historical and modern implementations
consume it.

## The Four Conditions

@cite{napoli-nespor-1976} §2 establish that bias-conditioned negation is
licensed exactly when ALL of the following hold:

1. **Contradicts prior belief** — the speaker presupposes the assertion
   contradicts a belief held prior to the discourse turn.
2. **Assertive force** — the move is an assertion. Encoded as
   `illocutionaryMood = .declarative` (derived through `isAssertive`).
3. **Matrix unnegated** — the matrix predicate is not negated.
4. **Imprecise / inferred** — the speaker's evidence is inferred, not
   explicit.

The four conditions are logically independent (one-axis blocking witnessed
below) and jointly necessary and sufficient for the Italian *non₂*
paradigm.

## Prop, not Bool

`licenses` is a `Prop` (not a `Bool`). The four atomic axes remain `Bool`
fields — they are user-supplied empirical data — but the conjunctive
licensing predicate exposes its logical structure (`∧` rather than `&&`)
so consumers can use `obtain`/`rintro` directly. Decidability is provided.

## Cross-construction connections

§6 connects the predicate to @cite{greco-2020}'s weak-EN polarity profile
in `Phenomena.Negation.ExpletiveNegation.PolarityLicensing`. The Romero-2024 HiNQ bridge — a
predicate-level correspondence between this licensing condition and
Romero's bias requirement — lives in
`Phenomena/Questions/Studies/Romero2024.lean`, so that this file does
not have to import the BiasedPQ stack.

These are **predicate-level correspondences**, not stipulated maps. An
earlier draft had `toRomeroForm := if licenses then HiNQ else none` (a
two-cell table dressed as a function); the relocated bridge instead
proves the relationship between the licensing condition and Romero's
bias requirement directly.

## Historical Note

@cite{napoli-nespor-1976}'s original implementation routed the licensing
condition through an abstract higher S in deep structure with *non₂*
base-generated in S₃ and optionally deleted by transformation. The
deep-structure-with-deletion-rule machinery is a Generative Semantics
artifact (1968–1976); the licensing predicate itself is foundational and
is the unit shared with covert-VERUM (@cite{romero-han-2004}) and
commitment-update (@cite{farkas-bruce-2010}) reanalyses.
-/

namespace Pragmatics.Bias

open Phenomena.Negation.ExpletiveNegation (PolarityLicensing weakENProfile)
open Core.Mood (IllocutionaryMood)

-- ════════════════════════════════════════════════════
-- § 1. The four licensing conditions
-- ════════════════════════════════════════════════════

/-- Bias-licensing profile: one bit per @cite{napoli-nespor-1976} §2
    condition (with the assertive-force axis recorded as a full
    `IllocutionaryMood`). The licensing predicate `licenses` is the
    conjunction of the four axes; see §2. -/
structure BiasLicensingProfile where
  /-- Speaker presupposes the assertion contradicts a prior belief.
      @cite{napoli-nespor-1976} §2 ex. 6–9. -/
  contradictsPriorBelief : Bool
  /-- Illocutionary force of the move. The licensing predicate fires
      only on `.declarative`; `isAssertive` is the projection.
      @cite{napoli-nespor-1976} §2.1 ex. 10b, 12b. -/
  illocutionaryMood : IllocutionaryMood
  /-- The matrix predicate is not negated.
      @cite{napoli-nespor-1976} §2.2 ex. 18. -/
  matrixUnnegated : Bool
  /-- Speaker's evidence is inferred and the construction does not
      require precise knowledge.
      @cite{napoli-nespor-1976} §2.3 ex. 22, §3.22 ex. 32–34. -/
  imprecise : Bool
  deriving DecidableEq, Repr

/-- Assertive force: declarative illocutionary mood. -/
def BiasLicensingProfile.isAssertive (p : BiasLicensingProfile) : Prop :=
  p.illocutionaryMood = .declarative

instance (p : BiasLicensingProfile) : Decidable p.isAssertive :=
  inferInstanceAs (Decidable (p.illocutionaryMood = .declarative))

-- ════════════════════════════════════════════════════
-- § 2. The licensing predicate
-- ════════════════════════════════════════════════════

/-- Bias-conditioned negation is licensed iff all four conditions hold.
    @cite{napoli-nespor-1976} §2: the central licensing claim, formalized
    as a `Prop`-valued conjunction so consumers can destructure it with
    `obtain ⟨h1, h2, h3, h4⟩`. -/
def BiasLicensingProfile.licenses (p : BiasLicensingProfile) : Prop :=
  p.contradictsPriorBelief = true ∧
  p.isAssertive ∧
  p.matrixUnnegated = true ∧
  p.imprecise = true

instance (p : BiasLicensingProfile) : Decidable p.licenses := by
  unfold BiasLicensingProfile.licenses
  infer_instance

-- ════════════════════════════════════════════════════
-- § 3. Canonical profiles (one per blocking axis)
-- ════════════════════════════════════════════════════

/-- All four conditions met: the licensed profile. -/
def licensedProfile : BiasLicensingProfile :=
  { contradictsPriorBelief := true, illocutionaryMood := .declarative,
    matrixUnnegated := true, imprecise := true }

/-- No condition met: fully blocked. The blocking illocutionary mood is
    `.interrogative` (the most common blocker in N&N §2.1). -/
def blockedProfile : BiasLicensingProfile :=
  { contradictsPriorBelief := false, illocutionaryMood := .interrogative,
    matrixUnnegated := false, imprecise := false }

/-- Questioned comparative: contradicts prior belief but not assertive.
    @cite{napoli-nespor-1976} §2.1 ex. 10b. -/
def questionedProfile : BiasLicensingProfile :=
  { licensedProfile with illocutionaryMood := .interrogative }

/-- Imperative bias context — also blocked because non-assertive.
    @cite{napoli-nespor-1976} §2.1: the assertive condition rules out
    *all* non-declarative force. -/
def imperativeProfile : BiasLicensingProfile :=
  { licensedProfile with illocutionaryMood := .imperative }

/-- Matrix-negated comparative: assertive but matrix is negated.
    @cite{napoli-nespor-1976} §2.2 ex. 18a. -/
def matrixNegatedProfile : BiasLicensingProfile :=
  { licensedProfile with matrixUnnegated := false }

/-- Precise / equality comparative: precision required incompatible with
    inferred-belief presupposition.
    @cite{napoli-nespor-1976} §2.3 ex. 22, §3.22 ex. 32–34. -/
def preciseProfile : BiasLicensingProfile :=
  { licensedProfile with imprecise := false }

/-- No prior belief to contradict (e.g., addressee gave no opinion).
    @cite{napoli-nespor-1976} §2 ex. 6. -/
def noContradictionProfile : BiasLicensingProfile :=
  { licensedProfile with contradictsPriorBelief := false }

-- ════════════════════════════════════════════════════
-- § 4. Distributional theorems
-- ════════════════════════════════════════════════════

/-- The licensed profile licenses bias-marked negation. -/
theorem licensed_licenses : licensedProfile.licenses := by decide

/-- Each blocking profile blocks bias-marked negation; the four
    distributional facts of @cite{napoli-nespor-1976} §2.1–§2.3
    fall out structurally from the licensing predicate. -/
theorem blocked_blocks : ¬ blockedProfile.licenses := by decide
theorem questioned_blocks : ¬ questionedProfile.licenses := by decide
theorem imperative_blocks : ¬ imperativeProfile.licenses := by decide
theorem matrix_negated_blocks : ¬ matrixNegatedProfile.licenses := by decide
theorem precise_blocks : ¬ preciseProfile.licenses := by decide
theorem no_contradiction_blocks : ¬ noContradictionProfile.licenses := by decide

/-- The licensed profile is **the** profile that licenses bias-marked
    negation: any licensing profile is structurally equal to
    `licensedProfile`. The proof is structural (no Fintype enumeration);
    each conjunct of `licenses` pins down one field. -/
theorem licenses_iff_eq_licensedProfile (p : BiasLicensingProfile) :
    p.licenses ↔ p = licensedProfile := by
  unfold BiasLicensingProfile.licenses BiasLicensingProfile.isAssertive
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨c, m, u, i⟩ := p
    simp_all
    rfl
  · rintro rfl
    refine ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Logical independence of the four conditions
-- ════════════════════════════════════════════════════

/-- Each blocking profile differs from the licensed profile in exactly
    one axis. Together these witness that the four conditions are
    logically independent: no axis is implied by the others. -/
theorem blocking_axes_independent :
    questionedProfile.contradictsPriorBelief = true ∧
    matrixNegatedProfile.isAssertive ∧
    preciseProfile.matrixUnnegated = true ∧
    noContradictionProfile.imprecise = true := by
  refine ⟨rfl, ?_, rfl, rfl⟩; rfl

-- ════════════════════════════════════════════════════
-- § 6. Bridge to Greco's PolarityLicensing
-- ════════════════════════════════════════════════════

/-- @cite{greco-2020}'s weak-EN profile is the polarity-licensing
    profile that bias-conditioned negation realizes: it licenses weak NPIs
    (Italian *pur* in @cite{napoli-nespor-1976} §3.11 ex. 46–48) and
    N-words, but rejects strong NPIs and not-also conjunctions. The
    correspondence is at the *predicate* level: a licensed bias profile
    is precisely the one that activates the weak-EN polarity profile. -/
theorem licensed_activates_weakEN :
    licensedProfile.licenses → weakENProfile.weakNPIs = true ∧
                               weakENProfile.nWords = true ∧
                               weakENProfile.strongNPIs = false ∧
                               weakENProfile.notAlsoConj = false := by
  intro _; refine ⟨rfl, rfl, rfl, rfl⟩

-- The Romero (2024) HiNQ bridge formerly lived here as §7 but was relocated
-- to `Phenomena/Questions/Studies/Romero2024.lean` so that this file does not
-- have to import the BiasedPQ stack (CommonGround / InformationStructure /
-- Discourse.{IllocutionaryForce,Intentionality,Commitment} / Kratzer.Flavor /
-- Core.IntensionalLogic.Examples). The bridge is predicate-level — sharing only the
-- licensing predicate, not the form-level structure — and lives naturally in
-- the polar-question phenomenon directory.

end Pragmatics.Bias