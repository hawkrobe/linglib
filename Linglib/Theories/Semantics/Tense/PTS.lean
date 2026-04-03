import Linglib.Theories.Semantics.Tense.TemporalAdverbials
import Linglib.Theories.Semantics.Tense.PerfectPolysemy
import Linglib.Theories.Semantics.Tense.Aspect.SubintervalProperty

/-!
# Perfect Time Span / Until Time Span — Unified Framework
@cite{iatridou-anagnostopoulou-izvorski-2001} @cite{iatridou-zeijlstra-2021}
@cite{von-fintel-iatridou-2019}

Boundary adverbials (*in years*, *since*, *until*, *in (the last) 5 years*)
set a boundary of a time span. @cite{iatridou-zeijlstra-2021} unify two
classes:

- **LB adverbials** (*in years*, *since*, *in (the last) 5 years*): set the
  **left boundary** of the **Perfect Time Span** (PTS). The RB is set by Tense.
- **RB adverbials** (*until*): set the **right boundary** of the **Until Time
  Span** (UTS). The LB is contextually set.

Both classes can be **boundary domain wideners** — they introduce subdomain
alternatives to their time span, triggering exhaustification. When they are,
they produce two noncancelable inferences:

1. **Actuality Inference** (AI): the relevant event took place
2. **Beyond Expectation Inference** (BEI): the time span is larger than expected

This module consolidates the PTS/UTS framework that was previously scattered
across `Aspect/Core.lean` (RB, LB, PERF), `TemporalAdverbials.lean`
(PTSConstraint), `PerfectPolysemy.lean` (PerfectReading), and
`MaximalInformativity.lean` (pts, MeasureFun). It re-exports the core
operators and adds the unified boundary-adverbial abstraction.

## Architecture

```
Aspect/Core.lean     RB, LB, PERF, PERF_XN, IMPF, PRFV
        ↑
TemporalAdverbials   PTSConstraint, AdverbialType, PERF_ADV
        ↑
PerfectPolysemy      PerfectReading, existential/universalReading
        ↑
   THIS FILE          BoundaryKind, TimeSpanKind, BoundaryAdverbial
                      SubdomainAlternatives, DomainWideningResult
```
-/

namespace Semantics.Tense.PTS

open Core.Time
open Semantics.Tense.Aspect.Core
open Semantics.Tense.Aspect.SubintervalProperty
open Semantics.Montague.Sentence.TemporalAdverbials (PTSConstraint AdverbialType)
open Semantics.Tense.PerfectPolysemy (PerfectReading)

variable {W Time : Type*} [LinearOrder Time]

-- ════════════════════════════════════════════════════
-- § 1. Boundary Classification
-- ════════════════════════════════════════════════════

/-- Which boundary of a time span an adverbial sets.
    - `left`: LB adverbials (*in years*, *since*, *in (the last) 5 years*)
    - `right`: RB adverbials (*until*) -/
inductive BoundaryKind where
  | left   -- sets the left boundary (e.g., *since Monday*, *in years*)
  | right  -- sets the right boundary (e.g., *until 5pm*)
  deriving DecidableEq, Repr

/-- Which time span the adverbial operates on.
    - `pts`: the Perfect Time Span (LB set by adverbial or context, RB by Tense)
    - `uts`: the Until Time Span (LB contextually set, RB by *until*'s argument) -/
inductive TimeSpanKind where
  | pts  -- Perfect Time Span
  | uts  -- Until Time Span
  deriving DecidableEq, Repr

/-- The boundary set by Tense (not by the adverbial).
    PTS: Tense sets the RB. UTS: context/Tense sets the LB.
    Mirror-image relationship (@cite{iatridou-zeijlstra-2021} §8). -/
def TimeSpanKind.tenseSetsBoundary : TimeSpanKind → BoundaryKind
  | .pts => .right
  | .uts => .left

/-- The boundary set by the adverbial itself.
    PTS adverbials set LB; UTS adverbials set RB. -/
def TimeSpanKind.adverbialSetsBoundary : TimeSpanKind → BoundaryKind
  | .pts => .left
  | .uts => .right

/-- PTS and UTS are mirror images: they set opposite boundaries. -/
theorem pts_uts_mirror :
    TimeSpanKind.adverbialSetsBoundary .pts ≠
    TimeSpanKind.adverbialSetsBoundary .uts := by decide

-- ════════════════════════════════════════════════════
-- § 2. Boundary Adverbial Structure
-- ════════════════════════════════════════════════════

/-- NPI strength classification. Strong NPIs require antiadditive
    environments; weak NPIs require only DE environments.
    @cite{zwarts-1998} @cite{gajewski-2011} -/
inductive NPIStrength where
  | strong  -- requires antiadditive (not, nobody, never)
  | weak    -- requires DE (few, at most, before)
  | none_   -- not an NPI
  deriving DecidableEq, Repr

/-- A boundary adverbial: a temporal expression that sets one boundary
    of a time span (PTS or UTS).

    @cite{iatridou-zeijlstra-2021} §3, §5: *in years* and *until* are
    both boundary adverbials that share the property of being domain
    wideners (introducing subdomain alternatives). -/
structure BoundaryAdverbial where
  /-- Surface form -/
  form : String
  /-- Which time span this adverbial operates on -/
  timeSpan : TimeSpanKind
  /-- Which boundary it sets -/
  boundary : BoundaryKind
  /-- Does this adverbial introduce subdomain alternatives? -/
  introducesDomainAlts : Bool
  /-- Is this adverbial a (strong) NPI? -/
  npiStrength : NPIStrength
  /-- Is the adverbial always contrastively focused?
      @cite{chierchia-2013}: domain widening requires contrastive focus
      under negation. *In years* is always contrastively focused;
      *until* is contrastively focused only when under negation. -/
  alwaysContrastive : Bool
  /-- Compatible perfect types (for PTS adverbials).
      *In years* is compatible only with E-perfect;
      *in (the last) 5 years* is compatible with both E-perfect and U-perfect. -/
  compatiblePerfect : List PerfectReading := [.existential, .universal]
  deriving Repr

-- ════════════════════════════════════════════════════
-- § 3. Concrete Boundary Adverbials
-- ════════════════════════════════════════════════════

/-- *In years* (*in days*, *in months*, etc.): strong NPI LB adverbial.
    Sets the LB of the PTS by stretching backward from the RB.
    Introduces subdomain alternatives. Always contrastively focused.
    Compatible only with E-perfect (not U-perfect).
    @cite{iatridou-zeijlstra-2021} §3–4 -/
def inYears : BoundaryAdverbial where
  form := "in years"
  timeSpan := .pts
  boundary := .left
  introducesDomainAlts := true
  npiStrength := .strong
  alwaysContrastive := true
  compatiblePerfect := [.existential]

/-- *In (the last) 5 years*: non-NPI LB adverbial.
    Sets the LB of the PTS by specifying a duration from the RB.
    Does NOT introduce domain alternatives (not a domain widener).
    Compatible with both E-perfect and U-perfect. -/
def inTheLast5Years : BoundaryAdverbial where
  form := "in (the last) 5 years"
  timeSpan := .pts
  boundary := .left
  introducesDomainAlts := false
  npiStrength := .none_
  alwaysContrastive := false
  compatiblePerfect := [.existential, .universal]

/-- *Since 2015*: non-NPI LB adverbial.
    Sets the LB of the PTS by naming it.
    Does NOT introduce domain alternatives. -/
def since2015 : BoundaryAdverbial where
  form := "since 2015"
  timeSpan := .pts
  boundary := .left
  introducesDomainAlts := false
  npiStrength := .none_
  alwaysContrastive := false

/-- *Until (5pm / I left)*: unified RB adverbial.
    Sets the RB of the UTS. Always introduces subdomain alternatives
    (the domain-widening effect surfaces only under contrastive focus).
    @cite{iatridou-zeijlstra-2021} §7: one *until*, not two. -/
def until_ : BoundaryAdverbial where
  form := "until"
  timeSpan := .uts
  boundary := .right
  introducesDomainAlts := true
  npiStrength := .strong
  alwaysContrastive := false  -- only contrastively focused under negation

-- ════════════════════════════════════════════════════
-- § 4. Structural Properties
-- ════════════════════════════════════════════════════

/-- *In years* sets the LB (matching PTS). -/
theorem inYears_sets_lb : inYears.boundary = TimeSpanKind.adverbialSetsBoundary .pts := rfl

/-- *Until* sets the RB (matching UTS). -/
theorem until_sets_rb : until_.boundary = TimeSpanKind.adverbialSetsBoundary .uts := rfl

/-- *In years* and *until* are both domain wideners. -/
theorem both_domain_wideners :
    inYears.introducesDomainAlts = true ∧ until_.introducesDomainAlts = true :=
  ⟨rfl, rfl⟩

/-- *In years* and *until* are both strong NPIs. -/
theorem both_strong_npis :
    inYears.npiStrength = .strong ∧ until_.npiStrength = .strong :=
  ⟨rfl, rfl⟩

/-- *In years* is always contrastive; *until* is not. -/
theorem contrastive_asymmetry :
    inYears.alwaysContrastive = true ∧ until_.alwaysContrastive = false :=
  ⟨rfl, rfl⟩

/-- *In years* is E-perfect only; *in (the last) 5 years* allows both. -/
theorem inYears_eperfect_only :
    PerfectReading.universal ∉ inYears.compatiblePerfect ∧
    PerfectReading.universal ∈ inTheLast5Years.compatiblePerfect := by
  exact ⟨
    fun h => by cases h; contradiction,
    List.Mem.tail _ (List.Mem.head _)⟩

/-- Non-NPI boundary adverbials do not introduce domain alternatives. -/
theorem nonNPI_no_domainAlts :
    since2015.introducesDomainAlts = false ∧
    inTheLast5Years.introducesDomainAlts = false :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Subdomain Alternatives for Time Spans
-- ════════════════════════════════════════════════════

/-- The subdomain alternatives of a time span τ are all subintervals of τ.
    @cite{chierchia-2013} Ch. 1; @cite{iatridou-zeijlstra-2021} §4:

    When *in years* is present, the assertion (49a) is:
      ∃e.[meet(e, Joe, Mary) ∧ Run(e) ⊆ τ]
    and its domain alternatives (49b) are:
      {∃e.[meet(e, Joe, Mary) ∧ Run(e) ⊆ τ'] | τ' ⊆ τ}

    These subdomain alternatives are logically stronger than the assertion
    (entailed by it), because if a culminated event took place in a
    subinterval of τ, it also took place in τ. -/
def SubdomainAlternatives (τ : Interval Time) : Set (Interval Time) :=
  { τ' | τ'.subinterval τ }

/-- Subdomain alternatives of τ include τ itself. -/
theorem self_in_subdomain (τ : Interval Time) :
    τ ∈ SubdomainAlternatives τ :=
  ⟨le_refl _, le_refl _⟩

/-- Subdomain alternatives of a subinterval are a subset of subdomain
    alternatives of the superinterval. -/
theorem subdomain_monotone (τ₁ τ₂ : Interval Time)
    (h : τ₁.subinterval τ₂) :
    SubdomainAlternatives τ₁ ⊆ SubdomainAlternatives τ₂ := by
  intro τ' ⟨hs, hf⟩
  exact ⟨le_trans h.1 hs, le_trans hf h.2⟩

-- ════════════════════════════════════════════════════
-- § 6. Event Predicate in Time Span
-- ════════════════════════════════════════════════════

/-- An event of type P has its runtime inside time span τ.
    This is the assertion form for both PTS and UTS:
    ∃e.[P(e) ∧ Run(e) ⊆ τ] -/
def eventInSpan (P : EventPred W Time) (w : W) (τ : Interval Time) : Prop :=
  ∃ e : Eventuality Time, e.τ.subinterval τ ∧ P w e

/-- Negated form: no P-event has runtime inside τ.
    ¬∃e.[P(e) ∧ Run(e) ⊆ τ] -/
def noEventInSpan (P : EventPred W Time) (w : W) (τ : Interval Time) : Prop :=
  ¬ eventInSpan P w τ

/-- If a culminated event occurs in a subinterval, it occurs in the
    superinterval. Entailment from subinterval to superinterval. -/
theorem eventInSpan_monotone (P : EventPred W Time) (w : W)
    (τ₁ τ₂ : Interval Time) (h : τ₁.subinterval τ₂) :
    eventInSpan P w τ₁ → eventInSpan P w τ₂ := by
  intro ⟨e, hsub, hP⟩
  exact ⟨e, ⟨le_trans h.1 hsub.1, le_trans hsub.2 h.2⟩, hP⟩

/-- Subdomain alternatives for culminated events are all nonweaker:
    every subdomain alternative entails the assertion.
    This is because eventInSpan is monotone in the time span. -/
theorem subdomain_alts_nonweaker (P : EventPred W Time) (w : W)
    (τ : Interval Time) (τ' : Interval Time) (h : τ' ∈ SubdomainAlternatives τ) :
    eventInSpan P w τ' → eventInSpan P w τ :=
  eventInSpan_monotone P w τ' τ h

-- ════════════════════════════════════════════════════
-- § 7. Exhaustification and Contradiction
-- ════════════════════════════════════════════════════

/-- **Positive environment contradiction** (@cite{iatridou-zeijlstra-2021} §4):
    In a positive (non-DE) context, exhaustification of subdomain alternatives
    requires negating all nonweaker alternatives. But ALL subdomain alternatives
    are entailed by the assertion (by `subdomain_alts_nonweaker`). Negating them
    contradicts the assertion → logical contradiction → ungrammaticality.

    This explains why *in years* is an NPI:
    "*Joe has met Mary in weeks" is ungrammatical because exhaustification
    of the domain alternatives in a positive context yields contradiction. -/
theorem positive_exhaustification_contradicts (P : EventPred W Time) (w : W)
    (τ : Interval Time)
    (_hassert : eventInSpan P w τ)
    -- The exhaustifier requires negating all stronger alternatives
    (hexh : ∀ τ' ∈ SubdomainAlternatives τ, τ' ≠ τ → noEventInSpan P w τ') :
    -- If any proper subinterval exists, we have a contradiction
    ∀ (τ_sub : Interval Time),
      τ_sub.subinterval τ → τ_sub ≠ τ →
      -- The assertion entails the subdomain alternative
      eventInSpan P w τ_sub → False := by
  intro τ_sub hsub hne hev
  exact hexh τ_sub hsub hne hev

/-- **Negative environment: exhaustification is vacuous.**
    Under negation, subdomain alternatives ¬∃e.[P(e) ∧ Run(e) ⊆ τ'] are
    WEAKER than the assertion ¬∃e.[P(e) ∧ Run(e) ⊆ τ] (for τ' ⊆ τ).
    Since no subdomain alternative is stronger, there is nothing to exclude,
    and exhaustification applies vacuously. No contradiction arises. -/
theorem negated_subdomain_weaker (P : EventPred W Time) (w : W)
    (τ τ' : Interval Time) (h : τ'.subinterval τ) :
    noEventInSpan P w τ → noEventInSpan P w τ' := by
  intro hneg hev
  exact hneg (eventInSpan_monotone P w τ' τ h hev)

-- ════════════════════════════════════════════════════
-- § 8. The Actuality Inference
-- ════════════════════════════════════════════════════

/-- **Actuality Inference** (@cite{iatridou-zeijlstra-2021} §4):
    With *in years*, the LB of the PTS can only be set at the point where
    an event of the relevant sort took place (since *in years* stretches
    backward from the RB until it finds such an event). Therefore, the
    existence of the event is presupposed — it is the only thing that
    can define the LB.

    Formally: if the LB is set by a domain-widening boundary adverbial
    that stretches as far as possible, the LB must be at the most recent
    occurrence of the event. This makes the event's occurrence a
    presupposition, not just an implicature — hence noncancelable. -/
def actualityInference (P : EventPred W Time) (w : W)
    (τ : Interval Time) : Prop :=
  eventInSpan P w τ

/-- The AI with *in years* is at the LB: the event occurs at the LB point. -/
def aiAtBoundary (P : EventPred W Time) (w : W)
    (τ : Interval Time) : Prop :=
  ∃ e : Eventuality Time, e.τ.finish = τ.start ∧ P w e

-- ════════════════════════════════════════════════════
-- § 9. The Beyond Expectation Inference
-- ════════════════════════════════════════════════════

/-- **Beyond Expectation Inference** (@cite{iatridou-zeijlstra-2021} §2):
    *In years* conveys that the PTS is larger than a contextually salient
    alternative. "*He hasn't had a seizure in months*" conveys the PTS is
    larger than a contextually salient number of months.

    This follows from domain widening: the time span is stretched beyond
    any contextual alternative, so the event occurred earlier than expected. -/
structure BeyondExpectationInference where
  /-- The actual time span -/
  actualSpan : Interval Time
  /-- The contextually expected upper bound on the time span -/
  expectedBound : Interval Time
  /-- The actual span is larger (the event is earlier than expected) -/
  beyondExpectation : expectedBound.subinterval actualSpan
  /-- The spans are not equal (the actual is strictly larger) -/
  strict : expectedBound ≠ actualSpan

-- ════════════════════════════════════════════════════
-- § 10. Aspect Interaction with Boundary Adverbials
-- ════════════════════════════════════════════════════

/-- Perfective contributes ST ⊆ TT: the event is contained in the time span.
    @cite{iatridou-zeijlstra-2021} §1 (eq. 17a), following @cite{klein-1994}.
    Equivalently, the E-perfect: the event is contained in the PTS. -/
def perfectiveContainment (e : Eventuality Time) (τ : Interval Time) : Prop :=
  e.τ.subinterval τ

/-- Imperfective contributes TT ⊆ ST: the time span is contained in the event.
    @cite{iatridou-zeijlstra-2021} §1 (eq. 17b).
    With the subinterval property, every subinterval of a P-event is also
    a P-event. This is the key to *until*-d (affirmative imperfective). -/
def imperfectiveContainment (e : Eventuality Time) (τ : Interval Time) : Prop :=
  τ.subinterval e.τ

/-- Under IMPF + subinterval property, all subdomain alternatives of the
    assertion are ENTAILED (not merely nonweaker). This means exhaustification
    is vacuous for affirmative imperfectives — explaining why *until*-d
    (affirmative imperfective + *until*) is fine without negation.
    @cite{iatridou-zeijlstra-2021} §7.2 -/
theorem impf_subdomain_entailed (P : EventPred W Time)
    (hSub : HasSubintervalProp P) (w : W)
    (e : Eventuality Time) (τ : Interval Time)
    (hP : P w e) (hImpf : τ.subinterval e.τ)
    (τ' : Interval Time) (hτ' : τ'.subinterval τ) :
    eventInSpan P w τ' := by
  -- τ' ⊆ τ ⊆ τ(e), so τ' ⊆ τ(e)
  have h_sub_e : τ'.subinterval e.τ :=
    ⟨le_trans hImpf.1 hτ'.1, le_trans hτ'.2 hImpf.2⟩
  -- By SUB, any event with runtime τ' is a P-event
  exact ⟨⟨τ'⟩, ⟨le_refl _, le_refl _⟩, hSub e w hP τ' h_sub_e ⟨τ'⟩ rfl⟩

-- ════════════════════════════════════════════════════
-- § 11. Bridge: Constant's Observation
-- ════════════════════════════════════════════════════

/-- **Constant's Observation** (@cite{iatridou-zeijlstra-2021} §1):
    The AI of *in years* is noncancelable, unlike the AI of
    *in (the last) 5 years*.

    (22a) "He hasn't had a seizure in years."
          ... #In fact, he has never had one.  [noncancelable]

    vs.

    (11b) "She hasn't had one in the last 5 years."
          ... I don't know about earlier.      [cancelable]

    This follows from domain widening: *in years* stretches the PTS
    maximally, so the LB can only be set by a prior event occurrence.
    *In (the last) 5 years* fixes the LB independently (by counting
    backward), so the event occurrence is merely implicated, not
    presupposed. -/
theorem constants_observation :
    inYears.introducesDomainAlts = true ∧
    inTheLast5Years.introducesDomainAlts = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 12. Bridge: PTS ↔ Existing Infrastructure
-- ════════════════════════════════════════════════════

/-- A BoundaryAdverbial that is a domain widener is predicted to be
    a strong NPI (not weak). This is because domain widening operates
    on presupposed content (the PTS/UTS existence), and strong NPIs
    are those whose exhaustifier accesses non-truth-conditional content.
    @cite{iatridou-zeijlstra-2021} §11 -/
def isDomainWidener (adv : BoundaryAdverbial) : Bool :=
  adv.introducesDomainAlts

/-- Domain wideners among boundary adverbials are strong NPIs. -/
theorem domain_widener_is_strong_npi :
    (isDomainWidener inYears = true ∧ inYears.npiStrength = .strong) ∧
    (isDomainWidener until_ = true ∧ until_.npiStrength = .strong) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Non-widener boundary adverbials are not NPIs. -/
theorem non_widener_not_npi :
    (isDomainWidener since2015 = false ∧ since2015.npiStrength = .none_) ∧
    (isDomainWidener inTheLast5Years = false ∧ inTheLast5Years.npiStrength = .none_) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end Semantics.Tense.PTS
