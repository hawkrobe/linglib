import Linglib.Semantics.NaturalLogic
import Linglib.Semantics.Aspect.Basic
import Linglib.Semantics.Aspect.SubintervalProperty
import Linglib.Core.Order.Interval
import Linglib.Semantics.Tense.TemporalAdverbials
import Linglib.Studies.IatridouEtAl2001
import Linglib.Studies.Kiparsky2002

/-!
# [iatridou-zeijlstra-2021]: The complex beauty of boundary adverbials: in years and until
[iatridou-zeijlstra-2021] [iatridou-anagnostopoulou-izvorski-2001]
[kiparsky-2002]

Iatridou & Zeijlstra (Linguistic Inquiry 52(1), 2021) unify two
classes of boundary adverbials:

- **LB adverbials** (*in years*, *since*, *in (the last) 5 years*):
  set the **left boundary** of the **Perfect Time Span (PTS)**, with
  RB set by Tense.
- **RB adverbials** (*until*): set the **right boundary** of the
  **Until Time Span (UTS)**, with LB contextually set.

Both classes can be **boundary domain wideners** — they introduce
subdomain alternatives to their time span, triggering exhaustification.
When they are, they produce two noncancelable inferences:

1. **Actuality Inference (AI)**: the relevant event took place
2. **Beyond Expectation Inference (BEI)**: the time span is larger
   than expected

The PTS framework (LB / RB / PTS terminology) is from
[iatridou-anagnostopoulou-izvorski-2001]; UTS, AI/BEI, and the
NPI-status analysis of *in years* / *until* are this paper's
contribution. The substrate below extends IAI 2001's PTS with the IZ
2021 machinery.

## Status

Substrate inherited from `Semantics/Tense/PTS.lean` (deleted;
relocated here per CLAUDE.md graduation rule). Verified against the
IZ 2021 PDF: the abbreviation table (PTS, UTS, LB, RB, AI, BEI, NPI)
confirms the terminology; the "in years / until unification" is the
paper's central claim; domain widener appears 15+ times in the text.
The Lean encoding of the NPI strength classification and the
exhaustification machinery is faithful to the paper's analytical
framework but has not been line-by-line cross-checked against IZ
2021's specific theorems.

-/

namespace IatridouZeijlstra2021

open Core.Order Tense
open Semantics.Aspect
open Semantics.Aspect.SubintervalProperty
open Tense.TemporalAdverbials (PTSConstraint AdverbialType)
open IatridouEtAl2001 (BoundaryKind)
open Kiparsky2002 (PerfectReading)

variable {W Time : Type*} [LinearOrder Time]


-- ════════════════════════════════════════════════════
-- § 1. Boundary Classification
-- ════════════════════════════════════════════════════

-- `BoundaryKind` (LB / RB) is from `IatridouEtAl2001`; imported above.

/-- Which time span the adverbial operates on.
    - `pts`: the Perfect Time Span (LB set by adverbial or context, RB by Tense)
    - `uts`: the Until Time Span (LB contextually set, RB by *until*'s argument) -/
inductive TimeSpanKind where
  | pts  -- Perfect Time Span
  | uts  -- Until Time Span
  deriving DecidableEq, Repr

/-- The boundary set by Tense (not by the adverbial).
    PTS: Tense sets the RB. UTS: context/Tense sets the LB.
    Mirror-image relationship ([iatridou-zeijlstra-2021] §8). -/
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

/-- A boundary adverbial: a temporal expression that sets one boundary
    of a time span (PTS or UTS).

    [iatridou-zeijlstra-2021] §3, §5: *in years* and *until* are
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
  /-- Minimum Zwarts strength of a licensing environment, in the shared
      `Polarity.Item` vocabulary (`none` = not an NPI); strong NPIs
      require anti-additivity ([zwarts-1998], [gajewski-2011]). -/
  licensor : Option NaturalLogic.DEStrength := none
  /-- Is the adverbial always contrastively focused?
      [chierchia-2013]: domain widening requires contrastive focus
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
    [iatridou-zeijlstra-2021] §3–4 -/
def inYears : BoundaryAdverbial where
  form := "in years"
  timeSpan := .pts
  boundary := .left
  introducesDomainAlts := true
  licensor := some .antiAdditive
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
  licensor := none
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
  licensor := none
  alwaysContrastive := false

/-- *Until (5pm / I left)*: unified RB adverbial.
    Sets the RB of the UTS. Always introduces subdomain alternatives
    (the domain-widening effect surfaces only under contrastive focus).
    [iatridou-zeijlstra-2021] §7: one *until*, not two. -/
def until_ : BoundaryAdverbial where
  form := "until"
  timeSpan := .uts
  boundary := .right
  introducesDomainAlts := true
  licensor := some .antiAdditive
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
    inYears.licensor = some .antiAdditive ∧ until_.licensor = some .antiAdditive :=
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
    [chierchia-2013] Ch. 1; [iatridou-zeijlstra-2021] §4:

    When *in years* is present, the assertion (49a) is:
      ∃e.[meet(e, Joe, Mary) ∧ Run(e) ⊆ τ]
    and its domain alternatives (49b) are:
      {∃e.[meet(e, Joe, Mary) ∧ Run(e) ⊆ τ'] | τ' ⊆ τ}

    These subdomain alternatives are logically stronger than the assertion
    (entailed by it), because if a culminated event took place in a
    subinterval of τ, it also took place in τ. -/
def SubdomainAlternatives (τ : NonemptyInterval Time) : Set (NonemptyInterval Time) :=
  Set.Iic τ

/-- Subdomain alternatives of τ include τ itself. -/
theorem self_in_subdomain (τ : NonemptyInterval Time) :
    τ ∈ SubdomainAlternatives τ :=
  ⟨le_refl _, le_refl _⟩

/-- Subdomain alternatives of a subinterval are a subset of subdomain
    alternatives of the superinterval. -/
theorem subdomain_monotone (τ₁ τ₂ : NonemptyInterval Time)
    (h : τ₁ ≤ τ₂) :
    SubdomainAlternatives τ₁ ⊆ SubdomainAlternatives τ₂ := by
  intro τ' ⟨hs, hf⟩
  exact ⟨le_trans h.1 hs, le_trans hf h.2⟩

-- ════════════════════════════════════════════════════
-- § 6. Event Predicate in Time Span
-- ════════════════════════════════════════════════════

/-- An event of type P has its runtime inside time span τ.
    This is the assertion form for both PTS and UTS:
    ∃e.[P(e) ∧ Run(e) ⊆ τ] -/
def eventInSpan (P : W → Event Time → Prop) (w : W) (τ : NonemptyInterval Time) : Prop :=
  ∃ e : Event Time, e.τ ≤ τ ∧ P w e

/-- Negated form: no P-event has runtime inside τ.
    ¬∃e.[P(e) ∧ Run(e) ⊆ τ] -/
def noEventInSpan (P : W → Event Time → Prop) (w : W) (τ : NonemptyInterval Time) : Prop :=
  ¬ eventInSpan P w τ

/-- If a culminated event occurs in a subinterval, it occurs in the
    superinterval. Entailment from subinterval to superinterval. -/
theorem eventInSpan_monotone (P : W → Event Time → Prop) (w : W)
    (τ₁ τ₂ : NonemptyInterval Time) (h : τ₁ ≤ τ₂) :
    eventInSpan P w τ₁ → eventInSpan P w τ₂ := by
  intro ⟨e, hsub, hP⟩
  exact ⟨e, ⟨le_trans h.1 hsub.1, le_trans hsub.2 h.2⟩, hP⟩

/-- Subdomain alternatives for culminated events are all nonweaker:
    every subdomain alternative entails the assertion.
    This is because eventInSpan is monotone in the time span. -/
theorem subdomain_alts_nonweaker (P : W → Event Time → Prop) (w : W)
    (τ : NonemptyInterval Time) (τ' : NonemptyInterval Time) (h : τ' ∈ SubdomainAlternatives τ) :
    eventInSpan P w τ' → eventInSpan P w τ :=
  eventInSpan_monotone P w τ' τ h

-- ════════════════════════════════════════════════════
-- § 7. Exhaustification and Contradiction
-- ════════════════════════════════════════════════════

/-- **Positive environment contradiction** ([iatridou-zeijlstra-2021] §4):
    In a positive (non-DE) context, exhaustification of subdomain alternatives
    requires negating all nonweaker alternatives. But ALL subdomain alternatives
    are entailed by the assertion (by `subdomain_alts_nonweaker`). Negating them
    contradicts the assertion → logical contradiction → ungrammaticality.

    This explains why *in years* is an NPI:
    "*Joe has met Mary in weeks" is ungrammatical because exhaustification
    of the domain alternatives in a positive context yields contradiction. -/
theorem positive_exhaustification_contradicts (P : W → Event Time → Prop) (w : W)
    (τ : NonemptyInterval Time)
    (_hassert : eventInSpan P w τ)
    -- The exhaustifier requires negating all stronger alternatives
    (hexh : ∀ τ' ∈ SubdomainAlternatives τ, τ' ≠ τ → noEventInSpan P w τ') :
    -- If any proper subinterval exists, we have a contradiction
    ∀ (τ_sub : NonemptyInterval Time),
      τ_sub ≤ τ → τ_sub ≠ τ →
      -- The assertion entails the subdomain alternative
      eventInSpan P w τ_sub → False := by
  intro τ_sub hsub hne hev
  exact hexh τ_sub hsub hne hev

/-- **Negative environment: exhaustification is vacuous.**
    Under negation, subdomain alternatives ¬∃e.[P(e) ∧ Run(e) ⊆ τ'] are
    WEAKER than the assertion ¬∃e.[P(e) ∧ Run(e) ⊆ τ] (for τ' ⊆ τ).
    Since no subdomain alternative is stronger, there is nothing to exclude,
    and exhaustification applies vacuously. No contradiction arises. -/
theorem negated_subdomain_weaker (P : W → Event Time → Prop) (w : W)
    (τ τ' : NonemptyInterval Time) (h : τ' ≤ τ) :
    noEventInSpan P w τ → noEventInSpan P w τ' := by
  intro hneg hev
  exact hneg (eventInSpan_monotone P w τ' τ h hev)

-- ════════════════════════════════════════════════════
-- § 8. The Actuality Inference
-- ════════════════════════════════════════════════════

/-- **Actuality Inference** ([iatridou-zeijlstra-2021] §4):
    With *in years*, the LB of the PTS can only be set at the point where
    an event of the relevant sort took place (since *in years* stretches
    backward from the RB until it finds such an event). Therefore, the
    existence of the event is presupposed — it is the only thing that
    can define the LB.

    Formally: if the LB is set by a domain-widening boundary adverbial
    that stretches as far as possible, the LB must be at the most recent
    occurrence of the event. This makes the event's occurrence a
    presupposition, not just an implicature — hence noncancelable. -/
def actualityInference (P : W → Event Time → Prop) (w : W)
    (τ : NonemptyInterval Time) : Prop :=
  eventInSpan P w τ

/-- The AI with *in years* is at the LB: the event occurs at the LB point. -/
def aiAtBoundary (P : W → Event Time → Prop) (w : W)
    (τ : NonemptyInterval Time) : Prop :=
  ∃ e : Event Time, e.τ.snd = τ.fst ∧ P w e

-- ════════════════════════════════════════════════════
-- § 9. The Beyond Expectation Inference
-- ════════════════════════════════════════════════════

/-- **Beyond Expectation Inference** ([iatridou-zeijlstra-2021] §2):
    *In years* conveys that the PTS is larger than a contextually salient
    alternative. "*He hasn't had a seizure in months*" conveys the PTS is
    larger than a contextually salient number of months.

    This follows from domain widening: the time span is stretched beyond
    any contextual alternative, so the event occurred earlier than expected. -/
structure BeyondExpectationInference where
  /-- The actual time span -/
  actualSpan : NonemptyInterval Time
  /-- The contextually expected upper bound on the time span -/
  expectedBound : NonemptyInterval Time
  /-- The actual span is larger (the event is earlier than expected) -/
  beyondExpectation : expectedBound ≤ actualSpan
  /-- The spans are not equal (the actual is strictly larger) -/
  strict : expectedBound ≠ actualSpan

-- ════════════════════════════════════════════════════
-- § 10. Aspect Interaction with Boundary Adverbials
-- ════════════════════════════════════════════════════

/-- Perfective contributes ST ⊆ TT: the event is contained in the time span.
    [iatridou-zeijlstra-2021] §1 (eq. 17a), following [klein-1994].
    Equivalently, the E-perfect: the event is contained in the PTS. -/
def perfectiveContainment (e : Event Time) (τ : NonemptyInterval Time) : Prop :=
  e.τ ≤ τ

/-- Imperfective contributes TT ⊆ ST: the time span is contained in the event.
    [iatridou-zeijlstra-2021] §1 (eq. 17b).
    With the subinterval property, every subinterval of a P-event is also
    a P-event. This is the key to *until*-d (affirmative imperfective). -/
def imperfectiveContainment (e : Event Time) (τ : NonemptyInterval Time) : Prop :=
  τ ≤ e.τ

/-- Under IMPF + subinterval property, all subdomain alternatives of the
    assertion are ENTAILED (not merely nonweaker). This means exhaustification
    is vacuous for affirmative imperfectives — explaining why *until*-d
    (affirmative imperfective + *until*) is fine without negation.
    [iatridou-zeijlstra-2021] §7.2 -/
theorem impf_subdomain_entailed (P : W → Event Time → Prop)
    (hSub : HasSubintervalProp P) (w : W)
    (e : Event Time) (τ : NonemptyInterval Time)
    (hP : P w e) (hImpf : τ ≤ e.τ)
    (τ' : NonemptyInterval Time) (hτ' : τ' ≤ τ) :
    eventInSpan P w τ' := by
  -- τ' ⊆ τ ⊆ τ(e), so τ' ⊆ τ(e)
  have h_sub_e : τ' ≤ e.τ :=
    ⟨le_trans hImpf.1 hτ'.1, le_trans hτ'.2 hImpf.2⟩
  -- By SUB, any event with runtime τ' is a P-event
  -- sort defaults to .action; the proof doesn't reference .sort
  exact ⟨⟨τ', .dynamic⟩, ⟨le_refl _, le_refl _⟩, hSub e w hP τ' h_sub_e ⟨τ', .dynamic⟩ rfl⟩

-- ════════════════════════════════════════════════════
-- § 11. Bridge: Constant's Observation
-- ════════════════════════════════════════════════════

/-- **Constant's Observation** ([iatridou-zeijlstra-2021] §1):
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
    [iatridou-zeijlstra-2021] §11 -/
def isDomainWidener (adv : BoundaryAdverbial) : Bool :=
  adv.introducesDomainAlts

/-- Domain wideners among boundary adverbials are strong NPIs. -/
theorem domain_widener_is_strong_npi :
    (isDomainWidener inYears = true ∧ inYears.licensor = some .antiAdditive) ∧
    (isDomainWidener until_ = true ∧ until_.licensor = some .antiAdditive) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Non-widener boundary adverbials are not NPIs. -/
theorem non_widener_not_npi :
    (isDomainWidener since2015 = false ∧ since2015.licensor = none) ∧
    (isDomainWidener inTheLast5Years = false ∧ inTheLast5Years.licensor = none) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩


end IatridouZeijlstra2021
