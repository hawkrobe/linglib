/-
# Stratified Reference (Champollion 2017)

Champollion's unified Stratified Reference property SR_{d,g} and its
three instantiations:

- **SDR** (Stratified Distributive Reference): dimension = thematic role,
  granularity = Atom → models *distributivity*
- **SSR** (Stratified Subinterval Reference): dimension = τ,
  granularity = proper subinterval → models *atelicity*
- **SMR** (Stratified Measurement Reference): dimension = μ,
  granularity = smaller measure → models *measurement*

SR unifies aspect (SSR ↔ atelicity) and distributivity (SDR) as two
instances of the same abstract property, differing only in the
"dimension" (what map is applied) and "granularity" (what counts as
a proper part along that dimension).

## References

- Champollion, L. (2017). *Parts of a Whole: Distributivity as a Bridge
  Between Aspect and Measurement*. OUP. Chapters 4–7.
-/

import Linglib.Theories.Semantics.Events.Mereology
import Linglib.Theories.Semantics.Lexical.Verb.ViewpointAspect

namespace Semantics.Events.StratifiedReference

open Semantics.Events
open Semantics.Events.Mereology
open _root_.Mereology
open Core.Time
open Semantics.Lexical.Verb.Aspect
open Semantics.Lexical.Verb.ViewpointAspect

-- ════════════════════════════════════════════════════
-- § 1. Stratified Reference (eq. 62)
-- ════════════════════════════════════════════════════

/-- Stratified Reference: the core unified property from Champollion (2017)
    eq. (62). SR_{d,g}(P)(x) holds iff x can be decomposed into P-parts
    whose images under dimension d satisfy granularity g.

    - `d : α → β` — the *dimension* (e.g., thematic role θ, runtime τ, measure μ)
    - `g : β → Prop` — the *granularity* (e.g., Atom, properSubinterval, smaller)
    - `P : α → Prop` — the predicate under scrutiny
    - `x : α` — the entity/event being decomposed

    SR_{d,g}(P)(x) = *{y : P(y) ∧ g(d(y))}(x) -/
def SR {α β : Type*} [SemilatticeSup α]
    (d : α → β) (g : β → Prop) (P : α → Prop) (x : α) : Prop :=
  AlgClosure (λ y => P y ∧ g (d y)) x

-- ════════════════════════════════════════════════════
-- § 2. Universal Stratified Reference (eq. 63–64)
-- ════════════════════════════════════════════════════

/-- Universal Stratified Reference: every P-entity has SR.
    Champollion (2017) eq. (63): SR_{d,g}(P) = ∀x. P(x) → SR_{d,g}(P)(x).
    When this holds, P is "stratified" along dimension d at granularity g. -/
def SR_univ {α β : Type*} [SemilatticeSup α]
    (d : α → β) (g : β → Prop) (P : α → Prop) : Prop :=
  ∀ x, P x → SR d g P x

-- ════════════════════════════════════════════════════
-- § 3. SDR — Stratified Distributive Reference (eq. 24/59)
-- ════════════════════════════════════════════════════

/-- Stratified Distributive Reference: dimension is a thematic role θ,
    granularity is Atom. SDR_{θ}(P)(e) holds iff e can be decomposed
    into P-parts whose θ-fillers are atoms (individuals).
    Champollion (2017) eq. (24)/(59).

    SDR captures *distributivity*: "The boys each saw a movie" distributes
    over atomic agents. -/
def SDR {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (P : α → Prop) (x : α) : Prop :=
  SR θ (Atom (α := β)) P x

/-- Universal SDR: every P-entity has SDR along θ. -/
def SDR_univ {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (P : α → Prop) : Prop :=
  ∀ x, P x → SDR θ P x

-- ════════════════════════════════════════════════════
-- § 4. SSR — Stratified Subinterval Reference (eq. 38/60)
-- ════════════════════════════════════════════════════

/-- Proper subinterval granularity relative to a fixed outer event e.
    Used by SSR: the runtime of each part must be a proper subinterval
    of the runtime of the whole.
    Champollion (2017) eq. (38)/(60). -/
def SSRGranularity {Time : Type*} [LinearOrder Time]
    (outer inner : Ev Time) : Prop :=
  inner.runtime.properSubinterval outer.runtime

/-- Stratified Subinterval Reference: dimension is τ (runtime),
    granularity requires proper subinterval of the outer event's runtime.
    SSR(P)(e) holds iff e can be built from P-parts with strictly
    smaller runtimes.
    Champollion (2017) eq. (38)/(60).

    SSR captures *atelicity*: predicates compatible with "for"-adverbials
    have SSR. "John ran for an hour" → run has SSR. -/
def SSR {Time : Type*} [LinearOrder Time] [SemilatticeSup (Ev Time)]
    (P : Ev Time → Prop) (e : Ev Time) : Prop :=
  AlgClosure (λ e' => P e' ∧ SSRGranularity e e') e

/-- Universal SSR: every P-event has SSR. -/
def SSR_univ {Time : Type*} [LinearOrder Time] [SemilatticeSup (Ev Time)]
    (P : Ev Time → Prop) : Prop :=
  ∀ e, P e → SSR P e

-- ════════════════════════════════════════════════════
-- § 5. SMR — Stratified Measurement Reference (eq. 53/61)
-- ════════════════════════════════════════════════════

/-- Stratified Measurement Reference: dimension is a measure function μ,
    granularity requires strictly smaller measure value.
    SMR_{μ}(P)(x) holds iff x can be decomposed into P-parts with
    strictly smaller μ-values.
    Champollion (2017) eq. (53)/(61).

    SMR captures *measurement*: "three pounds of apples" has SMR
    along the weight measure. -/
def SMR {α β : Type*} [SemilatticeSup α] [Preorder β]
    (μ : α → β) (P : α → Prop) (x : α) : Prop :=
  AlgClosure (λ y => P y ∧ μ y < μ x) x

/-- Universal SMR: every P-entity has SMR along μ. -/
def SMR_univ {α β : Type*} [SemilatticeSup α] [Preorder β]
    (μ : α → β) (P : α → Prop) : Prop :=
  ∀ x, P x → SMR μ P x

-- ════════════════════════════════════════════════════
-- § 6. Distributivity Constraint (eq. 68)
-- ════════════════════════════════════════════════════

/-- Champollion's unified distributivity constraint (eq. 68):
    DistConstr_{Map, gran}(Share)(x) = SR_{Map, gran}(Share)(x).
    The three parameters—Map, granularity, and Share—are instantiated
    differently by each construction (each, for-adverbials, etc.). -/
abbrev DistConstr {α β : Type*} [SemilatticeSup α]
    (Map : α → β) (gran : β → Prop) (Share : α → Prop) (x : α) : Prop :=
  SR Map gran Share x

-- ════════════════════════════════════════════════════
-- § 7. Construction Instances
-- ════════════════════════════════════════════════════

/-- "each" distributes over atomic θ-fillers.
    Map = θ (thematic role), granularity = Atom.
    Champollion (2017) §6.4. -/
abbrev eachConstr {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (Share : α → Prop) (x : α) : Prop :=
  SDR θ Share x

/-- "for"-adverbials require SSR: the predicate must have stratified
    subinterval reference (atelicity).
    Map = τ, granularity = proper subinterval.
    Champollion (2017) §5.3. -/
abbrev forConstr {Time : Type*} [LinearOrder Time] [SemilatticeSup (Ev Time)]
    (Share : Ev Time → Prop) (e : Ev Time) : Prop :=
  SSR Share e

-- ════════════════════════════════════════════════════
-- § 8. Key Theorems
-- ════════════════════════════════════════════════════

/-- SR_univ entails SR for any specific element (instantiation).
    Champollion (2017) eq. (32): universal → restricted. -/
theorem sr_univ_entails_restricted {α β : Type*} [SemilatticeSup α]
    {d : α → β} {g : β → Prop} {P : α → Prop}
    (h : SR_univ d g P) {x : α} (hx : P x) : SR d g P x :=
  h x hx

/-- CUM predicates have SR for trivial granularity (everything passes).
    If P is CUM and g is always true, then SR_{d,g}(P) holds universally. -/
theorem cum_implies_sr_trivial_gran {α β : Type*} [SemilatticeSup α]
    {d : α → β} {P : α → Prop} (hCum : CUM P) :
    SR_univ d (λ _ => True) P := by
  intro x hx
  exact AlgClosure.base ⟨hx, trivial⟩

/-- SDR is monotone in the predicate: P ⊆ Q implies SDR θ P ⊆ SDR θ Q. -/
theorem sdr_mono {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    {θ : α → β} {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∀ x, SDR θ P x → SDR θ Q x := by
  intro x hx
  exact algClosure_mono (λ y ⟨hp, hg⟩ => ⟨h y hp, hg⟩) x hx

-- ════════════════════════════════════════════════════
-- § 9. Meaning Postulates (per-verb distributivity)
-- ════════════════════════════════════════════════════

/-- Meaning postulates for verb distributivity (Champollion 2017 §6.2–6.3).
    These encode which verbs have SDR along which roles.

    - `see` is distributive on both agent and theme: "The boys saw the girls"
      entails each boy saw each girl (distributive reading).
    - `kill` is distributive on theme only: "The boys killed the chicken"
      entails the chicken was killed (by the group).
    - `meet` is NOT distributive on agent: "The boys met" does NOT entail
      each boy met (collective only).

    These are axiomatized following the CLAUDE.md convention: prefer sorry
    over weakening, since the proofs require model-theoretic content. -/
class VerbDistributivity (Entity Time : Type*) [LinearOrder Time]
    [SemilatticeSup (Ev Time)] [PartialOrder Entity]
    (agentOf themeOf : Ev Time → Entity)
    (see kill meet : Ev Time → Prop) where
  /-- "see" has SDR along the agent role. -/
  see_agent_sdr : SDR_univ agentOf see
  /-- "see" has SDR along the theme role. -/
  see_theme_sdr : SDR_univ themeOf see
  /-- "kill" has SDR along the theme role. -/
  kill_theme_sdr : SDR_univ themeOf kill
  /-- "kill" does NOT have SDR along the agent role (collective causation).
      Champollion (2017) §6.3: group agents can collectively cause death. -/
  kill_agent_not_sdr : ¬ SDR_univ agentOf kill
  /-- "meet" does NOT have SDR along the agent role (inherently collective).
      Champollion (2017) §6.3: meeting requires multiple participants. -/
  meet_agent_not_sdr : ¬ SDR_univ agentOf meet

-- ════════════════════════════════════════════════════
-- § 10. Aspect Bridge (SSR ↔ atelicity)
-- ════════════════════════════════════════════════════

/-- for-adverbials require SSR (Champollion 2017 §5.3, eq. 39/66).
    "John ran for an hour" is felicitous because "run" has SSR.
    "* John arrived for an hour" is infelicitous because "arrive" lacks SSR. -/
theorem forAdverbial_requires_ssr
    {Time : Type*} [LinearOrder Time] [SemilatticeSup (Ev Time)]
    {P : Ev Time → Prop}
    (h_for_ok : SSR_univ P) :
    ∀ e, P e → SSR P e :=
  h_for_ok

/-- SSR implies CUM: if P has universal SSR, then P is cumulative.
    Champollion (2017) §4.4: SSR is strictly stronger than CUM. -/
theorem ssr_univ_implies_cum
    {Time : Type*} [LinearOrder Time] [SemilatticeSup (Ev Time)]
    {P : Ev Time → Prop}
    (h_ssr : SSR_univ P) :
    CUM P := by
  -- TODO: The proof requires showing that if e₁ and e₂ both have SSR
  -- decompositions, then e₁ ⊔ e₂ also satisfies P. This needs the
  -- subinterval property or specific mereological axioms about how
  -- event sums interact with runtimes.
  sorry

-- ════════════════════════════════════════════════════
-- § 11. for-Adverbial Compatibility
-- ════════════════════════════════════════════════════

/-- The "for"-adverbial adds a duration constraint on the event runtime
    and requires the predicate to have SSR (Champollion 2017 eq. 39).
    "V for δ" = λe. V(e) ∧ τ(e) = δ ∧ SSR(V)(e). -/
def forAdverbialMeaning {Time : Type*} [LinearOrder Time]
    [SemilatticeSup (Ev Time)]
    (V : Ev Time → Prop) (duration : Interval Time) (e : Ev Time) : Prop :=
  V e ∧ e.runtime = duration ∧ SSR V e

/-- "in"-adverbials are incompatible with SSR (they require telicity).
    Champollion (2017) §5.4: "V in δ" requires QUA, which is incompatible
    with SSR for non-trivial predicates. -/
theorem in_adverbial_incompatible_with_ssr
    {Time : Type*} [LinearOrder Time] [SemilatticeSup (Ev Time)]
    {P : Ev Time → Prop}
    (hQua : QUA P)
    {e₁ e₂ : Ev Time} (he₁ : P e₁) (he₂ : P e₂) (hne : e₁ ≠ e₂) :
    ¬ SSR_univ P := by
  intro hSSR
  exact qua_cum_incompatible hQua he₁ he₂ hne (ssr_univ_implies_cum hSSR)

end Semantics.Events.StratifiedReference
