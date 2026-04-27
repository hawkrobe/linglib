/-
# Stratified Reference @cite{champollion-2017}

Champollion's unified Stratified Reference property `SR_{d,γ}` and the
three specializations linglib uses:

- **SDR** (Stratified Distributive Reference, @cite{champollion-2017} eq. 24):
  dimension = thematic role, granularity = `Atom` (inner is an atom in β).
  Models *distributivity*.
- **SSR** (Stratified Subinterval Reference, @cite{champollion-2017} eq. 38):
  dimension = τ (runtime), granularity = proper subinterval (inner < outer).
  Models *atelicity* (for-adverbial diagnostic).
- **SMR** — *linglib coinage* (Champollion does not name this specialization).
  Dimension = measure function μ, granularity = strict less-than on the scale.
  Champollion writes it directly as `SR_{μ, λd.d<μ(x)}` in @cite{champollion-2017}
  Ch 7 eqs. (18-26) for measurement of substance pseudopartitives ("three liters
  of water", "five feet of snow"). The "Stratified Measurement Reference" name
  is local to linglib.

## Granularity signature: binary, not unary

Champollion's eq. (16) gives `SR_{d,g}` with `g : β → Prop` (unary).
The next equation (eq. 17, the `[[of]]` lexical entry) constructs `g` via a
higher-order helper `γ(M, x) := λd. d < M(x)` — closing over the OUTER entity
`x`. Linglib uncurries this: `SR` takes `γ : β → β → Prop` directly with the
inner-then-outer convention, so `SR d γ P x := *λy(P(y) ∧ γ (d y) (d x))`.
Equivalent to Champollion's eq. (16) post-closure-elimination, but lets all
three specializations (SDR/SSR/SMR) be genuine instances of `SR` rather than
bypass it via per-specialization closures.

## Layered grounding

Built directly on `Mereology.AlgClosure` (= Champollion's `*` operator,
@cite{link-1983}). No new closure operator is introduced; SR is a
predicate-transformer over the existing one.

-/

import Linglib.Theories.Semantics.Events.Mereology

namespace Semantics.Events.StratifiedReference

open Semantics.Events
open Semantics.Events.Mereology
open _root_.Mereology
open Core.Time
open Semantics.Tense.Aspect.LexicalAspect
open Core.Verbs

-- ════════════════════════════════════════════════════
-- § 1. Stratified Reference (@cite{champollion-2017} eq. 16/17)
-- ════════════════════════════════════════════════════

/-- Stratified Reference: the core unified property from
    @cite{champollion-2017} eq. (16), with the binary-granularity
    convention from eq. (17)'s γ-helper inlined.

    `SR d γ P x` holds iff `x` can be decomposed into `P`-parts `y` whose
    `d`-images stand in relation `γ` to `d x`.

    - `d : α → β` — the *dimension* (thematic role θ, runtime τ, measure μ, ...)
    - `γ : β → β → Prop` — the *granularity* relating inner (`d y`) to outer
      (`d x`). Uncurried form of Champollion's eq. (17) γ-helper
      `γ(M, x) := λd. d < M(x)`.
    - `P : α → Prop` — the predicate under scrutiny ("the Share")
    - `x : α` — the entity being decomposed

    `SR d γ P x = *{y : P(y) ∧ γ (d y) (d x)}(x)`. -/
def SR {α β : Type*} [SemilatticeSup α]
    (d : α → β) (γ : β → β → Prop) (P : α → Prop) (x : α) : Prop :=
  AlgClosure (λ y => P y ∧ γ (d y) (d x)) x

-- ════════════════════════════════════════════════════
-- § 2. Universal Stratified Reference
-- ════════════════════════════════════════════════════

/-- Universal Stratified Reference: every `P`-entity has SR.
    `SR_univ d γ P := ∀ x, P x → SR d γ P x`. When this holds, `P` is
    "stratified" along `d` at granularity `γ`. -/
def SR_univ {α β : Type*} [SemilatticeSup α]
    (d : α → β) (γ : β → β → Prop) (P : α → Prop) : Prop :=
  ∀ x, P x → SR d γ P x

-- ════════════════════════════════════════════════════
-- § 3. SDR — Stratified Distributive Reference (@cite{champollion-2017} eq. 24)
-- ════════════════════════════════════════════════════

/-- Stratified Distributive Reference: dimension is a thematic role θ,
    granularity is `Atom` on the inner image (the outer is unused —
    atomicity is an absolute property). @cite{champollion-2017} eq. (24).

    SDR captures *distributivity*: "The boys each saw a movie" distributes
    over atomic agents.

    Genuine instance of `SR` with `γ := fun yβ _ => Atom yβ`. -/
def SDR {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (P : α → Prop) (x : α) : Prop :=
  SR θ (fun yβ _ => Atom yβ) P x

/-- Universal SDR: every P-entity has SDR along θ. -/
def SDR_univ {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (P : α → Prop) : Prop :=
  ∀ x, P x → SDR θ P x

-- ════════════════════════════════════════════════════
-- § 4. SSR — Stratified Subinterval Reference (@cite{champollion-2017} eq. 38)
-- ════════════════════════════════════════════════════

/-- Proper-subinterval granularity: inner runtime is a proper subinterval
    of outer runtime. The binary `γ` for SSR. -/
def SSRGranularity {Time : Type*} [LinearOrder Time]
    (inner outer : Interval Time) : Prop :=
  inner.properSubinterval outer

/-- Stratified Subinterval Reference: dimension is τ (runtime),
    granularity is proper-subinterval. `SSR P e` holds iff `e` can be
    built from `P`-parts with runtimes properly included in `τ e`.
    @cite{champollion-2017} eq. (38).

    SSR captures *atelicity*: predicates compatible with for-adverbials
    have SSR. "John ran for an hour" → run has SSR.

    Genuine instance of `SR` with `d := τ` and `γ := SSRGranularity`. -/
def SSR {Time : Type*} [LinearOrder Time] [SemilatticeSup (Ev Time)]
    (P : Ev Time → Prop) (e : Ev Time) : Prop :=
  SR (fun e' : Ev Time => e'.runtime) SSRGranularity P e

/-- Universal SSR: every P-event has SSR. -/
def SSR_univ {Time : Type*} [LinearOrder Time] [SemilatticeSup (Ev Time)]
    (P : Ev Time → Prop) : Prop :=
  ∀ e, P e → SSR P e

-- ════════════════════════════════════════════════════
-- § 5. SMR — Stratified Measurement Reference
-- ════════════════════════════════════════════════════

/-! **Naming caveat.** "SMR" is linglib's name for the measurement
    specialization of SR. @cite{champollion-2017} does not give this
    specialization a separate name — Ch 7 §7.4 writes it directly as
    `SR_{μ, λd.d < μ(x)}` (eqs. 18-26 for *thirty liters of water*,
    *five feet of snow*, *two degrees Celsius of global warming*, etc.).

    The strict-less-than granularity is Champollion's faithful translation
    of @cite{schwarzschild-2006}'s monotonic measure function predicate
    (Ch 7 eq. 8: `μ` is monotonic iff `a < b → μ(a) < μ(b)`), with
    Schwarzschild's intensive/extensive distinction
    (cf. @cite{krifka-1998} Sec. 3.4) reduced to whether the resulting
    SMR presupposition is satisfiable on the given substance noun.
-/

/-- Stratified Measurement Reference: dimension is a measure function μ,
    granularity is strict less-than on the scale.
    `SMR μ P x` holds iff `x` can be decomposed into `P`-parts with
    strictly smaller μ-values.

    Genuine instance of `SR` with `γ := (· < ·)`. -/
def SMR {α β : Type*} [SemilatticeSup α] [Preorder β]
    (μ : α → β) (P : α → Prop) (x : α) : Prop :=
  SR μ (· < ·) P x

/-- Universal SMR: every P-entity has SMR along μ. -/
def SMR_univ {α β : Type*} [SemilatticeSup α] [Preorder β]
    (μ : α → β) (P : α → Prop) : Prop :=
  ∀ x, P x → SMR μ P x

-- ════════════════════════════════════════════════════
-- § 6. Distributivity Constraint
-- ════════════════════════════════════════════════════

/-- @cite{champollion-2017} Ch 7 eq. (13) **Distributivity Constraint**:
    a distributive construction with Share `S`, Map `M`, granularity `γ`
    describing entity `x` is acceptable iff `SR_{M,γ}(S)(x)`. The same
    constraint underlies adverbial-*each*, *for*-adverbials, and
    pseudopartitives — they differ only in how `M`, `γ`, and `S` are set. -/
abbrev DistConstr {α β : Type*} [SemilatticeSup α]
    (Map : α → β) (gran : β → β → Prop) (Share : α → Prop) (x : α) : Prop :=
  SR Map gran Share x

-- ════════════════════════════════════════════════════
-- § 7. Construction Instances
-- ════════════════════════════════════════════════════

/-- "each" distributes over atomic θ-fillers.
    Map = θ (thematic role), granularity = Atom (inner only). -/
abbrev eachConstr {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (Share : α → Prop) (x : α) : Prop :=
  SDR θ Share x

/-- "for"-adverbials require SSR: the predicate must have stratified
    subinterval reference (atelicity).
    Map = τ, granularity = proper subinterval. -/
abbrev forConstr {Time : Type*} [LinearOrder Time] [SemilatticeSup (Ev Time)]
    (Share : Ev Time → Prop) (e : Ev Time) : Prop :=
  SSR Share e

-- ════════════════════════════════════════════════════
-- § 8. Key Theorems
-- ════════════════════════════════════════════════════

/-- SR_univ entails SR for any specific element (instantiation). -/
theorem sr_univ_entails_restricted {α β : Type*} [SemilatticeSup α]
    {d : α → β} {γ : β → β → Prop} {P : α → Prop}
    (h : SR_univ d γ P) {x : α} (hx : P x) : SR d γ P x :=
  h x hx

/-- Predicates have SR for trivial granularity: every `P x` is its own
    base-case stratum when γ is vacuously true. (No `CUM` required —
    `AlgClosure.base` suffices.) -/
theorem sr_trivial_gran {α β : Type*} [SemilatticeSup α]
    {d : α → β} {P : α → Prop} :
    SR_univ d (λ _ _ => True) P := by
  intro x hx
  exact AlgClosure.base ⟨hx, trivial⟩

/-- SDR is monotone in the predicate: P ⊆ Q implies SDR θ P ⊆ SDR θ Q. -/
theorem sdr_mono {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    {θ : α → β} {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∀ x, SDR θ P x → SDR θ Q x := by
  intro x hx
  exact algClosure_mono (λ y ⟨hp, hg⟩ => ⟨h y hp, hg⟩) x hx

/-- SR is monotone in the predicate, dimension-polymorphically.
    Generalizes `sdr_mono` to any dimension `d` and granularity `γ`. -/
theorem sr_mono {α β : Type*} [SemilatticeSup α]
    {d : α → β} {γ : β → β → Prop} {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∀ x, SR d γ P x → SR d γ Q x := by
  intro x hx
  exact algClosure_mono (λ y ⟨hp, hg⟩ => ⟨h y hp, hg⟩) x hx

/-- **Dimension-polymorphic substrate witness.** SR with reflexive
    granularity is satisfied by every `P`-element via the base case.
    Quantifies over any `d : α → β` (no `IsSumHom` needed for this
    direction, since the witness is structural).

    The companion direction — closure of SR under sums via `IsSumHom d` —
    is provided by `sr_join` below; together they establish that SR
    composes faithfully with the trace-function abstraction. -/
theorem sr_of_refl_gran {α β : Type*} [SemilatticeSup α]
    {d : α → β} {γ : β → β → Prop} (hRefl : ∀ b, γ b b)
    {P : α → Prop} {x : α} (hx : P x) : SR d γ P x :=
  AlgClosure.base ⟨hx, hRefl (d x)⟩

/-- SR is closed under join when (i) the dimension is a sum-homomorphism
    and (ii) the granularity is monotone in the outer position with
    respect to `≤` on β. The substrate validation that the trace-function
    abstraction (`[IsSumHom d]`, applicable uniformly to τ, σ, agentOf,
    patientOf, themeOf via the instances in `Events/Mereology.lean`)
    composes correctly with stratified reference.

    The IsSumHom assumption ensures `d (x ⊔ y) = d x ⊔ d y`; the
    monotonicity assumption on γ then carries the stratification
    witnesses for `x` and `y` over to a witness for `x ⊔ y`. -/
theorem sr_join {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (d : α → β) [hHom : IsSumHom d]
    {γ : β → β → Prop}
    (hMono : ∀ a b₁ b₂, γ a b₁ → b₁ ≤ b₂ → γ a b₂)
    {P : α → Prop} {x y : α}
    (hx : SR d γ P x) (hy : SR d γ P y) : SR d γ P (x ⊔ y) := by
  unfold SR at hx hy ⊢
  -- The closure structure already gives us closure under sum
  -- (algClosure_cum); we just need to weaken the granularity witness via
  -- monotonicity to compare against the joined outer dimension.
  have hxy : AlgClosure (λ z => P z ∧ γ (d z) (d x ⊔ d y)) (x ⊔ y) := by
    have hx' : AlgClosure (λ z => P z ∧ γ (d z) (d x ⊔ d y)) x := by
      exact algClosure_mono
        (λ z ⟨hp, hg⟩ => ⟨hp, hMono _ _ _ hg le_sup_left⟩) x hx
    have hy' : AlgClosure (λ z => P z ∧ γ (d z) (d x ⊔ d y)) y := by
      exact algClosure_mono
        (λ z ⟨hp, hg⟩ => ⟨hp, hMono _ _ _ hg le_sup_right⟩) y hy
    exact AlgClosure.sum hx' hy'
  -- IsSumHom gives d (x ⊔ y) = d x ⊔ d y, closing the goal.
  rw [hHom.map_sup]
  exact hxy

-- ════════════════════════════════════════════════════
-- § 9. Meaning Postulates (per-verb distributivity)
-- ════════════════════════════════════════════════════

/-- Meaning postulates for verb distributivity (§6.2–6.3).
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
      §6.3: group agents can collectively cause death. -/
  kill_agent_not_sdr : ¬ SDR_univ agentOf kill
  /-- "meet" does NOT have SDR along the agent role (inherently collective).
      §6.3: meeting requires multiple participants. -/
  meet_agent_not_sdr : ¬ SDR_univ agentOf meet

-- ════════════════════════════════════════════════════
-- § 10. Aspect Bridge (SSR ↔ atelicity)
-- ════════════════════════════════════════════════════

/-- for-adverbials require SSR (§5.3, eq. 39/66).
    "John ran for an hour" is felicitous because "run" has SSR.
    "* John arrived for an hour" is infelicitous because "arrive" lacks SSR. -/
theorem forAdverbial_requires_ssr
    {Time : Type*} [LinearOrder Time] [SemilatticeSup (Ev Time)]
    {P : Ev Time → Prop}
    (h_for_ok : SSR_univ P) :
    ∀ e, P e → SSR P e :=
  h_for_ok

/-- QUA and SSR are directly incompatible: if P(e) and SSR(P)(e) hold,
    then P cannot be quantized. The AlgClosure decomposition yields a
    base element a with P(a) and a.runtime ⊂ e.runtime. Since a ≤ e
    (from the join structure) and a ≠ e (properSubinterval is irreflexive),
    we get a < e, contradicting QUA.

    This is strictly stronger than the route through CUM
    (§4.4), which would require additional
    mereological axioms (SSR_univ → CUM is false in general: P = "events
    with runtime length ≤ 1" has SSR_univ but not CUM over dense time). -/
theorem qua_incompatible_with_ssr
    {Time : Type*} [LinearOrder Time] [SemilatticeSup (Ev Time)]
    {P : Ev Time → Prop}
    (hQua : QUA P)
    {e : Ev Time} (he : P e) (hSSR : SSR P e) :
    False := by
  obtain ⟨a, ⟨hPa, hGran⟩, hle⟩ := algClosure_has_base hSSR
  have hne : a ≠ e := by
    intro heq; rw [heq] at hGran
    exact Interval.properSubinterval_irrefl _ hGran
  exact hQua e a he (lt_of_le_of_ne hle hne) hPa

-- ════════════════════════════════════════════════════
-- § 11. for-Adverbial Compatibility
-- ════════════════════════════════════════════════════

/-- The "for"-adverbial adds a duration constraint on the event runtime
    and requires the predicate to have SSR (eq. 39).
    "V for δ" = λe. V(e) ∧ τ(e) = δ ∧ SSR(V)(e). -/
def forAdverbialMeaning {Time : Type*} [LinearOrder Time]
    [SemilatticeSup (Ev Time)]
    (V : Ev Time → Prop) (duration : Interval Time) (e : Ev Time) : Prop :=
  V e ∧ e.runtime = duration ∧ SSR V e

/-- "in"-adverbials are incompatible with SSR (they require telicity).
    §5.4: "V in δ" requires QUA, which is incompatible
    with SSR. Any P-event with SSR has a strict P-part, contradicting QUA. -/
theorem in_adverbial_incompatible_with_ssr
    {Time : Type*} [LinearOrder Time] [SemilatticeSup (Ev Time)]
    {P : Ev Time → Prop}
    (hQua : QUA P)
    {e₁ e₂ : Ev Time} (he₁ : P e₁) (_he₂ : P e₂) (_hne : e₁ ≠ e₂) :
    ¬ SSR_univ P := by
  intro hSSR
  exact qua_incompatible_with_ssr hQua he₁ (hSSR e₁ he₁)

end Semantics.Events.StratifiedReference
