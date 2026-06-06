import Linglib.Semantics.Events.CEM

/-!
# Stratified Reference [champollion-2017]

Champollion's unified Stratified Reference property `SR_{d,γ}` and the
three specializations linglib uses.

## Main definitions

* `SR` — Champollion's unified `SR_{d,γ}` (defined Ch 4 §4.6, motivated Ch 5)
* `SR_univ` — universal closure: `∀x, P x → SR d γ P x`
* `SDR` / `SDR_univ` — Stratified Distributive Reference (Ch 4 §4.6
  distributivity-via-θ; Ch 6 atelicity reuse): `d = θ`, `γ = Atom`.
* `SSR` / `SSR_univ` — Stratified Subinterval Reference (Ch 4 §4.6
  atelicity-via-τ; Ch 5 §5.4 motivation): `d = τ`, `γ = proper subinterval`.
* `SMR` / `SMR_univ` — *linglib coinage*; `d = μ`, `γ = strict less-than`
  (Ch 7 §7.4 measurement of substance pseudopartitives: *thirty liters of
  water*, *five feet of snow*).

## Granularity signature: binary, not unary

Champollion's primary `SR` schema has `g : β → Prop` (unary); his
`[[of]]` lexical entry constructs `g` via `γ(M, x) := λd. d < M(x)`,
closing over the outer entity. Linglib uncurries: `SR` takes
`γ : β → β → Prop` directly with inner-then-outer convention.
Equivalent post-closure-elimination but lets all three specializations
be genuine instances of `SR`.

## Relation to Krifka's CUM/QUA (Champollion §2.7.2)

The naive bridge `SSR_univ τ P ↔ CUM P` does **not** hold, in either
direction, by Champollion's own design:

* **`CUM P → SSR_univ τ P` is false**. Champollion §2.7.2 adopts
  *lexical cumulativity* as a foundational assumption: every verb is
  cumulative (`[[V]] = *[[V]]`). Counterexample: *reach the summit* is
  telic but cumulative; lacks SSR along τ.
* **`SSR_univ τ P → CUM P` is false**. SSR is about subdividing into
  τ-smaller `P`-parts — it does not entail closure under sum.
  Counterexample (linglib): `P := λe. e.runtime.length ≤ 1` over dense
  time has SSR (split each event in halves) but fails CUM (two unit-
  length disjoint events sum to length 2).

The contrast with Krifka [krifka-1998] that Champollion makes in
Ch 6 is **SR vs. divisive-reference**, not SR vs. CUM. Champollion
retains CUM as a baseline holding of all VPs and replaces Krifka's
`≤_τ`-divisiveness diagnostic with the strictly weaker SR diagnostic.
This makes `Aspect/Stratified.lean` (this file) and
`Aspect/Cumulativity.lean` (sibling) genuinely independent: SR is the
atelicity diagnostic; CUM is the NP→VP propagation property.

## TODO

* The stativity opposition along τ (Champollion's fourth opposition) is
  realized in linglib by `HasSubintervalProp` in
  `Tense/Aspect/SubintervalProperty.lean` rather than as an
  SR-decomposition form. The SR form at `(τ, point-granularity)` has
  no current consumer.
* `Studies/Champollion2017.lean` covers distributivity
  (Ch 6 SDR) + a basic SSR↔Vendler atelicity bridge (§ 5), but does NOT
  yet formalize Champollion's distinctive Ch 6 *push carts all the way
  to the store for fifty minutes* contrast — the empirical case where
  SR and Krifka's divisive-reference diagnostic make divergent predictions.
  Adding it as a § 6 there (or a TenseAspect-side companion study file)
  would be the highest-value Champollion vs Krifka empirical engagement.

## References

* [champollion-2017] (primary, all SR primitives + §2.7.2 lexical
  cumulativity stance + Ch 6 vs-Krifka argument)
* [krifka-1998] (the divisive-reference atelicity diagnostic SR
  replaces, per Champollion Ch 6)
* [link-1983] (the `*` algebraic-closure operator SR builds on)
-/

namespace Semantics.Aspect.Stratified

open Semantics.Events.CEM
open _root_.Mereology
open Core.Order
open Features

/-! ### Stratified Reference ([champollion-2017] eq. 16/17) -/

/-- Stratified Reference: the core unified property from
    [champollion-2017] eq. (16), with the binary-granularity
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

/-! ### Universal Stratified Reference -/

/-- Universal Stratified Reference: every `P`-entity has SR.
    `SR_univ d γ P := ∀ x, P x → SR d γ P x`. When this holds, `P` is
    "stratified" along `d` at granularity `γ`. -/
def SR_univ {α β : Type*} [SemilatticeSup α]
    (d : α → β) (γ : β → β → Prop) (P : α → Prop) : Prop :=
  ∀ x, P x → SR d γ P x

/-! ### Atomic granularity (shared γ) -/

/-- Atomic granularity for dimensions where `[PartialOrder β]` is
    available: the inner d-image is an `Atom` in β. Used by `SDR`
    (dimension = θ thematic role; entities have a partial-order
    instance via the entity lattice).

    For dimensions without a `PartialOrder` instance — notably the
    runtime dimension (`Interval Time`) used by stativity — atomicity
    is expressed dimension-natively (e.g., `Interval.IsPoint` for
    `Interval Time`). The unification is at the `SR` parameter-space
    level: both express "γ = inner is atomic in the dimension's
    natural sense" at different concrete instantiations. -/
def AtomicGranularity {β : Type*} [PartialOrder β] : β → β → Prop :=
  fun inner _outer => Atom inner

/-! ### SDR — Stratified Distributive Reference ([champollion-2017] eq. 24) -/

/-- Stratified Distributive Reference: dimension is a thematic role θ,
    granularity is `Atom` on the inner image (the outer is unused —
    atomicity is an absolute property). [champollion-2017] eq. (24).

    SDR captures *distributivity*: "The boys each saw a movie" distributes
    over atomic agents.

    Genuine instance of `SR` with `γ := AtomicGranularity`. -/
def SDR {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (P : α → Prop) (x : α) : Prop :=
  SR θ AtomicGranularity P x

/-- Universal SDR: every P-entity has SDR along θ. -/
def SDR_univ {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (P : α → Prop) : Prop :=
  ∀ x, P x → SDR θ P x

/-! ### SSR — Stratified Subinterval Reference ([champollion-2017] eq. 38) -/

/-- Proper-subinterval granularity: inner runtime is a proper subinterval
    of outer runtime. The binary `γ` for SSR. -/
def SSRGranularity {Time : Type*} [LinearOrder Time]
    (inner outer : Interval Time) : Prop :=
  inner.properSubinterval outer

/-- Stratified Subinterval Reference: dimension is τ (runtime),
    granularity is proper-subinterval. `SSR P e` holds iff `e` can be
    built from `P`-parts with runtimes properly included in `τ e`.
    [champollion-2017] eq. (38).

    SSR captures *atelicity*: predicates compatible with for-adverbials
    have SSR. "John ran for an hour" → run has SSR.

    Genuine instance of `SR` with `d := τ` and `γ := SSRGranularity`. -/
def SSR {Time : Type*} [LinearOrder Time] [SemilatticeSup (Event Time)]
    (P : Event Time → Prop) (e : Event Time) : Prop :=
  SR (fun e' : Event Time => e'.runtime) SSRGranularity P e

/-- Universal SSR: every P-event has SSR. -/
def SSR_univ {Time : Type*} [LinearOrder Time] [SemilatticeSup (Event Time)]
    (P : Event Time → Prop) : Prop :=
  ∀ e, P e → SSR P e

/-! ### SMR — Stratified Measurement Reference -/

/-! **Naming caveat.** "SMR" is linglib's name for the measurement
    specialization of SR. [champollion-2017] does not give this
    specialization a separate name — Ch 7 §7.4 writes it directly as
    `SR_{μ, λd.d < μ(x)}` (eqs. 18-26 for *thirty liters of water*,
    *five feet of snow*, *two degrees Celsius of global warming*, etc.).

    The strict-less-than granularity is Champollion's faithful translation
    of [schwarzschild-2006]'s monotonic measure function predicate
    (Ch 7 eq. 8: `μ` is monotonic iff `a < b → μ(a) < μ(b)`), with
    Schwarzschild's intensive/extensive distinction
    (cf. [krifka-1998] Sec. 3.4) reduced to whether the resulting
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

/-! ### Distributivity Constraint -/

/-- [champollion-2017] Ch 4 §4.6 **Distributivity Constraint**
    (restated in Ch 7 §7.4 for the measurement chapter):
    a distributive construction with Share `S`, Map `M`, granularity `γ`
    describing entity `x` is acceptable iff `SR_{M,γ}(S)(x)`. The same
    constraint underlies adverbial-*each*, *for*-adverbials, and
    pseudopartitives — they differ only in how `M`, `γ`, and `S` are set. -/
abbrev DistConstr {α β : Type*} [SemilatticeSup α]
    (Map : α → β) (gran : β → β → Prop) (Share : α → Prop) (x : α) : Prop :=
  SR Map gran Share x

/-! ### Construction Instances -/

/-- "each" distributes over atomic θ-fillers.
    Map = θ (thematic role), granularity = Atom (inner only). -/
abbrev eachConstr {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (Share : α → Prop) (x : α) : Prop :=
  SDR θ Share x

/-- "for"-adverbials require SSR: the predicate must have stratified
    subinterval reference (atelicity).
    Map = τ, granularity = proper subinterval. -/
abbrev forConstr {Time : Type*} [LinearOrder Time] [SemilatticeSup (Event Time)]
    (Share : Event Time → Prop) (e : Event Time) : Prop :=
  SSR Share e

/-! ### Key Theorems -/

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
    patientOf, themeOf via the instances in `Events/CEM.lean`)
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

/-! ### Meaning Postulates (per-verb distributivity) -/

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
    [SemilatticeSup (Event Time)] [PartialOrder Entity]
    (agentOf themeOf : Event Time → Entity)
    (see kill meet : Event Time → Prop) where
  /-- "see" has SDR along the agent role. -/
  see_agent_sdr : SDR_univ agentOf see
  /-- "see" has SDR along the theme role. -/
  see_theme_sdr : SDR_univ themeOf see
  /-- "kill" has SDR along the theme role. -/
  kill_theme_sdr : SDR_univ themeOf kill
  /-- "kill" does NOT have SDR along the agent role (collective causation).
      Ch 4 §4.5.1: group agents can collectively cause death. -/
  kill_agent_not_sdr : ¬ SDR_univ agentOf kill
  /-- "meet" does NOT have SDR along the agent role (inherently collective).
      Ch 4 §4.5.1: meeting requires multiple participants. -/
  meet_agent_not_sdr : ¬ SDR_univ agentOf meet

/-! ### Aspect Bridge (SSR ↔ atelicity) -/

/-- for-adverbials require SSR (Champollion Ch 5 §5.4).
    "John ran for an hour" is felicitous because "run" has SSR.
    "* John arrived for an hour" is infelicitous because "arrive" lacks SSR. -/
theorem forAdverbial_requires_ssr
    {Time : Type*} [LinearOrder Time] [SemilatticeSup (Event Time)]
    {P : Event Time → Prop}
    (h_for_ok : SSR_univ P) :
    ∀ e, P e → SSR P e :=
  h_for_ok

/-- QUA and SSR are directly incompatible: if P(e) and SSR(P)(e) hold,
    then P cannot be quantized. The AlgClosure decomposition yields a
    base element a with P(a) and a.runtime ⊂ e.runtime. Since a ≤ e
    (from the join structure) and a ≠ e (properSubinterval is irreflexive),
    we get a < e, contradicting QUA.

    Direct, not routed through CUM: the would-be route `SSR_univ → CUM
    → ¬QUA` fails at the first step. `SSR_univ → CUM` is false in
    general (counterexample: `P := λe. e.runtime.length ≤ 1` over
    dense time). See module docstring "Relation to Krifka's CUM/QUA". -/
theorem qua_incompatible_with_ssr
    {Time : Type*} [LinearOrder Time] [SemilatticeSup (Event Time)]
    {P : Event Time → Prop}
    (hQua : QUA P)
    {e : Event Time} (he : P e) (hSSR : SSR P e) :
    False := by
  obtain ⟨a, ⟨hPa, hGran⟩, hle⟩ := algClosure_has_base hSSR
  have hne : a ≠ e := by
    intro heq; rw [heq] at hGran
    exact Interval.properSubinterval_irrefl _ hGran
  exact hQua e a he (lt_of_le_of_ne hle hne) hPa

/-! ### for-Adverbial Compatibility -/

/-- The "for"-adverbial adds a duration constraint on the event runtime
    and requires the predicate to have SSR (eq. 39).
    "V for δ" = λe. V(e) ∧ τ(e) = δ ∧ SSR(V)(e). -/
def forAdverbialMeaning {Time : Type*} [LinearOrder Time]
    [SemilatticeSup (Event Time)]
    (V : Event Time → Prop) (duration : Interval Time) (e : Event Time) : Prop :=
  V e ∧ e.runtime = duration ∧ SSR V e

/-- "in"-adverbials are incompatible with SSR (they require telicity).
    "V in δ" requires QUA, which is incompatible with SSR. Any P-event
    with SSR has a strict P-part, contradicting QUA. -/
theorem in_adverbial_incompatible_with_ssr
    {Time : Type*} [LinearOrder Time] [SemilatticeSup (Event Time)]
    {P : Event Time → Prop}
    (hQua : QUA P)
    {e₁ e₂ : Event Time} (he₁ : P e₁) (_he₂ : P e₂) (_hne : e₁ ≠ e₂) :
    ¬ SSR_univ P := by
  intro hSSR
  exact qua_incompatible_with_ssr hQua he₁ (hSSR e₁ he₁)

end Semantics.Aspect.Stratified
