import Linglib.Semantics.Mereology
import Linglib.Semantics.Events.Basic

/-!
# Stratified Reference [champollion-2017]

Champollion's unified stratified-reference property `SR_{d,γ}` and the
three specializations linglib uses. Named in the namespace-carried scheme:
the `Stratified` namespace supplies the "stratified" qualifier, so the
core property is `Stratified.Reference` and the specializations are
`Stratified.DistributiveReference` / `SubintervalReference` /
`MeasurementReference`.

## Main definitions

* `Reference` — Champollion's unified `SR_{d,γ}` (defined Ch 4 §4.6,
  motivated Ch 5); `ReferenceUniv` is its universal closure
  `∀x, P x → Reference d γ P x`.
* `DistributiveReference` / `…Univ` — Stratified Distributive Reference
  (Ch 4 §4.6 distributivity-via-θ; Ch 6 atelicity reuse): `d = θ`,
  `γ = Atom`.
* `RelationalDistributiveReference` / `…Univ` — the relational-role form
  (`R : Entity → Event → Prop`), composing with `Verb.denote`; coincides
  with the functional form on a role's graph.
* `SubintervalReference` / `…Univ` — Stratified Subinterval Reference
  (Ch 4 §4.6 atelicity-via-τ; Ch 5 §5.4 motivation): `d = τ`,
  `γ = proper subinterval`.
* `MeasurementReference` / `…Univ` — [champollion-2017]'s *stratified
  measurement reference* (Def 61 in §4.6; final Defs 52–53 in Ch 7 §7.4);
  `d = μ`, `γ = strict less-than` (substance pseudopartitives: *thirty
  liters of water*, *five feet of snow*).

## Granularity signature: binary, not unary

Champollion's primary schema has `g : β → Prop` (unary); his `[[of]]`
lexical entry constructs `g` via `γ(M, x) := λd. d < M(x)`, closing over
the outer entity. Linglib uncurries: `Reference` takes `γ : β → β → Prop`
directly with inner-then-outer convention. Equivalent
post-closure-elimination but lets all specializations be genuine
instances of `Reference`.

## Relation to Krifka's CUM/QUA (Champollion §2.7.2)

The naive bridge `SubintervalReferenceUniv τ P ↔ CUM P` does **not** hold,
in either direction, by Champollion's own design:

* **`CUM P → SubintervalReferenceUniv τ P` is false**. Champollion §2.7.2
  adopts *lexical cumulativity* as a foundational assumption: every verb
  is cumulative (`[[V]] = *[[V]]`). Counterexample: *reach the summit* is
  telic but cumulative; lacks subinterval reference along τ.
* **`SubintervalReferenceUniv τ P → CUM P` is false**. Subinterval
  reference is about subdividing into τ-smaller `P`-parts — it does not
  entail closure under sum. Counterexample (linglib):
  `P := λe. e.runtime.length ≤ 1` over dense time has subinterval
  reference (split each event in halves) but fails CUM (two unit-length
  disjoint events sum to length 2).

The contrast with Krifka [krifka-1998] that Champollion makes in Ch 6 is
**stratified reference vs. divisive-reference**, not vs. CUM. Champollion
retains CUM as a baseline holding of all VPs and replaces Krifka's
`≤_τ`-divisiveness diagnostic with the strictly weaker stratified-reference
diagnostic. This makes `Aspect/Stratified.lean` (this file) and
`Aspect/Cumulativity.lean` (sibling) genuinely independent: stratified
reference is the atelicity diagnostic; CUM is the NP→VP propagation
property.

## TODO

* The stativity opposition along τ (Champollion's fourth opposition) is
  realized in linglib by `HasSubintervalProp` in
  `Semantics/Aspect/SubintervalProperty.lean` rather than as a decomposition
  form. The `(τ, point-granularity)` form has no current consumer.
* `Studies/Champollion2017.lean` covers distributivity (Ch 6) + a basic
  subinterval-reference↔Vendler atelicity bridge (§ 5), but does NOT yet
  formalize Champollion's distinctive Ch 6 *push carts all the way to the
  store for fifty minutes* contrast — the empirical case where stratified
  reference and Krifka's divisive-reference diagnostic make divergent
  predictions.

## References

* [champollion-2017] (primary, all stratified-reference primitives +
  §2.7.2 lexical cumulativity stance + Ch 6 vs-Krifka argument)
* [krifka-1998] (the divisive-reference atelicity diagnostic stratified
  reference replaces, per Champollion Ch 6)
* [link-1983] (the `*` algebraic-closure operator stratified reference
  builds on)
-/

namespace Semantics.Aspect.Stratified

open _root_.Mereology
open Features

/-! ### Stratified Reference ([champollion-2017] eq. 16/17) -/

/-- Stratified Reference: the core unified property from
    [champollion-2017] eq. (16), with the binary-granularity
    convention from eq. (17)'s γ-helper inlined.

    `Reference d γ P x` holds iff `x` can be decomposed into `P`-parts `y`
    whose `d`-images stand in relation `γ` to `d x`.

    - `d : α → β` — the *dimension* (thematic role θ, runtime τ, measure μ, ...)
    - `γ : β → β → Prop` — the *granularity* relating inner (`d y`) to outer
      (`d x`). Uncurried form of Champollion's eq. (17) γ-helper
      `γ(M, x) := λd. d < M(x)`.
    - `P : α → Prop` — the predicate under scrutiny ("the Share")
    - `x : α` — the entity being decomposed

    `Reference d γ P x = *{y : P(y) ∧ γ (d y) (d x)}(x)`. -/
def Reference {α β : Type*} [SemilatticeSup α]
    (d : α → β) (γ : β → β → Prop) (P : α → Prop) (x : α) : Prop :=
  AlgClosure (λ y => P y ∧ γ (d y) (d x)) x

/-! ### Universal Stratified Reference -/

/-- Universal Stratified Reference: every `P`-entity has stratified
    reference. `ReferenceUniv d γ P := ∀ x, P x → Reference d γ P x`. When
    this holds, `P` is "stratified" along `d` at granularity `γ`. -/
def ReferenceUniv {α β : Type*} [SemilatticeSup α]
    (d : α → β) (γ : β → β → Prop) (P : α → Prop) : Prop :=
  ∀ x, P x → Reference d γ P x

/-! ### Atomic granularity (shared γ) -/

/-- Atomic granularity for dimensions where `[PartialOrder β]` is
    available: the inner d-image is an `Atom` in β. Used by
    `DistributiveReference` (dimension = θ thematic role; entities have a
    partial-order instance via the entity lattice).

    For dimensions without a `PartialOrder` instance — notably the
    runtime dimension (`NonemptyInterval Time`) used by stativity — atomicity
    is expressed dimension-natively (e.g., `NonemptyInterval.IsPoint` for
    `NonemptyInterval Time`). The unification is at the `Reference`
    parameter-space level: both express "γ = inner is atomic in the
    dimension's natural sense" at different concrete instantiations. -/
def AtomicGranularity {β : Type*} [PartialOrder β] : β → β → Prop :=
  λ inner _outer => Atom inner

/-! ### Stratified Distributive Reference ([champollion-2017] eq. 24) -/

/-- Stratified Distributive Reference: dimension is a thematic role θ,
    granularity is `Atom` on the inner image (the outer is unused —
    atomicity is an absolute property). [champollion-2017] eq. (24).

    Captures *distributivity*: "The boys each saw a movie" distributes
    over atomic agents.

    Genuine instance of `Reference` with `γ := AtomicGranularity`. -/
def DistributiveReference {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (P : α → Prop) (x : α) : Prop :=
  Reference θ AtomicGranularity P x

/-- Universal distributive reference: every P-entity distributes along θ. -/
def DistributiveReferenceUniv {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (P : α → Prop) : Prop :=
  ∀ x, P x → DistributiveReference θ P x

/-! ### Relational distributive reference (neo-Davidsonian roles)

Champollion's `DistributiveReference` takes a *functional* thematic role
`θ : α → Entity` (the unique role-filler). linglib's neo-Davidsonian roles
are *relational* — `ArgumentStructure.ThematicRel = Entity → Event → Prop`,
`Agent(a, e)` — with thematic uniqueness available as
`ArgumentStructure.UP`. `RelationalDistributiveReference` is the relational
form, so the distributivity property composes directly with a
`ThematicFrame` / `Verb.denote` without picking a role function. It
coincides with the functional form on a role's graph
(`relationalDistributiveReference_graph`). -/

/-- Relational Stratified Distributive Reference: the role is a
    neo-Davidsonian relation `R : Entity → α → Prop`. A stratum `y` counts
    iff it has an atomic `R`-filler. Under thematic uniqueness
    (`ArgumentStructure.UP R`) that filler is unique, recovering "the
    `R`-filler of `y` is atomic". -/
def RelationalDistributiveReference {Entity α : Type*} [PartialOrder Entity]
    [SemilatticeSup α] (R : Entity → α → Prop) (P : α → Prop) (x : α) : Prop :=
  AlgClosure (λ y => P y ∧ ∃ a, R a y ∧ Atom a) x

/-- Universal relational distributive reference: every P-element
    distributes along R. -/
def RelationalDistributiveReferenceUniv {Entity α : Type*} [PartialOrder Entity]
    [SemilatticeSup α] (R : Entity → α → Prop) (P : α → Prop) : Prop :=
  ∀ x, P x → RelationalDistributiveReference R P x

/-- Relational distributive reference is monotone in the predicate. -/
theorem relationalDistributiveReference_mono {Entity α : Type*}
    [PartialOrder Entity] [SemilatticeSup α]
    {R : Entity → α → Prop} {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∀ x, RelationalDistributiveReference R P x →
      RelationalDistributiveReference R Q x := by
  intro x hx
  exact algClosure_mono (λ y ⟨hp, ha⟩ => ⟨h y hp, ha⟩) x hx

/-- Relational distributive reference along a functional role's graph
    coincides with the functional `DistributiveReference` — the bridge
    justifying the relational form as the faithful generalization of
    [champollion-2017]'s distributive reference. -/
theorem relationalDistributiveReference_graph {Entity α : Type*}
    [PartialOrder Entity] [SemilatticeSup α]
    {θ : α → Entity} {P : α → Prop} {x : α} :
    RelationalDistributiveReference (λ a y => θ y = a) P x ↔
      DistributiveReference θ P x := by
  unfold RelationalDistributiveReference DistributiveReference Reference
    AtomicGranularity
  simp only [exists_eq_left']

/-! ### Stratified Subinterval Reference ([champollion-2017] eq. 38) -/

/-- Proper-subinterval granularity: inner runtime is a proper subinterval
    of outer runtime. The binary `γ` for subinterval reference. -/
def SubintervalGranularity {Time : Type*} [LinearOrder Time]
    (inner outer : NonemptyInterval Time) : Prop :=
  inner < outer

/-- Stratified Subinterval Reference: dimension is τ (runtime),
    granularity is proper-subinterval. `SubintervalReference P e` holds
    iff `e` can be built from `P`-parts with runtimes properly included in
    `τ e`. [champollion-2017] eq. (38).

    Captures *atelicity*: predicates compatible with for-adverbials have
    subinterval reference. "John ran for an hour" → run has it.

    Genuine instance of `Reference` with `d := τ` and
    `γ := SubintervalGranularity`. -/
def SubintervalReference {Time : Type*} [LinearOrder Time]
    [SemilatticeSup (Event Time)]
    (P : Event Time → Prop) (e : Event Time) : Prop :=
  Reference (λ e' : Event Time => e'.runtime) SubintervalGranularity P e

/-- Universal subinterval reference: every P-event has it. -/
def SubintervalReferenceUniv {Time : Type*} [LinearOrder Time]
    [SemilatticeSup (Event Time)]
    (P : Event Time → Prop) : Prop :=
  ∀ e, P e → SubintervalReference P e

/-! ### Stratified Measurement Reference -/

/-! **`MeasurementReference`** is [champollion-2017]'s *stratified
    measurement reference* (his named property and abbreviation): Def 61
    in the Ch 4 §4.6 unification, with final universal/restricted forms
    Defs 52–53 in Ch 7 §7.4, written as `SR_{μ, λd.d < μ(x)}` (*thirty
    liters of water*, *five feet of snow*, *two degrees Celsius of global
    warming*).

    The strict-less-than granularity is Champollion's faithful translation
    of [schwarzschild-2006]'s monotonic measure-function predicate
    (Ch 7 eq. 8: `μ` is monotonic iff `a < b → μ(a) < μ(b)`), with the
    extensive/intensive measure-function distinction ([krifka-1998])
    reduced to whether the resulting measurement-reference presupposition
    is satisfiable on the given substance noun.
-/

/-- Stratified Measurement Reference: dimension is a measure function μ,
    granularity is strict less-than on the scale.
    `MeasurementReference μ P x` holds iff `x` can be decomposed into
    `P`-parts with strictly smaller μ-values.

    Genuine instance of `Reference` with `γ := (· < ·)`. -/
def MeasurementReference {α β : Type*} [SemilatticeSup α] [Preorder β]
    (μ : α → β) (P : α → Prop) (x : α) : Prop :=
  Reference μ (· < ·) P x

/-- Universal measurement reference: every P-entity has it along μ. -/
def MeasurementReferenceUniv {α β : Type*} [SemilatticeSup α] [Preorder β]
    (μ : α → β) (P : α → Prop) : Prop :=
  ∀ x, P x → MeasurementReference μ P x

/-! ### Distributivity Constraint -/

/-- [champollion-2017] Ch 4 §4.6 **Distributivity Constraint**
    (restated in Ch 7 §7.4 for the measurement chapter):
    a distributive construction with Share `S`, Map `M`, granularity `γ`
    describing entity `x` is acceptable iff `SR_{M,γ}(S)(x)`. The same
    constraint underlies adverbial-*each*, *for*-adverbials, and
    pseudopartitives — they differ only in how `M`, `γ`, and `S` are set. -/
abbrev DistributivityConstraint {α β : Type*} [SemilatticeSup α]
    (Map : α → β) (gran : β → β → Prop) (Share : α → Prop) (x : α) : Prop :=
  Reference Map gran Share x

/-! ### Construction Instances -/

/-- "each" distributes over atomic θ-fillers.
    Map = θ (thematic role), granularity = Atom (inner only). -/
abbrev eachConstr {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (Share : α → Prop) (x : α) : Prop :=
  DistributiveReference θ Share x

/-- "for"-adverbials require subinterval reference: the predicate must
    have stratified subinterval reference (atelicity).
    Map = τ, granularity = proper subinterval. -/
abbrev forConstr {Time : Type*} [LinearOrder Time] [SemilatticeSup (Event Time)]
    (Share : Event Time → Prop) (e : Event Time) : Prop :=
  SubintervalReference Share e

/-! ### Key Theorems -/

/-- `ReferenceUniv` entails `Reference` for any specific element. -/
theorem referenceUniv_entails_restricted {α β : Type*} [SemilatticeSup α]
    {d : α → β} {γ : β → β → Prop} {P : α → Prop}
    (h : ReferenceUniv d γ P) {x : α} (hx : P x) : Reference d γ P x :=
  h x hx

/-- Predicates have stratified reference for trivial granularity: every
    `P x` is its own base-case stratum when γ is vacuously true. (No `CUM`
    required — `AlgClosure.base` suffices.) -/
theorem reference_trivial_granularity {α β : Type*} [SemilatticeSup α]
    {d : α → β} {P : α → Prop} :
    ReferenceUniv d (λ _ _ => True) P := by
  intro x hx
  exact AlgClosure.base ⟨hx, trivial⟩

/-- Distributive reference is monotone in the predicate. -/
theorem distributiveReference_mono {α β : Type*} [SemilatticeSup α]
    [PartialOrder β]
    {θ : α → β} {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∀ x, DistributiveReference θ P x → DistributiveReference θ Q x := by
  intro x hx
  exact algClosure_mono (λ y ⟨hp, hg⟩ => ⟨h y hp, hg⟩) x hx

/-- Stratified reference is monotone in the predicate, dimension-
    polymorphically. Generalizes `distributiveReference_mono` to any
    dimension `d` and granularity `γ`. -/
theorem reference_mono {α β : Type*} [SemilatticeSup α]
    {d : α → β} {γ : β → β → Prop} {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∀ x, Reference d γ P x → Reference d γ Q x := by
  intro x hx
  exact algClosure_mono (λ y ⟨hp, hg⟩ => ⟨h y hp, hg⟩) x hx

/-- **Dimension-polymorphic substrate witness.** Stratified reference with
    reflexive granularity is satisfied by every `P`-element via the base
    case. Quantifies over any `d : α → β` (no `IsSumHom` needed for this
    direction, since the witness is structural).

    The companion direction — closure under sums via `IsSumHom d` — is
    `reference_join` below; together they establish that stratified
    reference composes faithfully with the trace-function abstraction. -/
theorem reference_of_refl_granularity {α β : Type*} [SemilatticeSup α]
    {d : α → β} {γ : β → β → Prop} (hRefl : ∀ b, γ b b)
    {P : α → Prop} {x : α} (hx : P x) : Reference d γ P x :=
  AlgClosure.base ⟨hx, hRefl (d x)⟩

/-- Stratified reference is closed under join when (i) the dimension is a
    sum-homomorphism and (ii) the granularity is monotone in the outer
    position w.r.t. `≤` on β. The substrate validation that the
    trace-function abstraction (`[IsSumHom d]`, applicable uniformly to τ,
    σ, agentOf, patientOf, themeOf via the instances in `Events/CEM.lean`)
    composes correctly with stratified reference.

    The `IsSumHom` assumption ensures `d (x ⊔ y) = d x ⊔ d y`; the
    monotonicity assumption on γ then carries the stratification witnesses
    for `x` and `y` over to a witness for `x ⊔ y`. -/
theorem reference_join {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (d : α → β) [hHom : IsSumHom d]
    {γ : β → β → Prop}
    (hMono : ∀ a b₁ b₂, γ a b₁ → b₁ ≤ b₂ → γ a b₂)
    {P : α → Prop} {x y : α}
    (hx : Reference d γ P x) (hy : Reference d γ P y) :
    Reference d γ P (x ⊔ y) := by
  unfold Reference at hx hy ⊢
  -- The closure structure already gives closure under sum (algClosure_cum);
  -- we just weaken the granularity witness via monotonicity to compare
  -- against the joined outer dimension.
  have hxy : AlgClosure (λ z => P z ∧ γ (d z) (d x ⊔ d y)) (x ⊔ y) := by
    have hx' : AlgClosure (λ z => P z ∧ γ (d z) (d x ⊔ d y)) x := by
      exact algClosure_mono
        (λ z ⟨hp, hg⟩ => ⟨hp, hMono _ _ _ hg le_sup_left⟩) x hx
    have hy' : AlgClosure (λ z => P z ∧ γ (d z) (d x ⊔ d y)) y := by
      exact algClosure_mono
        (λ z ⟨hp, hg⟩ => ⟨hp, hMono _ _ _ hg le_sup_right⟩) y hy
    exact AlgClosure.sum hx' hy'
  rw [hHom.map_sup]
  exact hxy

/-! ### Aspect Bridge (subinterval reference ↔ atelicity) -/

/-- for-adverbials require subinterval reference (Champollion Ch 5 §5.4).
    "John ran for an hour" is felicitous because "run" has it.
    "* John arrived for an hour" is infelicitous because "arrive" lacks it. -/
theorem forAdverbial_requires_subintervalReference
    {Time : Type*} [LinearOrder Time] [SemilatticeSup (Event Time)]
    {P : Event Time → Prop}
    (h_for_ok : SubintervalReferenceUniv P) :
    ∀ e, P e → SubintervalReference P e :=
  h_for_ok

/-- QUA and subinterval reference are directly incompatible: if P(e) and
    `SubintervalReference P e` hold, then P cannot be quantized. The
    AlgClosure decomposition yields a base element a with P(a) and
    a.runtime ⊂ e.runtime. Since a ≤ e (from the join structure) and
    a ≠ e (proper subinterval is irreflexive), we get a < e, contradicting
    QUA.

    Direct, not routed through CUM: the would-be route
    `SubintervalReferenceUniv → CUM → ¬QUA` fails at the first step
    (`SubintervalReferenceUniv → CUM` is false in general; counterexample:
    `P := λe. e.runtime.length ≤ 1` over dense time). See module docstring
    "Relation to Krifka's CUM/QUA". -/
theorem qua_incompatible_with_subintervalReference
    {Time : Type*} [LinearOrder Time] [SemilatticeSup (Event Time)]
    {P : Event Time → Prop}
    (hQua : QUA P)
    {e : Event Time} (he : P e) (hSub : SubintervalReference P e) :
    False := by
  obtain ⟨a, ⟨hPa, hGran⟩, hle⟩ := algClosure_has_base hSub
  have hne : a ≠ e := by
    intro heq; rw [heq] at hGran
    exact lt_irrefl _ hGran
  exact hQua hPa he hne hle

/-! ### for-Adverbial Compatibility -/

/-- The "for"-adverbial adds a duration constraint on the event runtime
    and requires the predicate to have subinterval reference
    ([champollion-2017]'s for-adverbial entry, eq. (72), restated for
    *for an hour* as eq. (21); eq. (39) is the constraint on its Share).
    "V for δ" = λe. V(e) ∧ τ(e) = δ ∧ SubintervalReference V e. -/
def forAdverbialMeaning {Time : Type*} [LinearOrder Time]
    [SemilatticeSup (Event Time)]
    (V : Event Time → Prop) (duration : NonemptyInterval Time) (e : Event Time) : Prop :=
  V e ∧ e.runtime = duration ∧ SubintervalReference V e

/-- "in"-adverbials are incompatible with subinterval reference (they
    require telicity). "V in δ" requires QUA, which is incompatible with
    subinterval reference. Any P-event with subinterval reference has a
    strict P-part, contradicting QUA. -/
theorem in_adverbial_incompatible_with_subintervalReference
    {Time : Type*} [LinearOrder Time] [SemilatticeSup (Event Time)]
    {P : Event Time → Prop}
    (hQua : QUA P)
    {e₁ e₂ : Event Time} (he₁ : P e₁) (_he₂ : P e₂) (_hne : e₁ ≠ e₂) :
    ¬ SubintervalReferenceUniv P := by
  intro hSub
  exact qua_incompatible_with_subintervalReference hQua he₁ (hSub e₁ he₁)

end Semantics.Aspect.Stratified
