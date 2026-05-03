import Linglib.Theories.Semantics.Events.StratifiedReference

/-!
# Strata-theory specializations: the four oppositions
@cite{champollion-2017} §1.2

User-facing aliases for the four oppositions @cite{champollion-2017}'s
*Parts of a Whole* unifies under stratified reference, each a thin
specialization of `SR_univ d γ P` at a fixed (dimension, granularity):

| Opposition         | Dimension d | Granularity γ        | Alias              |
|--------------------|-------------|----------------------|--------------------|
| atelic / telic     | τ runtime   | proper subinterval   | `IsAtelic`         |
| stative / non-     | τ runtime   | point interval       | `IsStative`        |
| role-distributive  | θ role      | atomic               | `IsRoleDistributive` |
| mass / count       | μ measure   | strict less-than     | `IsMassReference`  |

No new algebraic content: each predicate unfolds to an existing
`SR_univ` instance. The point is to expose the named oppositions
@cite{champollion-2017} §1.2 catalogues so that consumers can write
`IsStative verb_pred` rather than constructing the full SR parameter
tuple, and so that downstream framework-attribution theorems (Bennett-
Partee 1972, Zhao 2025, Krifka 1998) all anchor against one substrate.

`IsRoleDistributive` (rather than `IsDistributive`) avoids collision
with `Semantics.Dynamic.Core.IsDistributive` (CCP per-element
distributivity), which is widely consumed elsewhere in the codebase.
-/

namespace Semantics.Events.StratifiedReference

open Semantics.Events
open Core.Time

-- ════════════════════════════════════════════════════
-- § 1. Atelic (aspect, dim = τ runtime, γ = proper subinterval)
-- ════════════════════════════════════════════════════

/-- A predicate is *atelic* iff it has Stratified Subinterval Reference
    along the runtime — the *for*-adverbial diagnostic of
    @cite{champollion-2017} ch 5. Specializes `SR_univ` at dimension τ,
    granularity = proper-subinterval (the granularity-relativization
    that solves the minimal-parts problem).

    Activities (run, dance) and states (love, know) both satisfy this;
    accomplishments (build a sandcastle) and achievements (arrive) do
    not. -/
abbrev IsAtelic {Time : Type*} [LinearOrder Time] [SemilatticeSup (Event Time)]
    (P : Event Time → Prop) : Prop :=
  SSR_univ P

-- ════════════════════════════════════════════════════
-- § 2. Stative (Bennett-Partee/Zhao, dim = τ, γ = point interval)
-- ════════════════════════════════════════════════════

/-- A predicate is *stative* (at the strata-theory predicate level) iff
    every P-event decomposes into P-parts whose runtimes are point
    intervals (`Interval.IsPoint`). The strata-theory analog of
    @cite{zhao-2025} Def. 5.36 (p. 165) ATOM-DIST_t (Zhao states the
    quantifier-level form via `Core.Time.AtomDist`) and of the
    Bennett-Partee 1972 atomic SIP framing.

    **Caveat — non-equivalence with the universal-witness form.** This
    SR-form requires the existence of a point-interval decomposition;
    the Bennett-Partee form (`HasSubintervalProp` in
    `Tense/Aspect/SubintervalProperty.lean`) requires that every
    subinterval-witness event satisfies P. The two formulations
    correspond to the *same* (dimension, granularity) point in
    Champollion's parameter space (τ, atomic) but differ in
    universal-quantification structure. They are not directly
    interderivable without auxiliary witness-existence assumptions. -/
abbrev IsStative {Time : Type*} [LinearOrder Time] [SemilatticeSup (Event Time)]
    (P : Event Time → Prop) : Prop :=
  SR_univ (fun e : Event Time => e.runtime)
    (fun inner _outer => inner.IsPoint) P

-- ════════════════════════════════════════════════════
-- § 3. Role-distributive (dim = θ role, γ = atomic)
-- ════════════════════════════════════════════════════

/-- A predicate is *role-distributive* along thematic role θ iff it has
    Stratified Distributive Reference. @cite{champollion-2017} eq. (24).
    "The boys each saw a movie" is role-distributive on the agent role.

    Named `IsRoleDistributive` rather than `IsDistributive` to avoid
    collision with `Semantics.Dynamic.Core.IsDistributive` (CCP
    per-element distributivity), a different sense of "distributive"
    widely consumed elsewhere in the codebase. -/
abbrev IsRoleDistributive {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (P : α → Prop) : Prop :=
  SDR_univ θ P

-- ════════════════════════════════════════════════════
-- § 4. Mass-reference (dim = μ measure, γ = strict <)
-- ════════════════════════════════════════════════════

/-- A predicate has *mass reference* along measure function μ iff it
    has Stratified Measurement Reference: every entity decomposes into
    parts with strictly smaller μ-values. Subsumes the
    @cite{krifka-1998} / @cite{schwarzschild-2006} treatment of
    pseudopartitives like *thirty liters of water*. -/
abbrev IsMassReference {α β : Type*} [SemilatticeSup α] [Preorder β]
    (μ : α → β) (P : α → Prop) : Prop :=
  SMR_univ μ P

-- ════════════════════════════════════════════════════
-- § 5. Parameter-space relationships
-- ════════════════════════════════════════════════════

/-! The four specializations occupy distinct points in Champollion's
    (dimension, granularity) parameter space:

    - `IsStative` and `IsAtelic` share dimension (τ runtime) but differ
      in granularity (point-interval vs proper-subinterval). Conceptually
      states are atelic, but the implication does NOT hold cleanly in
      this SR-decomposition formalization: a state event whose runtime
      is itself a point interval has no proper-subinterval witnesses,
      so the implication fails on the degenerate case. The relationship
      is parameter-space adjacency, not direct entailment.

    - `IsStative` and `IsRoleDistributive` share granularity (atomic in
      the dimension's natural sense) but differ in dimension (τ vs θ).
      Again, parameter-space adjacency.

    - `IsMassReference` is genuinely orthogonal — the strict-less-than
      granularity is intermediate between proper-subinterval and atomic.

    The strata-theory unification claim is that all four specializations
    are *the same higher-order property `SR`* under different parameter
    settings — not that there are direct implications between them. The
    framework-attribution theorems (e.g., the bridge to `AtomDist`) live
    elsewhere and require the relevant universal-witness assumptions
    explicitly. -/

end Semantics.Events.StratifiedReference
