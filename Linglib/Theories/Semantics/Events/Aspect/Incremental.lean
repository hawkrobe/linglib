import Linglib.Theories.Semantics.Events.ThematicRole.Properties
import Linglib.Theories.Semantics.Events.Scalar.Affectedness
import Linglib.Theories.Semantics.Events.Aspect.PrecedenceClosure

/-!
# Incrementality (SINC, INC) and Verb-Class Typeclass Hierarchy
@cite{krifka-1998} @cite{tenny-1994} @cite{dowty-1991}

The incrementality story: a thematic relation θ that establishes a
correspondence between an object and an event. K98 distinguishes:
- **SINC** (strictly incremental, eq. 51): bijective sub-object ↔
  sub-event correspondence (consumption/creation: *eat the apples*,
  *draw the circle*).
- **INC** (incremental, eq. 59): closure of some SINC θ′ under sum
  (allows backups: *read the article*).

Plus the verb-class typeclass hierarchy formed by these properties
together with `CumTheta` (and `UP`) from `ThematicRoleProperties.lean`,
declared as a mathlib-style `extends` chain:

    IsCumThetaVerb (in ThematicRoleProperties.lean)
        ↑
    IsIncVerb extends IsCumThetaVerb
        ↑
    IsSincVerb extends IsIncVerb

so that synthesis automatically derives weaker classes from stronger
ones. Mathlib analogue: `Group extends Monoid extends Semigroup`.

Topic-named (not paper-named): SINC originates in @cite{krifka-1998}
§3.2 (eq. 51) but the underlying concept is shared by
@cite{tenny-1994}'s aspectual roles, @cite{dowty-1991}'s proto-roles,
and any modern incremental-theme account.

## References

* @cite{krifka-1998} §3.2 (SINC eq. 51), §3.6 (INC eq. 59)
* @cite{tenny-1994} (aspectual roles)
* @cite{dowty-1991} (proto-roles)
-/

namespace Semantics.Events.Incrementality

open Semantics.Events.ThematicRoleProperties

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-! ### Strict Incrementality (K98 §3.2 eq. 51) -/

/-- Strict Incrementality (SINC): the conjunction of MSO, UO, MSE, UE
    plus a non-degeneracy condition requiring extended entities.
    @cite{krifka-1998} eq. 51:

    SINC(θ) iff
      (i) MSO(θ) ∧ UO(θ) ∧ MSE(θ) ∧ UE(θ)
      (ii) ∃x,y∈U_P ∃e,e'∈U_E [y < x ∧ e' < e ∧ θ(x,e) ∧ θ(y,e')]

    Condition (i) guarantees a bijective correspondence between the part
    structure of the object and the part structure of the event.
    Condition (ii) ensures θ actually applies to extended entities (ones
    with proper parts), ruling out degenerate cases where θ only relates
    atoms. K98 §3.2 page 13-14 worked example: *eat the apples*,
    *draw the circle*. -/
structure SINC (θ : α → β → Prop) : Prop where
  /-- Proper subevents map to proper object parts. -/
  mso : MSO θ
  /-- Each event part has a unique object counterpart. -/
  uo  : UO θ
  /-- Proper object parts map to proper subevents. -/
  mse : MSE θ
  /-- Each object part has a unique event counterpart. -/
  ue  : UE θ
  /-- Non-degeneracy: θ applies to at least one extended entity pair.
      eq. (51.ii): the relation must involve entities with
      proper parts, not just atoms. -/
  extended : ∃ (x y : α) (e e' : β), y < x ∧ e' < e ∧ θ x e ∧ θ y e'

-- ────────────────────────────────────────────────────
-- §1.1 Derived monotonicity properties
-- ────────────────────────────────────────────────────

/-- MSE implies ME: weaken strict to non-strict. If proper parts map to
    proper subevents, then parts (including the whole) also map, taking
    e' = e when y = x. -/
theorem me_of_mse {θ : α → β → Prop} (h : MSE θ) : ME θ := by
  intro x e y hθ hle
  by_cases heq : y = x
  · exact ⟨e, le_rfl, heq ▸ hθ⟩
  · have hlt : y < x := lt_of_le_of_ne hle heq
    obtain ⟨e', hlt', hθ'⟩ := h x e y hθ hlt
    exact ⟨e', le_of_lt hlt', hθ'⟩

/-- MSO implies MO: weaken strict to non-strict (dual of `me_of_mse`). -/
theorem mo_of_mso {θ : α → β → Prop} (h : MSO θ) : MO θ := by
  intro x e e' hθ hle
  by_cases heq : e' = e
  · exact ⟨x, le_rfl, heq ▸ hθ⟩
  · have hlt : e' < e := lt_of_le_of_ne hle heq
    obtain ⟨y, hlt', hθ'⟩ := h x e e' hθ hlt
    exact ⟨y, le_of_lt hlt', hθ'⟩

/-- SINC implies ME (via MSE). -/
theorem me_of_sinc {θ : α → β → Prop} (h : SINC θ) : ME θ :=
  me_of_mse h.mse

/-- SINC implies MO (via MSO). -/
theorem mo_of_sinc {θ : α → β → Prop} (h : SINC θ) : MO θ :=
  mo_of_mso h.mso

-- Note on UP vs UO + GUE: K98 eq. 43 lists UP as a separate property
-- from the SINC components. UO is relativized to an outer (x,e) pair, so
-- two independent fillers x,y of the same event e aren't directly
-- connected by UO's uniqueness clause. UP must be assumed separately
-- where needed (e.g., in `qua_propagation`).

-- In CEM models, SINC implies CumTheta: the bijection between object
-- parts and event parts extends to sums. However, CumTheta does not
-- follow from SINC in arbitrary join semilattices (it requires CEM
-- complementation to decompose sums). Following K98 eq. 44, we require
-- CumTheta as a separate hypothesis where needed (see `cum_propagation`
-- in `CumulativityPropagation.lean`).

/-! ### General Incrementality (K98 §3.6 eq. 59) -/

/-- General Incrementality (INC): θ is the closure of some strictly
    incremental θ' under sum formation.
    @cite{krifka-1998} eq. 59: θ is incremental iff there exists a
    SINC θ' such that θ(x,e) holds iff (x,e) can be decomposed into
    θ'-pairs that sum to (x,e). This handles "read the article"
    (allows re-reading/backups): reading events are built from
    strictly incremental reading-parts that can overlap in their
    object coverage.

    Specialization of `Semantics.Events.PrecedenceClosure` with the
    trivial precedence condition: arbitrary sums are admitted. -/
abbrev IncClosure (θ' : α → β → Prop) : α → β → Prop :=
  Semantics.Events.PrecedenceClosure (fun _ _ ↦ True) θ'

/-- General Incrementality: θ is the IncClosure of some SINC θ'. -/
def INC (θ : α → β → Prop) : Prop :=
  ∃ θ' : α → β → Prop, SINC θ' ∧ ∀ (x : α) (e : β), θ x e ↔ IncClosure θ' x e

/-- SINC + CumTheta implies INC: a strictly incremental θ that is
    cumulative is trivially its own closure. CumTheta ensures the
    reverse direction: `IncClosure θ ⊆ θ`. -/
theorem inc_of_sinc {θ : α → β → Prop} (h : SINC θ) (hCum : CumTheta θ) : INC θ :=
  ⟨θ, h, fun x e => ⟨fun hθ => Semantics.Events.PrecedenceClosure.base hθ,
    fun hcl => Semantics.Events.PrecedenceClosure.closure_subset
      (fun _ _ h => h) (fun x₁ x₂ e₁ e₂ h₁ h₂ _ => hCum _ _ _ _ h₁ h₂) hcl⟩⟩

/-! ### VerbIncClass — Verb Incrementality Classification (K98 §3.6) -/

/-- Incrementality annotations for verbs.
    @cite{krifka-1998} §3.2-3.7: verbs differ in which thematic role
    properties their incremental theme satisfies. -/
inductive VerbIncClass where
  /-- Strictly incremental: consumption/creation verbs (K98 §3.2 page
      13-14: *eat the apples*, *draw the circle*). Per K98 §3.7, *build*
      and *write a sequence* require the necessary-preparatory-event
      extension to fit cleanly. -/
  | sinc
  /-- Incremental: allows backups (*read the article*, K98 §3.6). -/
  | inc
  /-- Cumulative only: non-incremental (*push, pull, carry*, K98 §3.2
      page 12-13). "cumOnly" is the formaliser's shorthand for
      "CumTheta-without-incrementality"; K98 doesn't use this literal
      label. -/
  | cumOnly
  deriving DecidableEq, Repr

/-! ### Verb-Class Typeclass Hierarchy -/

/-! Mathlib-style `extends` chain. The empirical K98 verb classes
    correspond to *partition* membership; the typeclass chain encodes
    *structural strength*: every property satisfied by a SINC verb is
    also satisfied by an INC verb, and every property satisfied by an
    INC verb is also satisfied by a CumTheta verb. So `[IsSincVerb θ]
    → [IsIncVerb θ] → [IsCumThetaVerb θ]` via `extends`.

    Linguistic note: this is **not** a claim that *eat* (a SINC verb)
    is empirically classified as both SINC and cumOnly. The typeclass
    chain only encodes "*eat* satisfies all the properties needed to
    apply theorems stated at the IsCumThetaVerb level." Empirical
    verb-class membership is captured by `VerbIncClass` (above). -/

/-- Incremental verbs (mathlib-discipline typeclass form bundling
    `INC` and inheriting `CumTheta` from `IsCumThetaVerb` via
    `extends`).

    Linguistic exemplar (K98 §3.6 page 18): *read (the article)* —
    K98's running case for INC-but-not-SINC. Concretely, *read* fails
    UE (a passage can be read at two distinct subevents) and MSO
    (sub-events e₁ ⊕ e₂' ⊕ e₃ and e₁ ⊕ e₂ ⊕ e₃ relate to the same
    object), and additionally fails ME on the spine of a book
    (K98 §3.7 page 19 — the spine, though part of the book, isn't
    subjected to a reading event). The "allows backups" gloss is
    correct but partial.

    Strictly weaker than `IsSincVerb`: every SINC verb is INC via
    the extends chain (witness: `inc_of_sinc`), but not conversely. -/
class IsIncVerb (θ : α → β → Prop) : Prop extends IsCumThetaVerb θ where
  /-- General incrementality: θ is the IncClosure of some SINC θ'
      (K98 eq. 59). -/
  inc : INC θ

/-- Strictly incremental verbs (mathlib-discipline typeclass form
    bundling `SINC` and `UP`, inheriting `INC` and `CumTheta` from
    `IsIncVerb` via `extends`).

    Bundles the witnesses that `qua_propagation` and `cum_propagation`
    require for the K89 → K98 propagation chain.

    Linguistic exemplars (K98 §3.2 page 13-14): *eat (the apples)* and
    *draw (the circle)* — pure consumption / creation verbs whose
    object incrementally measures out the event with no backups.
    K98 §3.6 distinguishes these from INC-only verbs like *read*.
    K98 §3.7 explicitly flags *build (a house)* and *write (a sequence
    of numbers)* as needing the "necessary preparatory event"
    extension to fit the schema — they are NOT clean SINC exemplars
    and instances should not be declared without addressing K98's §3.7
    caveats (scaffold erection, sequence-quantization, surface-only
    verbs like *peel*).

    Smart constructor `IsSincVerb.mk'` derives the inherited `inc`
    field automatically via `inc_of_sinc`; consumers usually want
    `mk'` rather than the auto-generated `mk`. -/
class IsSincVerb (θ : α → β → Prop) : Prop extends IsIncVerb θ where
  /-- Strict incrementality: bijective correspondence between proper
      object parts and proper event parts (K98 eq. 51). -/
  sinc : SINC θ
  /-- Uniqueness of participants: each event has at most one θ-filler
      (K98 eq. 43). -/
  up : UP θ

/-- Smart constructor for `IsSincVerb`: takes the three K98 meaning
    postulates (`SINC`, `UP`, `CumTheta`) and derives the inherited
    `inc : INC θ` field automatically via `inc_of_sinc`. The
    auto-generated `IsSincVerb.mk` requires consumers to provide
    `inc` explicitly, which is wasteful since SINC + CumTheta
    determines INC.

    Use this when declaring concrete instances:

    ```lean
    instance : IsSincVerb θ := IsSincVerb.mk' sinc up cumTheta
    ```
-/
@[reducible]
def IsSincVerb.mk' {θ : α → β → Prop}
    (sinc : SINC θ) (up : UP θ) (cumTheta : CumTheta θ) :
    IsSincVerb θ where
  toIsIncVerb :=
    { toIsCumThetaVerb := { cumTheta := cumTheta }
      inc := inc_of_sinc sinc cumTheta }
  sinc := sinc
  up := up

/-! ### Bridge: K98 SINC → Beavers Quantized -/

/-! K98 SINC and Beavers Quantized are related but DIFFERENT formal
    commitments:
    - K98 SINC: bijective sub-event ↔ sub-object correspondence
      (structural property of θ).
    - Beavers Quantized: patient ends event with specific final
      degree `g_φ` on a scale (scalar result-state property).

    K98 SINC does NOT structurally imply Beavers Quantized — a
    bijective theme-event correspondence says nothing about a final
    state on a scale. The two coincide empirically for consumption /
    creation verbs (*eat*, *build*) where the scale is "consumption
    progress" with `g_φ = 1` (fully consumed/created), but the
    inference requires an explicit `[HasScalarResult]` instance and a
    final-degree witness.

    This bridge is a SMART CONSTRUCTOR (not an `instance`) because the
    final degree is verb-specific lexical content that cannot be
    derived from SINC alone. -/

open Semantics.Events.AffectednessHierarchy
open Semantics.Events.ScalarResult

/-- Bridge: a K98 SINC verb θ with an explicit final-degree witness
    becomes a Beavers `IsQuantizedAffected` instance. The `forget`
    link is needed to provide the inherited `HasLatentScale`
    derivation (any verb with a result state is a fortiori a
    force-recipient).

    Example use:
    ```
    instance : IsQuantizedAffected eatThemeToy :=
      IsQuantizedAffected.ofIsSincVerb (forget := ...) (g_φ := fullyEaten) (h := ...)
    ```
-/
@[reducible]
def IsQuantizedAffected.ofIsSincVerb {α β δ : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    [HasScalarResult α δ β] [HasLatentScale α β]
    (θ : α → β → Prop) [_h : IsSincVerb θ]
    (forget : ∀ (x : α) (e : β), (∃ g : δ, HasScalarResult.resultAt x g e) →
              HasLatentScale.latentScale x e)
    (g_φ : δ) (h_quantized : Quantized θ g_φ) :
    IsQuantizedAffected (δ := δ) θ :=
  IsQuantizedAffected.mk' forget g_φ h_quantized

end Semantics.Events.Incrementality
