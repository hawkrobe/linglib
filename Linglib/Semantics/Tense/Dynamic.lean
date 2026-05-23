import Linglib.Semantics.Dynamic.Core.ContextFilter
import Linglib.Semantics.Tense.Compositional

/-!
# Dynamic Tense as Eliminative Update of Static Tense
@cite{veltman-1996} @cite{groenendijk-stokhof-veltman-1996} @cite{de-groote-2006} @cite{charlow-2021} @cite{heim-1982}

`dynPAST`/`dynPRES`/`dynFUT` are the dynamic-context-update counterparts
of the static `PAST`/`PRES`/`FUT` operators in `Tense/Compositional.lean`.
Each is defined here as `dynRelation` applied to the static temporal-
relation kernel (`precedes`/`coincides`/`follows`) — so the static and
dynamic operators are *the same temporal constraint*, lifted from a
state-level predicate to a context-level filter.

## Theoretical anchor

The pattern instantiates a long-standing thread in dynamic semantics:

- @cite{heim-1982} principle (A) — file change for a static condition is
  intersection with the satisfaction set: `SAT(F + φ) = SAT(F) ∩ {a : a SAT φ}`.
  This is the prototype "static condition lifts to context filter."

- @cite{veltman-1996} formalizes this as the *test* operator:
  `[φ]σ = {w ∈ σ : w ⊨ φ}`. A test never adds entries; it only removes
  worlds that fail the static condition.

- @cite{groenendijk-stokhof-veltman-1996} ("Coreference and Modality")
  generalize tests to *eliminative updates* — context-level operations
  `f : Set α → Set α` with `f c ⊆ c`. Linglib's
  `Dynamic/Core/ContextFilter.IsContextFilter` captures exactly this property,
  and `dynRelation R v₁ v₂` is the canonical eliminative update for a
  binary relation on situation-variable values.

- @cite{de-groote-2006} gives a continuation-passing-style translation
  from static Montague semantics to dynamic, recovering the static reading
  by applying the trivial continuation. The `dynPAST = dynRelation precedes`
  factoring below is the linguistic-tense fragment of that CPS translation:
  the static predicate `precedes` is the pure computation, and `dynRelation`
  is the contextual lift.

- @cite{charlow-2021} recasts dynamic semantics as a monadic effect over
  static semantics. `dynRelation` is (a fragment of) the lift `return :
  StaticPred → DynamicOp`; the static reading is recovered by the closure
  `∃ gs ∈ c, R (gs.1 v₁) (gs.1 v₂)`.

## What this file proves

Three rfl-bridges (`dynPAST_eq_dynRelation_precedes` etc.) establish that
the dynamic operators *definitionally* call the static kernel. Three
realization theorems (`dynPAST_iff_PAST_with_true` etc.) confirm that a
context entry survives the dynamic filter iff the static `PAST`/`PRES`/`FUT`
holds (with the trivial propositional payload) at the entry's
event/reference situations — the "wrapper actually wraps" check.

The temporal-algebra theorems (`temporal_partition`, the three
contradictory-pair lemmas, `dynPAST_transitive`) now derive from the
shared kernel results in `Tense/Compositional.lean`
(`precedes_or_coincides_or_follows`, `not_precedes_and_follows`, etc.)
via `dynRelation`'s generic algebra (`dynRelation_trichotomy`,
`dynRelation_contradictory`, `dynRelation_transitive`). Static and
dynamic tense inherit the same partition properties from a single source.

Sibling of `Tense/Compositional.lean` (where `precedes`/`coincides`/`follows`
and the static `PAST`/`PRES`/`FUT` live) and `Mood/Dynamic.lean` (parallel
realization pattern for SUBJ/IND). Used by
`Studies/Mendes2025.lean`'s analysis of the
Subordinate Future.
-/

namespace Semantics.Tense

open _root_.Core (Assignment WorldTimeIndex)
open Semantics.Dynamic.Core

/--
Dynamic PAST: lifts the static `precedes` relation to an eliminative
update on situation contexts. A context entry survives iff its event-
variable situation precedes its reference-variable situation in time.
-/
def dynPAST {W Time : Type*} [LT Time]
    (eventVar refVar : SVar) : SitContext W Time → SitContext W Time :=
  dynRelation (precedes (W := W) (Time := Time)) eventVar refVar

/--
Dynamic PRES: lifts `coincides` to an eliminative update.
-/
def dynPRES {W Time : Type*}
    (eventVar refVar : SVar) : SitContext W Time → SitContext W Time :=
  dynRelation (coincides (W := W) (Time := Time)) eventVar refVar

/--
Dynamic FUT: lifts `follows` to an eliminative update.
-/
def dynFUT {W Time : Type*} [LT Time]
    (eventVar refVar : SVar) : SitContext W Time → SitContext W Time :=
  dynRelation (follows (W := W) (Time := Time)) eventVar refVar


-- ════════════════════════════════════════════════════════════════
-- § Definitional bridges: dynamic operators ARE dynRelation
-- ════════════════════════════════════════════════════════════════

theorem dynPAST_eq_dynRelation_precedes {W Time : Type*} [LT Time]
    (e r : SVar) (c : SitContext W Time) :
    dynPAST e r c = dynRelation precedes e r c := rfl

theorem dynPRES_eq_dynRelation_coincides {W Time : Type*}
    (e r : SVar) (c : SitContext W Time) :
    dynPRES e r c = dynRelation coincides e r c := rfl

theorem dynFUT_eq_dynRelation_follows {W Time : Type*} [LT Time]
    (e r : SVar) (c : SitContext W Time) :
    dynFUT e r c = dynRelation follows e r c := rfl


-- ════════════════════════════════════════════════════════════════
-- § Static realization: dynamic IS the eliminative update of static
-- ════════════════════════════════════════════════════════════════

/-!
For each tense, the static operator (with the trivial propositional
payload `fun _ => True`) holds at `(s_event, s_ref)` iff the dynamic
operator's filter retains that situation pair. This makes precise the
@cite{de-groote-2006} sense in which static and dynamic tense are the
same operator at different layers — the dynamic version is the
eliminative-update lift of the static one with the propositional payload
collapsed to truth.
-/

theorem dynPAST_iff_PAST_with_true {W Time : Type*} [LT Time]
    (e r : SVar) (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time) :
    gs ∈ dynPAST e r c ↔ gs ∈ c ∧ PAST (fun _ => True) (gs.1 e) (gs.1 r) :=
  ⟨fun h => ⟨h.1, h.2, trivial⟩, fun ⟨hc, hp, _⟩ => ⟨hc, hp⟩⟩

theorem dynPRES_iff_PRES_with_true {W Time : Type*}
    (e r : SVar) (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time) :
    gs ∈ dynPRES e r c ↔ gs ∈ c ∧ PRES (fun _ => True) (gs.1 e) (gs.1 r) :=
  ⟨fun h => ⟨h.1, h.2, trivial⟩, fun ⟨hc, hp, _⟩ => ⟨hc, hp⟩⟩

theorem dynFUT_iff_FUT_with_true {W Time : Type*} [LT Time]
    (e r : SVar) (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time) :
    gs ∈ dynFUT e r c ↔ gs ∈ c ∧ FUT (fun _ => True) (gs.1 e) (gs.1 r) :=
  ⟨fun h => ⟨h.1, h.2, trivial⟩, fun ⟨hc, hp, _⟩ => ⟨hc, hp⟩⟩


-- ════════════════════════════════════════════════════════════════
-- § Temporal algebra (derived from kernel + dynRelation)
-- ════════════════════════════════════════════════════════════════

/-- PAST ∪ PRES ∪ FUT = identity. Derived from `lt_trichotomy` via the
shared `precedes`/`coincides`/`follows` kernel. -/
theorem temporal_partition {W Time : Type*} [LinearOrder Time]
    (v₁ v₂ : SVar) (c : SitContext W Time) :
    dynPAST v₁ v₂ c ∪ dynPRES v₁ v₂ c ∪ dynFUT v₁ v₂ c = c :=
  dynRelation_trichotomy (fun s => s.time) v₁ v₂ c

/-- PAST and FUT are contradictory on the same variables. Derived from
the kernel result `not_precedes_and_follows`. -/
theorem dynPAST_dynFUT_empty {W Time : Type*} [Preorder Time]
    (v₁ v₂ : SVar) (c : SitContext W Time) :
    dynPAST v₁ v₂ (dynFUT v₁ v₂ c) = ∅ :=
  dynRelation_contradictory _ _
    (fun s₁ s₂ h₁ h₂ => not_precedes_and_follows s₁ s₂ ⟨h₁, h₂⟩) v₁ v₂ c

/-- PAST and PRES are contradictory on the same variables. -/
theorem dynPAST_dynPRES_empty {W Time : Type*} [Preorder Time]
    (v₁ v₂ : SVar) (c : SitContext W Time) :
    dynPAST v₁ v₂ (dynPRES v₁ v₂ c) = ∅ :=
  dynRelation_contradictory _ _
    (fun s₁ s₂ h₁ h₂ => not_precedes_and_coincides s₁ s₂ ⟨h₁, h₂⟩) v₁ v₂ c

/-- PRES and FUT are contradictory on the same variables. -/
theorem dynPRES_dynFUT_empty {W Time : Type*} [Preorder Time]
    (v₁ v₂ : SVar) (c : SitContext W Time) :
    dynPRES v₁ v₂ (dynFUT v₁ v₂ c) = ∅ :=
  dynRelation_contradictory _ _
    (fun s₁ s₂ h₁ h₂ => not_coincides_and_follows s₁ s₂ ⟨h₁, h₂⟩) v₁ v₂ c

/-- Chained PAST constraints compose: e < r ∧ r < s → e < s. -/
theorem dynPAST_transitive {W Time : Type*} [Preorder Time]
    (e r s : SVar) (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynPAST r s (dynPAST e r c)) :
    (gs.1 e).time < (gs.1 s).time :=
  dynRelation_transitive
    (R₁ := precedes) (R₂ := precedes)
    (R₃ := fun s₁ s₂ => s₁.time < s₂.time)
    (fun _ _ _ h1 h2 => lt_trans h1 h2) e r s c gs h

end Semantics.Tense
