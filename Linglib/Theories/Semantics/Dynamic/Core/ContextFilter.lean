import Mathlib.Data.Set.Basic
import Linglib.Core.Assignment
import Linglib.Core.WorldTimeIndex
import Linglib.Theories.Semantics.Dynamic.Core.DiscourseRef

/-!
# Context Filters and Situation Contexts

A *context filter* is a function `f : Set α → Set α` that only removes
entries, never adds them. This is the dynamic-semantics notion that
unifies linguistic operations like predication, temporal constraints,
and mood retrieval (IND): they all narrow an information state.

The most common source of context filters is set-builder filtering
(`Set.sep`, the `{x ∈ c | p x}` notation), which is *always* a context
filter — see `sep_isContextFilter` below, a thin restatement of
`Set.sep_subset`.

This file also hosts `SitContext` — the carrier of situation-variable
dynamic semantics — and `dynRelation`, the workhorse filter behind
temporal trichotomy (`<`/`=`/`>` on `.time`, used to define
`Semantics.Tense.dynPAST`/`dynPRES`/`dynFUT`).
-/

namespace Semantics.Dynamic.Core

variable {α : Type*}

/-- A context filter: a `Set α → Set α` operation that only removes
entries, never introduces new ones. -/
def IsContextFilter (f : Set α → Set α) : Prop :=
  ∀ c, f c ⊆ c

namespace IsContextFilter

/-- The identity is a context filter (removes nothing). -/
theorem id_isContextFilter : IsContextFilter (id : Set α → Set α) :=
  fun _ _ h => h

/-- Composition of two context filters is a context filter. -/
theorem comp {f g : Set α → Set α}
    (hf : IsContextFilter f) (hg : IsContextFilter g) :
    IsContextFilter (fun c => g (f c)) :=
  fun c => Set.Subset.trans (hg (f c)) (hf c)

end IsContextFilter

/-- Set-builder filtering by `p` is always a context filter. -/
theorem sep_isContextFilter (p : α → Prop) :
    IsContextFilter (fun c : Set α => {x ∈ c | p x}) :=
  fun _ => Set.sep_subset _ _

-- ════════════════════════════════════════════════════════════════
-- Situation contexts
-- ════════════════════════════════════════════════════════════════

open _root_.Core (Assignment WorldTimeIndex)

/--
A situation-variable dynamic context.

Each entry is a pair `(g, s)` where `g : Nat → WorldTimeIndex W Time`
is a Tarski-style assignment of situation variables (using the shared
`Core.Assignment` substrate) and `s : WorldTimeIndex W Time` is the
current evaluation situation.

The original Mendes-style formalization bundled this with an
`ICDRTAssignment W E` for individual and propositional drefs
(`structure SitAssignment`), but no consumer of `SitContext` actually
accesses entity drefs — situation-variable semantics is independent of
the individual-dref machinery. Co-locating with `Core.Assignment`
keeps the carrier flat and removes the `E` parameter.

Kept as `abbrev` so it inherits `Set α`'s `Membership`,
`EmptyCollection`, `HasSubset`, `Union`, `Inter`, and `Singleton`
instances directly.
-/
abbrev SitContext (W Time : Type*) :=
  Set (Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)

/--
Filter a context by a binary relation on situation variable lookups.

All temporal constraints (`Semantics.Tense.dynPAST`, `dynPRES`,
`dynFUT`) are instances of `dynRelation` with the appropriate ordering
on `.time`.
-/
def dynRelation {W Time : Type*}
    (R : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    (v₁ v₂ : SVar) (c : SitContext W Time) : SitContext W Time :=
  { gs ∈ c | R (gs.1 v₁) (gs.1 v₂) }

theorem dynRelation_isFilter {W Time : Type*}
    (R : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop) (v₁ v₂ : SVar) :
    IsContextFilter (α := Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
      (dynRelation R v₁ v₂) :=
  fun _ _ h => h.1

/-- Applying the same relation filter twice is the same as applying it once. -/
theorem dynRelation_idempotent {W Time : Type*}
    (R : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    (v₁ v₂ : SVar) (c : SitContext W Time) :
    dynRelation R v₁ v₂ (dynRelation R v₁ v₂ c) = dynRelation R v₁ v₂ c := by
  apply Set.ext; intro gs
  unfold dynRelation
  exact ⟨fun ⟨⟨hc, _⟩, hR⟩ => ⟨hc, hR⟩, fun ⟨hc, hR⟩ => ⟨⟨hc, hR⟩, hR⟩⟩

/-- Contradictory relation filters compose to the empty context. -/
theorem dynRelation_contradictory {W Time : Type*}
    (R₁ R₂ : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    (h : ∀ s₁ s₂, R₁ s₁ s₂ → R₂ s₁ s₂ → False)
    (v₁ v₂ : SVar) (c : SitContext W Time) :
    dynRelation R₁ v₁ v₂ (dynRelation R₂ v₁ v₂ c) = ∅ := by
  apply Set.ext; intro gs
  unfold dynRelation
  constructor
  · rintro ⟨⟨_, hR₂⟩, hR₁⟩
    exact absurd hR₁ (fun hR₁ => h _ _ hR₁ hR₂)
  · exact False.elim

/-- Transitive relations chain across three situation variables. -/
theorem dynRelation_transitive {W Time : Type*}
    (R₁ R₂ R₃ : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    (hTrans : ∀ a b c, R₁ a b → R₂ b c → R₃ a c)
    (v₁ v₂ v₃ : SVar) (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynRelation R₂ v₂ v₃ (dynRelation R₁ v₁ v₂ c)) :
    R₃ (gs.1 v₁) (gs.1 v₃) :=
  hTrans _ _ _ h.1.2 h.2

/--
Trichotomy on any linearly ordered projection lifts to a context partition.

For any function `f : WorldTimeIndex → α` into a linear order, the three
comparison operators (<, =, >) form a complete partition of any context.
The temporal partition (`PAST ∪ PRES ∪ FUT = c`) is the special case
where `f = WorldTimeIndex.time`.
-/
theorem dynRelation_trichotomy {W Time α : Type*} [LinearOrder α]
    (f : WorldTimeIndex W Time → α)
    (v₁ v₂ : SVar) (c : SitContext W Time) :
    dynRelation (fun s₁ s₂ => f s₁ < f s₂) v₁ v₂ c ∪
    dynRelation (fun s₁ s₂ => f s₁ = f s₂) v₁ v₂ c ∪
    dynRelation (fun s₁ s₂ => f s₁ > f s₂) v₁ v₂ c = c := by
  apply Set.ext; intro gs
  unfold dynRelation
  constructor
  · rintro ((⟨hc, _⟩ | ⟨hc, _⟩) | ⟨hc, _⟩) <;> exact hc
  · intro hc
    rcases lt_trichotomy (f (gs.1 v₁)) (f (gs.1 v₂)) with h | h | h
    · exact Or.inl (Or.inl ⟨hc, h⟩)
    · exact Or.inl (Or.inr ⟨hc, h⟩)
    · exact Or.inr ⟨hc, h⟩

end Semantics.Dynamic.Core
