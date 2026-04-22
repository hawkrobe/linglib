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
Filter a context by a binary relation between two projections of each entry.

The general eliminative-update primitive: every entry survives iff `R`
holds between the two projected `WorldTimeIndex` values. The two
common specializations are:

- `dynRelation` (both projections look up bound variables `gs.1 v₁`,
  `gs.1 v₂`) — used by `Semantics.Tense.dynPAST`/`dynPRES`/`dynFUT`.
- `Semantics.Mood.dynIND` (one projection is the entry's current
  situation `gs.2`, the other is a bound variable `gs.1 v`).

Mathlib precedent: `Set.image2` over `Set.image`.
-/
def dynRelationOn {W Time : Type*}
    (proj₁ proj₂ :
      Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time
        → WorldTimeIndex W Time)
    (R : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    (c : SitContext W Time) : SitContext W Time :=
  { gs ∈ c | R (proj₁ gs) (proj₂ gs) }

theorem dynRelationOn_isFilter {W Time : Type*}
    (proj₁ proj₂ :
      Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time
        → WorldTimeIndex W Time)
    (R : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop) :
    IsContextFilter (α := Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
      (dynRelationOn proj₁ proj₂ R) :=
  fun _ _ h => h.1

/-- Idempotence of any `dynRelationOn` filter. -/
theorem dynRelationOn_idempotent {W Time : Type*}
    (proj₁ proj₂ :
      Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time
        → WorldTimeIndex W Time)
    (R : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    (c : SitContext W Time) :
    dynRelationOn proj₁ proj₂ R (dynRelationOn proj₁ proj₂ R c) =
      dynRelationOn proj₁ proj₂ R c := by
  apply Set.ext; intro gs
  unfold dynRelationOn
  exact ⟨fun ⟨⟨hc, _⟩, hR⟩ => ⟨hc, hR⟩, fun ⟨hc, hR⟩ => ⟨⟨hc, hR⟩, hR⟩⟩

/-- Two contradictory `dynRelationOn` filters compose to the empty context. -/
theorem dynRelationOn_contradictory {W Time : Type*}
    (proj₁ proj₂ :
      Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time
        → WorldTimeIndex W Time)
    (R₁ R₂ : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    (h : ∀ s₁ s₂, R₁ s₁ s₂ → R₂ s₁ s₂ → False)
    (c : SitContext W Time) :
    dynRelationOn proj₁ proj₂ R₁ (dynRelationOn proj₁ proj₂ R₂ c) = ∅ := by
  apply Set.ext; intro gs
  unfold dynRelationOn
  refine ⟨fun ⟨⟨_, hR₂⟩, hR₁⟩ => absurd hR₁ (fun hR₁ => h _ _ hR₁ hR₂), False.elim⟩

/--
Filter a context by a binary relation on two situation-variable lookups.

The "two bound variables" specialization of `dynRelationOn`. All temporal
constraints (`Semantics.Tense.dynPAST`, `dynPRES`, `dynFUT`) are instances
of `dynRelation` with the appropriate ordering on `.time`.
-/
def dynRelation {W Time : Type*}
    (R : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    (v₁ v₂ : SVar) (c : SitContext W Time) : SitContext W Time :=
  { gs ∈ c | R (gs.1 v₁) (gs.1 v₂) }

/-- `dynRelation` is the `dynRelationOn` specialization with both
projections looking up bound variables. -/
theorem dynRelation_eq_dynRelationOn {W Time : Type*}
    (R : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    (v₁ v₂ : SVar) (c : SitContext W Time) :
    dynRelation R v₁ v₂ c =
      dynRelationOn (fun gs => gs.1 v₁) (fun gs => gs.1 v₂) R c := rfl

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

-- ════════════════════════════════════════════════════════════════
-- § Generative updates: Kleisli composition for the powerset monad
-- ════════════════════════════════════════════════════════════════

/-!
The eliminative-vs-generative dichotomy from @cite{groenendijk-stokhof-veltman-1996}
is exactly the `Set.filter` vs `Set.bind` dichotomy of the powerset monad.
`dynRelationOn`/`dynRelation` cover the eliminative side
(`f c ⊆ c`); `dynIntroduce` covers the generative side: it produces
fresh entries by binding a situation variable to alternatives drawn from
a Kleisli arrow `gen : WorldTimeIndex → Set WorldTimeIndex`.

This is the canonical primitive behind `Semantics.Mood.dynSUBJ` (with
`gen = historicalBase history`) and any other operator that introduces
a fresh situation dref.
-/

/--
Generative update: for each entry `(g, s)`, replace it by
`{ (g[v ↦ s'], s') | s' ∈ gen s }`.

The current situation is updated to the new dref, and the assignment
is extended at `v`. Definitionally a `Set.bind`/Kleisli composition
for the powerset monad.

Unlike `dynRelationOn`/`dynRelation`, this is *not* a context filter
— it can produce entries that did not appear in the input context.
-/
def dynIntroduce {W Time : Type*}
    (gen : WorldTimeIndex W Time → Set (WorldTimeIndex W Time))
    (v : SVar) (c : SitContext W Time) : SitContext W Time :=
  { gs' |
    ∃ g s s',
      (g, s) ∈ c ∧
      s' ∈ gen s ∧
      gs'.1 = g.update v s' ∧
      gs'.2 = s' }

/-- After `dynIntroduce gen v`, looking up `v` in the assignment always
returns the new current situation. This is the structural property that
makes a same-variable filter (e.g. `dynIND v ∘ dynIntroduce gen v`) vacuous. -/
theorem dynIntroduce_binds_current {W Time : Type*}
    (gen : WorldTimeIndex W Time → Set (WorldTimeIndex W Time))
    (v : SVar) (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynIntroduce gen v c) :
    gs.1 v = gs.2 := by
  unfold dynIntroduce at h
  obtain ⟨g, _, s', _, _, h_upd, h_eq⟩ := h
  rw [h_upd, h_eq]; simp only [Assignment.update_at]

/-- Every output entry of `dynIntroduce` has its current situation drawn
from `gen` applied to some input situation. -/
theorem dynIntroduce_current_in_gen {W Time : Type*}
    (gen : WorldTimeIndex W Time → Set (WorldTimeIndex W Time))
    (v : SVar) (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynIntroduce gen v c) :
    ∃ s, (∃ g, (g, s) ∈ c) ∧ gs.2 ∈ gen s := by
  unfold dynIntroduce at h
  obtain ⟨g, s, s', hc, h_gen, _, h_eq⟩ := h
  exact ⟨s, ⟨g, hc⟩, h_eq ▸ h_gen⟩

end Semantics.Dynamic.Core
