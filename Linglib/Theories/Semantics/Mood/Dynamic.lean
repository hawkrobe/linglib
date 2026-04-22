import Linglib.Theories.Semantics.Dynamic.Core.ContextFilter
import Linglib.Core.Modality.HistoricalAlternatives
import Linglib.Theories.Semantics.Mood.Basic

/-!
# Dynamic Mood Operators on Situation Variables

`dynSUBJ` and `dynIND` are the dynamic counterparts of the static
`Mood.SUBJ` and `Mood.IND` operators in `Mood/Basic.lean`:

- `dynSUBJ` introduces a fresh situation dref via historical
  alternatives and binds it to a situation variable. It is *not* a
  context filter — it adds new entries.
- `dynIND` retrieves a situation dref via a same-world check, and
  *is* a context filter (`dynIND_isFilter`).

The bridge theorems prove the correspondence with the static
operators: `dynSUBJ_realizes_SUBJ` gives an iff with the static
existential, `dynIND_realizes_IND` gives an iff with the static
presuppositional check, and `dynIND_after_dynSUBJ_same_var` formalises
the principle that indicative retrieval after subjunctive introduction
on the *same* variable is vacuous.

Sibling of `Mood/Basic.lean`. Used by
`Phenomena/TenseAspect/Studies/Mendes2025.lean`.
-/

namespace Semantics.Mood

open _root_.Core (Assignment WorldTimeIndex)
open Core.Modality.HistoricalAlternatives
open Semantics.Dynamic.Core


/--
Dynamic SUBJ: Introduces a situation dref.

⟦SUBJ^v_{s₀}⟧ = λc. { (g[v↦s₁], s₁) | (g, s₀) ∈ c, s₁ ∈ hist(s₀) }

The subjunctive:
1. Takes an input context with current situation s₀
2. Introduces a NEW situation s₁ from the historical alternatives
3. Binds s₁ to situation variable v
4. Updates the context to use s₁ as the new current situation

See `Mood.SUBJ` in `Mood/Basic.lean` for the static counterpart.
-/
def dynSUBJ {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (c : SitContext W Time) : SitContext W Time :=
  { gs' |
    ∃ g s₀ s₁,
      (g, s₀) ∈ c ∧
      s₁ ∈ historicalBase history s₀ ∧
      gs'.1 = g.update v s₁ ∧
      gs'.2 = s₁ }

/--
Dynamic IND: Retrieves a situation dref.

⟦IND_v⟧ = λc. { (g, s) | (g, s) ∈ c, s.world = g(v).world }

The indicative:
1. Retrieves the situation from variable v
2. Requires the current situation to be in the same world
3. Passes through (presuppositional)

See `Mood.IND` in `Mood/Basic.lean` for the static counterpart.
-/
def dynIND {W Time : Type*}
    (v : SVar)
    (c : SitContext W Time) : SitContext W Time :=
  { gs ∈ c | gs.2.world = (gs.1 v).world }

theorem dynIND_isFilter {W Time : Type*} (v : SVar) :
    IsContextFilter (α := Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
      (dynIND v) :=
  fun _ _ h => h.1


-- ════════════════════════════════════════════════════════════════
-- Summaries: SUBJ existential, IND same-world
-- ════════════════════════════════════════════════════════════════

/-- SUBJ is existential over historical base. -/
theorem dynSUBJ_existential {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynSUBJ history v c) :
    ∃ s₀, (∃ g₀, (g₀, s₀) ∈ c) ∧ gs.2 ∈ historicalBase history s₀ := by
  unfold dynSUBJ at h
  obtain ⟨g, s₀, s₁, hc, h_hist, _, h_eq⟩ := h
  use s₀
  constructor
  · exact ⟨g, hc⟩
  · rw [h_eq]; exact h_hist

/-- IND is presuppositional (same-world check). -/
theorem dynIND_same_world {W Time : Type*}
    (v : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynIND v c) :
    gs.2.world = (gs.1 v).world := by
  unfold dynIND at h
  exact h.2


-- ════════════════════════════════════════════════════════════════
-- Bridge theorems: dynamic operators realize static operators
-- ════════════════════════════════════════════════════════════════

/-!
## Static↔Dynamic Bridge

The dynamic operators `dynSUBJ` and `dynIND` are the context-level lifts of
the static operators `Mood.SUBJ` and `Mood.IND` (defined in
`Mood/Basic.lean`).

These bridge theorems prove the correspondence:
- `dynSUBJ` implements `SUBJ`'s existential quantification over historical
  alternatives, with additional bookkeeping (binding the result to a variable
  and updating the current situation).
- `dynIND` implements `IND`'s same-world presuppositional check as a
  context filter.
-/

/--
Full set characterization of `dynSUBJ` on singleton contexts.

Strictly stronger than `dynSUBJ_realizes_SUBJ`: gives the exact output set
rather than just an existential iff. The output of `dynSUBJ` on `{(g, s₀)}`
is precisely the set of `(g[v↦s₁], s₁)` for `s₁ ∈ historicalBase history s₀`.
-/
theorem dynSUBJ_singleton_eq {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (g : Assignment (WorldTimeIndex W Time))
    (s₀ : WorldTimeIndex W Time) :
    dynSUBJ history v ({(g, s₀)} : SitContext W Time) =
    { gs | ∃ s₁ ∈ historicalBase history s₀, gs = (g.update v s₁, s₁) } := by
  apply Set.ext; intro gs
  unfold dynSUBJ
  constructor
  · rintro ⟨g', s₀', s₁, h_ctx, h_hist, h_upd, h_eq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.mp h_ctx)
    exact ⟨s₁, h_hist, Prod.ext h_upd h_eq⟩
  · rintro ⟨s₁, h_hist, h_eq⟩
    rw [h_eq]
    exact ⟨g, s₀, s₁, rfl, h_hist, rfl, rfl⟩

/--
Bridge: dynamic SUBJ realizes static SUBJ.

For a singleton context `{(g, s₀)}`, the set of situations reachable via
`dynSUBJ` at variable `v` that satisfy `P` is exactly the set that static
`SUBJ` existentially quantifies over.
-/
theorem dynSUBJ_realizes_SUBJ {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (g : Assignment (WorldTimeIndex W Time))
    (s₀ : WorldTimeIndex W Time)
    (P : SitPred W Time) :
    (∃ gs ∈ dynSUBJ history v ({(g, s₀)} : SitContext W Time),
      P (gs.1 v) s₀) ↔
    SUBJ history P s₀ := by
  unfold SUBJ dynSUBJ
  constructor
  · rintro ⟨gs, ⟨g', s₀', s₁, h_ctx, h_hist, h_upd, h_eq⟩, h_P⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.mp h_ctx)
    have h_sit : gs.1 v = s₁ := by
      rw [h_upd]; simp only [Assignment.update_at]
    exact ⟨s₁, h_hist, h_sit ▸ h_P⟩
  · rintro ⟨s₁, h_hist, h_P⟩
    refine ⟨(g.update v s₁, s₁), ?_, ?_⟩
    · exact ⟨g, s₀, s₁, rfl, h_hist, rfl, rfl⟩
    · simp only [Assignment.update_at]; exact h_P

/--
`dynSUBJ` invariant: variable `v` always equals the current situation.

After `dynSUBJ` binds `v`, looking up `v` in the assignment always
returns the current situation. This is the structural property that
makes `dynIND` vacuous on the same variable (see
`dynIND_after_dynSUBJ_same_var`).
-/
theorem dynSUBJ_binds_current {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynSUBJ history v c) :
    gs.1 v = gs.2 := by
  unfold dynSUBJ at h
  obtain ⟨g, s₀, s₁, _, _, h_upd, h_eq⟩ := h
  rw [h_upd, h_eq]; simp only [Assignment.update_at]

/--
Bridge: dynamic IND realizes static IND.

The filter condition imposed by `dynIND` is exactly the same-world
constraint of static `Mood.IND`: membership in the filtered context
plus a predicate on the situations is equivalent to membership in the
original context plus the static IND applied to those situations.
-/
theorem dynIND_realizes_IND {W Time : Type*}
    (v : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (P : SitPred W Time) :
    (gs ∈ dynIND v c ∧ P gs.2 (gs.1 v)) ↔
    (gs ∈ c ∧ IND P (gs.1 v) gs.2) := by
  unfold dynIND IND
  constructor
  · rintro ⟨⟨hc, hw⟩, hP⟩
    exact ⟨hc, hw, hP⟩
  · rintro ⟨hc, hw, hP⟩
    exact ⟨⟨hc, hw⟩, hP⟩

/--
IND is identity after SUBJ on the same variable.

When SUBJ introduces s₁ and binds it to `v`, IND's same-world check
on `v` is trivially satisfied (`gs.2 = s₁ = gs.1 v` by construction).
This explains why `crossClausalBinding` with shared variables
preserves the full SUBJ output.
-/
theorem dynIND_after_dynSUBJ_same_var {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (c : SitContext W Time) :
    dynIND v (dynSUBJ history v c) = dynSUBJ history v c := by
  apply Set.ext; intro gs
  unfold dynIND
  constructor
  · exact fun ⟨h_mem, _⟩ => h_mem
  · intro h_mem
    exact ⟨h_mem, by rw [dynSUBJ_binds_current history v c gs h_mem]⟩

end Semantics.Mood
