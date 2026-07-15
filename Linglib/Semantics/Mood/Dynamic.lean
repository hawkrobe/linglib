/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Dynamic.Update
import Linglib.Semantics.Intensional.WorldTimeIndex
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Semantics.Mood.Situation
import Linglib.Semantics.Mood.Defs

/-!
# Dynamic mood operators

This file defines the dynamic counterparts of the static mood
operators of `Mood/Situation.lean`: `dynIND` and `dynSUBJ` are the
two basic operations of the powerset monad on contexts of world-time
possibilities — a filter and a Kleisli bind. This
eliminative/generative contrast is the classical two-sorted update
repertoire of dynamic semantics ([groenendijk-stokhof-veltman-1996]),
and `Grammatical.dynOp` assigns an operator to each grammatical mood,
so the polarity of a mood is a theorem about the assignment rather
than a stipulated feature.

Contexts are level-0 states over `WorldTimeIndex.Possibility` — the
world coordinate is the current evaluation index, drefs are indices.
`dynIND` is the spine's `lift (test ·)`; `dynIntroduce` (the
generative primitive behind `dynSUBJ`) is this file's genuine delta: a
*world-shifting* introduction that extends the assignment at a fresh
dref *and* moves the evaluation index to the introduced situation.

## Main statements

* `dynSUBJ_realizes_SUBJ`: on singleton contexts, `dynSUBJ` realizes
  the static existential `SUBJ` of [mendes-2025].
* `dynOp_indicative_isEliminative`, `dynOp_subjunctive_introduces`: the
  polarity contrast, derived from the `dynOp` assignment.
* `dynIND_after_dynSUBJ_same_var`: indicative retrieval of a
  just-introduced subjunctive variable is vacuous.

## References

* [heim-1982]: file change semantics — intersection for conditions,
  file-card creation for indefinites.
* [veltman-1996]: the eliminative test `[φ]σ = {w ∈ σ : w ⊨ φ}`.
* [groenendijk-stokhof-veltman-1996]: eliminative tests and
  generative introductions for discourse referents.
* [charlow-2021], [de-groote-2006]: the monadic and
  continuation-style renderings; here `dynIND` is `Set.filter`
  and `dynIntroduce` is `Set.bind`.
-/

namespace Mood

open Intensional (WorldTimeIndex)
open HistoricalAlternatives DynamicSemantics

variable {W Time : Type*}

/-- The generative update behind `dynSUBJ`: for each entry with
assignment `g` and current index `s`, produce the entries
`⟨s', Function.update g v s'⟩` for every `s' ∈ gen s` — extend the
assignment at `v` *and* move the evaluation index to the introduced
situation. Unlike a test filter, this is *not* eliminative: it can
produce entries that did not appear in the input context. -/
def dynIntroduce (gen : WorldTimeIndex W Time → Set (WorldTimeIndex W Time))
    (v : ℕ) (c : Set (WorldTimeIndex.Possibility W Time)) :
    Set (WorldTimeIndex.Possibility W Time) :=
  { p' |
    ∃ g s s',
      (⟨s, g⟩ : WorldTimeIndex.Possibility W Time) ∈ c ∧
      s' ∈ gen s ∧
      p'.assignment = Function.update g v s' ∧
      p'.world = s' }

/-- After `dynIntroduce gen v`, looking up `v` in the assignment always
returns the new current index — the structural property that makes a
same-variable filter (`dynIND v ∘ dynIntroduce gen v`) vacuous. -/
theorem dynIntroduce_binds_current
    (gen : WorldTimeIndex W Time → Set (WorldTimeIndex W Time))
    {v : ℕ} {c : Set (WorldTimeIndex.Possibility W Time)}
    {p : WorldTimeIndex.Possibility W Time}
    (h : p ∈ dynIntroduce gen v c) :
    p.assignment v = p.world := by
  obtain ⟨g, _, s', _, _, h_upd, h_eq⟩ := h
  rw [h_upd, h_eq, Function.update_self]

/-- Every output entry of `dynIntroduce` has its current index drawn
from `gen` applied to some input index. -/
theorem dynIntroduce_current_in_gen
    (gen : WorldTimeIndex W Time → Set (WorldTimeIndex W Time))
    {v : ℕ} {c : Set (WorldTimeIndex.Possibility W Time)}
    {p : WorldTimeIndex.Possibility W Time}
    (h : p ∈ dynIntroduce gen v c) :
    ∃ s, (∃ g, (⟨s, g⟩ : WorldTimeIndex.Possibility W Time) ∈ c) ∧
      p.world ∈ gen s := by
  obtain ⟨g, s, s', hc, h_gen, _, h_eq⟩ := h
  exact ⟨s, ⟨g, hc⟩, h_eq ▸ h_gen⟩

/-- Dynamic IND: the eliminative update filtering entries whose current
index shares its world with the situation bound to `v` — the spine's
test filter at `sameWorld`. -/
def dynIND (v : ℕ) : Set (WorldTimeIndex.Possibility W Time) →
    Set (WorldTimeIndex.Possibility W Time) :=
  lift (test fun p => sameWorld p.world (p.assignment v))

/-! ### The eliminative side -/

/-- `dynIND` is a context filter. -/
theorem dynIND_isEliminative (v : ℕ) :
    IsEliminative (dynIND (W := W) (Time := Time) v) :=
  lift_test_isEliminative _

/-- Surviving `dynIND` means the current and bound situations share a
world. -/
theorem dynIND_same_world {v : ℕ}
    {c : Set (WorldTimeIndex.Possibility W Time)}
    {p : WorldTimeIndex.Possibility W Time} (h : p ∈ dynIND v c) :
    p.world.world = (p.assignment v).world :=
  (mem_lift_test.mp h).2

/-- `dynIND` is idempotent. -/
theorem dynIND_idempotent (v : ℕ)
    (c : Set (WorldTimeIndex.Possibility W Time)) :
    dynIND v (dynIND v c) = dynIND v c :=
  lift_test_idem _ c

section Subjunctive

variable [LE Time] (history : HistoricalAlternatives W Time) (v : ℕ)
  (c : Set (WorldTimeIndex.Possibility W Time))
  (p : WorldTimeIndex.Possibility W Time)

/-- Dynamic SUBJ: the generative update sending each entry to its
extensions at every historically accessible situation. -/
def dynSUBJ : Set (WorldTimeIndex.Possibility W Time) →
    Set (WorldTimeIndex.Possibility W Time) :=
  dynIntroduce (historicalBase history) v

/-! ### The generative side -/

/-- Every `dynSUBJ` output situation is drawn from the historical base
of some input situation. -/
theorem dynSUBJ_existential (h : p ∈ dynSUBJ history v c) :
    ∃ s₀, (∃ g₀, (⟨s₀, g₀⟩ : WorldTimeIndex.Possibility W Time) ∈ c) ∧
      p.world ∈ historicalBase history s₀ :=
  dynIntroduce_current_in_gen _ h

/-- After `dynSUBJ`, looking up `v` returns the current situation. -/
theorem dynSUBJ_binds_current (h : p ∈ dynSUBJ history v c) :
    p.assignment v = p.world :=
  dynIntroduce_binds_current _ h

/-! ### Static ↔ dynamic bridge -/

/-- The exact output of `dynSUBJ` on a singleton context:
`⟨s₁, g[v↦s₁]⟩` for each `s₁` in the historical base of `s₀`. -/
theorem dynSUBJ_singleton_eq (g : ℕ → WorldTimeIndex W Time)
    (s₀ : WorldTimeIndex W Time) :
    dynSUBJ history v
      ({⟨s₀, g⟩} : Set (WorldTimeIndex.Possibility W Time)) =
    { p | ∃ s₁ ∈ historicalBase history s₀,
        p = ⟨s₁, Function.update g v s₁⟩ } := by
  apply Set.ext; intro p
  unfold dynSUBJ dynIntroduce
  constructor
  · rintro ⟨g', s₀', s₁, h_ctx, h_hist, h_upd, h_eq⟩
    have h₁ := Set.mem_singleton_iff.mp h_ctx
    obtain ⟨rfl, rfl⟩ : s₀' = s₀ ∧ g' = g :=
      ⟨congrArg Possibility.world h₁, congrArg Possibility.assignment h₁⟩
    exact ⟨s₁, h_hist, Possibility.ext h_eq h_upd⟩
  · rintro ⟨s₁, h_hist, rfl⟩
    exact ⟨g, s₀, s₁, rfl, h_hist, rfl, rfl⟩

/-- `dynSUBJ` realizes the static `SUBJ`: on a singleton context, some
output satisfies `P` at the bound variable iff `SUBJ` holds. -/
theorem dynSUBJ_realizes_SUBJ (g : ℕ → WorldTimeIndex W Time)
    (s₀ : WorldTimeIndex W Time) (P : SitPred W Time) :
    (∃ p ∈ dynSUBJ history v
        ({⟨s₀, g⟩} : Set (WorldTimeIndex.Possibility W Time)),
      P (p.assignment v) s₀) ↔
    SUBJ history P s₀ := by
  rw [dynSUBJ_singleton_eq]
  unfold SUBJ
  constructor
  · rintro ⟨p, ⟨s₁, h_hist, rfl⟩, h_P⟩
    refine ⟨s₁, h_hist, ?_⟩
    simpa [Function.update_self] using h_P
  · rintro ⟨s₁, h_hist, h_P⟩
    exact ⟨⟨s₁, Function.update g v s₁⟩, ⟨s₁, h_hist, rfl⟩,
      by simpa [Function.update_self] using h_P⟩

/-- Indicative retrieval of a just-introduced subjunctive variable is
vacuous: the filter's projections are forced equal by `dynSUBJ`. -/
theorem dynIND_after_dynSUBJ_same_var :
    dynIND v (dynSUBJ history v c) = dynSUBJ history v c := by
  apply Set.ext; intro p
  unfold dynIND
  rw [mem_lift_test]
  refine ⟨fun ⟨h_mem, _⟩ => h_mem, fun h_mem => ⟨h_mem, ?_⟩⟩
  show sameWorld p.world (p.assignment v)
  rw [dynSUBJ_binds_current history v c p h_mem]

/-! ### Mood as update polarity -/

/-- The dynamic operator each grammatical mood denotes: indicative the
eliminative `dynIND`, subjunctive the generative `dynSUBJ`. -/
def Grammatical.dynOp :
    Grammatical → ℕ → Set (WorldTimeIndex.Possibility W Time) →
      Set (WorldTimeIndex.Possibility W Time)
  | .indicative  => dynIND
  | .subjunctive => dynSUBJ history

/-- Indicative's dynamic operator is eliminative: a context filter. -/
theorem dynOp_indicative_isEliminative :
    IsEliminative (Grammatical.indicative.dynOp history v) :=
  dynIND_isEliminative v

/-- Subjunctive's dynamic operator is generative: every output entry
carries a freshly introduced situation, bound to `v`. -/
theorem dynOp_subjunctive_introduces
    (h : p ∈ Grammatical.subjunctive.dynOp history v c) :
    p.assignment v = p.world ∧
      ∃ s₀, (∃ g₀, (⟨s₀, g₀⟩ : WorldTimeIndex.Possibility W Time) ∈ c) ∧
        p.world ∈ historicalBase history s₀ :=
  ⟨dynSUBJ_binds_current history v c p h,
   dynSUBJ_existential history v c p h⟩

end Subjunctive

end Mood
