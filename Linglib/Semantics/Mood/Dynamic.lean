import Linglib.Semantics.Dynamic.Core.ContextFilter
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Semantics.Mood.Situation
import Linglib.Semantics.Mood.Defs

/-!
# Dynamic Mood as Eliminative + Generative Updates of Static Mood
[veltman-1996] [groenendijk-stokhof-veltman-1996] [heim-1982]
[de-groote-2006] [charlow-2021] [mendes-2025]

`dynIND` and `dynSUBJ` are the dynamic-context-update counterparts of
the static `Mood.IND` and `Mood.SUBJ` operators in `Mood/Situation.lean`.
Together they instantiate the two basic operations of the powerset
monad on situation contexts:

- `dynIND` is *eliminative* (an `IsContextFilter`): it specializes
  the generic `dynRelationOn` filter to the `sameWorld` kernel,
  with one projection picking the entry's current situation
  (`gs.2`) and the other picking a bound variable (`gs.1 v`).
- `dynSUBJ` is *generative* (it adds entries): it specializes the
  generic `dynIntroduce` Kleisli composition to the `historicalBase`
  generator, binding the freshly drawn situation to a variable.

## Theoretical anchor

The eliminative-vs-generative split is the canonical algebraic shape
of dynamic semantics:

- [heim-1982] principle (A) — file change for a static condition
  is intersection with the satisfaction set (eliminative); for an
  indefinite, file card creation extends the file (generative).
- [veltman-1996] formalizes the eliminative side as the *test*
  operator `[φ]σ = {w ∈ σ : w ⊨ φ}`.
- [groenendijk-stokhof-veltman-1996] ("Coreference and
  Modality") split context updates into eliminative tests and
  generative introductions for discourse referents. `dynIND` is the
  eliminative arm; `dynSUBJ` is the generative arm.
- [de-groote-2006] CPS translation: the static predicate is the
  pure computation, the dynamic operator is the contextual lift.
- [charlow-2021] casts dynamic semantics as a monadic effect over
  static semantics; here the underlying monad is the powerset monad
  on situation contexts. `dynRelationOn` is `Set.filter`; `dynIntroduce`
  is `Set.bind` (Kleisli composition).

`Semantics.Mood.IND` and `Semantics.Mood.SUBJ` (defined in
`Mood/Situation.lean`) call the same two kernels (`sameWorld` and
`historicalBase`) directly. The static and dynamic faces share *one
modal constraint and one alternative-generator*, lifted from a
state-level predicate to a context-level operation.

## What this file proves

Two rfl-bridges (`dynIND_eq_dynRelationOn_sameWorld`,
`dynSUBJ_eq_dynIntroduce_historicalBase`) establish that the dynamic
operators *definitionally* call the generic primitives on the shared
kernels.

`dynIND_iff_IND_with_true` is the "wrapper actually wraps" check on
the eliminative side: an entry survives the dynamic filter iff the
static `IND` (with the trivial propositional payload) holds at the
entry's current and bound situations.

`dynSUBJ_realizes_SUBJ` does the same on the generative side, for
singleton contexts. `dynIND_after_dynSUBJ_same_var` records that
indicative retrieval of the just-introduced subjunctive variable is
vacuous — the algebraic fact that a `dynRelationOn` filter is
trivially satisfied after the projections it compares are forced
equal by the preceding `dynIntroduce`.

Sibling of `Mood/Situation.lean` and `Tense/Dynamic.lean`. Used by
`Studies/Mendes2025.lean` (which hosts the SF
operator and the modal donkey anaphora chain that consumes
`dynSUBJ`/`dynIND`).
-/

namespace Semantics.Mood

open _root_.Core (Assignment)
open _root_.Intensional (WorldTimeIndex)
open HistoricalAlternatives
open Semantics.Dynamic.Core


/--
Dynamic IND: lifts the `sameWorld` kernel to an eliminative update on
situation contexts.

A context entry survives iff its current situation `gs.2` shares its
world with the bound situation `gs.1 v`. The "current vs bound"
projection asymmetry is exactly the case that motivates
`dynRelationOn` over `dynRelation`.
-/
def dynIND {W Time : Type*}
    (v : SVar) : SitContext W Time → SitContext W Time :=
  dynRelationOn (fun gs => gs.2) (fun gs => gs.1 v)
    (sameWorld (W := W) (Time := Time))

/--
Dynamic SUBJ: lifts the `historicalBase history` generator to a
generative update on situation contexts.

For each entry `(g, s₀)`, the output contains `(g[v ↦ s₁], s₁)` for
every `s₁ ∈ historicalBase history s₀`. The current situation is
updated to the freshly drawn `s₁`, and `v` is bound to it.
-/
def dynSUBJ {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    (v : SVar) : SitContext W Time → SitContext W Time :=
  dynIntroduce (historicalBase history) v


-- ════════════════════════════════════════════════════════════════
-- § Definitional bridges: dynamic operators ARE the generic primitives
-- ════════════════════════════════════════════════════════════════

theorem dynIND_eq_dynRelationOn_sameWorld {W Time : Type*}
    (v : SVar) (c : SitContext W Time) :
    dynIND v c =
      dynRelationOn (fun gs => gs.2) (fun gs => gs.1 v) sameWorld c := rfl

theorem dynSUBJ_eq_dynIntroduce_historicalBase {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time) (v : SVar) (c : SitContext W Time) :
    dynSUBJ history v c =
      dynIntroduce (historicalBase history) v c := rfl


-- ════════════════════════════════════════════════════════════════
-- § Filter property and immediate consequences for `dynIND`
-- ════════════════════════════════════════════════════════════════

theorem dynIND_isFilter {W Time : Type*} (v : SVar) :
    IsContextFilter (α := Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
      (dynIND v) :=
  dynRelationOn_isFilter _ _ _

/-- IND is presuppositional (same-world check). -/
theorem dynIND_same_world {W Time : Type*}
    (v : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynIND v c) :
    gs.2.world = (gs.1 v).world := h.2

/-- Idempotence inherited from the generic `dynRelationOn` algebra. -/
theorem dynIND_idempotent {W Time : Type*}
    (v : SVar) (c : SitContext W Time) :
    dynIND v (dynIND v c) = dynIND v c :=
  dynRelationOn_idempotent _ _ _ c


-- ════════════════════════════════════════════════════════════════
-- § Immediate consequences for `dynSUBJ`
-- ════════════════════════════════════════════════════════════════

/-- SUBJ is existential over the historical base. Inherited from
`dynIntroduce_current_in_gen`. -/
theorem dynSUBJ_existential {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    (v : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynSUBJ history v c) :
    ∃ s₀, (∃ g₀, (g₀, s₀) ∈ c) ∧ gs.2 ∈ historicalBase history s₀ :=
  dynIntroduce_current_in_gen _ _ _ _ h

/-- After `dynSUBJ`, looking up `v` always returns the current
situation. Inherited from `dynIntroduce_binds_current`. -/
theorem dynSUBJ_binds_current {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    (v : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynSUBJ history v c) :
    gs.1 v = gs.2 :=
  dynIntroduce_binds_current _ _ _ _ h


-- ════════════════════════════════════════════════════════════════
-- § Static realization: dynamic IS the eliminative/generative lift
-- ════════════════════════════════════════════════════════════════

/-!
For each operator, the static version (with the trivial propositional
payload `fun _ _ => True`) holds at the relevant situation pair iff
the dynamic operator's update retains/produces the corresponding
context entry. This makes precise the [de-groote-2006] sense in
which static and dynamic mood are the same operator at different
layers.
-/

/-- `dynIND` realizes static `IND` with the trivial propositional
payload — the "wrapper actually wraps" check on the eliminative side. -/
theorem dynIND_iff_IND_with_true {W Time : Type*}
    (v : SVar) (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time) :
    gs ∈ dynIND v c ↔ gs ∈ c ∧ IND (fun _ _ => True) (gs.1 v) gs.2 :=
  ⟨fun h => ⟨h.1, h.2, trivial⟩, fun ⟨hc, hp, _⟩ => ⟨hc, hp⟩⟩


/-!
## Static↔Dynamic Bridge for SUBJ

`dynSUBJ` implements `SUBJ`'s existential quantification over historical
alternatives, with additional bookkeeping (binding the result to a
variable and updating the current situation).
-/

/--
Full set characterization of `dynSUBJ` on singleton contexts.

Strictly stronger than `dynSUBJ_realizes_SUBJ`: gives the exact output
set rather than just an existential iff. The output of `dynSUBJ` on
`{(g, s₀)}` is precisely the set of `(g[v↦s₁], s₁)` for
`s₁ ∈ historicalBase history s₀`.
-/
theorem dynSUBJ_singleton_eq {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    (v : SVar)
    (g : Assignment (WorldTimeIndex W Time))
    (s₀ : WorldTimeIndex W Time) :
    dynSUBJ history v ({(g, s₀)} : SitContext W Time) =
    { gs | ∃ s₁ ∈ historicalBase history s₀, gs = (Function.update g v s₁, s₁) } := by
  apply Set.ext; intro gs
  unfold dynSUBJ dynIntroduce
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
    (history : HistoricalAlternatives W Time)
    (v : SVar)
    (g : Assignment (WorldTimeIndex W Time))
    (s₀ : WorldTimeIndex W Time)
    (P : SitPred W Time) :
    (∃ gs ∈ dynSUBJ history v ({(g, s₀)} : SitContext W Time),
      P (gs.1 v) s₀) ↔
    SUBJ history P s₀ := by
  unfold SUBJ dynSUBJ dynIntroduce
  constructor
  · rintro ⟨gs, ⟨g', s₀', s₁, h_ctx, h_hist, h_upd, h_eq⟩, h_P⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.mp h_ctx)
    have h_sit : gs.1 v = s₁ := by
      rw [h_upd]; simp only [Function.update_self]
    exact ⟨s₁, h_hist, h_sit ▸ h_P⟩
  · rintro ⟨s₁, h_hist, h_P⟩
    refine ⟨(Function.update g v s₁, s₁), ?_, ?_⟩
    · exact ⟨g, s₀, s₁, rfl, h_hist, rfl, rfl⟩
    · simp only [Function.update_self]; exact h_P

/-!
### Mood as update polarity, by assignment

`Grammatical.dynOp` assigns each grammatical mood its dynamic
operator. The eliminative/generative contrast — indicative *tests*
(a context filter), subjunctive *introduces* (a fresh dref) — is then
a pair of theorems about the assignment, not a stipulated feature:
this replaces the former `Effect.introducesSituation` table. -/

/-- The dynamic operator each grammatical mood denotes: indicative the
    eliminative `dynIND`, subjunctive the generative `dynSUBJ`. The
    assignment is the theory's sole stipulation; its polarity facts
    (`dynOp_indicative_isFilter`, `dynOp_subjunctive_introduces`)
    follow. -/
def Grammatical.dynOp {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time) :
    Grammatical → SVar → SitContext W Time → SitContext W Time
  | .indicative  => dynIND
  | .subjunctive => dynSUBJ history

/-- Indicative's dynamic operator is eliminative: a context filter.
    Half of the polarity contrast formerly stipulated as
    `introducesSituation := false`. -/
theorem dynOp_indicative_isFilter {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time) (v : SVar) :
    IsContextFilter (α := Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
      (Grammatical.indicative.dynOp history v) :=
  dynIND_isFilter v

/-- Subjunctive's dynamic operator is generative: every output entry
    carries a freshly introduced situation from the historical base,
    bound to `v`. Half of the polarity contrast formerly stipulated as
    `introducesSituation := true`. -/
theorem dynOp_subjunctive_introduces {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time) (v : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ Grammatical.subjunctive.dynOp history v c) :
    gs.1 v = gs.2 ∧ ∃ s₀, (∃ g₀, (g₀, s₀) ∈ c) ∧ gs.2 ∈ historicalBase history s₀ :=
  ⟨dynSUBJ_binds_current history v c gs h, dynSUBJ_existential history v c gs h⟩

/--
IND is identity after SUBJ on the same variable.

When SUBJ introduces `s₁` and binds it to `v`, IND's same-world check
on `v` is trivially satisfied — `gs.2 = s₁ = gs.1 v` by
`dynSUBJ_binds_current`. This explains why `crossClausalBinding` with
shared variables preserves the full SUBJ output.
-/
theorem dynIND_after_dynSUBJ_same_var {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    (v : SVar)
    (c : SitContext W Time) :
    dynIND v (dynSUBJ history v c) = dynSUBJ history v c := by
  apply Set.ext; intro gs
  refine ⟨fun ⟨h_mem, _⟩ => h_mem, fun h_mem => ⟨h_mem, ?_⟩⟩
  show sameWorld gs.2 (gs.1 v)
  rw [dynSUBJ_binds_current history v c gs h_mem]

end Semantics.Mood
