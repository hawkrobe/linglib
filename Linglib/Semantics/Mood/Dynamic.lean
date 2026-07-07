import Linglib.Semantics.Dynamic.Core.ContextFilter
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Semantics.Mood.Situation
import Linglib.Semantics.Mood.Defs

/-!
# Dynamic Mood Operators

`dynIND` and `dynSUBJ` are the dynamic counterparts of the static
`Mood.IND` and `Mood.SUBJ` of [mendes-2025] (`Mood/Situation.lean`),
instantiating the two basic operations of the powerset monad on
situation contexts: `dynIND` is *eliminative* — the `dynRelationOn`
filter on the `sameWorld` kernel, comparing the entry's current
situation with a bound variable — and `dynSUBJ` is *generative* — the
`dynIntroduce` Kleisli composition over the `historicalBase`
generator, binding the freshly drawn situation. The static and
dynamic faces call the same kernel and the same generator, lifted
from a state-level predicate to a context-level operation
(`dynSUBJ_realizes_SUBJ`).

The eliminative/generative split is the canonical algebraic shape of
dynamic semantics: [heim-1982]'s file change is intersection for a
static condition and file-card creation for an indefinite;
[veltman-1996] formalizes the eliminative side as the test
`[φ]σ = {w ∈ σ : w ⊨ φ}`; [groenendijk-stokhof-veltman-1996] split
context updates into eliminative tests and generative introductions
for discourse referents; [charlow-2021] casts both as monadic effects
— here `dynRelationOn` is `Set.filter` and `dynIntroduce` is
`Set.bind` — with [de-groote-2006]'s CPS translation as the
continuation-style rendering. `Grammatical.dynOp` assigns each
grammatical mood its operator, so the polarity contrast is a pair of
theorems about the assignment rather than a stipulated feature.
-/

namespace Mood

open _root_.Core (Assignment)
open _root_.Intensional (WorldTimeIndex)
open HistoricalAlternatives
open Semantics.Dynamic.Core

/-- Dynamic IND: the eliminative update filtering entries whose current
situation shares its world with the situation bound to `v`. -/
def dynIND {W Time : Type*}
    (v : SVar) : SitContext W Time → SitContext W Time :=
  dynRelationOn (fun gs => gs.2) (fun gs => gs.1 v)
    (sameWorld (W := W) (Time := Time))

/-- Dynamic SUBJ: the generative update sending each entry `(g, s₀)` to
`(g[v ↦ s₁], s₁)` for every `s₁ ∈ historicalBase history s₀`. -/
def dynSUBJ {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    (v : SVar) : SitContext W Time → SitContext W Time :=
  dynIntroduce (historicalBase history) v

/-! ### The eliminative side -/

/-- `dynIND` is a context filter. -/
theorem dynIND_isFilter {W Time : Type*} (v : SVar) :
    IsContextFilter (α := Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
      (dynIND v) :=
  dynRelationOn_isFilter _ _ _

/-- Surviving `dynIND` means the current and bound situations share a
world. -/
theorem dynIND_same_world {W Time : Type*}
    (v : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynIND v c) :
    gs.2.world = (gs.1 v).world := h.2

/-- `dynIND` is idempotent. -/
theorem dynIND_idempotent {W Time : Type*}
    (v : SVar) (c : SitContext W Time) :
    dynIND v (dynIND v c) = dynIND v c :=
  dynRelationOn_idempotent _ _ _ c

/-! ### The generative side -/

/-- Every `dynSUBJ` output situation is drawn from the historical base
of some input situation. -/
theorem dynSUBJ_existential {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    (v : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynSUBJ history v c) :
    ∃ s₀, (∃ g₀, (g₀, s₀) ∈ c) ∧ gs.2 ∈ historicalBase history s₀ :=
  dynIntroduce_current_in_gen _ _ _ _ h

/-- After `dynSUBJ`, looking up `v` returns the current situation. -/
theorem dynSUBJ_binds_current {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    (v : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynSUBJ history v c) :
    gs.1 v = gs.2 :=
  dynIntroduce_binds_current _ _ _ _ h

/-! ### Static ↔ dynamic bridge -/

/-- The exact output of `dynSUBJ` on a singleton context:
`(g[v↦s₁], s₁)` for each `s₁` in the historical base of `s₀`. -/
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

/-- `dynSUBJ` realizes the static `SUBJ`: on a singleton context, some
output satisfies `P` at the bound variable iff `SUBJ` holds. -/
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

/-- Indicative retrieval of a just-introduced subjunctive variable is
vacuous: the filter's projections are forced equal by `dynSUBJ`. -/
theorem dynIND_after_dynSUBJ_same_var {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    (v : SVar)
    (c : SitContext W Time) :
    dynIND v (dynSUBJ history v c) = dynSUBJ history v c := by
  apply Set.ext; intro gs
  refine ⟨fun ⟨h_mem, _⟩ => h_mem, fun h_mem => ⟨h_mem, ?_⟩⟩
  show sameWorld gs.2 (gs.1 v)
  rw [dynSUBJ_binds_current history v c gs h_mem]

/-! ### Mood as update polarity -/

/-- The dynamic operator each grammatical mood denotes: indicative the
eliminative `dynIND`, subjunctive the generative `dynSUBJ`. -/
def Grammatical.dynOp {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time) :
    Grammatical → SVar → SitContext W Time → SitContext W Time
  | .indicative  => dynIND
  | .subjunctive => dynSUBJ history

/-- Indicative's dynamic operator is eliminative: a context filter. -/
theorem dynOp_indicative_isFilter {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time) (v : SVar) :
    IsContextFilter (α := Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
      (Grammatical.indicative.dynOp history v) :=
  dynIND_isFilter v

/-- Subjunctive's dynamic operator is generative: every output entry
carries a freshly introduced situation, bound to `v`. -/
theorem dynOp_subjunctive_introduces {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time) (v : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ Grammatical.subjunctive.dynOp history v c) :
    gs.1 v = gs.2 ∧ ∃ s₀, (∃ g₀, (g₀, s₀) ∈ c) ∧ gs.2 ∈ historicalBase history s₀ :=
  ⟨dynSUBJ_binds_current history v c gs h, dynSUBJ_existential history v c gs h⟩

end Mood
