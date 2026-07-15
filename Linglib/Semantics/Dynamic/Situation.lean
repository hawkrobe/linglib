import Linglib.Core.Logic.Assignment
import Linglib.Semantics.Dynamic.ContextChange
import Linglib.Semantics.Intensional.WorldTimeIndex

/-!
# Situation contexts

`SitContext` is the carrier of situation-variable dynamic semantics: sets
of pairs of a situation-variable assignment and a current evaluation
situation. Its two update primitives split along the
eliminative-vs-generative dichotomy of [groenendijk-stokhof-veltman-1996]
(`IsEliminative`, `ContextChange.lean`):

* `dynRelationOn` / `dynRelation` — eliminative filters by a relation
  between two projections; the workhorse behind temporal trichotomy
  (`<`/`=`/`>` on `.time`, used by `Tense.dynPAST`/`dynPRES`/`dynFUT`) and
  mood retrieval (`Mood.dynIND`).
* `dynIntroduce` — generative introduction of a fresh situation dref from
  a Kleisli arrow (`Mood.dynSUBJ`).
-/

namespace DynamicSemantics

open _root_.Core (Assignment)
open _root_.Intensional (WorldTimeIndex)

/--
An entry of a situation-variable context: a pair `(g, s)` where
`g : Nat → WorldTimeIndex W Time` is a Tarski-style assignment of situation
variables (the shared `Core.Assignment` substrate) and `s` is the current
evaluation situation. Unlike [mendes-2025]'s assignments, which also carry
individual and propositional drefs, entries hold only the situation
component — situation-variable semantics is independent of the
individual-dref machinery.
-/
abbrev SitEntry (W Time : Type*) :=
  Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time

/--
A situation-variable dynamic context: a set of `SitEntry`s.

Kept as `abbrev` so it inherits `Set α`'s `Membership`,
`EmptyCollection`, `HasSubset`, `Union`, `Inter`, and `Singleton`
instances directly.
-/
abbrev SitContext (W Time : Type*) := Set (SitEntry W Time)

/--
A situation variable (names a situation dref).

Kept as an `abbrev` so it inherits `DecidableEq`/`Repr`/`Hashable`/numeric
literals from `Nat`. Situation drefs are introduced by `Mood.dynSUBJ` and
retrieved by `Mood.dynIND` and the `Tense.dynPAST`/`dynPRES`/`dynFUT`
constraints (see `Semantics/{Tense,Mood}/Dynamic.lean`).
-/
abbrev SVar := Nat

variable {W Time : Type*} (proj₁ proj₂ : SitEntry W Time → WorldTimeIndex W Time)
  (R : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)

/--
Filter a context by a binary relation between two projections of each entry.

The general eliminative-update primitive: every entry survives iff `R`
holds between the two projected `WorldTimeIndex` values. The two
common specializations are:

- `dynRelation` (both projections look up bound variables `gs.1 v₁`,
  `gs.1 v₂`) — used by `Tense.dynPAST`/`dynPRES`/`dynFUT`.
- `Mood.dynIND` (one projection is the entry's current
  situation `gs.2`, the other is a bound variable `gs.1 v`).

Mathlib precedent: `Set.image2` over `Set.image`.
-/
def dynRelationOn (c : SitContext W Time) : SitContext W Time :=
  { gs ∈ c | R (proj₁ gs) (proj₂ gs) }

theorem dynRelationOn_isEliminative :
    IsEliminative (P := SitEntry W Time) (dynRelationOn proj₁ proj₂ R) :=
  fun _ _ h => h.1

/-- Idempotence of any `dynRelationOn` filter. -/
theorem dynRelationOn_idempotent (c : SitContext W Time) :
    dynRelationOn proj₁ proj₂ R (dynRelationOn proj₁ proj₂ R c) =
      dynRelationOn proj₁ proj₂ R c :=
  Set.ext fun _ => ⟨fun ⟨⟨hc, _⟩, hR⟩ => ⟨hc, hR⟩, fun ⟨hc, hR⟩ => ⟨⟨hc, hR⟩, hR⟩⟩

/-- Two contradictory `dynRelationOn` filters compose to the empty context. -/
theorem dynRelationOn_contradictory
    (R₁ R₂ : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    (h : ∀ s₁ s₂, R₁ s₁ s₂ → R₂ s₁ s₂ → False) (c : SitContext W Time) :
    dynRelationOn proj₁ proj₂ R₁ (dynRelationOn proj₁ proj₂ R₂ c) = ∅ :=
  Set.ext fun _ => ⟨fun ⟨⟨_, hR₂⟩, hR₁⟩ => h _ _ hR₁ hR₂, False.elim⟩

/--
Filter a context by a binary relation on two situation-variable lookups.

The "two bound variables" specialization of `dynRelationOn`. All temporal
constraints (`Tense.dynPAST`, `dynPRES`, `dynFUT`) are instances
of `dynRelation` with the appropriate ordering on `.time`.
-/
def dynRelation (v₁ v₂ : SVar) (c : SitContext W Time) : SitContext W Time :=
  dynRelationOn (fun gs => gs.1 v₁) (fun gs => gs.1 v₂) R c

/-- Contradictory relation filters compose to the empty context. -/
theorem dynRelation_contradictory
    (R₁ R₂ : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    (h : ∀ s₁ s₂, R₁ s₁ s₂ → R₂ s₁ s₂ → False)
    (v₁ v₂ : SVar) (c : SitContext W Time) :
    dynRelation R₁ v₁ v₂ (dynRelation R₂ v₁ v₂ c) = ∅ :=
  dynRelationOn_contradictory _ _ R₁ R₂ h c

/-- Transitive relations chain across three situation variables. -/
theorem dynRelation_transitive
    (R₁ R₂ R₃ : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    (hTrans : ∀ a b c, R₁ a b → R₂ b c → R₃ a c)
    (v₁ v₂ v₃ : SVar) (c : SitContext W Time) (gs : SitEntry W Time)
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
theorem dynRelation_trichotomy {α : Type*} [LinearOrder α]
    (f : WorldTimeIndex W Time → α) (v₁ v₂ : SVar) (c : SitContext W Time) :
    dynRelation (fun s₁ s₂ => f s₁ < f s₂) v₁ v₂ c ∪
    dynRelation (fun s₁ s₂ => f s₁ = f s₂) v₁ v₂ c ∪
    dynRelation (fun s₁ s₂ => f s₁ > f s₂) v₁ v₂ c = c := by
  apply Set.ext; intro gs
  unfold dynRelation dynRelationOn
  constructor
  · rintro ((⟨hc, _⟩ | ⟨hc, _⟩) | ⟨hc, _⟩) <;> exact hc
  · intro hc
    rcases lt_trichotomy (f (gs.1 v₁)) (f (gs.1 v₂)) with h | h | h
    · exact Or.inl (Or.inl ⟨hc, h⟩)
    · exact Or.inl (Or.inr ⟨hc, h⟩)
    · exact Or.inr ⟨hc, h⟩

/-! ### Generative updates: Kleisli composition for the powerset monad

The eliminative-vs-generative dichotomy from [groenendijk-stokhof-veltman-1996]
is exactly the `Set.filter` vs `Set.bind` dichotomy of the powerset monad.
`dynRelationOn`/`dynRelation` cover the eliminative side
(`f c ⊆ c`); `dynIntroduce` covers the generative side: it produces
fresh entries by binding a situation variable to alternatives drawn from
a Kleisli arrow `gen : WorldTimeIndex → Set WorldTimeIndex`.

This is the canonical primitive behind `Mood.dynSUBJ` (with
`gen = historicalBase history`) and any other operator that introduces
a fresh situation dref.
-/

/--
Generative update: for each entry `(g, s)`, replace it by
`{ (g[v ↦ s'], s') | s' ∈ gen s }`.

The current situation is updated to the new dref, and the assignment
is extended at `v`. Definitionally a `Set.bind`/Kleisli composition
for the powerset monad.

Unlike `dynRelationOn`/`dynRelation`, this is *not* eliminative
— it can produce entries that did not appear in the input context.
-/
def dynIntroduce (gen : WorldTimeIndex W Time → Set (WorldTimeIndex W Time))
    (v : SVar) (c : SitContext W Time) : SitContext W Time :=
  { gs' |
    ∃ g s s',
      (g, s) ∈ c ∧
      s' ∈ gen s ∧
      gs'.1 = Function.update g v s' ∧
      gs'.2 = s' }

/-- After `dynIntroduce gen v`, looking up `v` in the assignment always
returns the new current situation. This is the structural property that
makes a same-variable filter (e.g. `dynIND v ∘ dynIntroduce gen v`) vacuous. -/
theorem dynIntroduce_binds_current
    (gen : WorldTimeIndex W Time → Set (WorldTimeIndex W Time))
    (v : SVar) (c : SitContext W Time) (gs : SitEntry W Time)
    (h : gs ∈ dynIntroduce gen v c) :
    gs.1 v = gs.2 := by
  unfold dynIntroduce at h
  obtain ⟨g, _, s', _, _, h_upd, h_eq⟩ := h
  rw [h_upd, h_eq, Function.update_self]

/-- Every output entry of `dynIntroduce` has its current situation drawn
from `gen` applied to some input situation. -/
theorem dynIntroduce_current_in_gen
    (gen : WorldTimeIndex W Time → Set (WorldTimeIndex W Time))
    (v : SVar) (c : SitContext W Time) (gs : SitEntry W Time)
    (h : gs ∈ dynIntroduce gen v c) :
    ∃ s, (∃ g, (g, s) ∈ c) ∧ gs.2 ∈ gen s := by
  unfold dynIntroduce at h
  obtain ⟨g, s, s', hc, h_gen, _, h_eq⟩ := h
  exact ⟨s, ⟨g, hc⟩, h_eq ▸ h_gen⟩

end DynamicSemantics
