import Linglib.Semantics.Questions.Basic
import Linglib.Core.Logic.Team.Closure
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.SupClosed

/-!
# Flatness of Question — Anttila 2.2.16 specialised to inquisitive content

@cite{anttila-2021} @cite{ciardelli-groenendijk-roelofsen-2018}
@cite{aloni-2022}

Anttila Proposition 2.2.16 (specialised from Proposition 2.2.2): a
team-semantic predicate is *flat* iff it is downward-closed, sup-closed,
and contains the empty team. This file specialises that fact to
`Question W` — the bundled inquisitive-semantics propositional content
type — and discovers an exact correspondence:

  inquisitive `isDeclarative`  ↔  team-semantic flatness (under `teamSupport`)

since `Question`'s structural axioms `contains_empty` and `downward_closed`
already provide two of the three Anttila properties; declarativity is
exactly what supplies the third (union closure).

## Main declarations

* `isLowerSet_props` — `Question.downward_closed` IS `IsLowerSet P.props`.
* `bot_mem_props` — `Question.contains_empty` IS `⊥ ∈ P.props`.
* `isDeclarative_iff_sUnion_closed` — declarativity ↔ closure under
  arbitrary unions on `P.props`.
* `supClosed_props_of_isDeclarative` — declarative `Question`s have
  mathlib-`SupClosed` (binary) `P.props`.
* `teamSupport` — natural carrier-bridge from `Set W` (Question's native
  carrier) to `Finset W` (team-semantic substrate's carrier).
* `isFlat_teamSupport_of_isDeclarative` — the capstone: declarative
  `Question`s are *flat* in `Core.Logic.Team.IsFlat`'s sense.

## Why this is one fact, not two

Inquisitive semantics (Ciardelli-Groenendijk-Roelofsen) and team-semantic
modal logic (Aloni / Anttila) developed independently. "Flatness" (Anttila
2.2.16) and "declarativity" (CGR 2018) were named in different literatures
for the same structural property. This file makes that identification
explicit through the carrier-bridge.

## Carrier note

`Question`'s natural carrier is `Set W` (arbitrary unions via `⋃₀`); the
team-semantic substrate's carrier is `Finset W` (binary unions). For
finite `W` the two coincide; for infinite `W` arbitrary union is the
principled form because binary union doesn't suffice to recover
`info P = ⋃₀ P.props`. Mathlib's `IsLowerSet` and `SupClosed` are already
polymorphic in their carrier; `IsFlat` is `Finset α`-specific by design.
The `teamSupport` bridge is how a `Set W`-carried `Question` instantiates
the `Finset W`-carried `IsFlat`.
-/

namespace Question

variable {W : Type*}

/-! ### Question's bundled axioms ARE `IsLowerSet` + `⊥ ∈ ·` on `Set W` -/

/-- **`Question.downward_closed` IS `IsLowerSet`** at the `Set W` carrier.
    For `Set W` the `LE` instance is `⊆`, so this matches mathlib's
    `IsLowerSet (s : Set α) [LE α]`. -/
theorem isLowerSet_props (P : Question W) : IsLowerSet P.props :=
  fun _ _ hba ha => P.downward_closed _ ha _ hba

/-- **`Question.contains_empty` IS `⊥ ∈ P.props`**. For `Set W`, `⊥ = ∅`. -/
theorem bot_mem_props (P : Question W) : (⊥ : Set W) ∈ P.props :=
  P.contains_empty

/-! ### Declarativity ↔ arbitrary union closure -/

/-- A `Question W` is **declarative** iff its `props` is closed under
    arbitrary unions. The bridge between two traditions:
    - **Anttila/Aloni**: the third Anttila Definition 2.2.1 property is
      union closure; combined with downward closure and empty-team it
      characterises *flat* contents (Anttila Proposition 2.2.2).
    - **Ciardelli-Groenendijk-Roelofsen**: a content is *declarative*
      iff `info P ∈ P.props`, i.e., the union of its resolving states
      is itself a resolving state.

    The two predicates are the same. Every `Question` automatically
    satisfies the first two Anttila properties; declarativity is exactly
    when it also satisfies the third. -/
theorem isDeclarative_iff_sUnion_closed (P : Question W) :
    P.isDeclarative ↔ ∀ S ⊆ P.props, ⋃₀ S ∈ P.props := by
  constructor
  · intro hdecl S hSsub
    have hsub : ⋃₀ S ⊆ P.info := by
      intro w ⟨s, hsS, hws⟩
      exact ⟨s, hSsub hsS, hws⟩
    exact P.downward_closed P.info hdecl (⋃₀ S) hsub
  · intro huc
    show P.info ∈ P.props
    exact huc P.props (subset_refl _)

/-- Restated using `info`: a `Question` is declarative iff every union of
    resolving states is itself a resolving state. -/
theorem isDeclarative_iff_info_in_props (P : Question W) :
    P.isDeclarative ↔ P.info ∈ P.props := Iff.rfl

/-- Declarativity gives mathlib's `SupClosed` (binary closure under `⊔ = ∪`)
    on `P.props`. Direct corollary of arbitrary-union closure via
    `isDeclarative_iff_sUnion_closed` applied to the binary case. -/
theorem supClosed_props_of_isDeclarative (P : Question W)
    (hdecl : P.isDeclarative) : SupClosed P.props := by
  intro s hs t ht
  have hs_info : s ⊆ P.info := fun w hw => ⟨s, hs, hw⟩
  have ht_info : t ⊆ P.info := fun w hw => ⟨t, ht, hw⟩
  have hunion : s ∪ t ⊆ P.info := Set.union_subset hs_info ht_info
  exact P.downward_closed P.info hdecl _ hunion

/-! ### Bridge to `Finset W` carrier and the flatness capstone -/

/-- The natural team-semantic predicate of a `Question`: a `Finset W` team
    is "supported" iff its underlying `Set W` is in `P.props`.
    Carrier-bridge between `Question`'s `Set W` and the team-semantic
    substrate's `Finset W`. -/
def teamSupport (P : Question W) (s : Finset W) : Prop :=
  (↑s : Set W) ∈ P.props

theorem isLowerSet_teamSupport [DecidableEq W] (P : Question W) :
    IsLowerSet { s : Finset W | teamSupport P s } :=
  fun _ _ hab hb => P.downward_closed _ hb _ (Finset.coe_subset.mpr hab)

theorem teamSupport_empty (P : Question W) :
    teamSupport P (∅ : Finset W) := by
  show (↑(∅ : Finset W) : Set W) ∈ P.props
  rw [Finset.coe_empty]
  exact P.contains_empty

theorem supClosed_teamSupport_of_isDeclarative [DecidableEq W] (P : Question W)
    (hdecl : P.isDeclarative) :
    SupClosed { s : Finset W | teamSupport P s } := by
  intro a ha b hb
  show (↑(a ∪ b) : Set W) ∈ P.props
  rw [Finset.coe_union]
  exact supClosed_props_of_isDeclarative P hdecl ha hb

/-- **Capstone bridge** (Anttila Proposition 2.2.16 instantiated for
    inquisitive content): a declarative `Question` is flat in the
    `Core.Logic.Team.IsFlat` sense at the `teamSupport` carrier-bridge.

    The substrate-unity claim made concrete: the inquisitive
    `isDeclarative` predicate and the team-semantic `IsFlat` predicate
    are the same property under the natural carrier-bridge. Two
    communities, one fact. -/
theorem isFlat_teamSupport_of_isDeclarative [DecidableEq W] (P : Question W)
    (hdecl : P.isDeclarative) :
    Core.Logic.Team.IsFlat { s : Finset W | teamSupport P s } :=
  Core.Logic.Team.isFlat_of_isLowerSet_supClosed_empty
    (isLowerSet_teamSupport P)
    (supClosed_teamSupport_of_isDeclarative P hdecl)
    (teamSupport_empty P)

end Question
