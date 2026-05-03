import Linglib.Core.Question.Basic
import Linglib.Core.Logic.Team.Properties
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.SupClosed

/-!
# Flatness of Question — Anttila Proposition 2.2.16 specialised to inquisitive content

@cite{anttila-2021} @cite{ciardelli-groenendijk-roelofsen-2018}
@cite{aloni-2022}

Anttila 2021 Proposition 2.2.16 (specialised from Proposition 2.2.2): a
team-semantic predicate is *flat* iff it is downward-closed, union-closed,
and contains the empty team. This file specialises that fact to
`Question W` — the bundled inquisitive-semantics propositional content
type — and discovers an exact correspondence:

  inquisitive `isDeclarative`  ↔  team-semantic `flat` (under `teamSupport`)

since `Question`'s structural axioms `contains_empty` and `downward_closed`
already provide two of the three Anttila properties; declarativity is
exactly what supplies the third (union closure).

## What the file proves

For any `Question W`, with `teamSupport` lifting `(s : Finset W) ↦ ↑s ∈ P.props`:

- `teamSupport_downwardClosed` and `teamSupport_emptyTeam` are immediate
  re-statements of `P.downward_closed` and `P.contains_empty`.
- `isDeclarative_iff_sUnion_closed` characterises declarativity via
  arbitrary-union closure on `Set W` (the natural carrier for `Question`).
- `IsBinaryUnionClosed` is the binary form, directly comparable to
  `Core.Logic.Team.unionClosed` at the `Finset` carrier; the two coincide
  via finite induction.
- Capstone: `teamSupport_flat_of_isDeclarative` derives Anttila's
  `flat` predicate for declarative `Question`s by composing the three
  closure properties through `flat_of_downwardClosed_unionClosed_emptyTeam`.

## Why this is one fact, not two

Inquisitive semantics (Ciardelli-Groenendijk-Roelofsen) and team-semantic
modal logic (Aloni / Anttila) developed independently. "Flatness" (in
Anttila 2.2.16) and "declarativity" (in CGR 2018) were named in different
literatures for the same structural property. This file makes that
identification explicit.

## Carrier note

The substrate's `Core.Logic.Team.unionClosed` is stated over the `Finset W`
carrier (binary union); `Question`'s natural form is `Set W` (arbitrary
union via `⋃₀`). For finite `W` the two coincide via induction; for
infinite `W` arbitrary union is the principled form because binary union
doesn't suffice to recover `info P = ⋃₀ P.props`. A future
carrier-polymorphic substrate would let us state this with a single shared
predicate.
-/

namespace Core.Question

variable {W : Type*}

-- ============================================================================
-- §1 Question's bundled axioms ARE the team substrate's downward + empty
--    (instantiated at the natural Finset→Set membership predicate)
-- ============================================================================

/-- The natural team-semantic predicate of a `Question`: a `Finset W` team
    is "supported" iff its underlying `Set` is in `P.props`. Carrier-bridge
    between the substrate's `Finset W` and `Question`'s `Set W`.

    The `Unit → Unit →` shape matches `Core.Logic.Team.downwardClosed`'s
    `Model → Form →` signature with both pinned to `Unit`; `Question` is
    its own self-contained "model + formula." -/
def teamSupport (P : Question W) : Unit → Unit → Finset W → Prop :=
  fun _ _ s => (↑s : Set W) ∈ P.props

/-- **Substrate fact**: every `Question`'s `teamSupport` is downward-closed
    in `Core.Logic.Team.downwardClosed`'s sense. The proof IS just
    `P.downward_closed` lifted through `Finset.coe_subset`. -/
theorem teamSupport_downwardClosed (P : Question W) :
    Core.Logic.Team.downwardClosed (teamSupport P) () := by
  intro _ a b hab hb
  -- IsLowerSet shape: b ≤ a → support a → support b. For Finset, b ≤ a is b ⊆ a.
  exact P.downward_closed _ hb _ (Finset.coe_subset.mpr hab)

/-- **Substrate fact**: every `Question`'s `teamSupport` has the empty-team
    property. The proof IS `P.contains_empty` (modulo `Finset.coe_empty`). -/
theorem teamSupport_emptyTeam (P : Question W) :
    Core.Logic.Team.emptyTeam (teamSupport P) () := by
  intro _
  show (↑(∅ : Finset W) : Set W) ∈ P.props
  rw [Finset.coe_empty]
  exact P.contains_empty

-- ============================================================================
-- §2 The bridge theorem: declarative ↔ union-closed
-- ============================================================================

/-- A `Question W` is **declarative** iff its `props` is closed under
    arbitrary unions. This is the bridge between two traditions:
    - **Anttila/Aloni**: the third Anttila Definition 2.2.1 property is
      union closure; combined with downward closure and empty-team it
      characterises *flat* contents (Anttila Proposition 2.2.2).
    - **Ciardelli-Groenendijk-Roelofsen**: a content is *declarative*
      iff `info P ∈ P.props`, i.e., the union of its resolving states
      is itself a resolving state.

    The two predicates are the same. Every `Question` automatically
    satisfies the first two Anttila properties (by its bundled axioms);
    declarativity is exactly when it also satisfies the third. -/
theorem isDeclarative_iff_sUnion_closed (P : Question W) :
    P.isDeclarative ↔ ∀ S ⊆ P.props, ⋃₀ S ∈ P.props := by
  constructor
  · intro hdecl S hSsub
    -- `⋃₀ S ⊆ ⋃₀ P.props = info P`, so by downward closure, `⋃₀ S ∈ props`.
    have hsub : ⋃₀ S ⊆ P.info := by
      intro w ⟨s, hsS, hws⟩
      exact ⟨s, hSsub hsS, hws⟩
    exact P.downward_closed P.info hdecl (⋃₀ S) hsub
  · intro huc
    -- Take `S = P.props`; closure gives `⋃₀ P.props = info P ∈ P.props`.
    show P.info ∈ P.props
    exact huc P.props (subset_refl _)

/-- Restated using `info`: a `Question` is declarative iff every union of
    resolving states is itself a resolving state. Specialisation of
    `isDeclarative_iff_sUnion_closed` that emphasises the `info`
    decomposition. -/
theorem isDeclarative_iff_info_in_props (P : Question W) :
    P.isDeclarative ↔ P.info ∈ P.props := Iff.rfl

-- ============================================================================
-- §3 Binary form (carrier-comparable to `Core.Logic.Team.unionClosed`)
-- ============================================================================

/-- A `Question`'s `props` is **binary-union-closed** iff for any two
    resolving states their union is also resolving. This is the binary
    form, directly comparable to `Core.Logic.Team.unionClosed`'s shape
    (which is binary at the `Finset` carrier). -/
def IsBinaryUnionClosed (P : Question W) : Prop :=
  ∀ s t : Set W, s ∈ P.props → t ∈ P.props → s ∪ t ∈ P.props

/-- Declarative implies binary-union-closed: the union of two states
    each contained in `info P` is contained in `info P`, hence in `props`
    by downward closure. -/
theorem isDeclarative_imp_binary_union_closed (P : Question W)
    (hdecl : P.isDeclarative) : IsBinaryUnionClosed P := by
  intro s t hs ht
  have hs_info : s ⊆ P.info := fun w hw => ⟨s, hs, hw⟩
  have ht_info : t ⊆ P.info := fun w hw => ⟨t, ht, hw⟩
  have hunion : s ∪ t ⊆ P.info := Set.union_subset hs_info ht_info
  exact P.downward_closed P.info hdecl _ hunion

/-- For `Question`s with finite `props`, binary-union-closed implies
    declarative. Proof goes via `isDeclarative_iff_sUnion_closed` plus
    `Set.Finite.induction_on` to lift binary closure to arbitrary union. -/
theorem isDeclarative_of_binary_union_closed_of_finite_props
    (P : Question W) (hfin : P.props.Finite)
    (huc : IsBinaryUnionClosed P) : P.isDeclarative := by
  rw [isDeclarative_iff_sUnion_closed]
  intro S hSsub
  have hSfin : S.Finite := hfin.subset hSsub
  -- Generalise the subset hypothesis so the induction can re-extract it
  -- after each insert.
  induction S, hSfin using Set.Finite.induction_on with
  | empty =>
    rw [Set.sUnion_empty]
    exact P.contains_empty
  | @insert p T hpnT _ ih =>
    rw [Set.sUnion_insert]
    have hp_props : p ∈ P.props := hSsub (Set.mem_insert p T)
    have hT_sub : T ⊆ P.props := fun x hx => hSsub (Set.mem_insert_of_mem _ hx)
    exact huc p (⋃₀ T) hp_props (ih hT_sub)

-- ============================================================================
-- §4 Capstone: declarative Question is `flat` in the substrate's sense
-- ============================================================================

/-- Declarative `Question` `teamSupport` is binary-union-closed in the
    `Core.Logic.Team.unionClosed` sense (i.e., over `Finset W` with `s ∪ t`). -/
theorem teamSupport_unionClosed_of_isDeclarative [DecidableEq W] (P : Question W)
    (hdecl : P.isDeclarative) :
    Core.Logic.Team.unionClosed (teamSupport P) () := by
  -- SupClosed shape: ∀ ⦃a⦄, a ∈ T → ∀ ⦃b⦄, b ∈ T → a ⊔ b ∈ T (a ⊔ b = a ∪ b on Finset)
  intro _ a ha b hb
  show (↑(a ∪ b) : Set W) ∈ P.props
  rw [Finset.coe_union]
  exact isDeclarative_imp_binary_union_closed P hdecl _ _ ha hb

/-- **Capstone bridge** (Anttila Proposition 2.2.16 instantiated for
    inquisitive content): a declarative `Question` is *flat* in the
    `Core.Logic.Team.flat` sense. The substrate's flatness theorem
    `flat_of_downwardClosed_unionClosed_emptyTeam` applies because every
    `Question` already provides downward closure and the empty-team
    property by its bundled axioms; declarativity adds the missing union
    closure.

    This is the substrate-unity claim made concrete: the inquisitive
    `isDeclarative` predicate and the team-semantic `flat` predicate are
    the same property under the natural carrier-bridge. Two communities,
    one fact. -/
theorem teamSupport_flat_of_isDeclarative [DecidableEq W] (P : Question W)
    (hdecl : P.isDeclarative) :
    Core.Logic.Team.flat (teamSupport P) () :=
  Core.Logic.Team.flat_of_downwardClosed_unionClosed_emptyTeam
    (teamSupport_downwardClosed P)
    (teamSupport_unionClosed_of_isDeclarative P hdecl)
    (teamSupport_emptyTeam P)

-- ============================================================================
-- §5 Mathlib-aligned restatements: Question's structure IS IsLowerSet + bot
-- ============================================================================

/-- **Question's `downward_closed` axiom IS `IsLowerSet`** at the `Set W`
    carrier. The mathlib primitive `IsLowerSet (s : Set α) [LE α]` says
    `b ≤ a → a ∈ s → b ∈ s`; for `Set W` the `LE` instance is `⊆`, so this
    is exactly `Question.downward_closed`. -/
theorem isLowerSet_props (P : Question W) : IsLowerSet P.props :=
  fun _ _ hba ha => P.downward_closed _ ha _ hba

/-- **Mathlib-aligned binary union closure** for declarative `Question`s:
    `SupClosed P.props` (mathlib's binary-`⊔` closure on `Set α`, where
    `⊔ = ∪`). Direct corollary of `isDeclarative_imp_binary_union_closed`
    rewrapped in mathlib's predicate. -/
theorem supClosed_props_of_isDeclarative (P : Question W)
    (hdecl : P.isDeclarative) : SupClosed P.props :=
  fun s hs t ht => isDeclarative_imp_binary_union_closed P hdecl s t hs ht

/-- **Question's `contains_empty` IS `⊥ ∈ P.props`**. For `Set W`, `⊥ = ∅`. -/
theorem bot_mem_props (P : Question W) : (⊥ : Set W) ∈ P.props :=
  P.contains_empty

end Core.Question
