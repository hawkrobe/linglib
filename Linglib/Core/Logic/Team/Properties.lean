import Linglib.Core.Logic.Team.Closure

/-!
# Team-semantic properties of formulas (Anttila 2021 §2.2) — consumer wrapper

@cite{anttila-2021}

The four canonical properties of formulas in a team-semantic logic, from
Anttila Definition 2.2.1, exposed in **parametric form** for consumer
ergonomics:

- **Downward closure**: support survives subset
- **Union closure**: support survives binary union
- **Empty team property**: support holds vacuously on the empty team
- **Flatness**: support equivalent to pointwise support at each point in the team

Each predicate here takes `(support : Model → Form → Finset W → Prop) (φ : Form)`
and asserts the closure property of `support M φ` for every model `M`. This is
the shape consumers (BSML, QBSML, ...) actually invoke.

## Relationship to `Core/Logic/Team/Closure.lean`

The deep mathematical content is in `Core/Logic/Team/Closure.lean`: the
flatness theorem is a fact about subsets of `Finset α` (mathlib `IsLowerSet`,
`SupClosed`, plus `∅ ∈ T`). The `Form / Model` parameters here are
**ergonomic wrappers** — they curry the substrate fact across formulas and
models. The theorem `flat_iff_downwardClosed_unionClosed_emptyTeam` reduces
to `Closure.isTeamFlat_iff_isLowerSet_supClosed_empty` instantiated at
`{ t | support M φ t }` for every `M`.

## Provenance

Anttila axiomatizes six team-semantic logics (PT⁺, MDᵂ, SMLᵂ, SGMLᵂ, BSML,
BSMLᵂ) using this chassis. Anttila Proposition 2.2.8 (NE-free formulas have
downward + empty; ⨼-free formulas are union closed) becomes a per-logic theorem
proved against this substrate; the corollary "NE-free + ⨼-free → flat" follows
from `flat_iff_downwardClosed_unionClosed_emptyTeam` below — which itself
delegates to `Closure.lean`'s lattice-level statement.

## Naming: "team" vs "state"

Anttila §2.2 calls the property "the empty *state* property" and similar.
We use "team" (Hodges 1997, Väänänen 2007) — the foundational umbrella term
that generalizes uniformly across BSML (team = set of worlds), QBSML (team =
set of (world, assignment) indices), dependence logic (team = set of
assignments), etc. The two terms are interchangeable in this layer.
-/

namespace Core.Logic.Team

variable {W : Type*} [DecidableEq W]
variable {Form : Type*}
variable {Model : Type*}

-- ============================================================================
-- §1 The four team-semantic properties (Anttila Definition 2.2.1)
-- ============================================================================

/-- Downward closure: support is preserved under taking subsets of the team.
    Anttila Definition 2.2.1.

    NE-bearing formulas typically lack this (Anttila Proposition 2.2.8). -/
def downwardClosed (support : Model → Form → Finset W → Prop) (φ : Form) : Prop :=
  ∀ (M : Model) (s t : Finset W), t ⊆ s → support M φ s → support M φ t

/-- Union closure (binary form): support is preserved under binary union.

    Anttila Definition 2.2.1 uses the n-ary form `∀ S ≠ ∅, (∀s ∈ S, support M φ s)
    → support M φ (⋃S)`. Binary closure + the empty team property give the
    n-ary form by induction (see `unionClosed_finset` below).

    The global / inquisitive disjunction ⨼ in Anttila's BSMLᵂ is the source
    of union-closure failure (Anttila Proposition 2.2.8 part 2). BSML proper
    (without ⨼) has all formulas union-closed. -/
def unionClosed (support : Model → Form → Finset W → Prop) (φ : Form) : Prop :=
  ∀ (M : Model) (s t : Finset W), support M φ s → support M φ t → support M φ (s ∪ t)

/-- Empty team property: φ is supported on ∅ in every model.

    Most formulas have this. The exception is NE (Anttila Definition 2.1.5):
    `M, s ⊨ NE` iff `s ≠ ∅`, so NE fails on ∅. -/
def emptyTeam (support : Model → Form → Finset W → Prop) (φ : Form) : Prop :=
  ∀ (M : Model), support M φ ∅

/-- Flatness: team-support equals pointwise support at each point in the team.

    Anttila Definition 2.2.1 (note: the thesis writes "for all w ∈ W" but
    proves and uses "for all w ∈ s" — see Proposition 2.2.2 proof). The
    standard team-semantic notion (Yang & Väänänen 2017) is "for all w ∈ s",
    which is what we use here.

    Flat formulas reduce to classical modal logic on singleton teams
    (Anttila Proposition 2.2.16). -/
def flat (support : Model → Form → Finset W → Prop) (φ : Form) : Prop :=
  ∀ (M : Model) (s : Finset W), support M φ s ↔ ∀ w ∈ s, support M φ {w}

-- ============================================================================
-- §2 Anttila Proposition 2.2.2: flatness ↔ downward + union + empty
-- ============================================================================

/-- **Anttila Proposition 2.2.2** (parametric form): A formula has the
    flatness property iff it has downward closure, union closure, and the
    empty team property.

    Delegates to the substrate-level statement
    `Closure.isTeamFlat_iff_isLowerSet_supClosed_empty` instantiated at
    `{ t | support M φ t }` for each model. The deep content — flatness
    iff `IsLowerSet ∧ SupClosed ∧ ∅ ∈ T` for any team-set — is proved
    once at the lattice level; this theorem just curries it across all
    `(M, φ)`.

    Conservative-extension theorems (Anttila 2.2.13/2.2.15) follow from
    this + per-logic NE-free witnesses for the three properties. -/
theorem flat_iff_downwardClosed_unionClosed_emptyTeam
    (support : Model → Form → Finset W → Prop) (φ : Form) :
    flat support φ ↔
      downwardClosed support φ ∧ unionClosed support φ ∧ emptyTeam support φ := by
  constructor
  · intro hFlat
    refine ⟨?_, ?_, ?_⟩
    · intro M
      have h := (isTeamFlat_iff_isLowerSet_supClosed_empty
        (T := { t : Finset W | support M φ t })).mp (fun s => hFlat M s)
      intro s t hsub
      exact h.1 hsub
    · intro M s t hs ht
      have h := (isTeamFlat_iff_isLowerSet_supClosed_empty
        (T := { t : Finset W | support M φ t })).mp (fun s => hFlat M s)
      exact h.2.1 hs ht
    · intro M
      have h := (isTeamFlat_iff_isLowerSet_supClosed_empty
        (T := { t : Finset W | support M φ t })).mp (fun s => hFlat M s)
      exact h.2.2
  · rintro ⟨hd, hu, he⟩ M s
    have h_lower : IsLowerSet { t : Finset W | support M φ t } :=
      fun a b hba ha => hd M a b hba ha
    have h_sup : SupClosed { t : Finset W | support M φ t } :=
      fun a ha b hb => hu M a b ha hb
    have h_empty : ∅ ∈ { t : Finset W | support M φ t } := he M
    exact (isTeamFlat_iff_isLowerSet_supClosed_empty
      (T := { t : Finset W | support M φ t })).mpr ⟨h_lower, h_sup, h_empty⟩ s

-- ============================================================================
-- §3 Convenience corollaries
-- ============================================================================

/-- If φ is flat, then it is downward-closed. -/
theorem downwardClosed_of_flat
    {support : Model → Form → Finset W → Prop} {φ : Form}
    (h : flat support φ) : downwardClosed support φ :=
  ((flat_iff_downwardClosed_unionClosed_emptyTeam support φ).mp h).1

/-- If φ is flat, then it is union-closed. -/
theorem unionClosed_of_flat
    {support : Model → Form → Finset W → Prop} {φ : Form}
    (h : flat support φ) : unionClosed support φ :=
  ((flat_iff_downwardClosed_unionClosed_emptyTeam support φ).mp h).2.1

/-- If φ is flat, then it satisfies the empty team property. -/
theorem emptyTeam_of_flat
    {support : Model → Form → Finset W → Prop} {φ : Form}
    (h : flat support φ) : emptyTeam support φ :=
  ((flat_iff_downwardClosed_unionClosed_emptyTeam support φ).mp h).2.2

/-- Constructive form of Anttila 2.2.2: combine the three properties to get
    flatness. -/
theorem flat_of_downwardClosed_unionClosed_emptyTeam
    {support : Model → Form → Finset W → Prop} {φ : Form}
    (hd : downwardClosed support φ) (hu : unionClosed support φ)
    (he : emptyTeam support φ) : flat support φ :=
  (flat_iff_downwardClosed_unionClosed_emptyTeam support φ).mpr ⟨hd, hu, he⟩

-- ============================================================================
-- §4 N-ary union closure (derived from binary + empty)
-- ============================================================================

/-- N-ary union closure, derived from binary union closure + empty team property.
    Matches Anttila Definition 2.2.1's original n-ary statement. -/
theorem unionClosed_finset
    {support : Model → Form → Finset W → Prop} {φ : Form}
    (hu : unionClosed support φ) (he : emptyTeam support φ)
    (M : Model) (S : Finset (Finset W))
    (h : ∀ s ∈ S, support M φ s) :
    support M φ (S.sup id) := by
  induction S using Finset.induction_on with
  | empty => simp; exact he M
  | @insert s T hs ih =>
    have hs_supp : support M φ s := h s (Finset.mem_insert_self s T)
    have hT_supp : support M φ (T.sup id) := by
      apply ih
      intro t ht
      exact h t (Finset.mem_insert_of_mem ht)
    rw [Finset.sup_insert]
    exact hu M s (T.sup id) hs_supp hT_supp

end Core.Logic.Team
