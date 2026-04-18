import Linglib.Core.Nominal.Description
import Linglib.Core.Nominal.Interpret
import Linglib.Core.Nominal.Maximality

/-!
# Hanink (2021): DP Structure and Internally Headed Relatives in Wášiw
@cite{hanink-2021}

The architectural claim of @cite{hanink-2021} (developing the framework
of Hanink 2018) is that the resource situation evaluating a definite
description's restrictor is a *bound variable* in the syntactic
structure — a "situation pronoun" — rather than a free contextual
parameter handed to the interpretation function. The resource
situation is selected by an index inside DP, not by the matrix
context, and that index can be bound by higher operators.

## What this file tests

The IL substrate operationalizes this in two parallel pieces:

- **`SitAssignment F := Nat → F.Index`** in `Core.IntensionalLogic.Variables`
  is the situation-pronoun assignment, parallel to the entity
  assignment.
- **`NominalKind.unique R sIdx`** in `Core.Nominal.Description`
  carries a `situationIdx : Nat` recording *which* situation pronoun
  the description is bound to.

The empirical payoff is that the *same* description can pick out
different referents under different situation assignments. We test
this with a two-room frame where "the table" picks out different
tables depending on which resource situation the structure is bound
to.

We additionally verify:

1. **Restrictor sensitivity to the situation assignment** — a
   restrictor that consults `interpSitPronoun` returns different
   extensions under different `gs`.
2. **Index-record discipline** — the surface interpretation function
   ignores the index (it just records *which* pronoun is bound, the
   `gs` does the work), but the `usesSituationPronoun` classifier
   correctly flags `unique` and `demonstrative` as the binders.
3. **Anaphoric vs. unique split** — anaphoric definites consult the
   *entity* assignment (the antecedent index), so the situation
   assignment is irrelevant for them. This contrasts with `unique`,
   matching the Schwarz weak/strong split.
-/

namespace Phenomena.Definiteness.Studies.Hanink2021

open Core.IntensionalLogic
open Core.IntensionalLogic.Variables
open Core.Nominal

-- ════════════════════════════════════════════════════════════════
-- §1: A two-room frame for the resource-situation diagnostic
-- ════════════════════════════════════════════════════════════════

/-- Two tables, one in each room. The "the table" diagnostic in
    @cite{hanink-2021}'s style: shifting the bound resource situation
    flips the referent. -/
inductive Item where
  | tableKitchen
  | tableLiving
  deriving DecidableEq, Repr

/-- Two rooms, each its own situation. -/
inductive Room where
  | kitchen
  | living
  deriving DecidableEq, Repr

def F : Frame := { Entity := Item, Index := Room }

/-- "Table-in-room": the predicate is true at exactly one item per room.
    Encodes the @cite{hanink-2021} resource-situation idea — what counts
    as "the table" depends on the situation we evaluate at. -/
def tableIn : Room → Item → Prop
  | .kitchen, .tableKitchen => True
  | .kitchen, _             => False
  | .living,  .tableLiving  => True
  | .living,  _             => False

/-- The restrictor *the table at the situation pointed to by pronoun 0*:
    a `DenotGS` that consults `interpSitPronoun 0` to fetch the resource
    situation, then evaluates `tableIn` at that situation.

    This is the @cite{hanink-2021} situation-pronoun pattern: the
    structural index `0` selects which situation in `gs` to use. -/
def tableAtSit0 : DenotGS F .et :=
  fun _g gs x => tableIn (interpSitPronoun 0 gs) x

-- ════════════════════════════════════════════════════════════════
-- §2: Bi-assignment scaffolding
-- ════════════════════════════════════════════════════════════════

/-- A trivial entity assignment. Entity binding is not exercised here. -/
def g₀ : Core.Assignment F.Entity := fun _ => Item.tableKitchen

/-- Situation assignment with pronoun 0 ↦ kitchen. -/
def gsKitchen : SitAssignment F := fun _ => Room.kitchen

/-- Situation assignment with pronoun 0 ↦ living. -/
def gsLiving : SitAssignment F := fun _ => Room.living

-- ════════════════════════════════════════════════════════════════
-- §3: The same description picks different referents (the payoff)
-- ════════════════════════════════════════════════════════════════

/-- Restrictor uniqueness in the kitchen situation: only `tableKitchen`
    satisfies `tableAtSit0`. -/
theorem tableAtSit0_existsUnique_kitchen :
    existsUnique (F := F) (fun x => tableAtSit0 g₀ gsKitchen x) := by
  refine ⟨⟨Item.tableKitchen, trivial⟩, ?_⟩
  intro x y hx hy
  cases x <;> cases y <;>
    simp_all [tableAtSit0, tableIn, interpSitPronoun, gsKitchen]

/-- Restrictor uniqueness in the living-room situation: only
    `tableLiving` satisfies `tableAtSit0`. -/
theorem tableAtSit0_existsUnique_living :
    existsUnique (F := F) (fun x => tableAtSit0 g₀ gsLiving x) := by
  refine ⟨⟨Item.tableLiving, trivial⟩, ?_⟩
  intro x y hx hy
  cases x <;> cases y <;>
    simp_all [tableAtSit0, tableIn, interpSitPronoun, gsLiving]

/-- Witness extraction for the kitchen case: the unique satisfier is
    `tableKitchen`. -/
theorem theTable_kitchen :
    interpret (F := F) (.unique tableAtSit0 0) g₀ gsKitchen
      = some Item.tableKitchen := by
  have hExists : (interpret (F := F) (.unique tableAtSit0 0) g₀ gsKitchen).isSome
      = true := by
    rw [interpret_unique]
    exact (russellIota_isSome_iff_existsUnique _).mpr
      tableAtSit0_existsUnique_kitchen
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hExists
  rw [he]
  congr 1
  have hSat : tableAtSit0 g₀ gsKitchen e := by
    have : russellIota (fun x => tableAtSit0 g₀ gsKitchen x) = some e := by
      rw [← interpret_unique]; exact he
    exact russellIota_witness_satisfies _ e this
  cases e <;>
    first
      | rfl
      | (simp [tableAtSit0, tableIn, interpSitPronoun, gsKitchen] at hSat)

/-- Witness extraction for the living-room case: the unique satisfier
    is `tableLiving`. -/
theorem theTable_living :
    interpret (F := F) (.unique tableAtSit0 0) g₀ gsLiving
      = some Item.tableLiving := by
  have hExists : (interpret (F := F) (.unique tableAtSit0 0) g₀ gsLiving).isSome
      = true := by
    rw [interpret_unique]
    exact (russellIota_isSome_iff_existsUnique _).mpr
      tableAtSit0_existsUnique_living
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hExists
  rw [he]
  congr 1
  have hSat : tableAtSit0 g₀ gsLiving e := by
    have : russellIota (fun x => tableAtSit0 g₀ gsLiving x) = some e := by
      rw [← interpret_unique]; exact he
    exact russellIota_witness_satisfies _ e this
  cases e <;>
    first
      | rfl
      | (simp [tableAtSit0, tableIn, interpSitPronoun, gsLiving] at hSat)

/-- The Hanink payoff: the *same* `.unique` description picks out
    different referents under different situation assignments. The
    description is one syntactic object; the resource situation is a
    bound variable, not a free parameter. -/
theorem same_description_different_referents :
    interpret (F := F) (.unique tableAtSit0 0) g₀ gsKitchen
      ≠ interpret (F := F) (.unique tableAtSit0 0) g₀ gsLiving := by
  rw [theTable_kitchen, theTable_living]
  intro h
  cases (Option.some_inj.mp h)

-- ════════════════════════════════════════════════════════════════
-- §4: Index-record discipline
-- ════════════════════════════════════════════════════════════════

/-- The index argument to `.unique` does not select among situations at
    the interpretation layer — the restrictor `R` already takes the full
    situation assignment, and the index records *which* pronoun is
    bound. (`Core.Nominal.interpret_unique_index_irrelevant` makes this
    explicit.) The Hanink claim is recovered via the restrictor calling
    `interpSitPronoun sIdx`, not via the interpreter inspecting `sIdx`. -/
theorem unique_index_does_not_alter_referent_directly :
    interpret (F := F) (.unique tableAtSit0 0) g₀ gsKitchen
      = interpret (F := F) (.unique tableAtSit0 7) g₀ gsKitchen :=
  interpret_unique_index_irrelevant _ _ _ _ _

/-- Among `NominalKind` constructors, exactly `unique` and
    `demonstrative` are flagged as binding a structural situation
    pronoun. Anaphoric definites do not — they consult the entity
    assignment for an antecedent, not the situation assignment. -/
theorem situation_binders_classified
    (R : DenotGS F .et) (deictic : Core.Deixis.Feature) (sIdx d : Nat) :
    (NominalKind.unique R sIdx).usesSituationPronoun = true ∧
    (NominalKind.demonstrative R deictic sIdx d).usesSituationPronoun = true ∧
    (NominalKind.anaphoric R d).usesSituationPronoun = false ∧
    (NominalKind.bare R).usesSituationPronoun = false ∧
    (NominalKind.indefinite R).usesSituationPronoun = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- §5: Anaphoric vs. unique — orthogonal binding
-- ════════════════════════════════════════════════════════════════

/-- Anaphoric definites consult the entity assignment for the
    antecedent. When the restrictor itself is situation-insensitive
    (`R g₀ gsKitchen = R g₀ gsLiving`), the anaphoric reading is
    invariant under the resource-situation assignment — its referent
    is determined by the entity slot `g₀ d`. This is the orthogonality
    of entity-assignment binding and situation-assignment binding in
    @cite{hanink-2021}'s architecture: the *anaphoric* layer reads from
    `g`, the *unique* layer reads from `gs`. -/
theorem anaphoric_independent_of_situation
    (R : DenotGS F .et) (d : Nat)
    (hgs : R g₀ gsKitchen = R g₀ gsLiving) :
    interpret (F := F) (.anaphoric R d) g₀ gsKitchen =
    interpret (F := F) (.anaphoric R d) g₀ gsLiving := by
  rw [interpret_anaphoric, interpret_anaphoric, hgs]

/-- Concrete instance: with a constant restrictor (the antecedent is
    self-identifying, no situation needed), anaphoric definites are
    insensitive to the resource-situation assignment. -/
theorem anaphoric_const_restrictor_situation_insensitive (d : Nat) :
    interpret (F := F) (.anaphoric (DenotGS.const (fun _ => True)) d) g₀ gsKitchen =
    interpret (F := F) (.anaphoric (DenotGS.const (fun _ => True)) d) g₀ gsLiving :=
  anaphoric_independent_of_situation _ _ rfl

end Phenomena.Definiteness.Studies.Hanink2021
