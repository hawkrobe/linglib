import Linglib.Semantics.Definiteness.Description
import Linglib.Semantics.Definiteness.Interpret
import Linglib.Semantics.Definiteness.Maximality
import Linglib.Syntax.Category.Pronoun.Demonstrative

/-!
# Hanink (2021): DP Structure and Internally Headed Relatives in Wášiw
[hanink-2021]

The architectural claim of [hanink-2021] (developing the framework
of Hanink 2018) is that the resource situation evaluating a definite
description's restrictor is a *bound variable* in the syntactic
structure — a "situation pronoun" — rather than a free contextual
parameter handed to the interpretation function. The resource
situation is selected by an index inside DP, not by the matrix
context, and that index can be bound by higher operators.

## What this file tests

The IL substrate operationalizes this in two parallel pieces:

- **`SitAssignment W := Nat → W`** in `Intensional.Variables`
  is the situation-pronoun assignment, parallel to the entity
  assignment.
- **`Description.unique R sIdx`** in `Semantics.Definiteness.Description`
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

namespace Hanink2021

open Intensional
open Intensional.Variables
open Semantics.Definiteness

-- ════════════════════════════════════════════════════════════════
-- §1: A two-room frame for the resource-situation diagnostic
-- ════════════════════════════════════════════════════════════════

/-- Two tables, one in each room. The "the table" diagnostic in
    [hanink-2021]'s style: shifting the bound resource situation
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

/-- "Table-in-room": the predicate is true at exactly one item per room.
    Encodes the [hanink-2021] resource-situation idea — what counts
    as "the table" depends on the situation we evaluate at. -/
def tableIn : Room → Item → Prop
  | .kitchen, .tableKitchen => True
  | .kitchen, _             => False
  | .living,  .tableLiving  => True
  | .living,  _             => False

/-- The restrictor *the table at the situation pointed to by pronoun 0*:
    a `DenotGS` that consults `interpSitPronoun 0` to fetch the resource
    situation, then evaluates `tableIn` at that situation.

    This is the [hanink-2021] situation-pronoun pattern: the
    structural index `0` selects which situation in `gs` to use. -/
def tableAtSit0 : DenotGS Item Room .et :=
  fun _g gs x => tableIn (interpSitPronoun 0 gs) x

-- ════════════════════════════════════════════════════════════════
-- §2: Bi-assignment scaffolding
-- ════════════════════════════════════════════════════════════════

/-- A trivial entity assignment. Entity binding is not exercised here. -/
def g₀ : Core.Assignment Item := fun _ => Item.tableKitchen

/-- Situation assignment with pronoun 0 ↦ kitchen. -/
def gsKitchen : SitAssignment Room := fun _ => Room.kitchen

/-- Situation assignment with pronoun 0 ↦ living. -/
def gsLiving : SitAssignment Room := fun _ => Room.living

-- ════════════════════════════════════════════════════════════════
-- §3: The same description picks different referents (the payoff)
-- ════════════════════════════════════════════════════════════════

/-- Restrictor uniqueness in the kitchen situation: only `tableKitchen`
    satisfies `tableAtSit0`. -/
theorem tableAtSit0_existsUnique_kitchen :
    ∃! x : Item, tableAtSit0 g₀ gsKitchen x := by
  refine ⟨Item.tableKitchen, trivial, ?_⟩
  intro y hy
  cases y <;> simp_all [tableAtSit0, tableIn, interpSitPronoun, gsKitchen]

/-- Restrictor uniqueness in the living-room situation: only
    `tableLiving` satisfies `tableAtSit0`. -/
theorem tableAtSit0_existsUnique_living :
    ∃! x : Item, tableAtSit0 g₀ gsLiving x := by
  refine ⟨Item.tableLiving, trivial, ?_⟩
  intro y hy
  cases y <;> simp_all [tableAtSit0, tableIn, interpSitPronoun, gsLiving]

/-- Witness extraction for the kitchen case: the unique satisfier is
    `tableKitchen`. -/
theorem theTable_kitchen :
    interpret (E := Item) (W := Room) (.unique tableAtSit0 0) g₀ gsKitchen
      = some Item.tableKitchen :=
  interpret_unique_eq_some_of_existsUnique _ 0 g₀ gsKitchen Item.tableKitchen trivial
    (fun y hy => by cases y <;> simp_all [tableAtSit0, tableIn, interpSitPronoun, gsKitchen])

/-- Witness extraction for the living-room case: the unique satisfier
    is `tableLiving`. -/
theorem theTable_living :
    interpret (E := Item) (W := Room) (.unique tableAtSit0 0) g₀ gsLiving
      = some Item.tableLiving :=
  interpret_unique_eq_some_of_existsUnique _ 0 g₀ gsLiving Item.tableLiving trivial
    (fun y hy => by cases y <;> simp_all [tableAtSit0, tableIn, interpSitPronoun, gsLiving])

/-- The Hanink payoff: the *same* `.unique` description picks out
    different referents under different situation assignments. The
    description is one syntactic object; the resource situation is a
    bound variable, not a free parameter. -/
theorem same_description_different_referents :
    interpret (E := Item) (W := Room) (.unique tableAtSit0 0) g₀ gsKitchen
      ≠ interpret (E := Item) (W := Room) (.unique tableAtSit0 0) g₀ gsLiving := by
  rw [theTable_kitchen, theTable_living]
  intro h
  cases (Option.some_inj.mp h)

-- ════════════════════════════════════════════════════════════════
-- §4: Index-record discipline
-- ════════════════════════════════════════════════════════════════

/-- The index argument to `.unique` does not select among situations at
    the interpretation layer — the restrictor `R` already takes the full
    situation assignment, and the index records *which* pronoun is
    bound. (`Semantics.Definiteness.interpret_unique_index_irrelevant` makes this
    explicit.) The Hanink claim is recovered via the restrictor calling
    `interpSitPronoun sIdx`, not via the interpreter inspecting `sIdx`. -/
theorem unique_index_does_not_alter_referent_directly :
    interpret (E := Item) (W := Room) (.unique tableAtSit0 0) g₀ gsKitchen
      = interpret (E := Item) (W := Room) (.unique tableAtSit0 7) g₀ gsKitchen :=
  interpret_unique_index_irrelevant _ _ _ _ _

/-- Among `Description` constructors, exactly `unique` and
    `demonstrative` are flagged as binding a structural situation
    pronoun. Anaphoric definites do not — they consult the entity
    assignment for an antecedent, not the situation assignment. -/
theorem situation_binders_classified
    (R : DenotGS Item Room .et) (deictic : Features.Deixis.Feature) (sIdx d : Nat) :
    (Description.unique R sIdx).usesSituationPronoun = true ∧
    (Description.demonstrative R deictic sIdx d).usesSituationPronoun = true ∧
    (Description.anaphoric R d).usesSituationPronoun = false ∧
    (Description.bare R).usesSituationPronoun = false ∧
    (Description.indefinite R).usesSituationPronoun = false := by
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
    [hanink-2021]'s architecture: the *anaphoric* layer reads from
    `g`, the *unique* layer reads from `gs`. -/
theorem anaphoric_independent_of_situation
    (R : DenotGS Item Room .et) (d : Nat)
    (hgs : R g₀ gsKitchen = R g₀ gsLiving) :
    interpret (E := Item) (W := Room) (.anaphoric R d) g₀ gsKitchen =
    interpret (E := Item) (W := Room) (.anaphoric R d) g₀ gsLiving := by
  rw [interpret_anaphoric, interpret_anaphoric, hgs]

/-- Concrete instance: with a constant restrictor (the antecedent is
    self-identifying, no situation needed), anaphoric definites are
    insensitive to the resource-situation assignment. -/
theorem anaphoric_const_restrictor_situation_insensitive (d : Nat) :
    interpret (E := Item) (W := Room) (.anaphoric (DenotGS.const (fun _ => True)) d) g₀ gsKitchen =
    interpret (E := Item) (W := Room) (.anaphoric (DenotGS.const (fun _ => True)) d) g₀ gsLiving :=
  anaphoric_independent_of_situation _ _ rfl

-- ════════════════════════════════════════════════════════════════
-- §6: Grounding the Pronoun API — `DemonstrativePronoun` denotes via `demonstrative`
-- ════════════════════════════════════════════════════════════════

/-! [hanink-2021] is the theory hub for the demonstrative pronoun (`Syntax/Category/Pronoun/Demonstrative`):
a demonstrative is the bare anaphoric `idx` (Hanink's Washo *gí*; [elbourne-2005]
pronouns-as-definites) plus a deictic feature realized as a presupposition on D. The lexical
`DemonstrativePronoun` supplies its proximal/distal deixis via the `Demonstrative` capability; the
restrictor and indices come from context. -/

/-- The denotation of a demonstrative pronoun: `Description.demonstrative` over a context restrictor,
    with the pronoun's deictic feature as the presupposition on D ([hanink-2021] (34)/(35)). -/
def demDescription {E W : Type} (p : DemonstrativePronoun)
    (R : DenotGS E W .et) (sIdx d : Nat) : Description E W :=
  .demonstrative R p.deixis sIdx d

/-- A demonstrative pronoun picks the *same referent* as a plain anaphoric definite: its deixis is a
    presupposition filter, not a referent selector ([hanink-2021]). The Pronoun-API capability
    `Demonstrative.deixis` is exactly the presupposition that drops out of referent selection. -/
theorem demDescription_eq_anaphoric {E W : Type} (p : DemonstrativePronoun)
    (R : DenotGS E W .et) (sIdx d : Nat) (g : Core.Assignment E) (gs : SitAssignment W) :
    interpret (demDescription p R sIdx d) g gs = interpret (.anaphoric R d) g gs :=
  interpret_demonstrative_eq_anaphoric R p.deixis sIdx d g gs

/-- [patel-grosz-grosz-2017]'s orthogonality, now grounded in *meaning* (and stated in the later
    study, per chronology): German *der* — the strong-article personal pronoun, an **anaphoric**
    definite with no deixis — and a demonstrative pronoun pick the **same referent** (both anaphoric
    over `d`), yet only the demonstrative carries a deictic feature. Article-strength ⊥
    demonstrativehood: PG&G's "*der* is not a `Demonstrative`" is a semantic fact, not just typing. -/
theorem der_strong_vs_demonstrative {E W : Type} (p : DemonstrativePronoun)
    (hdist : (Demonstrative.deixis p).EncodesDistance)
    (R : DenotGS E W .et) (sIdx d : Nat) (g : Core.Assignment E) (gs : SitAssignment W) :
    interpret (demDescription p R sIdx d) g gs = interpret (.anaphoric R d) g gs
      ∧ (Demonstrative.deixis p).EncodesDistance :=
  ⟨demDescription_eq_anaphoric p R sIdx d g gs, hdist⟩

end Hanink2021
