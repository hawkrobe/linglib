module

public import Linglib.Semantics.ArgumentStructure.Affectedness
public import Linglib.Semantics.ArgumentStructure.DiathesisAlternation
public import Linglib.Data.Examples.Levin1993
public import Linglib.Data.Examples.Beavers2010
public import Mathlib.Order.Cover

/-!
# Beavers (2010): The Structure of Lexical Meaning

This file formalizes Beavers's account of object/oblique alternations. The direct realization of an
alternating argument carries monotonically stronger lexical entailments than its oblique
realization, rather than a different event structure. In the conative and locative alternations
the entailments are the degrees of affectedness, each an existential weakening of the next, so that
of the eight sets of the three affectedness entailments only four are contentful, and they form a
chain. The Morphosyntactic Alignment Principle requires the oblique to bear the minimally weaker
role, which on the chain is weak covering. Every attested contrast satisfies it, the three
conatives together realize each covering pair, and reversed and level-skipping alternations violate
it. The same principle runs on the traversal hierarchy of *climb (up) the stairs* and on the chain
of arrival and possession behind the dative alternation.

## Implementation notes

* A role is the set of affectedness entailments it contains, a Boolean triple, and a contrast
  records the degrees of the alternating participant in its two realizations.
* Beavers's rough correspondence between Dowty's proto-patient entailments and his own (Table 5)
  is not formalized, since it marks two of its cells as uncertain.

## TODO

* Derive the contrasts from the example rows of `Data.Examples.Beavers2010` rather than typing the
  verbs and degrees in.

## References

* [J. Beavers, *The structure of lexical meaning: Why semantics really matters*
  (2010)][beavers-2010]
* [J. Beavers, *On Affectedness* (2011)][beavers-2011]
* [B. Levin, *English Verb Classes and Alternations: A Preliminary Investigation*
  (1993)][levin-1993]
-/

@[expose] public section

namespace Beavers2010

open ArgumentStructure
open ArgumentStructure (AffectednessDegree)
open ArgumentStructure (DiathesisAlternation)

/-! ### L-thematic roles as entailment sets ((65)–(67)) -/

/-- An L-thematic role for patienthood records which of the three affectedness entailments (65)
it contains. -/
structure PatientLRole where
  /-- Undergoes a quantized change. -/
  quantized : Bool
  /-- Undergoes a nonquantized change. -/
  nonquantized : Bool
  /-- Has potential for change. -/
  potential : Bool
  deriving DecidableEq, Repr

instance : Fintype PatientLRole :=
  ⟨⟨(↑[(⟨false, false, false⟩ : PatientLRole), ⟨false, false, true⟩,
      ⟨false, true, false⟩, ⟨false, true, true⟩, ⟨true, false, false⟩,
      ⟨true, false, true⟩, ⟨true, true, false⟩, ⟨true, true, true⟩] :
      Multiset PatientLRole), by decide⟩,
   fun x ↦ by rcases x with ⟨q, n, p⟩; cases q <;> cases n <;> cases p <;> decide⟩

namespace PatientLRole

/-- A role is on the hierarchy iff it respects the implicational chain
quantized → nonquantized → potential; the other four combinations are
semantically vacuous (67). -/
def Valid (r : PatientLRole) : Prop :=
  (r.quantized → r.nonquantized) ∧ (r.nonquantized → r.potential)

instance : DecidablePred Valid := fun r ↦ by unfold Valid; infer_instance

/-- `{quantized, nonquantized, potential}`. -/
def quantizedRole : PatientLRole := ⟨true, true, true⟩

/-- `{nonquantized, potential}`. -/
def nonquantizedRole : PatientLRole := ⟨false, true, true⟩

/-- `{potential}`. -/
def potentialRole : PatientLRole := ⟨false, false, true⟩

/-- `{}`. -/
def unspecifiedRole : PatientLRole := ⟨false, false, false⟩

/-- Exactly four of the eight combinations are contentful (66)–(67). -/
theorem exactly_four_valid_roles :
    ∀ r : PatientLRole, Valid r ↔
      (r = quantizedRole ∨ r = nonquantizedRole ∨
       r = potentialRole ∨ r = unspecifiedRole) := by decide

/-- Entailment-set inclusion. -/
def Subset (r₁ r₂ : PatientLRole) : Prop :=
  (r₁.quantized → r₂.quantized) ∧ (r₁.nonquantized → r₂.nonquantized) ∧
    (r₁.potential → r₂.potential)

instance : ∀ r₁ r₂, Decidable (Subset r₁ r₂) := fun _ _ ↦ by
  unfold Subset; infer_instance

/-- `Q` is a minimal contrast of `R`, written `Q ⊆_M R` (68), when `Q = R` or `Q ⊂ R` with no
valid role strictly between them. -/
def MinimalContrast (q r : PatientLRole) : Prop :=
  q = r ∨ ((Subset q r ∧ q ≠ r) ∧
    ∀ p, Valid p → ¬((Subset q p ∧ q ≠ p) ∧ (Subset p r ∧ p ≠ r)))

instance : ∀ q r, Decidable (MinimalContrast q r) := fun _ _ ↦ by
  unfold MinimalContrast; infer_instance

/-- The affectedness degree of a valid role, named by its strongest
entailment. -/
def toDegree (r : PatientLRole) : AffectednessDegree :=
  if r.quantized then .quantized
  else if r.nonquantized then .nonquantized
  else if r.potential then .potential
  else .unspecified

/-- The valid role realizing a degree (a section of `toDegree`). -/
def ofDegree : AffectednessDegree → PatientLRole
  | .quantized => quantizedRole
  | .nonquantized => nonquantizedRole
  | .potential => potentialRole
  | .unspecified => unspecifiedRole

theorem ofDegree_valid : ∀ d, Valid (ofDegree d) := by decide

theorem toDegree_ofDegree : ∀ d, (ofDegree d).toDegree = d := by decide

/-- On valid roles, entailment-set inclusion is the degree order (66). -/
theorem subset_iff_toDegree_le :
    ∀ q r : PatientLRole, Valid q → Valid r →
      (Subset q r ↔ q.toDegree ≤ r.toDegree) := by decide

end PatientLRole

/-! ### The MAP ((68)–(69)) as weak covering -/

instance : DecidableRel (· ⩿ · : AffectednessDegree → AffectednessDegree → Prop) :=
  fun a b ↦ decidable_of_iff (a ≤ b ∧ ∀ c, a < c → ¬c < b) Iff.rfl

instance : DecidableRel (· ⋖ · : AffectednessDegree → AffectednessDegree → Prop) :=
  fun a b ↦ decidable_of_iff (a < b ∧ ∀ c, a < c → ¬c < b) Iff.rfl

/-- The Morphosyntactic Alignment Principle (69) holds of the degrees of an alternating
participant's direct and oblique realizations when the oblique is the minimally weaker role,
weakly covering the direct one from below. -/
def MAP (direct oblique : AffectednessDegree) : Prop :=
  oblique ⩿ direct

instance : ∀ d o, Decidable (MAP d o) := fun _ _ ↦ by
  unfold MAP; infer_instance

/-- On valid roles, minimal contrast (68) is weak covering of their degrees on the affectedness
chain. -/
theorem minimalContrast_iff_wcovby :
    ∀ q r : PatientLRole, PatientLRole.Valid q → PatientLRole.Valid r →
      (PatientLRole.MinimalContrast q r ↔ q.toDegree ⩿ r.toDegree) := by decide

/-- Under the MAP the oblique degree is at most the direct one, so the oblique's entailments are
among the direct realization's (27). -/
theorem MAP.oblique_le {d o : AffectednessDegree} (h : MAP d o) : o ≤ d :=
  h.le

/-! ### The attested contrasts (Tables 3–4, (75)) -/

/-- An alternation contrast records a verb and the affectedness degrees of its alternating
participant as direct object and as oblique. -/
structure AlternationContrast where
  /-- The verb. -/
  verb : String
  /-- The alternation it instantiates. -/
  alternationType : DiathesisAlternation
  /-- Degree in direct realization. -/
  directDegree : AffectednessDegree
  /-- Degree in oblique realization. -/
  obliqueDegree : AffectednessDegree
  deriving Repr, DecidableEq

/-- *Ate her cake* against *ate at her cake* (21) contrasts quantized with non-quantized change. -/
def eatConative : AlternationContrast :=
  ⟨"eat", .conative, .quantized, .nonquantized⟩

/-- *Cut the rope* against *cut at the rope* (20) contrasts non-quantized change with potential for
change. -/
def cutConative : AlternationContrast :=
  ⟨"cut", .conative, .nonquantized, .potential⟩

/-- *Hit Defarge* against *hit at Defarge* (22) contrasts potential for change with no entailment
about change. -/
def hitConative : AlternationContrast :=
  ⟨"hit", .conative, .potential, .unspecified⟩

/-- In *loaded the wagon (with hay)* (49) the location is completely filled as object and partly as
oblique. -/
def loadLocation : AlternationContrast :=
  ⟨"load", .locative, .quantized, .nonquantized⟩

/-- In *loaded the hay (onto the wagon)* (49) the theme is all moved as object and partly as
oblique. -/
def loadTheme : AlternationContrast :=
  ⟨"load", .locative, .quantized, .nonquantized⟩

/-- In *cut the window (with the diamond)* (54) the location is damaged as object and potentially
damaged as oblique. -/
def cutLocation : AlternationContrast :=
  ⟨"cut", .locative, .nonquantized, .potential⟩

/-- *Cut the diamond (on the window)* (54) shows the same contrast for the theme. -/
def cutTheme : AlternationContrast :=
  ⟨"cut", .locative, .nonquantized, .potential⟩

/-- In *hit the fence with the stick* against *hit the stick against the fence* ((24), (75)) both
realizations have potential for change, the equal-role alternation the MAP permits with no
truth-conditional contrast. -/
def hitLocative : AlternationContrast :=
  ⟨"hit", .locative, .potential, .potential⟩

/-- The attested contrasts. -/
def allContrasts : List AlternationContrast :=
  [eatConative, cutConative, hitConative,
   loadLocation, loadTheme, cutLocation, cutTheme, hitLocative]

/-- The MAP holds of a contrast. -/
def MapHolds (c : AlternationContrast) : Prop :=
  MAP c.directDegree c.obliqueDegree

instance (c : AlternationContrast) : Decidable (MapHolds c) := by
  unfold MapHolds; infer_instance

/-- The MAP holds of every attested contrast, each oblique realization being a minimal weakening
of its direct counterpart or, as in (75), the same role. -/
theorem MAP_holds_all_alternations : ∀ c ∈ allContrasts, MapHolds c := by decide

/-- Under the MAP the direct degree dominates the oblique one. -/
theorem MapHolds.oblique_le {c : AlternationContrast} (h : MapHolds c) :
    c.obliqueDegree ≤ c.directDegree :=
  MAP.oblique_le h

/-- The three conatives realize exactly the covering pairs of the affectedness hierarchy,
together tiling the chain (Table 3). -/
theorem conatives_witness_all_covers :
    ∀ q r : AffectednessDegree, q ⋖ r ↔
      ∃ c ∈ [eatConative, cutConative, hitConative],
        c.directDegree = r ∧ c.obliqueDegree = q := by decide

/-! ### Impossible alternations ((76)–(77)) -/

/-- In a reversed contrast (76) the oblique strictly outranks the direct realization. -/
def reversedConative : AlternationContrast :=
  ⟨"reversed", .conative, .potential, .quantized⟩

/-- A level-skipping contrast (77) has a quantized direct and a potential oblique realization. -/
def skippingLocative : AlternationContrast :=
  ⟨"skipping", .locative, .quantized, .potential⟩

theorem reversed_violates_MAP : ¬ MapHolds reversedConative := by decide

/-- Skipping a level violates the MAP even though the degree order is respected, since `⊆_M`
demands the next-weakest role, not any weaker one. -/
theorem skipping_violates_MAP :
    ¬ MapHolds skippingLocative ∧
      skippingLocative.obliqueDegree ≤ skippingLocative.directDegree :=
  ⟨by decide, by decide⟩

/-! ### Other hierarchies: traversal (85) and the dative (90) -/

/-- The degrees of the traversal hierarchy (85), each an existential weakening of the next,
parallel to affectedness but predicated of the scale. -/
inductive TraversalDegree where
  /-- No traversal entailment. -/
  | unspecified
  /-- Potentially traversed. -/
  | potentiallyTraversed
  /-- Some of the scale traversed. -/
  | traversed
  /-- All of the scale traversed. -/
  | totallyTraversed
  deriving DecidableEq, Fintype, Repr

/-- Strength on the traversal hierarchy. -/
def TraversalDegree.strength : TraversalDegree → Nat
  | .unspecified => 0
  | .potentiallyTraversed => 1
  | .traversed => 2
  | .totallyTraversed => 3

instance : LinearOrder TraversalDegree :=
  .lift' TraversalDegree.strength fun a b ↦ by
    cases a <;> cases b <;> simp [TraversalDegree.strength]

instance : DecidableRel (· ⩿ · : TraversalDegree → TraversalDegree → Prop) :=
  fun a b ↦ decidable_of_iff (a ≤ b ∧ ∀ c, a < c → ¬c < b) Iff.rfl

/-- *Climbed the stairs* against *climbed up the stairs* ((81)–(84)) contrasts total with partial
traversal of the path, a covering pair, so the MAP holds on the traversal hierarchy. -/
theorem climb_traversal_map :
    (TraversalDegree.traversed) ⩿ TraversalDegree.totallyTraversed := by decide

/-- The roles of the dative chain (90) are being arrived at and being arrived into the possession
of. -/
inductive DativeRole where
  /-- A goal is arrived at. -/
  | goal
  /-- A recipient-goal is arrived into the possession of. -/
  | recipientGoal
  deriving DecidableEq, Fintype, Repr

/-- Strength on the dative chain. -/
def DativeRole.strength : DativeRole → Nat
  | .goal => 0
  | .recipientGoal => 1

instance : LinearOrder DativeRole :=
  .lift' DativeRole.strength fun a b ↦ by
    cases a <;> cases b <;> simp [DativeRole.strength]

instance : DecidableRel (· ⩿ · : DativeRole → DativeRole → Prop) :=
  fun a b ↦ decidable_of_iff (a ≤ b ∧ ∀ c, a < c → ¬c < b) Iff.rfl

/-- In *mailed Mary the letter* against *mailed the letter to Mary* ((88)–(89)) the indirect object
adds prospective possession to arrival, the MAP on the possession chain. -/
theorem dative_map : DativeRole.goal ⩿ DativeRole.recipientGoal := by decide

/-! ### Bridge to [levin-1993]'s judgment rows -/

/-- The conative alternation is attested for *cut* and *hit* (Table 3). -/
theorem conative_data_attested :
    Levin1993.Examples.con_cut.judgment = .acceptable ∧
    Levin1993.Examples.con_hit.judgment = .acceptable := ⟨rfl, rfl⟩

/-- *Break* does not take the conative, since its object's quantized change is inherent to the
verb's meaning and the weakening is blocked. -/
theorem break_no_conative :
    Levin1993.Examples.con_break.judgment = .ungrammatical := rfl

/-- The locative alternation is attested for spray/load verbs (Table 4). -/
theorem locative_data_attested :
    Levin1993.Examples.loc_spray.judgment = .acceptable ∧
    Levin1993.Examples.loc_load.judgment = .acceptable := ⟨rfl, rfl⟩

end Beavers2010
