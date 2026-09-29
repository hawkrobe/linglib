module

public import Linglib.Semantics.ArgumentStructure.Affectedness
public import Linglib.Semantics.ArgumentStructure.DiathesisAlternation
public import Linglib.Data.Examples.Levin1993
public import Linglib.Data.Examples.Beavers2010
public import Mathlib.Order.Cover
public import Mathlib.Data.Fintype.Prod

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
it. Total traversal of a path is the same entailment as quantized change, read of the scale rather
than the theme, and adding it to the entailments of patienthood gives five contentful roles, among
which *climb the stairs* and *climb up the stairs* are a minimal contrast. The same principle runs
on the chain of arrival and possession behind the dative alternation.

## Implementation notes

* A role is the set of affectedness entailments it contains, a Boolean triple, and a contrast
  records the degrees of the alternating participant in its two realizations.
* The entailments are stated over a result relation relative to a world. Potential for change is
  modal ((38)), and it is an existential generalization of nonquantized change only when the actual
  world is among the worlds the modality ranges over, which the paper assumes and the file takes as
  a hypothesis. Beavers leaves the modal base open.
* The paper defines the degrees of traversal (85) by the formulas of the degrees of affectedness,
  abstracting over the scale instead of the theme, so the file states each formula once. Only total
  traversal enters the roles of (86), and a participant is either a theme or a scale, which is how
  the file reads the exclusion of affected paths in (87).
* The paper states its conditions of a sentence with the theme, scale and event given; the file
  states them of a relation, over all themes, scales and events. A predicate-supplied goal is fixed
  across the predicate's events, so the end of the path in (84a) is read as the endpoint of the
  goal type.
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

/-! ### The entailments ((31), (38))

The result relation `R w x s g e` says that in the world `w` the theme `x` ends the event `e` at
the goal `g` on the scale `s`, and `w₀` is the actual world. -/

section Entailments

variable {W α S G β : Type*} (acc : W → W → Prop) (w₀ : W) (R : W → α → S → G → β → Prop)
  (φ : α → S → β → Prop)

/-- A predicate entails a **quantized change** to the goal `g` when its theme ends every event of
it at `g` on its scale ((31a)). Of the scale, the same condition says it is **totally traversed**
((85a)). -/
def Quantized (g : G) : Prop := ∀ x s e, φ x s e → R w₀ x s g e

/-- A predicate entails a **nonquantized change** when its theme ends every event of it at some
goal on its scale ((31b)). Of the scale, the same condition says it is **traversed** ((85b)). -/
def Nonquantized : Prop := ∀ x s e, φ x s e → ∃ g, R w₀ x s g e

/-- A predicate gives its theme **potential for change** when in every event of it the theme ends
at some goal on its scale in some world accessible from the actual one ((38a)). Of the scale, the
same condition says it is **potentially traversed** ((85c)). -/
def Potential : Prop := ∀ x s e, φ x s e → ∃ w, acc w₀ w ∧ ∃ g, R w x s g e

variable {acc w₀ R φ}

theorem Quantized.nonquantized {g : G} (h : Quantized w₀ R φ g) : Nonquantized w₀ R φ :=
  fun x s e hx ↦ ⟨g, h x s e hx⟩

/-- A nonquantized change entails potential for change when the actual world is among the worlds
the modality ranges over, (38a) being the existential generalization of (31b) over worlds. -/
theorem Nonquantized.potential (hacc : acc w₀ w₀) (h : Nonquantized w₀ R φ) :
    Potential acc w₀ R φ :=
  fun x s e hx ↦ ⟨w₀, hacc, h x s e hx⟩

open Classical in
/-- The patient role of a predicate is the set of affectedness entailments it has about its
theme ((65)). -/
noncomputable def role (acc : W → W → Prop) (w₀ : W) (R : W → α → S → G → β → Prop)
    (φ : α → S → β → Prop) : PatientLRole :=
  ⟨decide (∃ g, Quantized w₀ R φ g), decide (Nonquantized w₀ R φ),
    decide (Potential acc w₀ R φ)⟩

/-- Every predicate's role is contentful, since each affectedness entailment entails the weaker
ones ((67)), given that the actual world is among the worlds the modality ranges over. -/
theorem role_valid (hacc : acc w₀ w₀) : (role acc w₀ R φ).Valid := by
  classical
  simp only [PatientLRole.Valid, role, decide_eq_true_eq]
  exact ⟨fun ⟨_, h⟩ ↦ h.nonquantized, Nonquantized.potential hacc⟩

end Entailments

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


/-! ### Total traversal ((84)–(87)) -/

instance : PartialOrder PatientLRole :=
  .lift (fun r ↦ (r.quantized, r.nonquantized, r.potential))
    (fun a b h ↦ by rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; simpa using h)

/-- On patient roles, the order is entailment-set inclusion. -/
theorem PatientLRole.le_iff_subset (q r : PatientLRole) : q ≤ r ↔ q.Subset r := by
  rcases q with ⟨_, _, _⟩; rcases r with ⟨_, _, _⟩
  simp [PatientLRole.Subset, LE.le]

/-- An L-thematic role of (86) adds total traversal of a path to the affectedness entailments of
a patient. -/
structure LRole extends PatientLRole where
  /-- Is totally traversed. -/
  totallyTraversed : Bool
  deriving DecidableEq, Repr

namespace LRole

instance : Fintype LRole :=
  Fintype.ofEquiv (PatientLRole × Bool)
    { toFun := fun p ↦ ⟨p.1, p.2⟩
      invFun := fun r ↦ (r.toPatientLRole, r.totallyTraversed)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

instance : PartialOrder LRole :=
  .lift (fun r ↦ (r.toPatientLRole, r.totallyTraversed))
    (fun a b h ↦ by rcases a with ⟨_, _⟩; rcases b with ⟨_, _⟩; simpa using h)

instance : DecidableRel (· ≤ · : PatientLRole → PatientLRole → Prop) := fun a b ↦
  inferInstanceAs (Decidable ((a.quantized, a.nonquantized, a.potential) ≤
    (b.quantized, b.nonquantized, b.potential)))

instance : DecidableRel (· ≤ · : LRole → LRole → Prop) := fun a b ↦
  inferInstanceAs (Decidable ((a.toPatientLRole, a.totallyTraversed) ≤
    (b.toPatientLRole, b.totallyTraversed)))

instance : DecidableRel (· < · : LRole → LRole → Prop) := fun a b ↦
  inferInstanceAs (Decidable (a ≤ b ∧ ¬ b ≤ a))

/-- A role of (86) is contentful when its affectedness entailments form a contentful patient role
and a totally traversed path is not also affected, which (87) rules out. -/
def Valid (r : LRole) : Prop :=
  r.toPatientLRole.Valid ∧ (r.totallyTraversed → r.toPatientLRole = PatientLRole.unspecifiedRole)

instance : DecidablePred Valid := fun r ↦ by unfold Valid; infer_instance

/-- `{}`. -/
def unspecified : LRole := ⟨PatientLRole.unspecifiedRole, false⟩

/-- `{totally traversed}`. -/
def totallyTraversedRole : LRole := ⟨PatientLRole.unspecifiedRole, true⟩

/-- Exactly five roles of (86) are contentful, the four patient roles and total traversal
((87)). -/
theorem exactly_five_valid_roles :
    ∀ r : LRole, Valid r ↔ r = ⟨PatientLRole.quantizedRole, false⟩ ∨
      r = ⟨PatientLRole.nonquantizedRole, false⟩ ∨ r = ⟨PatientLRole.potentialRole, false⟩ ∨
        r = unspecified ∨ r = totallyTraversedRole := by
  decide

section Participants

variable {W α S G β : Type*} {acc : W → W → Prop} {w₀ : W} {R : W → α → S → G → β → Prop}
  {φ : α → S → β → Prop}

/-- The role of (86) that a predicate assigns its theme is its patient role, without traversal. -/
noncomputable def ofTheme (acc : W → W → Prop) (w₀ : W) (R : W → α → S → G → β → Prop)
    (φ : α → S → β → Prop) : LRole :=
  ⟨role acc w₀ R φ, false⟩

open Classical in
/-- The role of (86) that a predicate assigns its scale is total traversal when the predicate
entails a quantized change on it, (85a) being (31a) read of the scale, and nothing otherwise. -/
noncomputable def ofScale (w₀ : W) (R : W → α → S → G → β → Prop) (φ : α → S → β → Prop) :
    LRole :=
  ⟨PatientLRole.unspecifiedRole, decide (∃ g, Quantized w₀ R φ g)⟩

theorem ofTheme_valid (hacc : acc w₀ w₀) : (ofTheme acc w₀ R φ).Valid :=
  ⟨role_valid hacc, fun h ↦ by simp [ofTheme] at h⟩

theorem ofScale_valid : (ofScale w₀ R φ).Valid :=
  ⟨⟨fun h ↦ h, fun h ↦ h⟩, fun _ ↦ rfl⟩

end Participants

end LRole

/-- The contentful roles of (86), ordered by inclusion. -/
abbrev ValidLRole := {r : LRole // r.Valid}

instance : DecidableRel (· ⩿ · : ValidLRole → ValidLRole → Prop) :=
  fun a b ↦ decidable_of_iff (a ≤ b ∧ ∀ c, a < c → ¬c < b) Iff.rfl

/-- *Climbed the stairs* against *climbed up the stairs* ((81)–(84)) contrasts a totally
traversed path with one of which nothing is entailed on (86). The oblique role is minimally weaker
than the direct one among the contentful roles, as the MAP (69) requires. -/
theorem climb_wcovby :
    (⟨LRole.unspecified, by decide⟩ : ValidLRole) ⩿ ⟨LRole.totallyTraversedRole, by decide⟩ := by
  decide

/-! ### The dative chain (90) -/

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
