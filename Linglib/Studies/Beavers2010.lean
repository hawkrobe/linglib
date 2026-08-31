import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Semantics.ArgumentStructure.Affectedness
import Linglib.Semantics.ArgumentStructure.Projection
import Linglib.Semantics.ArgumentStructure.RoleList
import Linglib.Semantics.ArgumentStructure.DiathesisAlternation
import Linglib.Data.Examples.Levin1993
import Linglib.Data.Examples.Beavers2010
import Mathlib.Order.Cover

/-!
# Beavers (2010): The Structure of Lexical Meaning

Direct/oblique alternations are governed not by event structure but by
strength of truth conditions: the direct realization of an alternating
argument carries monotonically stronger lexical entailments than the oblique
(27). In the locative and conative case studies the entailments are the
degrees of the affectedness hierarchy ([beavers-2011]), each an existential
weakening of the last; the three implicational entailments (65) admit exactly
four contentful L-thematic roles (66), which form a chain. The
Morphosyntactic Alignment Principle (69) requires the oblique role to be a
minimal weakening (`⊆_M`, (68)) of the direct role — order-theoretically, the
oblique weakly covers from below: `oblique ⩿ direct`. The same principle
runs on other implicational hierarchies: traversal for *climb (up) the
stairs* (85), prospective possession for the dative (90).

## Main statements

* `MAP`: (69) as mathlib's `⩿`; `minimalContrast_iff_wcovby` ties it to the
  entailment-set form (68).
* `MAP_holds_all_alternations`: every attested contrast (Tables 3–4, plus
  the equal-role *hit the fence/stick* type (75)) satisfies the MAP; the
  reversed, strengthened and level-skipping variants (76)–(77) violate it.
* `conatives_witness_all_covers`: the three conatives realize exactly the
  covering pairs of the affectedness hierarchy.

## References

* [beavers-2010]: The structure of lexical meaning: Why semantics really
  matters. *Language* 86.
* [beavers-2011]: On affectedness.
* [dowty-1991]: Thematic proto-roles and argument selection.
* [levin-1993]: English Verb Classes and Alternations.
* [grimm-2011]: The bounds of subjecthood: Evidence from instruments.
-/

namespace Beavers2010

open ArgumentStructure
open ArgumentStructure (AffectednessDegree profileToDegree)
open ArgumentStructure (DiathesisAlternation)

/-! ### L-thematic roles as entailment sets ((65)–(67)) -/

/-- An L-thematic role for patienthood: which of the three affectedness
entailments (65) it contains. -/
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
   fun x => by rcases x with ⟨q, n, p⟩; cases q <;> cases n <;> cases p <;> decide⟩

namespace PatientLRole

/-- A role is on the hierarchy iff it respects the implicational chain
quantized → nonquantized → potential; the other four combinations are
semantically vacuous (67). -/
def Valid (r : PatientLRole) : Prop :=
  (r.quantized → r.nonquantized) ∧ (r.nonquantized → r.potential)

instance : DecidablePred Valid := fun r => by unfold Valid; infer_instance

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

instance : ∀ r₁ r₂, Decidable (Subset r₁ r₂) := fun _ _ => by
  unfold Subset; infer_instance

/-- Minimal contrast (68): `Q ⊆_M R` iff `Q = R` or `Q ⊂ R` with no valid
role strictly between them. -/
def MinimalContrast (q r : PatientLRole) : Prop :=
  q = r ∨ ((Subset q r ∧ q ≠ r) ∧
    ∀ p, Valid p → ¬((Subset q p ∧ q ≠ p) ∧ (Subset p r ∧ p ≠ r)))

instance : ∀ q r, Decidable (MinimalContrast q r) := fun _ _ => by
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
  fun a b => decidable_of_iff (a ≤ b ∧ ∀ c, a < c → ¬c < b) Iff.rfl

instance : DecidableRel (· ⋖ · : AffectednessDegree → AffectednessDegree → Prop) :=
  fun a b => decidable_of_iff (a < b ∧ ∀ c, a < c → ¬c < b) Iff.rfl

/-- The Morphosyntactic Alignment Principle (69): when a participant
alternates, it bears role `R` as a direct argument and the minimally weaker
`Q ⊆_M R` as an oblique — the oblique degree weakly covers from below. -/
def MAP (direct oblique : AffectednessDegree) : Prop :=
  oblique ⩿ direct

instance : ∀ d o, Decidable (MAP d o) := fun _ _ => by
  unfold MAP; infer_instance

/-- The entailment-set form of minimal contrast (68) is weak covering of
degrees: `⊆_M` on the role hierarchy is `⩿` on the affectedness chain. -/
theorem minimalContrast_iff_wcovby :
    ∀ q r : PatientLRole, PatientLRole.Valid q → PatientLRole.Valid r →
      (PatientLRole.MinimalContrast q r ↔ q.toDegree ⩿ r.toDegree) := by decide

/-- The subset corollary of the MAP: the oblique's entailments are among the
direct realization's (27). -/
theorem MAP.oblique_le {d o : AffectednessDegree} (h : MAP d o) : o ≤ d :=
  h.le

/-! ### The attested contrasts (Tables 3–4, (75)) -/

/-- An alternation contrast: a verb with the affectedness degrees of its
alternating participant as direct object and as oblique. -/
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

/-- *ate her cake* / *ate at her cake* (21): quantized ⇔ nonquantized. -/
def eatConative : AlternationContrast :=
  ⟨"eat", .conative, .quantized, .nonquantized⟩

/-- *cut the rope* / *cut at the rope* (20): nonquantized ⇔ potential. -/
def cutConative : AlternationContrast :=
  ⟨"cut", .conative, .nonquantized, .potential⟩

/-- *hit Defarge* / *hit at Defarge* (22): potential ⇔ unspecified. -/
def hitConative : AlternationContrast :=
  ⟨"hit", .conative, .potential, .unspecified⟩

/-- *loaded the wagon (with hay)* (49): the location is completely filled as
object, partly as oblique. -/
def loadLocation : AlternationContrast :=
  ⟨"load", .locative, .quantized, .nonquantized⟩

/-- *loaded the hay (onto the wagon)* (49): the theme is all moved as
object, partly as oblique. -/
def loadTheme : AlternationContrast :=
  ⟨"load", .locative, .quantized, .nonquantized⟩

/-- *cut the window (with the diamond)* (54): damaged as object, potentially
as oblique. -/
def cutLocation : AlternationContrast :=
  ⟨"cut", .locative, .nonquantized, .potential⟩

/-- *cut the diamond (on the window)* (54): same contrast for the theme. -/
def cutTheme : AlternationContrast :=
  ⟨"cut", .locative, .nonquantized, .potential⟩

/-- *hit the fence with the stick* / *hit the stick against the fence* (24),
(75): both realizations potential — the equal-role alternation the MAP
permits, with no truth-conditional contrast. -/
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

/-- The MAP holds of every attested contrast: each oblique realization is a
minimal weakening — or exact repetition (75) — of its direct counterpart. -/
theorem MAP_holds_all_alternations : ∀ c ∈ allContrasts, MapHolds c := by decide

/-- Degree-level corollary: the direct degree dominates the oblique. -/
theorem MapHolds.oblique_le {c : AlternationContrast} (h : MapHolds c) :
    c.obliqueDegree ≤ c.directDegree :=
  MAP.oblique_le h

/-- The three conatives realize exactly the covering pairs of the
affectedness hierarchy: together they tile the chain (Table 3). -/
theorem conatives_witness_all_covers :
    ∀ q r : AffectednessDegree, q ⋖ r ↔
      ∃ c ∈ [eatConative, cutConative, hitConative],
        c.directDegree = r ∧ c.obliqueDegree = q := by decide

/-! ### Impossible alternations ((76)–(77)) -/

/-- A reversed contrast: the oblique strictly outranks the direct (76). -/
def reversedConative : AlternationContrast :=
  ⟨"reversed", .conative, .potential, .quantized⟩

/-- A level-skipping contrast (77): quantized direct, potential oblique. -/
def skippingLocative : AlternationContrast :=
  ⟨"skipping", .locative, .quantized, .potential⟩

theorem reversed_violates_MAP : ¬ MapHolds reversedConative := by decide

/-- Skipping a level violates the MAP even though the degree order is
respected: `⊆_M` demands the *next-weakest* role, not any weaker one. -/
theorem skipping_violates_MAP :
    ¬ MapHolds skippingLocative ∧
      skippingLocative.obliqueDegree ≤ skippingLocative.directDegree :=
  ⟨by decide, by decide⟩

/-! ### Other hierarchies: traversal (85) and the dative (90) -/

/-- The traversal hierarchy (85): each degree an existential weakening of
the last, exactly parallel to affectedness but predicated of the scale. -/
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
  .lift' TraversalDegree.strength fun a b => by
    cases a <;> cases b <;> simp [TraversalDegree.strength]

instance : DecidableRel (· ⩿ · : TraversalDegree → TraversalDegree → Prop) :=
  fun a b => decidable_of_iff (a ≤ b ∧ ∀ c, a < c → ¬c < b) Iff.rfl

/-- *climbed the stairs* / *climbed up the stairs* (81)–(84): total vs mere
traversal of the path — a covering pair, so the MAP holds on the traversal
hierarchy. -/
theorem climb_traversal_map :
    (TraversalDegree.traversed) ⩿ TraversalDegree.totallyTraversed := by decide

/-- The dative chain (90): being arrived at, and arrival into the possession
of. -/
inductive DativeRole where
  /-- Goal: arrived at. -/
  | goal
  /-- Recipient-goal: arrived into the possession of. -/
  | recipientGoal
  deriving DecidableEq, Fintype, Repr

/-- Strength on the dative chain. -/
def DativeRole.strength : DativeRole → Nat
  | .goal => 0
  | .recipientGoal => 1

instance : LinearOrder DativeRole :=
  .lift' DativeRole.strength fun a b => by
    cases a <;> cases b <;> simp [DativeRole.strength]

instance : DecidableRel (· ⩿ · : DativeRole → DativeRole → Prop) :=
  fun a b => decidable_of_iff (a ≤ b ∧ ∀ c, a < c → ¬c < b) Iff.rfl

/-- *mailed Mary the letter* / *mailed the letter to Mary* (88)–(89): the
indirect object monotonically adds prospective possession to arrival — the
MAP on the possession chain. -/
theorem dative_map : DativeRole.goal ⩿ DativeRole.recipientGoal := by decide

/-! ### Bridge to [levin-1993]'s judgment rows -/

/-- The conative alternation is attested for *cut* and *hit* (Table 3). -/
theorem conative_data_attested :
    Levin1993.Examples.con_cut.judgment = .acceptable ∧
    Levin1993.Examples.con_hit.judgment = .acceptable := ⟨rfl, rfl⟩

/-- *break* does not participate in the conative: its object's quantized
change is inherent to the verb's meaning, so the weakening is blocked. -/
theorem break_no_conative :
    Levin1993.Examples.con_break.judgment = .ungrammatical := rfl

/-- The locative alternation is attested for spray/load verbs (Table 4). -/
theorem locative_data_attested :
    Levin1993.Examples.loc_spray.judgment = .acceptable ∧
    Levin1993.Examples.loc_load.judgment = .acceptable := ⟨rfl, rfl⟩

/-! ### The MAP and subject selection are orthogonal (§6) -/

/-- Subject selection ([dowty-1991]'s ASP) and object/oblique alternation
(the MAP) operate on different argument positions: the ASP governs subjects
via P-Agent entailments, the MAP direct-vs-oblique objects via P-Patient
strength ((93)). -/
theorem asp_and_map_orthogonal :
    OutranksForSubject mannerContact.subjectProfile contactObject ∧
    profileToDegree contactObject = .potential ∧
    mannerContact.subjectProfile.pAgentScore > 0 ∧
    contactObject.pPatientScore > 0 :=
  ⟨by decide, rfl, by decide, by decide⟩

/-! ### Bridge to [grimm-2011]'s persistence lattice

Higher affectedness corresponds to lower persistence: both formalize degree
of change. The mapping is not injective — quantized and nonquantized change
both leave the entity persisting through a qualitative change; the
difference between them is specificity of the result state, which
persistence does not record. -/

/-- The typical persistence level of each affectedness degree. -/
def degreeToPersistence : AffectednessDegree → PersistenceLevel
  | .quantized    => .quPersBeginning
  | .nonquantized => .quPersBeginning
  | .potential    => .totalPersistence
  | .unspecified  => .totalPersistence

/-- Changed entities sit below unaffected ones on the persistence order. -/
theorem changed_lower_than_unaffected :
    (PersistenceLevel.quPersBeginning ≤ PersistenceLevel.totalPersistence) := by
  decide

/-- *kick*'s object: potential affectedness, total persistence — Beavers'
surface-contact classification ([beavers-2011]); [grimm-2011]'s own Fig. 5
places contact objects at `quPersBeginning` instead, a genuine cross-paper
disagreement over whether contact entails impingement. -/
theorem kick_grimm_beavers_consistent :
    PersistenceLevel.fromPatientProfile contactObject = .totalPersistence ∧
    profileToDegree contactObject = .potential := ⟨rfl, rfl⟩

/-- *build*'s object: created, and quantized — maximal on both scales. -/
theorem build_grimm_beavers_consistent :
    PersistenceLevel.fromPatientProfile creationObject = .exPersEnd ∧
    profileToDegree creationObject = .quantized := ⟨rfl, rfl⟩

/-- *eat*'s object: consumed, and quantized. -/
theorem eat_grimm_beavers_consistent :
    PersistenceLevel.fromPatientProfile consumptionObject = .exPersBeginning ∧
    profileToDegree consumptionObject = .quantized := ⟨rfl, rfl⟩

/-- Across canonical profiles the two orders move together: more affected
(Beavers) is less persistent (Grimm). -/
theorem grimm_beavers_monotone_canonical :
    profileToDegree contactObject = .potential ∧
    PersistenceLevel.fromPatientProfile contactObject = .totalPersistence ∧
    profileToDegree creationObject = .quantized ∧
    PersistenceLevel.fromPatientProfile creationObject = .exPersEnd ∧
    profileToDegree perception.subjectProfile = .unspecified ∧
    PersistenceLevel.fromPatientProfile perception.subjectProfile
      = .totalNonPersistence :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Projections from `RoleList` templates -/

/-- The Grimm participant type of a template's subject. -/
def subjectGrimm (t : RoleList) : ParticipantType :=
  ParticipantType.fromSubjectProfile t.subjectProfile

/-- The Grimm participant type of a template's object, if any. -/
def objectGrimm (t : RoleList) : Option ParticipantType :=
  t.objectProfile.map ParticipantType.fromObjectProfile

/-- The affectedness degree of a template's object, if any. -/
def objectAffectedness (t : RoleList) : Option AffectednessDegree :=
  t.objectProfile.map profileToDegree

/-- Manner-contact subjects are full agents on the Grimm lattice. -/
theorem mannerContact_subject_grimm :
    (subjectGrimm mannerContact).agentivity = ⊤ := by decide

/-- The canonical templates are ordered by object affectedness exactly as
the paper's hierarchy: creation/consumption > result-change >
manner-contact > perception. -/
theorem template_affectedness_hierarchy :
    AffectednessDegree.nonquantized ≤ .quantized ∧
    AffectednessDegree.potential ≤ .nonquantized ∧
    objectAffectedness creation = some .quantized ∧
    objectAffectedness resultChange = some .nonquantized ∧
    objectAffectedness mannerContact = some .potential ∧
    objectAffectedness perception = some .unspecified :=
  ⟨by decide, by decide, rfl, rfl, rfl, rfl⟩

/-- Intransitive templates have no object affectedness. -/
theorem selfMotion_no_object : objectAffectedness selfMotion = none := rfl

/-- Affectedness and persistence projections agree for manner-contact
objects. -/
theorem mannerContact_cross_projection :
    objectAffectedness mannerContact = some .potential ∧
    mannerContact.objectProfile.map PersistenceLevel.fromPatientProfile =
      some .totalPersistence := ⟨rfl, by decide⟩

/-- Result-change: changed but persisting. -/
theorem resultChange_cross_projection :
    objectAffectedness resultChange = some .nonquantized ∧
    resultChange.objectProfile.map PersistenceLevel.fromPatientProfile =
      some .quPersBeginning := ⟨rfl, by decide⟩

/-- Creation: quantized, coming into existence. -/
theorem creation_cross_projection :
    objectAffectedness creation = some .quantized ∧
    creation.objectProfile.map PersistenceLevel.fromPatientProfile =
      some .exPersEnd := ⟨rfl, by decide⟩

end Beavers2010
