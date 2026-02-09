/-
# Direct Reference Phenomena

Classic empirical phenomena motivating the theory of direct reference.
These are framework-neutral observations — the theoretical accounts live
in `Theories/IntensionalSemantics/Reference/`.

## Phenomena

1. **Hesperus/Phosphorus**: Co-referential names, informative identity
2. **Modal argument**: Names are rigid, descriptions are not
3. **Donnellan's martini**: Referential vs attributive definite descriptions
4. **Substitutivity failure**: Belief contexts block substitution
5. **"I am here now"**: Logically true, contingent content
6. **Necessity of identity**: If true, "a = b" is necessarily true

## References

- Kripke, S. (1980). Naming and Necessity. Harvard University Press.
- Donnellan, K. (1966). Reference and Definite Descriptions. Philosophical Review.
- Kaplan, D. (1989). Demonstratives.
- Frege, G. (1892). Über Sinn und Bedeutung.
-/

import Linglib.Core.Empirical

namespace Phenomena.Reference.DirectReference

/-! ## Hesperus/Phosphorus: The Informativeness Puzzle -/

/-- Frege's puzzle: "Hesperus = Phosphorus" is informative (empirical
discovery by the Babylonians), yet "Hesperus = Hesperus" is trivial.

If names are rigid designators (Kripke), both sentences are necessarily
true. The puzzle: how can two necessary truths differ in cognitive
significance?

Kaplan's answer: different *characters* (modes of presentation).
Kripke's answer: a posteriori necessity (epistemically contingent,
metaphysically necessary). -/
structure HesperusPhosphorus where
  /-- "Hesperus is Phosphorus" is true (both are Venus) -/
  identity_true : Bool := true
  /-- The identity is informative (empirical discovery) -/
  informative : Bool := true
  /-- "Hesperus is Hesperus" is trivial -/
  self_identity_trivial : Bool := true
  /-- Both names are rigid designators -/
  both_rigid : Bool := true

def hesperusPhosphorus : HesperusPhosphorus := {}

/-! ## The Modal Argument -/

/-- Kripke's modal argument: names and descriptions behave differently
in modal contexts, showing names are rigid.

"Nixon might not have been president" is true — there are worlds where
Nixon exists but isn't president. The name "Nixon" picks out the same
individual (Nixon) at every world.

"The president might not have been president" is trivially false on the
rigid reading, or means "whoever is actually president might not have
been" on the non-rigid reading.

This asymmetry shows that names ≠ descriptions. -/
structure ModalArgument where
  /-- The name -/
  name : String
  /-- The description that happens to co-refer -/
  description : String
  /-- "N might not have been D" is true (natural reading) -/
  name_modal_true : Bool
  /-- The name is rigid across possible worlds -/
  name_is_rigid : Bool := true
  /-- The description is NOT rigid (varies across worlds) -/
  description_is_rigid : Bool := false

def nixonPresident : ModalArgument :=
  { name := "Nixon"
  , description := "the president"
  , name_modal_true := true }

/-! ## Donnellan's Martini Case -/

/-- Donnellan (1966): "The man drinking a martini is happy" said at a party.

The speaker points at Jones, who is actually drinking water.
Smith, unbeknownst to the speaker, is the one drinking a martini.

- Referential use: the speaker refers to Jones → evaluates Jones's happiness
- Attributive use: whoever is drinking a martini → evaluates Smith's happiness

The two uses come apart because the description misfits. -/
structure DonnellanMartini where
  /-- The speaker's intended referent -/
  intended : String := "Jones"
  /-- Who actually satisfies the description -/
  actualSatisfier : String := "Smith"
  /-- The description -/
  description : String := "the man drinking a martini"
  /-- The intended referent doesn't satisfy the description -/
  intendedFails : Bool := true
  /-- Referential use: speaker successfully communicates about Jones -/
  referentialSucceeds : Bool := true
  /-- Attributive use: picks out Smith instead -/
  attributivePicksOther : Bool := true

def donnellanMartini : DonnellanMartini := {}

/-! ## Substitutivity Failure in Belief Contexts -/

/-- Substitutivity failure: co-referential names are not interchangeable
in belief contexts.

"Lois believes Superman can fly" is true.
"Lois believes Clark Kent can fly" is false.
Yet Superman = Clark Kent.

This shows that attitude contexts are *opaque* — they are sensitive to
the mode of presentation, not just the referent. Singular propositions
(structured content) explain this: ⟨Superman, can-fly⟩ ≠ ⟨Clark, can-fly⟩
even though Superman = Clark. -/
structure SubstitutivityFailure where
  /-- The two co-referential names -/
  name₁ : String
  name₂ : String
  /-- The predicate -/
  predicate : String
  /-- The believer -/
  believer : String
  /-- "B believes name₁ is P" -/
  belief₁ : Bool
  /-- "B believes name₂ is P" -/
  belief₂ : Bool
  /-- name₁ = name₂ (co-referential) -/
  coreferential : Bool := true
  /-- belief₁ ≠ belief₂ (substitution failure) -/
  substitutionFails : Bool := true

def supermanClark : SubstitutivityFailure :=
  { name₁ := "Superman"
  , name₂ := "Clark Kent"
  , predicate := "can fly"
  , believer := "Lois"
  , belief₁ := true
  , belief₂ := false }

/-! ## Kaplan's "I am here now" -/

/-- Kaplan (1989): "I am here now" is a logical truth — true at every
context of utterance — yet its content is contingent.

At a context where Alice is in Paris on Monday, the content is the
proposition "Alice is in Paris on Monday", which is contingent (Alice
might have been in London).

This separates two notions of truth:
- Logical truth (truth at every context)
- Necessity (truth at every world) -/
structure IAmHereNow where
  /-- True at every context of utterance -/
  logicallyTrue : Bool := true
  /-- Content is contingent (not true at every world) -/
  contentContingent : Bool := true
  /-- Separates logical truth from necessity -/
  logicalTruthNotNecessity : Bool := true

def iAmHereNow : IAmHereNow := {}

/-! ## Kripke's Necessity of Identity -/

/-- Kripke (1980): if an identity "a = b" is true and both terms are
rigid designators, then the identity is necessarily true.

"Hesperus = Phosphorus" is true. Both "Hesperus" and "Phosphorus" are
rigid designators. Therefore "Hesperus = Phosphorus" is necessarily true
— true at every possible world.

Yet the identity is a posteriori — it was an empirical discovery.
This yields the category of *a posteriori necessities*. -/
structure NecessityOfIdentity where
  /-- The two names -/
  name₁ : String
  name₂ : String
  /-- The identity is true -/
  identityTrue : Bool := true
  /-- Both names are rigid -/
  bothRigid : Bool := true
  /-- The identity is necessary (true at every world) -/
  identityNecessary : Bool := true
  /-- The identity is a posteriori (empirical discovery) -/
  identityAPosteriori : Bool := true

def hesperusPhosphorusNecessity : NecessityOfIdentity :=
  { name₁ := "Hesperus"
  , name₂ := "Phosphorus" }

def waterH2O : NecessityOfIdentity :=
  { name₁ := "water"
  , name₂ := "H₂O" }

/-! ## Kaplan's Anti-Monster Thesis -/

/-- Kaplan's (1989) thesis that natural language has no context-shifting
operators ("monsters").

Status: holds for English; challenged cross-linguistically by indexical
shift under attitude verbs in Amharic (Schlenker 2003), Zazaki (Anand &
Nevins 2004), Slave, Navajo, and Uyghur.

Theoretical account: `Theories/IntensionalSemantics/Reference/Monsters.lean`. -/
structure MonsterThesis where
  /-- The thesis: no NL operator shifts the context of utterance -/
  thesis : String := "No natural language operator shifts the context of utterance"
  /-- Holds for English -/
  holdsForEnglish : Bool := true
  /-- Challenged by at least some languages -/
  challengedCrossLinguistically : Bool := true
  /-- Languages with documented indexical shift -/
  shiftLanguages : List String := ["Amharic", "Zazaki", "Slave", "Navajo", "Uyghur"]
  /-- Quotation is excluded from the thesis -/
  quotationExcluded : Bool := true

def monsterThesis : MonsterThesis := {}

end Phenomena.Reference.DirectReference
