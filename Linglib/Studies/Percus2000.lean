import Linglib.Logic.Assignment
import Linglib.Semantics.Reference.Context.Index

/-!
# Percus (2000): Constraints on Some Other Variables in Syntax

This file formalizes the situation-pronoun syntax of [percus-2000]. Every predicate carries a
situation pronoun, every clause introduces a situation binder, and two generalizations
restrict which binder a pronoun may take: Generalization X, that the situation pronoun of a
verb is bound by the nearest c-commanding binder, and Generalization Y, that the situation
argument of an adverb of quantification is likewise locally bound, whereas the pronoun of a
noun phrase may be bound from higher up (`LF.GenX`, `QLF.GenY`). Under an attitude verb this
gives the noun phrase a de re reading, *my brother* evaluated at the matrix situation, while
the embedded predicate is read de dicto only (`genX_licenses`); on a model where the brother
is Bill in fact and Charlie in Mary's belief worlds, the two licensed LFs of *Mary believes
my brother is a spy* come apart (`dpDeRe_true_allDeDicto_false`), and the LF that would
read *John is Canadian* at the actual situation, true on the model, is excluded
(`canadian_predicate_de_re_excluded`). For *always* the compliant LF quantifies over the
situations of the belief world and the violating one over actual situations (`genY`).

## Implementation notes

Situation assignments specialize the assignments of `Logic/Assignment` to indices of world
and time, and the models are two-world toy models. The paper's LF trees and examples are
described in prose without the paper's numbering.

## References

* [percus-2000]
* [heim-kratzer-1998]
-/

namespace Percus2000

open Semantics.Context

/-- An assignment of situations to variable indices. -/
abbrev SituationAssignment (W T : Type*) := Assignment (Index W T)

/-- Belief with situation binding: the complement holds at every doxastic alternative of the
agent, the binder `n` reset to that alternative. -/
def believeSit {W T E : Type*} (dox : E → Index W T → List (Index W T)) (agent : E) (n : ℕ)
    (complement : SituationAssignment W T → Prop) (g : SituationAssignment W T)
    (s : Index W T) : Prop :=
  ∀ s' ∈ dox agent s, complement (Function.update g n s')

instance {W T E : Type*} (dox : E → Index W T → List (Index W T)) (agent : E) (n : ℕ)
    (complement : SituationAssignment W T → Prop) [DecidablePred complement]
    (g : SituationAssignment W T) (s : Index W T) :
    Decidable (believeSit dox agent n complement g s) := by
  unfold believeSit; infer_instance

/-- An adverb of quantification over the situations its restrictor supplies, the binder `n`
reset to each. -/
def alwaysAt {W T : Type*} (domain : Index W T → List (Index W T)) (restrictor : Index W T)
    (n : ℕ) (scope : SituationAssignment W T → Prop) (g : SituationAssignment W T) : Prop :=
  ∀ s' ∈ domain restrictor, scope (Function.update g n s')

instance {W T : Type*} (domain : Index W T → List (Index W T)) (restrictor : Index W T)
    (n : ℕ) (scope : SituationAssignment W T → Prop) [DecidablePred scope]
    (g : SituationAssignment W T) : Decidable (alwaysAt domain restrictor n scope g) := by
  unfold alwaysAt; infer_instance

/-! ### Generalizations X and Y -/

/-- An LF of an attitude sentence: the matrix clause binds situation variable 1 and the
embedded clause variable 2, and the LF records which binder the embedded verb's situation
pronoun and the embedded noun phrase's pronoun take. -/
structure LF where
  verb : ℕ
  noun : ℕ
  deriving DecidableEq

/-- Generalization X: the verb's situation pronoun is bound by the nearest binder; the noun
phrase's pronoun is unconstrained. -/
def LF.GenX (lf : LF) : Prop := lf.verb = 2

instance : DecidablePred LF.GenX := λ lf => inferInstanceAs (Decidable (lf.verb = 2))

/-- The LF with everything read in the belief situations. -/
def allDeDicto : LF := ⟨2, 2⟩

/-- The LF reading the noun phrase at the matrix situation. -/
def dpDeRe : LF := ⟨2, 1⟩

/-- The LF reading the predicate at the matrix situation. -/
def predicateDeRe : LF := ⟨1, 2⟩

/-- Generalization X licenses the all-de-dicto and the de re noun phrase LFs and excludes the
de re predicate LF. -/
theorem genX_licenses : allDeDicto.GenX ∧ dpDeRe.GenX ∧ ¬ predicateDeRe.GenX := by decide

/-- An LF for an adverb of quantification in an attitude complement: the binder its situation
argument takes. -/
structure QLF where
  quant : ℕ
  deriving DecidableEq

/-- Generalization Y: the adverb's situation argument is bound by the nearest binder. -/
def QLF.GenY (q : QLF) : Prop := q.quant = 2

instance : DecidablePred QLF.GenY := λ q => inferInstanceAs (Decidable (q.quant = 2))

/-! ### A model -/

/-- The actual world and Mary's belief world. -/
inductive W where
  | actual
  | belief
  deriving DecidableEq

inductive Person where
  | mary
  | john
  | bill
  | charlie
  deriving DecidableEq

/-- Situations with a trivial time coordinate. -/
abbrev Sit := Index W Unit

def sActual : Sit := ⟨.actual, ()⟩
def sBelief : Sit := ⟨.belief, ()⟩

/-- John is Canadian in fact and not in Mary's belief world. -/
def IsCanadian (p : Person) (s : Sit) : Prop :=
  match p, s.world with
  | .john, .actual => True
  | _, _ => False

instance (p : Person) (s : Sit) : Decidable (IsCanadian p s) := by
  unfold IsCanadian; cases p <;> cases s.world <;> infer_instance

/-- The speaker's brother is Bill in fact and Charlie in Mary's belief world. -/
def IsBrother (p : Person) (s : Sit) : Prop :=
  match p, s.world with
  | .bill, .actual => True
  | .charlie, .belief => True
  | _, _ => False

instance (p : Person) (s : Sit) : Decidable (IsBrother p s) := by
  unfold IsBrother; cases p <;> cases s.world <;> infer_instance

/-- Bill is a spy in Mary's belief world only. -/
def IsSpy (p : Person) (s : Sit) : Prop :=
  match p, s.world with
  | .bill, .belief => True
  | _, _ => False

instance (p : Person) (s : Sit) : Decidable (IsSpy p s) := by
  unfold IsSpy; cases p <;> cases s.world <;> infer_instance

/-- Mary's doxastic alternatives: the belief world. -/
def doxMary : Sit → List Sit := λ _ => [sBelief]

/-- The unique brother at a situation. -/
def theBrother (s : Sit) : Person :=
  if IsBrother .bill s then .bill else if IsBrother .charlie s then .charlie else .mary

private def g₀ : SituationAssignment W Unit := λ _ => sActual

/-- The reading of an LF of *Mary believes my brother is a spy*: the noun phrase's and the
verb's situation pronouns are interpreted at the situations their binders supply. -/
def spyReading (lf : LF) : Prop :=
  believeSit (λ _ => doxMary) Person.mary 2 (λ g => IsSpy (theBrother (g lf.noun)) (g lf.verb))
    g₀ sActual

instance (lf : LF) : Decidable (spyReading lf) := by
  unfold spyReading believeSit; infer_instance

/-- The two licensed LFs are distinct readings: with the brother read at the matrix situation
the sentence is true, and with everything read in the belief world it is false. -/
theorem dpDeRe_true_allDeDicto_false : spyReading dpDeRe ∧ ¬ spyReading allDeDicto := by
  decide

/-- The reading of an LF of *Mary believes John is Canadian*. -/
def canadianReading (lf : LF) : Prop :=
  believeSit (λ _ => doxMary) Person.mary 2 (λ g => IsCanadian .john (g lf.verb)) g₀ sActual

instance (lf : LF) : Decidable (canadianReading lf) := by
  unfold canadianReading believeSit; infer_instance

/-- Generalization X has empirical bite: the LF reading the predicate at the matrix situation
would make the sentence true on the model, but it is excluded, and the licensed LF is
false. -/
theorem canadian_predicate_de_re_excluded :
    canadianReading predicateDeRe ∧ ¬ predicateDeRe.GenX ∧ ¬ canadianReading allDeDicto := by
  decide

/-! ### Generalization Y -/

/-- Three rounds of the game. -/
inductive Round where
  | r1
  | r2
  | r3
  deriving DecidableEq

/-- Situations with a round as their time coordinate. -/
abbrev RSit := Index W Round

/-- Bill won the first two rounds in fact and every round in Mary's belief world. -/
def Won (p : Person) (s : RSit) : Prop :=
  match p, s.world, s.time with
  | .bill, .actual, .r1 => True
  | .bill, .actual, .r2 => True
  | .bill, .belief, _ => True
  | _, _, _ => False

instance (p : Person) (s : RSit) : Decidable (Won p s) := by
  unfold Won; cases p <;> cases s.world <;> cases s.time <;> infer_instance

/-- The rounds of a situation's world. -/
def rounds (s : RSit) : List RSit := [⟨s.world, .r1⟩, ⟨s.world, .r2⟩, ⟨s.world, .r3⟩]

/-- Mary's doxastic alternatives, round by round. -/
def doxMaryR : RSit → List RSit := λ s => [⟨.belief, s.time⟩]

private def g₃ : SituationAssignment W Round := λ _ => ⟨.actual, .r1⟩

/-- The reading of an LF of *Mary thinks my brother always won the game*: the adverb ranges
over the rounds of the situation its binder supplies. -/
def alwaysReading (q : QLF) : Prop :=
  believeSit (λ _ => doxMaryR) Person.mary 2
    (λ g => alwaysAt rounds (g q.quant) 3 (λ g' => Won .bill (g' 3)) g) g₃ ⟨.actual, .r1⟩

instance (q : QLF) : Decidable (alwaysReading q) := by
  unfold alwaysReading believeSit alwaysAt; infer_instance

/-- Generalization Y licenses the LF whose adverb ranges over the belief world's rounds, on
which the sentence is true, and excludes the one ranging over the actual rounds, on which it
is false. -/
theorem genY :
    (⟨2⟩ : QLF).GenY ∧ alwaysReading ⟨2⟩ ∧ ¬ (⟨1⟩ : QLF).GenY ∧ ¬ alwaysReading ⟨1⟩ := by
  decide

end Percus2000
