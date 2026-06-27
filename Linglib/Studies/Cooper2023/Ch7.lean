import Linglib.Semantics.TypeTheoretic.Discourse
import Linglib.Semantics.TypeTheoretic.WitnessQuantification
import Linglib.Semantics.Quantification.Counting
import Mathlib.Data.Finset.Card

/-!
# Cooper (2023) Ch. 7 — Witness-based quantification

[cooper-2023]
[barwise-cooper-1981] [van-benthem-1984]

Cooper's *From Perception to Communication* Ch. 7 replaces classical
set-theoretic GQ denotations (cf. `Quantification.GQ`) with *witness
sets* — finite sets of individuals satisfying cardinality conditions
specific to each quantifier. The reusable substrate (witness-set types,
particular/general witness conditions, induced GQ denotations,
conservativity proofs, anaphora-availability tables) lives in
`Linglib/Semantics/TypeTheoretic/WitnessQuantification.lean`; this file
contains Cooper's chapter-specific deployment.

## Main definitions

* `PPpty.isPure`, `WitnessType`, `WitnessTypeP` — pure-property witness types
  (§7.2.3).
* `purify` (`𝔓`), `purifyUniv` (`𝔓ʸ`) — Cooper's purification operators
  (§7.2.3) extracting pure properties for weak/strong donkey readings.
* `ExperienceBase` and friends — Austinian-propositions / frequentist
  conditional-probability machinery (§7.3).
* `pptyConj`, `CntxtWithGap`, `CntxtFull`, `SlashCat`, `IsWhNP`,
  `TypedPpty`, `recSubtract`, `dependencyFamily`, `depFamilyQuant` —
  long-distance-dependency apparatus (§7.5).

## Main statements

* `purify_trivial`, `purify_nonempty_iff`, `purifyUniv_nonempty_iff` —
  characterising lemmas for the purification operators.
* `purify_pure_equiv`, `purifyUniv_pure_equiv`,
  `donkey_readings_agree_when_pure` — for pure properties, weak and
  strong donkey readings coincide.
* Phenomenon-anchored theorems (`dog_ext_card`, `aDogBarks`,
  `not_noDogBarks`, `few_has_compset`, `a_few_no_compset`,
  `bark_given_dog_prob`) — Cooper's worked examples against the
  graduated witness-set substrate.

-/

namespace Cooper2023Ch7

open Semantics.TypeTheoretic
  (Ppty PPpty Parametric Quant propT
   WitnessSet IsExistW IsExistPlW IsNoW IsEveryW IsMostW IsManyAbsW
   IsManyPropW IsFewAbsW IsFewPropW IsAFewAbsW IsAFewPropW IsCompFewAbsW
   IsCompFewPropW fullExtFinset AnaphoraRef QuantName anaphoraAvailable
   GeneralWC_Incr GeneralWC_Decr ParticularWC_Exist ParticularWC_No
   ParticularWC_FewComp witnessGQ_exist witnessGQ_every)

-- ============================================================================
-- Chapter 7: Witness-based Quantification (§7.1–7.6)
-- ============================================================================

section Ch7_WitnessQuantification

/-! ### §7.2.3 Pure properties, purification, and 𝔗(P) (eqs 11–19)

A parametric property P : PPpty E has background P.Bg and foreground P.fg.
P is *pure* when Bg is trivial (≅ Unit): no extra background constraints.

Purification folds background conditions into the property body:
- 𝔓(P): existential — ∃ context satisfying bg, body holds (weak donkey)
- 𝔓ʸ(P): universal — ∀ contexts satisfying bg, body holds (strong donkey) -/

variable {E : Type}

/-- A parametric property is *pure* when its background is trivial.
    §7.2.3, eq (7a): P.bg has only the x-field. -/
def PPpty.isPure (P : PPpty E) : Prop := Nonempty P.Bg ∧ Subsingleton P.Bg

/-- The type of witnesses for property P.
    §7.2.3, eq (17): a : 𝔗(P) iff 𝔓(P){a} is witnessed.
    For a pure property, 𝔗(P) = {a : E // Nonempty (P a)}. -/
def WitnessType (P : Ppty E) : Type := {a : E // Nonempty (P a)}

/-- Existential purification of a parametric property.
    §7.2.3, eq (12): 𝔓(P) merges background conditions
    into the body via existential quantification.
    𝔓(P)(a) = Σ (c : Bg), fg c a. -/
def purify (P : PPpty E) : Ppty E := λ a => (c : P.Bg) × P.fg c a

/-- Universal purification of a parametric property.
    §7.2.3, eq (13): 𝔓ʸ(P) universally quantifies
    over background contexts. Used for strong donkey readings. -/
def purifyUniv (P : PPpty E) : Ppty E := λ a => (c : P.Bg) → P.fg c a

/-- Notation for purification operators. -/
scoped prefix:max "𝔓" => purify
scoped prefix:max "𝔓ʸ" => purifyUniv

/-- For a trivial parametric property, purification adds only a Unit factor. -/
theorem purify_trivial (P : Ppty E) (a : E) :
    𝔓 (Parametric.trivial P) a = ((_ : Unit) × P a) := rfl

/-- Purified property is witnessed iff the original is witnessable
    under some context. -/
theorem purify_nonempty_iff (P : PPpty E) (a : E) :
    Nonempty (𝔓 P a) ↔ ∃ c : P.Bg, Nonempty (P.fg c a) := by
  constructor
  · rintro ⟨c, w⟩; exact ⟨c, ⟨w⟩⟩
  · rintro ⟨c, ⟨w⟩⟩; exact ⟨⟨c, w⟩⟩

/-- Universal purification: witnessed iff property holds under all contexts. -/
theorem purifyUniv_nonempty_iff (P : PPpty E) (a : E) :
    Nonempty (𝔓ʸ P a) ↔ ∀ c : P.Bg, Nonempty (P.fg c a) := by
  constructor
  · rintro ⟨f⟩ c; exact ⟨f c⟩
  · intro h; exact ⟨λ c => (h c).some⟩

/-- WitnessType for parametric properties via purification. -/
def WitnessTypeP (P : PPpty E) : Type := WitnessType (𝔓 P)

variable [DecidableEq E]

/-! ### §7.3 Austinian propositions and probabilistic quantification (eqs 36–58)

Probabilities for quantifiers are estimated from an agent's finite
experience base 𝔉 — a set of Austinian propositions recording
categorical judgments [sit=a, type=T].

Frequentist conditional probability:
  p_𝔉(T₁‖T₂) = |[T₁∧T₂]_𝔉| / |[T₂]_𝔉| -/

/-- An experience base: the agent's memory of categorical judgments.
    §7.3, eq (37): 𝔉 is a finite set of [sit=a, type=T] records.
    Parameterized over entity type E and predicate type P. -/
structure ExperienceBase (E : Type) (P : Type) [DecidableEq E] [DecidableEq P] where
  /-- The observed entity-predicate judgments -/
  judgments : Finset (E × P)

section ExperienceBaseOps

variable {E : Type} {P : Type} [DecidableEq E] [DecidableEq P]

/-- Extension of predicate p relative to 𝔉.
    §7.3, eq (38): [T]_𝔉 = {a | a :_𝔉 T}. -/
def ExperienceBase.ext (𝔉 : ExperienceBase E P) (p : P) : Finset E :=
  𝔉.judgments.filter (·.2 = p) |>.image Prod.fst

/-- Joint extension: entities classified under both predicates. -/
def ExperienceBase.jointExt (𝔉 : ExperienceBase E P) (p q : P) : Finset E :=
  (𝔉.ext p) ∩ (𝔉.ext q)

/-- Frequentist conditional probability estimate (as numerator/denominator).
    §7.3, eq (36):
    p_𝔉(T₁‖T₂) = |[T₁∧T₂]_𝔉| / |[T₂]_𝔉|. -/
def ExperienceBase.condProb (𝔉 : ExperienceBase E P) (p q : P) : ℕ × ℕ :=
  ((𝔉.jointExt p q).card, (𝔉.ext q).card)

/-- Reliability of a probability estimate (count before log).
    §7.3, eq (40):
    reliability = ln min(|[T₁]_𝔉|, |[T₂]_𝔉|). -/
def ExperienceBase.reliability (𝔉 : ExperienceBase E P) (p q : P) : ℕ :=
  min (𝔉.ext p).card (𝔉.ext q).card

end ExperienceBaseOps

variable {E : Type}

/-! ### §7.5 Long distance dependencies (eqs 114–158)

Cooper extends contexts with gap and wh-assignments to handle
extraction, relative clauses, and wh-questions. -/

/-- Context with gap assignment.
    §7.5: Cntxt = [𝔰, 𝔤, 𝔠] (the 3-field gap-aware context Cooper
    introduces around the slash-category discussion). -/
structure CntxtWithGap (AssgnType CntxtType : Type) where
  𝔰 : AssgnType
  𝔤 : AssgnType
  𝔠 : CntxtType

/-- Full context with wh- and gap assignments.
    §7.5: Cntxt = [𝔰, 𝔴, 𝔤, 𝔠] (the 4-field context for wh-extraction;
    Cooper's Ch. 8 eq (10) extends this to the 5-field {q, 𝔰, 𝔴, 𝔤, 𝔠}). -/
structure CntxtFull (AssgnType CntxtType : Type) where
  𝔰 : AssgnType
  𝔴 : AssgnType
  𝔤 : AssgnType
  𝔠 : CntxtType

/-- Slash category: S/i is a sentence missing constituent at gap i.
    §7.5, eq (149): the TTR analogue of slash categories. -/
structure SlashCat where
  mother : String
  gapIdx : ℕ
  deriving DecidableEq, Repr

/-- WhNP condition.
    §7.5, eq (149a): σ : WhNP iff σ : NP and
    Ω.bg ⊑ [𝔴:[xᵢ:Ind]] for some i. -/
structure IsWhNP where
  whIdx : ℕ

/-- Property conjunction.
    §7.5, eq (153): P₁ & P₂ for relative clauses.
    "child who Sam hugged" = child ∧ hugged-by-Sam. -/
def pptyConj (P₁ P₂ : Ppty E) : Ppty E := λ x => P₁ x × P₂ x

/-- Property conjunction preserves witnesses. -/
theorem pptyConj_nonempty (P₁ P₂ : Ppty E) (x : E)
    (h₁ : Nonempty (P₁ x)) (h₂ : Nonempty (P₂ x)) :
    Nonempty (pptyConj P₁ P₂ x) :=
  ⟨⟨h₁.some, h₂.some⟩⟩

/-- Type-indexed property: properties of objects of type T.
    §7.5, eq (152): P : ᵀPpty iff P.bg ⊑ [x:T]. -/
def TypedPpty (T : Type) := T → Type

/-- Type-indexed parametric property. -/
def TypedPPpty (T : Type) := Parametric (T → Type)

/-! ### Phenomena -/

section Ch7Phenomena

/-- Example: "a dog barks" (§7.4.1). -/
inductive DogWorld where | fido | rex | spot | luna
  deriving DecidableEq, Repr

instance : Fintype DogWorld where
  elems := {.fido, .rex, .spot, .luna}
  complete x := by cases x <;> decide

/-- Dog property. -/
def isDog : DogWorld → Prop
  | .fido => True | .rex => True | .spot => True | .luna => False

instance : DecidablePred isDog := λ x => by cases x <;> simp [isDog] <;> infer_instance

/-- Bark property. -/
def doesBark : DogWorld → Prop
  | .fido => True | .rex => False | .spot => True | .luna => False

instance : DecidablePred doesBark := λ x => by cases x <;> simp [doesBark] <;> infer_instance

/-- The full extension of isDog is {fido, rex, spot}. -/
theorem dog_ext_card : (fullExtFinset isDog).card = 3 := by decide

/-- Particular witness for "a dog barks": fido barks and is a dog. -/
def aDogBarks : ParticularWC_Exist
    (λ x : DogWorld => PLift (isDog x))
    (λ x => PLift (doesBark x)) where
  x := .fido
  pWit := ⟨trivial⟩
  qWit := ⟨trivial⟩

/-- "No dog barks" fails: fido is a dog that barks. -/
theorem not_noDogBarks :
    ¬ ParticularWC_No
      (λ x : DogWorld => PLift (isDog x))
      (λ x => PLift (doesBark x)) := by
  intro ⟨f⟩
  exact (f .fido ⟨trivial⟩).elim ⟨trivial⟩

/-- few predicts COMPSET; a_few does not. -/
theorem few_has_compset : AnaphoraRef.compset ∈ anaphoraAvailable .few := by decide
theorem a_few_no_compset : AnaphoraRef.compset ∉ anaphoraAvailable .aFew := by decide

/-- Predicate type for the dog example. -/
inductive DogPred where | dog | bark
  deriving DecidableEq, Repr

/-- Simple experience base: 3 dogs observed, 2 bark. -/
def simpleExp : ExperienceBase DogWorld DogPred where
  judgments := {(.fido, .dog), (.rex, .dog), (.spot, .dog),
                (.fido, .bark), (.spot, .bark)}

/-- Two of three dogs bark: p(bark‖dog) = 2/3. -/
theorem bark_given_dog_prob :
    simpleExp.condProb .bark .dog = (2, 3) := by decide

end Ch7Phenomena

/-! ### Structural theorems

Key theoretical claims of Ch 7, connecting witness-based
quantification to classical GQ properties and each other. -/

section Ch7Theorems

variable {E : Type} [DecidableEq E]

open Quantification

end Ch7Theorems

section Ch7Theorems_contd

variable {E : Type} [DecidableEq E]

open Quantification

/-! #### Purification and donkey anaphora

Existential purification 𝔓 gives weak donkey readings;
universal purification 𝔓ʸ gives strong donkey readings.
For pure properties (trivial Bg), both collapse to identity. -/

/-- Purification of a pure property is equivalent to the original.
    §7.2.3: if P.Bg ≅ Unit, then 𝔓(P) ≃ P.fg. -/
theorem purify_pure_equiv {E : Type} (P : PPpty E)
    (hPure : PPpty.isPure P) (a : E) :
    Nonempty (𝔓 P a) ↔ Nonempty (P.fg (hPure.1.some) a) := by
  rw [purify_nonempty_iff]
  constructor
  · rintro ⟨c, hc⟩
    have : c = hPure.1.some := hPure.2.allEq c _
    rwa [this] at hc
  · exact λ h => ⟨_, h⟩

/-- Universal purification of a pure property also collapses. -/
theorem purifyUniv_pure_equiv {E : Type} (P : PPpty E)
    (hPure : PPpty.isPure P) (a : E) :
    Nonempty (𝔓ʸ P a) ↔ Nonempty (P.fg (hPure.1.some) a) := by
  rw [purifyUniv_nonempty_iff]
  constructor
  · exact λ h => h _
  · intro h c
    have : c = hPure.1.some := hPure.2.allEq c _
    rwa [this]

/-- For pure properties, weak and strong donkey readings agree.
    §7.2.3: the distinction only matters when Bg is non-trivial. -/
theorem donkey_readings_agree_when_pure {E : Type} (P : PPpty E)
    (hPure : PPpty.isPure P) (a : E) :
    Nonempty (𝔓 P a) ↔ Nonempty (𝔓ʸ P a) := by
  rw [purify_pure_equiv P hPure, purifyUniv_pure_equiv P hPure]

/-! #### Record path subtraction (⊖) for LDD

§7.5, eq (118): T ⊖ π removes a field from a record type.
This is the operation underlying gap-threading: a transitive verb type
minus its object field yields the gap-containing type. -/

/-- Record path subtraction: remove a named field from a record.
    §7.5, eq (118): T ⊖ π removes field π from T.
    Encoded as filtering on a list of (label, type) pairs. -/
def recSubtract (fields : List (String × Type)) (path : String) :
    List (String × Type) :=
  fields.filter (λ p => decide (p.1 ≠ path))

/-- Subtraction removes exactly the targeted field. -/
theorem recSubtract_removes (fields : List (String × Type)) (path : String) :
    ∀ p ∈ recSubtract fields path, p.1 ≠ path := by
  intro p hp
  simp [recSubtract, List.mem_filter] at hp
  exact hp.2

/-- Subtraction preserves other fields. -/
theorem recSubtract_preserves (fields : List (String × Type)) (path label : String)
    (h : label ≠ path) :
    ∀ p ∈ fields, p.1 = label → p ∈ recSubtract fields path := by
  intro p hp hlabel
  simp [recSubtract, List.mem_filter]
  exact ⟨hp, hlabel ▸ h⟩

/-! #### Dependency families and generalization (T^π)

§7.5, eq (133): T^π = λv.[T ⊖ π ∧ {π : v}].
A dependency family abstracts over the gap, yielding a function
from entities to record types. This is the TTR analogue of
lambda-abstraction over a trace in transformational grammar. -/

/-- Dependency family: abstract over a gap to get a property.
    §7.5, eq (133): T^π(v) fills gap π with v. -/
def dependencyFamily {E : Type} (body : E → Ppty E) : Ppty E → Type :=
  λ P => (a : E) × body a a × P a

/-- Merging a dependency family with a quantifier yields a
    scope-taking constituent. §7.5, eq (137):
    "which child Sam hugged" = Quant derived from T^π. -/
def depFamilyQuant {E : Type} (body : E → Ppty E) (q : Quant E) : Type :=
  q (λ x => (a : E) × body a x)

end Ch7Theorems_contd

end Ch7_WitnessQuantification

end Cooper2023Ch7
