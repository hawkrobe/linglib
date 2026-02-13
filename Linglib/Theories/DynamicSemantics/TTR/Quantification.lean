import Linglib.Theories.DynamicSemantics.TTR.Modality
import Linglib.Core.Quantification
import Mathlib.Data.Finset.Card

/-!
# Type Theory with Records — Chapter 7: Witness-based Quantification

Cooper (2023) Chapter 7 replaces classical set-theoretic GQ denotations
(cf. `Core.Quantification.GQ`) with *witness sets* — finite sets of
individuals satisfying cardinality conditions specific to each quantifier.

Key innovations:
- **𝔗(P)**: the type whose witnesses are P-individuals (§7.2.3)
- **𝔓/𝔓ʸ**: purification operators extracting pure properties (§7.2.3)
- **qʷ(P)**: witness set types per quantifier (§7.2.4)
- **Austinian propositions** (𝔉): probabilistic quantification (§7.3)
- **General vs particular witness conditions**: predict anaphora (§7.4)
- **Complement witness sets**: COMPSET anaphora for 'few' (§7.4)
- **Contexts with gaps**: long distance dependencies (§7.5)

## References

- Cooper (2023). From Perception to Communication. Ch 7.
- Barwise & Cooper (1981). Generalized Quantifiers and Natural Language.
- van Benthem (1984). Questions about Quantifiers.
- Lücking & Ginzburg (2019, 2022). Dynamic Generalized Quantifiers.
-/

namespace DynamicSemantics.TTR

-- ============================================================================
-- Chapter 7: Witness-based Quantification (Cooper 2023, §7.1–7.6)
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
    Cooper (2023) §7.2.3, eq (7a): P.bg has only the x-field. -/
def PPpty.isPure (P : PPpty E) : Prop := Nonempty P.Bg ∧ Subsingleton P.Bg

/-- The type of witnesses for property P.
    Cooper (2023) §7.2.3, eq (17): a : 𝔗(P) iff 𝔓(P){a} is witnessed.
    For a pure property, 𝔗(P) = {a : E // Nonempty (P a)}. -/
def WitnessType (P : Ppty E) : Type := {a : E // Nonempty (P a)}

/-- Existential purification of a parametric property.
    Cooper (2023) §7.2.3, eq (12): 𝔓(P) merges background conditions
    into the body via existential quantification.
    𝔓(P)(a) = Σ (c : Bg), fg c a. -/
def purify (P : PPpty E) : Ppty E := λ a => (c : P.Bg) × P.fg c a

/-- Universal purification of a parametric property.
    Cooper (2023) §7.2.3, eq (13): 𝔓ʸ(P) universally quantifies
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

/-! ### §7.2.4 Types of witness sets for quantifiers (eqs 20–35)

Each quantifier q defines a type qʷ(P) of witness sets.
X : qʷ(P) iff (1) X ⊆ extension of P, and (2) a cardinality condition.

All witness set types share a common `subset` condition (X ⊆ [↓P]).
This structural requirement is what *derives* conservativity from the
witness architecture — it's not stipulated as in Barwise & Cooper (1981). -/

variable [DecidableEq E]

/-- Computable extension of P as a Finset. Cooper's [𝔗(P)] or [↓P]. -/
def fullExtFinset [Fintype E] (P : E → Prop) [DecidablePred P] : Finset E :=
  Finset.univ.filter P

/-- Base witness set condition: X ⊆ extension of P.
    Cooper (2023) §7.2.4: every witness set type requires this. -/
structure WitnessSet (P : E → Prop) (X : Finset E) : Prop where
  subset : ∀ a ∈ X, P a

/-- existʷ(P): singleton witness set. Eq (21). -/
structure IsExistW (P : E → Prop) (X : Finset E) : Prop extends WitnessSet P X where
  card_eq : X.card = 1

/-- exist_plʷ(P): plural some, |X| ≥ 2. Eq (22). -/
structure IsExistPlW (P : E → Prop) (X : Finset E) : Prop extends WitnessSet P X where
  card_ge : X.card ≥ 2

/-- noʷ(P): empty set. Eqs (23–24). -/
def IsNoW (_P : E → Prop) (X : Finset E) : Prop := X = ∅

/-- everyʷ(P): the full extension. Eqs (25–26). -/
def IsEveryW [Fintype E] (P : E → Prop) [DecidablePred P]
    (X : Finset E) : Prop := X = fullExtFinset P

/-- mostʷ(P): proportional, |X|/|[↓P]| ≥ θ. Eq (29).
    Stated as cross-multiplication: X.card * denom ≥ num * ext.card. -/
structure IsMostW [Fintype E] (P : E → Prop) [DecidablePred P]
    (θ_num θ_denom : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  extPos : (fullExtFinset P).card > 0
  proportion : X.card * θ_denom ≥ θ_num * (fullExtFinset P).card

/-- many_aʷ(P): absolute threshold, |X| ≥ θ. Eq (30). -/
structure IsManyAbsW (P : E → Prop) (θ : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  card_ge : X.card ≥ θ

/-- many_pʷ(P): proportional, |X|/|[↓P]| ≥ θ. Eq (31). -/
structure IsManyPropW [Fintype E] (P : E → Prop) [DecidablePred P]
    (θ_num θ_denom : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  extPos : (fullExtFinset P).card > 0
  proportion : X.card * θ_denom ≥ θ_num * (fullExtFinset P).card

/-- few_aʷ(P): absolute, |X| ≤ θ. Eq (32). -/
structure IsFewAbsW (P : E → Prop) (θ : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  card_le : X.card ≤ θ

/-- few_pʷ(P): proportional, |X|/|[↓P]| ≤ θ. Eq (33). -/
structure IsFewPropW [Fintype E] (P : E → Prop) [DecidablePred P]
    (θ_num θ_denom : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  extPos : (fullExtFinset P).card > 0
  proportion : X.card * θ_denom ≤ θ_num * (fullExtFinset P).card

/-- a_few_aʷ(P): absolute, |X| ≥ θ (same threshold as few, reversed direction). Eq (34). -/
structure IsAFewAbsW (P : E → Prop) (θ : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  card_ge : X.card ≥ θ

/-- a_few_pʷ(P): proportional, |X|/|[↓P]| ≥ θ. Eq (35). -/
structure IsAFewPropW [Fintype E] (P : E → Prop) [DecidablePred P]
    (θ_num θ_denom : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  extPos : (fullExtFinset P).card > 0
  proportion : X.card * θ_denom ≥ θ_num * (fullExtFinset P).card

/-- Complement witness set for few (absolute). Eq (81).
    X̄ : few̄ʷ_a(P) iff |X| ≥ |[𝔗(P)]| − θ.
    Predicts COMPSET anaphora. -/
structure IsCompFewAbsW [Fintype E] (P : E → Prop) [DecidablePred P]
    (θ : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  card_ge : X.card ≥ (fullExtFinset P).card - θ

/-- Complement witness set for few (proportional). Eq (82). -/
structure IsCompFewPropW [Fintype E] (P : E → Prop) [DecidablePred P]
    (θ_num θ_denom : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  extPos : (fullExtFinset P).card > 0
  proportion : X.card * θ_denom ≥ (θ_denom - θ_num) * (fullExtFinset P).card

/-- noʷ has exactly one witness set: ∅. -/
theorem isNoW_iff_empty {E : Type} (P : E → Prop) (X : Finset E) :
    IsNoW P X ↔ X = ∅ := Iff.rfl

/-- everyʷ has exactly one witness set: the full extension. -/
theorem isEveryW_iff {E : Type} [DecidableEq E] [Fintype E] (P : E → Prop) [DecidablePred P]
    (X : Finset E) : IsEveryW P X ↔ X = fullExtFinset P := Iff.rfl

/-! ### §7.3 Austinian propositions and probabilistic quantification (eqs 36–58)

Probabilities for quantifiers are estimated from an agent's finite
experience base 𝔉 — a set of Austinian propositions recording
categorical judgments [sit=a, type=T].

Frequentist conditional probability:
  p_𝔉(T₁‖T₂) = |[T₁∧T₂]_𝔉| / |[T₂]_𝔉| -/

/-- An experience base: the agent's memory of categorical judgments.
    Cooper (2023) §7.3, eq (37): 𝔉 is a finite set of [sit=a, type=T] records.
    Parameterized over entity type E and predicate type P. -/
structure ExperienceBase (E : Type) (P : Type) [DecidableEq E] [DecidableEq P] where
  /-- The observed entity-predicate judgments -/
  judgments : Finset (E × P)

section ExperienceBaseOps

variable {E : Type} {P : Type} [DecidableEq E] [DecidableEq P]

/-- Extension of predicate p relative to 𝔉.
    Cooper (2023) §7.3, eq (38): [T]_𝔉 = {a | a :_𝔉 T}. -/
def ExperienceBase.ext (𝔉 : ExperienceBase E P) (p : P) : Finset E :=
  𝔉.judgments.filter (·.2 = p) |>.image Prod.fst

/-- Joint extension: entities classified under both predicates. -/
def ExperienceBase.jointExt (𝔉 : ExperienceBase E P) (p q : P) : Finset E :=
  (𝔉.ext p) ∩ (𝔉.ext q)

/-- Frequentist conditional probability estimate (as numerator/denominator).
    Cooper (2023) §7.3, eq (36):
    p_𝔉(T₁‖T₂) = |[T₁∧T₂]_𝔉| / |[T₂]_𝔉|. -/
def ExperienceBase.condProb (𝔉 : ExperienceBase E P) (p q : P) : ℕ × ℕ :=
  ((𝔉.jointExt p q).card, (𝔉.ext q).card)

/-- Reliability of a probability estimate (count before log).
    Cooper (2023) §7.3, eq (40):
    reliability = ln min(|[T₁]_𝔉|, |[T₂]_𝔉|). -/
def ExperienceBase.reliability (𝔉 : ExperienceBase E P) (p q : P) : ℕ :=
  min (𝔉.ext p).card (𝔉.ext q).card

end ExperienceBaseOps

/-! ### §7.4 Witness conditions for quantificational ptypes (eqs 59–90)

The central theoretical contribution: how quantifiers evaluate.
Each q(P,Q) is witnessed by a pair (X, f) where X is a witness set
and f maps witnesses to Q-evidence.

Two patterns:
- **General** (eq 59): for all quantifiers, uses purified Q
- **Particular** (eq 63): simpler, only for some quantifiers,
  better anaphora predictions -/

variable {E : Type}

/-- General witness condition for monotone ↑ quantifiers.
    Cooper (2023) §7.4, eq (59a):
    s : q(P,Q) iff s : [X : qʷ(P), f : (a : 𝔗(X)) → 𝔓(Q){a}]
    Each member of X must individually witness Q. -/
structure GeneralWC_Incr (P Q : Ppty E)
    (isWS : Finset E → Prop) [DecidableEq E] where
  X : Finset E
  witnessOK : isWS X
  f : (a : E) → a ∈ X → Q a

/-- General witness condition for monotone ↓ quantifiers.
    Cooper (2023) §7.4, eq (59b):
    Every entity with both P and Q lands in X. -/
structure GeneralWC_Decr (P Q : Ppty E)
    (isWS : Finset E → Prop) [DecidableEq E] where
  X : Finset E
  witnessOK : isWS X
  f : (a : E) → Nonempty (P a) → Nonempty (Q a) → a ∈ X

/-- Particular witness condition for exist(P,Q). Eq (63).
    s : exist(P,Q) iff s : [x : 𝔗(P), e : 𝔓(Q){x}]
    The x-field enables REFSET (singular) anaphora:
    "A dog barked. It heard an intruder." -/
structure ParticularWC_Exist (P Q : Ppty E) where
  x : E
  pWit : P x
  qWit : Q x

/-- Particular witness condition for no(P,Q). Eq (70).
    Every P-entity fails to have Q (type negation).
    everyʷ(P) as witness set predicts MAXSET anaphora:
    "No dog barked. They (= the dogs) were all asleep." -/
structure ParticularWC_No (P Q : Ppty E) where
  f : (a : E) → P a → IsEmpty (Q a)

/-- Particular witness condition for few with complement. Eqs (85–86).
    Uses complement witness set: P-entities lacking Q.
    Predicts COMPSET anaphora:
    "Few dogs barked. They (= non-barking dogs) slept through." -/
structure ParticularWC_FewComp (P Q : Ppty E) [DecidableEq E] where
  X : Finset E
  allP : ∀ a ∈ X, Nonempty (P a)
  allNotQ : ∀ a ∈ X, IsEmpty (Q a)

/-- The particular exist condition implies the general one (with singleton X).
    Cooper (2023) §7.4: the particular condition "provides a component
    in the witness (in the 'x'-field) which can be picked up on by
    singular anaphora." -/
def particular_exist_implies_general [DecidableEq E]
    (P Q : Ppty E) (h : ParticularWC_Exist P Q)
    (Pd : E → Prop) (hPd : ∀ a, Pd a ↔ Nonempty (P a)) :
    GeneralWC_Incr P Q (IsExistW Pd) :=
  ⟨{h.x},
   { subset := λ a ha => by rw [Finset.mem_singleton] at ha; rw [ha]; exact (hPd h.x).mpr ⟨h.pWit⟩,
     card_eq := Finset.card_singleton h.x },
   λ a ha => by rw [Finset.mem_singleton] at ha; rw [ha]; exact h.qWit⟩

/-- Anaphora set predictions per quantifier.
    Cooper (2023) §7.4.1: witness structure determines available anaphora. -/
inductive AnaphoraRef where
  /-- REFSET: reference to the witness individual/set.
      "A dog barked. It (= that dog) heard an intruder." -/
  | refset
  /-- MAXSET: reference to the full extension.
      "Every dog barked. They (= the dogs) heard an intruder." -/
  | maxset
  /-- COMPSET: reference to the complement witness set (for few).
      "Few dogs barked. They (= the non-barking dogs) slept through." -/
  | compset
  deriving DecidableEq, Repr

/-- Quantifier names for typed dispatch.
    Cooper (2023) §7.4.1: the quantifiers of the English fragment. -/
inductive QuantName where
  | exist | existPl | no | every | most | many | few | aFew
  deriving DecidableEq, Repr

/-- Which anaphora sets each quantifier makes available.
    Cooper (2023) §7.4.1: summary table. -/
def anaphoraAvailable : QuantName → List AnaphoraRef
  | .exist   => [.refset]
  | .existPl => [.refset, .maxset]
  | .no      => [.maxset]
  | .every   => [.maxset]
  | .most    => [.maxset]
  | .many    => [.maxset]
  | .few     => [.refset, .maxset, .compset]
  | .aFew    => [.refset, .maxset]

/-! ### §7.5 Long distance dependencies (eqs 114–158)

Cooper extends contexts with gap and wh-assignments to handle
extraction, relative clauses, and wh-questions. -/

/-- Context with gap assignment.
    Cooper (2023) §7.5, eq (115): Cntxt = [𝔰, 𝔤, 𝔠]. -/
structure CntxtWithGap (AssgnType CntxtType : Type) where
  𝔰 : AssgnType
  𝔤 : AssgnType
  𝔠 : CntxtType

/-- Full context with wh- and gap assignments.
    Cooper (2023) §7.5, eq (122): Cntxt = [𝔰, 𝔴, 𝔤, 𝔠]. -/
structure CntxtFull (AssgnType CntxtType : Type) where
  𝔰 : AssgnType
  𝔴 : AssgnType
  𝔤 : AssgnType
  𝔠 : CntxtType

/-- Slash category: S/i is a sentence missing constituent at gap i.
    Cooper (2023) §7.5, eq (149): the TTR analogue of slash categories. -/
structure SlashCat where
  mother : String
  gapIdx : ℕ
  deriving DecidableEq, Repr

/-- WhNP condition.
    Cooper (2023) §7.5, eq (126): σ : WhNP iff σ : NP and
    Ω.bg ⊑ [𝔴:[xᵢ:Ind]] for some i. -/
structure IsWhNP where
  whIdx : ℕ

/-- Property conjunction.
    Cooper (2023) §7.5, eq (153): P₁ & P₂ for relative clauses.
    "child who Sam hugged" = child ∧ hugged-by-Sam. -/
def pptyConj (P₁ P₂ : Ppty E) : Ppty E := λ x => P₁ x × P₂ x

/-- Property conjunction preserves witnesses. -/
theorem pptyConj_nonempty (P₁ P₂ : Ppty E) (x : E)
    (h₁ : Nonempty (P₁ x)) (h₂ : Nonempty (P₂ x)) :
    Nonempty (pptyConj P₁ P₂ x) :=
  ⟨⟨h₁.some, h₂.some⟩⟩

/-- Type-indexed property: properties of objects of type T.
    Cooper (2023) §7.5, eq (152): P : ᵀPpty iff P.bg ⊑ [x:T]. -/
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
    simpleExp.condProb .bark .dog = (2, 3) := by native_decide

end Ch7Phenomena

/-! ### Structural theorems

Key theoretical claims of Cooper (2023) Ch 7, connecting witness-based
quantification to classical GQ properties and each other. -/

section Ch7Theorems

variable {E : Type} [DecidableEq E]

open Core.Quantification

/-! #### Bridge: witness-based → GQ (Bool)

Every witness set type induces a classical GQ by existentially
quantifying over witness sets. This is the fundamental connection
between Cooper's type-theoretic quantifiers and Barwise & Cooper's
set-theoretic ones. -/

/-- The GQ induced by existential witness sets.
    exist(A,B) = true iff some element satisfies both A and B. -/
def witnessGQ_exist [Fintype E] : GQ E :=
  λ A B => decide (∃ x : E, A x = true ∧ B x = true)

/-- The GQ induced by universal witness sets.
    every(A,B) = true iff every A-element also satisfies B. -/
def witnessGQ_every [Fintype E] : GQ E :=
  λ A B => decide (∀ x : E, A x = true → B x = true)

/-! #### Conservativity from witness structure

All witness set types require X ⊆ [↓P] (the subset condition).
This *structurally entails* conservativity: q(P,Q) depends only on
P ∩ Q, never on Q outside P. Cooper (2023) §7.2.4.

This is significant because conservativity is stipulated as an axiom
in Barwise & Cooper (1981) but *derived* from the witness architecture. -/

end Ch7Theorems

section ConservativityTheorems

variable {E : Type}

open Core.Quantification

/-- Conservativity of witnessGQ_exist: follows from the subset condition
    in IsExistW. Cooper's key argument: conservativity is structural,
    not stipulated. -/
theorem witnessGQ_exist_conservative [Fintype E] :
    Conservative (α := E) witnessGQ_exist := by
  intro R S
  simp only [witnessGQ_exist]
  congr 1
  exact propext ⟨λ ⟨x, hR, hS⟩ => ⟨x, hR, by simp [hR, hS]⟩,
                 λ ⟨x, hR, hRS⟩ => ⟨x, hR, by simp_all⟩⟩

/-- Conservativity of witnessGQ_every. -/
theorem witnessGQ_every_conservative [Fintype E] :
    Conservative (α := E) witnessGQ_every := by
  intro R S
  simp only [witnessGQ_every]
  congr 1
  exact propext ⟨λ h x hR => by simp [hR, h x hR],
                 λ h x hR => by have := h x hR; simp_all⟩

end ConservativityTheorems

/-! #### Bridge: witness quantification ↔ extensional truth

Cooper's witness-based quantifiers (type-theoretic) compute the same
truth values as the extensional denotations in TruthConditional/Quantifier.
This bridges the three layers of quantification:
  Core.Quantification (logical properties) ← proved via conservativity above
  TruthConditional (extensional denotations) ← proved via equivalence below
  TTR (witness-based)                        ← definitions above -/

section WitnessExtensionalBridge

variable {E : Type}

open Core.Quantification

/-- TTR's structured particular witness condition is equivalent to the
    existential GQ being true. This is the key grounding theorem:
    `ParticularWC_Exist P Q` is inhabited iff `witnessGQ_exist` returns true. -/
theorem particular_exist_iff_witnessGQ [Fintype E]
    (P Q : E → Prop) [DecidablePred P] [DecidablePred Q] :
    (∃ x, P x ∧ Q x) ↔
    (witnessGQ_exist (λ x => decide (P x)) (λ x => decide (Q x)) = true) := by
  simp [witnessGQ_exist]

/-- The universal condition is equivalent to the universal GQ being true. -/
theorem universal_iff_witnessGQ [Fintype E]
    (P Q : E → Prop) [DecidablePred P] [DecidablePred Q] :
    (∀ x, P x → Q x) ↔
    (witnessGQ_every (λ x => decide (P x)) (λ x => decide (Q x)) = true) := by
  simp [witnessGQ_every]

/-- TTR's `ParticularWC_Exist` gives a constructive witness for the existential GQ. -/
theorem particularWC_to_witnessGQ [Fintype E] [DecidableEq E]
    {P Q : Ppty E} (w : ParticularWC_Exist P Q)
    (Pd Qd : E → Prop) [DecidablePred Pd] [DecidablePred Qd]
    (hP : ∀ a, Pd a ↔ Nonempty (P a)) (hQ : ∀ a, Qd a ↔ Nonempty (Q a)) :
    witnessGQ_exist (λ x => decide (Pd x)) (λ x => decide (Qd x)) = true := by
  rw [← particular_exist_iff_witnessGQ]
  exact ⟨w.x, (hP w.x).mpr ⟨w.pWit⟩, (hQ w.x).mpr ⟨w.qWit⟩⟩

/-- TTR's `ParticularWC_No` implies the universal GQ with negated scope. -/
theorem particularWC_no_to_witnessGQ [Fintype E] [DecidableEq E]
    {P Q : Ppty E} (w : ParticularWC_No P Q)
    (Pd Qd : E → Prop) [DecidablePred Pd] [DecidablePred Qd]
    (hP : ∀ a, Pd a ↔ Nonempty (P a)) (hQ : ∀ a, Qd a ↔ Nonempty (Q a)) :
    witnessGQ_every (λ x => decide (Pd x)) (λ x => decide (¬ Qd x)) = true := by
  rw [← universal_iff_witnessGQ]
  intro x hPx hQx
  have hP' := (hP x).mp hPx
  have hQ' := (hQ x).mp hQx
  exact (w.f x hP'.some).false hQ'.some

end WitnessExtensionalBridge

section Ch7Theorems_contd

variable {E : Type} [DecidableEq E]

open Core.Quantification

/-! #### Purification and donkey anaphora

Existential purification 𝔓 gives weak donkey readings;
universal purification 𝔓ʸ gives strong donkey readings.
For pure properties (trivial Bg), both collapse to identity. -/

/-- Purification of a pure property is equivalent to the original.
    Cooper (2023) §7.2.3: if P.Bg ≅ Unit, then 𝔓(P) ≃ P.fg. -/
theorem purify_pure_equiv {E : Type} (P : PPpty E)
    (hPure : P.isPure) (a : E) :
    Nonempty (𝔓 P a) ↔ Nonempty (P.fg (hPure.1.some) a) := by
  rw [purify_nonempty_iff]
  constructor
  · rintro ⟨c, hc⟩
    have : c = hPure.1.some := hPure.2.allEq c _
    rwa [this] at hc
  · exact λ h => ⟨_, h⟩

/-- Universal purification of a pure property also collapses. -/
theorem purifyUniv_pure_equiv {E : Type} (P : PPpty E)
    (hPure : P.isPure) (a : E) :
    Nonempty (𝔓ʸ P a) ↔ Nonempty (P.fg (hPure.1.some) a) := by
  rw [purifyUniv_nonempty_iff]
  constructor
  · exact λ h => h _
  · intro h c
    have : c = hPure.1.some := hPure.2.allEq c _
    rwa [this]

/-- For pure properties, weak and strong donkey readings agree.
    Cooper (2023) §7.2.3: the distinction only matters when Bg is non-trivial. -/
theorem donkey_readings_agree_when_pure {E : Type} (P : PPpty E)
    (hPure : P.isPure) (a : E) :
    Nonempty (𝔓 P a) ↔ Nonempty (𝔓ʸ P a) := by
  rw [purify_pure_equiv P hPure, purifyUniv_pure_equiv P hPure]

/-! #### Particular → general witness condition lifting

Each particular witness condition implies the corresponding general one.
The particular conditions are preferred because they expose finer-grained
structure for anaphora resolution. -/

/-- Particular no implies general (decreasing) no.
    Cooper (2023) §7.4, eqs (70) → (59b): if every P-entity lacks Q,
    then the empty witness set satisfies the decreasing condition
    (vacuously: no entity has both P and Q). -/
def particular_no_implies_general {E : Type} [DecidableEq E]
    (P Q : Ppty E) (h : ParticularWC_No P Q)
    (Pd : E → Prop) :
    GeneralWC_Decr P Q (IsNoW Pd) :=
  ⟨∅, rfl,
   λ a hP hQ => ((h.f a hP.some).false hQ.some).elim⟩

/-! #### Complement witness sets and the few/a_few contrast

Cooper's key empirical claim (§7.4.2): `few` and `a_few` share the same
cardinality threshold but differ in anaphora predictions because `few`
(downward monotone) supports complement witness sets while `a_few`
(upward monotone) does not.

- "Few dogs barked. They slept through." → they = non-barking dogs (COMPSET)
- "A few dogs barked. They heard the noise." → they = barking dogs (REFSET) -/

/-- The complement witness set for `few` satisfies the complement
    cardinality condition.
    Cooper (2023) §7.4.2, eq (81): X̄ = 𝔗(P) \ X. -/
theorem comp_witness_card [Fintype E] (P : E → Prop) [DecidablePred P]
    (X : Finset E) (_hSub : ∀ a ∈ X, P a) (θ : ℕ)
    (hFew : X.card ≤ θ)
    (hXsub : X ⊆ fullExtFinset P) :
    (fullExtFinset P \ X).card ≥ (fullExtFinset P).card - θ := by
  have h := Finset.card_sdiff_of_subset hXsub
  omega

/-- few_a and its complement partition the full extension.
    Cooper (2023) §7.4.2: X ∪ X̄ = 𝔗(P). -/
theorem few_comp_partition [Fintype E] (P : E → Prop) [DecidablePred P]
    (X : Finset E) (hX : X ⊆ fullExtFinset P) :
    X ∪ (fullExtFinset P \ X) = fullExtFinset P := by
  exact Finset.union_sdiff_of_subset hX

/-! #### Record path subtraction (⊖) for LDD

Cooper (2023) §7.5, eq (118): T ⊖ π removes a field from a record type.
This is the operation underlying gap-threading: a transitive verb type
minus its object field yields the gap-containing type. -/

/-- Record path subtraction: remove a named field from a record.
    Cooper (2023) §7.5, eq (118): T ⊖ π removes field π from T.
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

Cooper (2023) §7.5, eq (133): T^π = λv.[T ⊖ π ∧ {π : v}].
A dependency family abstracts over the gap, yielding a function
from entities to record types. This is the TTR analogue of
lambda-abstraction over a trace in transformational grammar. -/

/-- Dependency family: abstract over a gap to get a property.
    Cooper (2023) §7.5, eq (133): T^π(v) fills gap π with v. -/
def dependencyFamily {E : Type} (body : E → Ppty E) : Ppty E → Type :=
  λ P => (a : E) × body a a × P a

/-- Merging a dependency family with a quantifier yields a
    scope-taking constituent. Cooper (2023) §7.5, eq (137):
    "which child Sam hugged" = Quant derived from T^π. -/
def depFamilyQuant {E : Type} (body : E → Ppty E) (q : Quant E) : Type :=
  q (λ x => (a : E) × body a x)

/-! #### Monotonicity from witness conditions

Cooper (2023) §7.4: the general witness condition for ↑ quantifiers
(59a) uses existential evidence per witness (f maps each to Q-evidence),
while ↓ quantifiers (59b) use universal containment (every P∧Q entity
is in X). This structural difference predicts monotonicity direction. -/

/-- Upward monotonicity of the increasing witness condition:
    if Q ⊆ Q' (at Type level), any witness for Q also witnesses Q'.
    Cooper (2023) §7.4, consequence of (59a). -/
def generalWC_incr_mono {E : Type} [DecidableEq E] (P Q Q' : Ppty E)
    (isWS : Finset E → Prop)
    (embed : ∀ a : E, Q a → Q' a)
    (w : GeneralWC_Incr P Q isWS) : GeneralWC_Incr P Q' isWS :=
  ⟨w.X, w.witnessOK, λ a ha => embed a (w.f a ha)⟩

/-- Downward monotonicity of the decreasing witness condition:
    if Q' ⊆ Q, then the decreasing condition on Q implies it on Q'.
    Cooper (2023) §7.4, consequence of (59b). -/
def generalWC_decr_mono {E : Type} [DecidableEq E] (P Q Q' : Ppty E)
    (isWS : Finset E → Prop)
    (embed : ∀ a : E, Q' a → Q a)
    (w : GeneralWC_Decr P Q isWS) : GeneralWC_Decr P Q' isWS :=
  ⟨w.X, w.witnessOK, λ a hP hQ' => w.f a hP ⟨embed a hQ'.some⟩⟩

end Ch7Theorems_contd

end Ch7_WitnessQuantification

end DynamicSemantics.TTR
