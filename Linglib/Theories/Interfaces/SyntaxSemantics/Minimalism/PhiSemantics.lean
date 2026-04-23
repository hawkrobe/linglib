import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic

/-!
# φ-Feature Semantics: Denotational Composition of Person and Animacy
@cite{toosarvandani-2023} @cite{harbour-2016} @cite{kratzer-2009}

Unified API for the semantic interpretation of φ-features (person, animacy,
number) as lattice predicates over a domain of individuals, following
@cite{toosarvandani-2023}'s analysis of Santiago Laxopa Zapotec.

## Key ideas

**Person and animacy features as nested sublattice predicates.** SPEAKER ⊂
PARTICIPANT ⊂ π (the full domain); ELDER ⊂ HUMAN ⊂ ANIMATE ⊂ π. Each feature
denotes a set of individual sums (nonempty subsets of atoms satisfying the
predicate).

**⊕ (oplus) composition** (@cite{harbour-2016}, @cite{kratzer-2009}): pointwise
lattice join of two feature denotations: `{x ⊔ y | x ∈ F, y ∈ G}`. This is the
composition mode for person and animacy features — it generates heterogeneous
pluralities and is ASSOCIATIVE.

**Lexical Complementarity (LC)**: for F ⊂ G, use of the G-form is restricted to
G \ F. This derives marked reference patterns.

**Two composition modes**: person/animacy compose via ⊕; number/gender compose
via ∩. This structural difference explains why person/animacy trigger PCC effects
(they compete for the same D-head position) but number/gender do not.

**Connection to `Features.PrivativePair`**: the containment hierarchy SPEAKER ⊂
PARTICIPANT ⊂ π is the set-theoretic realization of the [+inner] → [+outer]
constraint in `Features.PrivativePair`. The 3-cell partition (speaker/participant/π)
corresponds to the three well-formed cells (maximal/intermediate/minimal) of the
privative pair. See `Harbour2016` for bridge theorems
connecting the algebraic and syntactic person hierarchies.

## Sections

1. Operators (oplus, lexComp, singularFilter, pluralFilter)
2. PhiDomain (parameterized individual domain)
3. Feature denotations (as Finset (Finset Ind))
4. Pronoun composition via nested oplus
5. Third-person restriction
6. Lexical complementarity within third person
-/

namespace Minimalism.PhiSemantics

-- ============================================================================
-- § 1: Operators
-- ============================================================================

/-- Nonempty powerset: all nonempty subsets of `atoms`. This is the denotation
    of a feature predicate — every nonempty sum of atoms satisfying the feature.
    Corresponds to @cite{toosarvandani-2023} (48)–(50). -/
def npow {α : Type*} [DecidableEq α] (atoms : Finset α) : Finset (Finset α) :=
  atoms.powerset.erase ∅

/-- ⊕ (oplus): pointwise join of two feature denotations.
    `oplus F G = {x ∪ y | x ∈ F, y ∈ G}`
    @cite{harbour-2016}, @cite{kratzer-2009}. Generates heterogeneous
    pluralities: `oplus SPEAKER ANIMATE` includes `{speaker, animal}`.

    Implemented via eager Finset product + image to avoid exponential blowup
    in nested applications. -/
def oplus {α : Type*} [DecidableEq α]
    (F G : Finset (Finset α)) : Finset (Finset α) :=
  (F ×ˢ G).image fun yz => yz.1 ∪ yz.2

/-- Lexical Complementarity: for feature denotations F ⊂ G, the G-form
    is restricted to G \ F. @cite{toosarvandani-2023} (62). -/
def lexComp {α : Type*} [DecidableEq α]
    (G F : Finset (Finset α)) : Finset (Finset α) :=
  G \ F

/-- SINGULAR: intersection filter for atomic (singleton) sums.
    @cite{toosarvandani-2023} (56a): ⟦SINGULAR⟧ = λx . ∀y[y ≤ x → x = y].
    In the Finset encoding, atomic = singleton (card 1).
    Number features compose via ∩ (intersection), not ⊕. -/
def singularFilter {α : Type*} [DecidableEq α]
    (den : Finset (Finset α)) : Finset (Finset α) :=
  den.filter fun s => s.card = 1

/-- PLURAL: intersection filter for nonatomic (multi-element) sums.
    @cite{toosarvandani-2023} (56b): ⟦PLURAL⟧ = λx . ∃y[y ≤ x ∧ x ≠ y].
    In the Finset encoding, nonatomic = card > 1. -/
def pluralFilter {α : Type*} [DecidableEq α]
    (den : Finset (Finset α)) : Finset (Finset α) :=
  den.filter fun s => s.card > 1

-- ============================================================================
-- § 2: PhiDomain
-- ============================================================================

/-- A φ-domain: a finite set of individuals with speaker/addressee roles
    and animacy predicates forming a containment hierarchy.

    The hierarchy constraints (elder→human→animate) ensure the feature
    lattice is well-formed. Speaker and addressee are required to be human
    (following @cite{toosarvandani-2023}'s assumption that SAPs are at least
    human, which ensures PARTICIPANT ⊂ HUMAN in standard cases). -/
structure PhiDomain where
  /-- The type of individuals (atoms of the domain). -/
  Ind : Type
  [instDE : DecidableEq Ind]
  [instFT : Fintype Ind]
  /-- The speaker. -/
  speaker : Ind
  /-- The addressee. -/
  addressee : Ind
  /-- Elder predicate (senior kinship status). -/
  isElder : Ind → Bool
  /-- Human predicate. -/
  isHuman : Ind → Bool
  /-- Animate predicate. -/
  isAnimate : Ind → Bool
  /-- Hierarchy: elder → human. -/
  elder_human : ∀ x, isElder x = true → isHuman x = true
  /-- Hierarchy: human → animate. -/
  human_animate : ∀ x, isHuman x = true → isAnimate x = true
  /-- Speaker is human. -/
  speaker_human : isHuman speaker = true
  /-- Addressee is human. -/
  addressee_human : isHuman addressee = true
  /-- Speaker and addressee are distinct. -/
  speaker_ne : speaker ≠ addressee

attribute [instance] PhiDomain.instDE PhiDomain.instFT

-- ============================================================================
-- § 3: Feature Denotations
-- ============================================================================

variable (pd : PhiDomain)

/-- SPEAKER: `npow {speaker}` — singleton sums containing the speaker. -/
def speakerDen : Finset (Finset pd.Ind) :=
  npow {pd.speaker}

/-- PARTICIPANT: `npow {speaker, addressee}` — sums of SAPs. -/
def participantDen : Finset (Finset pd.Ind) :=
  npow {pd.speaker, pd.addressee}

/-- π: `npow univ` — all nonempty sums of individuals.
    The maximal feature denotation (top of the hierarchy). -/
def piDen : Finset (Finset pd.Ind) :=
  npow Finset.univ

/-- ELDER: nonempty sums of elders ∪ SAPs.
    SAPs are included because PARTICIPANT ⊂ ELDER in languages with elder
    features — the speaker and addressee are treated as at least elder-rank.
    @cite{toosarvandani-2023} (58). -/
def elderDen : Finset (Finset pd.Ind) :=
  npow (Finset.univ.filter fun a =>
    pd.isElder a || a == pd.speaker || a == pd.addressee)

/-- HUMAN: nonempty sums of humans. SAPs included via `speaker_human`
    and `addressee_human`. @cite{toosarvandani-2023} (59). -/
def humanDen : Finset (Finset pd.Ind) :=
  npow (Finset.univ.filter fun a => pd.isHuman a)

/-- ANIMATE: nonempty sums of animate individuals. -/
def animateDen : Finset (Finset pd.Ind) :=
  npow (Finset.univ.filter fun a => pd.isAnimate a)

-- ============================================================================
-- § 4: Pronoun Composition via Nested Oplus
-- ============================================================================

/-- Elder pronoun (full feature stack): ELDER ⊕ HUMAN ⊕ ANIMATE ⊕ π.
    Contains all sums reachable by joining an elder with any combination
    of lower-ranked individuals. @cite{toosarvandani-2023} (60). -/
def elderPron : Finset (Finset pd.Ind) :=
  oplus (elderDen pd) (oplus (humanDen pd) (oplus (animateDen pd) (piDen pd)))

/-- Human pronoun: HUMAN ⊕ ANIMATE ⊕ π. -/
def humanPron : Finset (Finset pd.Ind) :=
  oplus (humanDen pd) (oplus (animateDen pd) (piDen pd))

/-- Animal pronoun: ANIMATE ⊕ π. -/
def animalPron : Finset (Finset pd.Ind) :=
  oplus (animateDen pd) (piDen pd)

/-- Inanimate pronoun: π (no animacy restriction). -/
def inanimatePron : Finset (Finset pd.Ind) :=
  piDen pd

-- ============================================================================
-- § 5: Third-Person Restriction
-- ============================================================================

/-- Remove sums containing the speaker or addressee.
    Restricts a pronoun denotation to third-person reference. -/
def thirdOnly (den : Finset (Finset pd.Ind)) : Finset (Finset pd.Ind) :=
  den.filter fun s => pd.speaker ∉ s ∧ pd.addressee ∉ s

/-- Third-person elder pronoun. -/
def thirdElderPron : Finset (Finset pd.Ind) := thirdOnly pd (elderPron pd)

/-- Third-person human pronoun. -/
def thirdHumanPron : Finset (Finset pd.Ind) := thirdOnly pd (humanPron pd)

/-- Third-person animal pronoun. -/
def thirdAnimalPron : Finset (Finset pd.Ind) := thirdOnly pd (animalPron pd)

/-- Third-person inanimate pronoun. -/
def thirdInanimatePron : Finset (Finset pd.Ind) := thirdOnly pd (inanimatePron pd)

-- ============================================================================
-- § 6: Lexical Complementarity within Third Person
-- ============================================================================

/-- Third-person elder form after LC: the most marked form keeps its
    full denotation (smallest set — no subtraction needed).
    @cite{toosarvandani-2023} (62). -/
def thirdElderLC : Finset (Finset pd.Ind) := thirdElderPron pd

/-- Third-person human form after LC: human referents that are NOT
    also elder referents. -/
def thirdHumanLC : Finset (Finset pd.Ind) :=
  lexComp (thirdHumanPron pd) (thirdElderPron pd)

/-- Third-person animal form after LC: animate referents that are NOT
    also human referents. -/
def thirdAnimalLC : Finset (Finset pd.Ind) :=
  lexComp (thirdAnimalPron pd) (thirdHumanPron pd)

/-- Third-person inanimate form after LC: all referents not in the
    animate pronoun. The least marked (largest) set minus the next. -/
def thirdInanimateLC : Finset (Finset pd.Ind) :=
  lexComp (thirdInanimatePron pd) (thirdAnimalPron pd)

-- ============================================================================
-- § 7: Feature Containment PCC
-- ============================================================================

/-! Parameterized feature containment PCC: given any mapping from pronoun
    types to feature sets, the subject licenses the object iff the subject
    has all of the object's features. This derives the PCC from feature
    geometry rather than stipulating it.

    @cite{toosarvandani-2023} (86): "A functional head F Agrees with two
    pronouns A and B, where A is higher than B, iff A has all of the
    features of B." -/

/-- Feature containment PCC: the subject licenses the object iff
    `features(obj) ⊆ features(subj)`. -/
def featureContainmentLicit {P F : Type*} [DecidableEq F]
    (features : P → Finset F) (subj obj : P) : Bool :=
  decide (features obj ⊆ features subj)

/-- Feature containment is reflexive: same-rank is always licit. -/
theorem featureContainment_refl {P F : Type*} [DecidableEq F]
    (features : P → Finset F) (p : P) :
    featureContainmentLicit features p p = true := by
  simp [featureContainmentLicit]

/-- Feature containment is transitive. -/
theorem featureContainment_trans {P F : Type*} [DecidableEq F]
    (features : P → Finset F) {p1 p2 p3 : P}
    (h12 : featureContainmentLicit features p1 p2 = true)
    (h23 : featureContainmentLicit features p2 p3 = true) :
    featureContainmentLicit features p1 p3 = true := by
  simp only [featureContainmentLicit, decide_eq_true_eq] at *
  exact h23.trans h12

/-- Feature containment is antisymmetric on feature sets:
    mutual licitness implies identical features. -/
theorem featureContainment_antisymm {P F : Type*} [DecidableEq F]
    (features : P → Finset F) {p1 p2 : P}
    (h12 : featureContainmentLicit features p1 p2 = true)
    (h21 : featureContainmentLicit features p2 p1 = true) :
    features p1 = features p2 := by
  simp only [featureContainmentLicit, decide_eq_true_eq] at *
  exact h21.antisymm h12

/-- Feature containment is total when feature sets form a containment
    chain: for any two pronoun types, at least one direction is licit.
    This holds when person and animacy form a SINGLE hierarchy. -/
theorem featureContainment_total {P F : Type*} [DecidableEq F]
    (features : P → Finset F)
    (chain : ∀ p1 p2 : P, features p1 ⊆ features p2 ∨
                           features p2 ⊆ features p1) :
    ∀ p1 p2 : P,
      featureContainmentLicit features p1 p2 = true ∨
      featureContainmentLicit features p2 p1 = true := by
  intro p1 p2
  simp only [featureContainmentLicit, decide_eq_true_eq]
  exact (chain p1 p2).elim Or.inr Or.inl

end Minimalism.PhiSemantics
