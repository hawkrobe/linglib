import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Fintype.Basic
import Linglib.Features.Person
import Linglib.Syntax.Minimalist.Phi.Lattice

/-!
# Toosarvandani (2023): The Interpretation and Grammatical Representation of Animacy
[toosarvandani-2023] [harbour-2016] [kratzer-2009]
[foley-toosarvandani-2022]

Language 99(4): 760–808.

Formalizes the core empirical and theoretical contributions of Toosarvandani's
analysis of Santiago Laxopa Zapotec (and other Southeastern Sierra Zapotec
varieties), in which third-person plural pronouns encode a four-way animacy
distinction (elder humans, nonelder humans, animals, inanimates) that exhibits
ASSOCIATIVITY — the cluster of interpretive properties otherwise associated
with first- and second-person plural pronouns.

## Key formal apparatus (paper §3–§4)

- **Lattice-denoting features.** SPEAKER, PARTICIPANT, π are person features
  denoting predicates over a lattice of singular and plural individuals (48).
  ELDER, HUMAN, ANIMATE are animacy features with parallel structure (58).
- **⊕ operator** (50): pointwise lattice join of two feature denotations,
  generalising Kratzer's (2009) sum operator. Generates plural individuals
  (and thus heterogeneity) when applied to lattice-denoting features.
- **Lexical Complementarity (LC)** (52): for ⟦F⟧ ⊂ ⟦G⟧, use of G is
  restricted to ⟦G⟧ \ ⟦F⟧. Derives marked reference patterns.
- **SINGULAR/PLURAL** (56): intersection-composing number features.
- **Composition order** (57, 63): person/animacy features compose via ⊕
  first, then number composes via ∩. The reverse order is non-functional —
  ⊕ would re-introduce pluralities that ∩ SINGULAR removed.
- **Person Case Constraint** (86): a functional head F Agrees with two
  pronouns A and B (A higher than B) iff A has all of the features of B.

## File structure

- §1 Operators (oplus, lexComp, singularFilter, pluralFilter, nePowerset encoding)
- §2 PhiDomain and the Zapotec instantiation
- §3 Feature denotations
- §4 Pronoun composition (Zapotec 4-way animacy + LC)
- §5 PCC via feature containment (data from (77)–(82))
- §6 Structural properties of the PCC condition
- §7 Denotation ↔ PCC correspondence
- §8 Heterogeneity and SINGULAR/PLURAL composition order
- §9 Bridges to `Features.Person` and `Features.Prominence`

## Note on absolute vs relative PCC

(86) is the formal Agree condition. It predicts same-rank pairings (e.g.
1>1, 2>2) are licit because A trivially has all of A's features. The paper
acknowledges (footnote 22, p. 798) that the empirical *person*-based PCC in
many languages is ABSOLUTE — any local-person object is illicit, even with
a local-person subject. The animacy-based PCC in Zapotec is RELATIVE and is
what (86) directly derives. Cross-linguistic variation between absolute and
relative PCC is attributed to the probe's featural relativization (§4.3,
not formalized here).
-/

namespace Toosarvandani2023

open Minimalist.Phi.Lattice

-- ============================================================================
-- § 1: Operators (lattice ops lifted to Syntax.Minimalist.Phi.Lattice; number filters local)
-- ============================================================================


/-- SINGULAR (56a): `⟦SINGULAR⟧ = λx . ∀y[y ≤ x → x = y]`. Picks out the
    atomic individuals. In the Finset encoding, atomic = singleton. Number
    features compose with person/animacy features by ∩ (intersection),
    not ⊕. -/
def singularFilter {α : Type*} [DecidableEq α]
    (den : Finset (Finset α)) : Finset (Finset α) :=
  den.filter fun s => s.card = 1

/-- PLURAL (56b): `⟦PLURAL⟧ = λx . ∃y[y ≤ x ∧ x ≠ y]`. Picks out the
    nonatomic individuals. In the Finset encoding, nonatomic = card > 1. -/
def pluralFilter {α : Type*} [DecidableEq α]
    (den : Finset (Finset α)) : Finset (Finset α) :=
  den.filter fun s => s.card > 1

-- ============================================================================
-- § 2: PhiDomain + Zapotec Instantiation
-- ============================================================================

/-- A φ-domain: a finite set of individuals with speaker/addressee roles
    and animacy predicates forming the entailment hierarchy
    ELDER ⊂ HUMAN ⊂ ANIMATE (58, p. 786). Speaker and addressee are
    required to be human (per the paper's footnote 15, p. 787). -/
structure PhiDomain where
  /-- The type of atomic individuals. -/
  Ind : Type
  [instDE : DecidableEq Ind]
  [instFT : Fintype Ind]
  /-- The speaker. -/
  speaker : Ind
  /-- The addressee. -/
  addressee : Ind
  /-- Elder predicate (salient social role per (58a)). -/
  isElder : Ind → Bool
  /-- Human predicate (58b). -/
  isHuman : Ind → Bool
  /-- Animate predicate (58c). -/
  isAnimate : Ind → Bool
  /-- Hierarchy: ELDER entails HUMAN (commentary after (58)). -/
  elder_human : ∀ x, isElder x = true → isHuman x = true
  /-- Hierarchy: HUMAN entails ANIMATE. -/
  human_animate : ∀ x, isHuman x = true → isAnimate x = true
  /-- Speaker is human (footnote 15). -/
  speaker_human : isHuman speaker = true
  /-- Addressee is human (footnote 15). -/
  addressee_human : isHuman addressee = true
  /-- Speaker and addressee are distinct. -/
  speaker_ne : speaker ≠ addressee

attribute [instance] PhiDomain.instDE PhiDomain.instFT

/-! ## Santiago Laxopa Zapotec instance

Six representative individuals spanning the four-way animacy scale.
This is Toosarvandani's didactic minimum for the Zapotec lattice — not
real lexical data. -/

/-- Six individuals: speaker, addressee, an elder, a nonelder human, an
    animal, and an inanimate. -/
inductive ZapInd where
  | i  -- speaker (always human, SAP)
  | u  -- addressee (always human, SAP)
  | e  -- nonconversational elder
  | h  -- nonelder human
  | a  -- animal
  | o  -- inanimate
  deriving DecidableEq, Repr

instance : Fintype ZapInd where
  elems := {.i, .u, .e, .h, .a, .o}
  complete := by intro x; cases x <;> decide

/-- The Zapotec PhiDomain with 4-way animacy. -/
def zapotecDomain : PhiDomain where
  Ind := ZapInd
  speaker := .i
  addressee := .u
  isElder := fun | .e => true | _ => false
  isHuman := fun | .i | .u | .e | .h => true | _ => false
  isAnimate := fun | .i | .u | .e | .h | .a => true | _ => false
  elder_human := by intro x; cases x <;> decide
  human_animate := by intro x; cases x <;> decide
  speaker_human := by decide
  addressee_human := by decide
  speaker_ne := by decide

/-- Convenience abbreviation. -/
abbrev zd : PhiDomain := zapotecDomain

-- ============================================================================
-- § 3: Feature Denotations
-- ============================================================================

variable (pd : PhiDomain)

/-- ⟦SPEAKER⟧ (48a): singleton sums containing the speaker. -/
def speakerDen : Finset (Finset pd.Ind) :=
  nePowerset {pd.speaker}

/-- ⟦PARTICIPANT⟧ (48b): nonempty subsets of {speaker, addressee}. -/
def participantDen : Finset (Finset pd.Ind) :=
  nePowerset {pd.speaker, pd.addressee}

/-- ⟦π⟧ (48c): all nonempty sums of individuals — the maximal feature
    denotation. -/
def piDen : Finset (Finset pd.Ind) :=
  nePowerset Finset.univ

/-- ⟦ELDER⟧ (58a): individuals holding a salient social role. With (58a)'s
    semantics, the denotation includes SAPs as well as nonconversational
    elders, since SAPs trivially satisfy any salient-role test (paper
    p. 787). The pronoun-level restriction to nonconversational elders
    arises only after lexical complementarity (62). -/
def elderDen : Finset (Finset pd.Ind) :=
  nePowerset (Finset.univ.filter fun a =>
    pd.isElder a || a == pd.speaker || a == pd.addressee)

/-- ⟦HUMAN⟧ (58b). SAPs are included via `speaker_human`/`addressee_human`. -/
def humanDen : Finset (Finset pd.Ind) :=
  nePowerset (Finset.univ.filter fun a => pd.isHuman a)

/-- ⟦ANIMATE⟧ (58c). -/
def animateDen : Finset (Finset pd.Ind) :=
  nePowerset (Finset.univ.filter fun a => pd.isAnimate a)

-- ============================================================================
-- § 4: Pronoun Composition via Nested Oplus
-- ============================================================================

/-- The 3SG.EL feature stack from (61a): π ⊕ ANIMATE ⊕ HUMAN ⊕ ELDER.
    We elide the SINGULAR component (which is intersected separately) and
    return the elder-pronoun denotation prior to LC. The actual pronoun
    denotation in (62a) is `lexComp elderPron` over the next-less-marked
    pronoun — but for the elder pronoun itself, LC is trivial since it's
    the most marked. -/
def elderPron : Finset (Finset pd.Ind) :=
  oplus (elderDen pd) (oplus (humanDen pd) (oplus (animateDen pd) (piDen pd)))

/-- The 3SG.HU stack from (61b): π ⊕ ANIMATE ⊕ HUMAN. -/
def humanPron : Finset (Finset pd.Ind) :=
  oplus (humanDen pd) (oplus (animateDen pd) (piDen pd))

/-- The 3SG.AN stack from (61c): π ⊕ ANIMATE. -/
def animalPron : Finset (Finset pd.Ind) :=
  oplus (animateDen pd) (piDen pd)

/-- The 3SG.IN stack from (61d): π only. -/
def inanimatePron : Finset (Finset pd.Ind) :=
  piDen pd

-- ============================================================================
-- § 4b: Third-Person Restriction and LC
-- ============================================================================

/-- Remove sums containing the speaker or addressee — restricts a pronoun
    denotation to third-person reference. -/
def thirdOnly (den : Finset (Finset pd.Ind)) : Finset (Finset pd.Ind) :=
  den.filter fun s => pd.speaker ∉ s ∧ pd.addressee ∉ s

/-- Third-person elder, human, animal, inanimate denotations (post-thirdOnly). -/
def thirdElderPron : Finset (Finset pd.Ind) := thirdOnly pd (elderPron pd)
def thirdHumanPron : Finset (Finset pd.Ind) := thirdOnly pd (humanPron pd)
def thirdAnimalPron : Finset (Finset pd.Ind) := thirdOnly pd (animalPron pd)
def thirdInanimatePron : Finset (Finset pd.Ind) := thirdOnly pd (inanimatePron pd)

/-- Elder pronoun after LC: most marked, no subtraction needed (62a). -/
def thirdElderLC : Finset (Finset pd.Ind) := thirdElderPron pd

/-- Human pronoun after LC (62b): human \ elder. -/
def thirdHumanLC : Finset (Finset pd.Ind) :=
  lexComp (thirdHumanPron pd) (thirdElderPron pd)

/-- Animal pronoun after LC (62c): animal \ human. -/
def thirdAnimalLC : Finset (Finset pd.Ind) :=
  lexComp (thirdAnimalPron pd) (thirdHumanPron pd)

/-- Inanimate pronoun after LC: π \ animal. -/
def thirdInanimateLC : Finset (Finset pd.Ind) :=
  lexComp (thirdInanimatePron pd) (thirdAnimalPron pd)

-- ============================================================================
-- § 4c: Empirical Properties of the Denotations
-- ============================================================================

/-! Concrete checks on the Zapotec instance, proved structurally via
    explicit `mem_oplus_of_mem` witness construction rather than `decide`.
    The kernel decide on Finset-of-Finset membership over a 6-atom
    universe is too heavy (each side up to 63 elements); the structural
    witnesses build up `{x} = {x} ∪ {x}` decompositions through the
    nested `oplus`. -/

/-- Helper: a singleton lifts through any `oplus` whose factors both
    contain it. The key fact is `{x} ∪ {x} = {x}`. -/
private lemma singleton_mem_oplus {x : ZapInd}
    {F G : Finset (Finset ZapInd)}
    (hF : ({x} : Finset ZapInd) ∈ F) (hG : ({x} : Finset ZapInd) ∈ G) :
    ({x} : Finset ZapInd) ∈ oplus F G := by
  have h : ({x} : Finset ZapInd) = ({x} : Finset ZapInd) ∪ ({x} : Finset ZapInd) :=
    (Finset.union_self _).symm
  rw [h]
  exact mem_oplus_of_mem hF hG

/-- Helper: a doubleton `{x, y}` arises from `{x} ∪ {y}`. -/
private lemma doubleton_mem_oplus {x y : ZapInd}
    {F G : Finset (Finset ZapInd)}
    (hF : ({x} : Finset ZapInd) ∈ F) (hG : ({y} : Finset ZapInd) ∈ G) :
    ({x, y} : Finset ZapInd) ∈ oplus F G := by
  have h : ({x, y} : Finset ZapInd) = ({x} : Finset ZapInd) ∪ ({y} : Finset ZapInd) := by
    ext; simp
  rw [h]
  exact mem_oplus_of_mem hF hG

theorem elderPron_nonempty : (elderPron zd).Nonempty :=
  ⟨{.i}, singleton_mem_oplus (by decide)
    (singleton_mem_oplus (by decide)
      (singleton_mem_oplus (by decide) (by decide)))⟩

theorem humanPron_nonempty : (humanPron zd).Nonempty :=
  ⟨{.i}, singleton_mem_oplus (by decide)
    (singleton_mem_oplus (by decide) (by decide))⟩

theorem animalPron_nonempty : (animalPron zd).Nonempty :=
  ⟨{.i}, singleton_mem_oplus (by decide) (by decide)⟩

theorem inanimatePron_nonempty : (inanimatePron zd).Nonempty := by
  refine ⟨{.i}, ?_⟩; decide

/-- An elder + nonelder human group `{e, h}` is in the elder pronoun
    denotation. Heterogeneity: elder pronouns can refer to mixed groups
    of elders and others. Paper §2.3 + (62a). -/
theorem elder_heterogeneous :
    ({.e, .h} : Finset ZapInd) ∈ elderPron zd :=
  doubleton_mem_oplus (by decide)
    (singleton_mem_oplus (by decide)
      (singleton_mem_oplus (by decide) (by decide)))

/-- Elder + animal group `{e, a}` is in the elder pronoun denotation.
    Witness construction: e = {e}, y = {e, a} = {e} ∪ {a} where {e} ∈
    humanDen (e is human, being elder) and {a} ∈ animalPron (a is in
    animateDen ∩ piDen). -/
theorem elder_with_animal :
    ({.e, .a} : Finset ZapInd) ∈ elderPron zd := by
  have eq1 : ({.e, .a} : Finset ZapInd) =
      ({.e} : Finset ZapInd) ∪ ({.e, .a} : Finset ZapInd) := by ext; simp
  rw [eq1]
  refine mem_oplus_of_mem (by decide) ?_  -- {.e} ∈ elderDen
  -- {.e, .a} ∈ humanPron via {.e} ∪ {.a}, {.e} ∈ humanDen, {.a} ∈ animalPron
  refine doubleton_mem_oplus (by decide) ?_
  exact singleton_mem_oplus (by decide) (by decide)

/-! Base-feature containment: each animacy denotation is contained in
    the next less-marked one. These follow from `nePowerset_mono` plus a small
    `decide` on the underlying 6-atom filter. -/

theorem elderDen_sub_humanDen :
    elderDen zd ⊆ humanDen zd := nePowerset_mono (by decide)

theorem humanDen_sub_animateDen :
    humanDen zd ⊆ animateDen zd := nePowerset_mono (by decide)

theorem animateDen_sub_piDen :
    animateDen zd ⊆ piDen zd := nePowerset_mono (by decide)

/-! Denotation containment chain. Each pronoun is `oplus` of progressively
    less-marked feature denotations. The proof pattern: replace the
    most-marked component (e.g. elder in elderPron) with the next
    component (human) using `oplus_subset` + base-feature monotonicity,
    then use `oplus_assoc` and `oplus_nePowerset_self_subset` to absorb the
    duplicated component. -/

theorem animalPron_sub_piDen :
    animalPron zd ⊆ piDen zd := by
  -- animalPron = oplus animateDen piDen ⊆ nePowerset univ = piDen.
  -- Both args are ⊆ nePowerset univ (their elements are subsets of univ).
  refine oplus_subset_nePowerset (X := Finset.univ) ?_ (Finset.Subset.refl _)
  exact nePowerset_mono (Finset.subset_univ _)

theorem humanPron_sub_animalPron :
    humanPron zd ⊆ animalPron zd := by
  -- humanPron = oplus humanDen animalPron ⊆ animalPron via:
  --   oplus humanDen animalPron ⊆ oplus animateDen animalPron  (humanDen ⊆ animateDen)
  --   = oplus animateDen (oplus animateDen piDen)              (defn animalPron)
  --   = oplus (oplus animateDen animateDen) piDen              (assoc)
  --   ⊆ oplus animateDen piDen = animalPron                    (oplus_npow_self)
  refine Finset.Subset.trans
    (oplus_subset humanDen_sub_animateDen (Finset.Subset.refl _)) ?_
  show oplus (animateDen zd) (oplus (animateDen zd) (piDen zd)) ⊆
       oplus (animateDen zd) (piDen zd)
  rw [← oplus_assoc]
  exact oplus_subset (oplus_nePowerset_self_subset _) (Finset.Subset.refl _)

theorem elderPron_sub_humanPron :
    elderPron zd ⊆ humanPron zd := by
  -- Same shape: elderDen ⊆ humanDen, then absorb humanDen into humanPron
  -- via oplus_npow_self.
  refine Finset.Subset.trans
    (oplus_subset elderDen_sub_humanDen (Finset.Subset.refl _)) ?_
  show oplus (humanDen zd) (oplus (humanDen zd) (oplus (animateDen zd) (piDen zd))) ⊆
       oplus (humanDen zd) (oplus (animateDen zd) (piDen zd))
  rw [← oplus_assoc]
  exact oplus_subset (oplus_nePowerset_self_subset _) (Finset.Subset.refl _)

/-- SPEAKER ⊂ PARTICIPANT at the feature-denotation level. -/
theorem speaker_sub_participant :
    speakerDen zd ⊆ participantDen zd := by decide

/-- ⊕ is associative on any Zapotec denotations. Direct corollary of the
    generic `oplus_assoc`; no `decide` needed. -/
theorem oplus_assoc_elder :
    oplus (oplus (elderDen zd) (humanDen zd)) (animateDen zd) =
    oplus (elderDen zd) (oplus (humanDen zd) (animateDen zd)) :=
  oplus_assoc _ _ _

-- ============================================================================
-- § 5: PCC via Feature Containment
-- ============================================================================

/-! The PCC (Person Case Constraint), here extended with animacy, derived
    from feature containment per (86):

    > A functional head F Agrees with two pronouns A and B, where A is
    > higher than B, iff A has all of the features of B.

    Person and animacy features occupy the same structural position (D),
    forming a SINGLE hierarchy. Feature containment — not numeric ranking —
    determines licitness. -/

/-- Decompositional φ-features in the nested geometry
    D → [π [ANIMATE [HUMAN [ELDER [PARTICIPANT [SPEAKER]]]]]] (60). -/
inductive DFeature where
  | speaker
  | participant
  | elder
  | human
  | animate
  | pi
  deriving DecidableEq, Repr

instance : Fintype DFeature where
  elems := {.speaker, .participant, .elder, .human, .animate, .pi}
  complete := by intro x; cases x <;> decide

/-- Pronoun types in the extended person/animacy hierarchy. -/
inductive PronType where
  | first
  | second
  | thirdElder
  | thirdHuman
  | thirdAnimal
  | thirdInanimate
  deriving DecidableEq, Repr

instance : Fintype PronType where
  elems := {.first, .second, .thirdElder, .thirdHuman, .thirdAnimal, .thirdInanimate}
  complete := by intro x; cases x <;> decide

/-- All 6 pronoun types. -/
def PronType.all : List PronType :=
  [.first, .second, .thirdElder, .thirdHuman, .thirdAnimal, .thirdInanimate]

/-- Feature specification per pronoun type. SAPs include all animacy
    features because speaker/addressee are at least elder-rank under
    (58a)'s "salient social role" predicate. The feature sets form a
    strict containment chain: 1P ⊃ 2P ⊃ 3.EL ⊃ 3.HU ⊃ 3.AN ⊃ 3.IN. -/
def PronType.features : PronType → Finset DFeature
  | .first          => {.speaker, .participant, .elder, .human, .animate, .pi}
  | .second         => {.participant, .elder, .human, .animate, .pi}
  | .thirdElder     => {.elder, .human, .animate, .pi}
  | .thirdHuman     => {.human, .animate, .pi}
  | .thirdAnimal    => {.animate, .pi}
  | .thirdInanimate => {.pi}

/-- PCC licitness via feature containment (86): subject Agrees with object
    iff subject has all of object's features. Implemented directly via
    `Finset.Subset` decidability. -/
def pccLicit (subj obj : PronType) : Bool :=
  decide (PronType.features obj ⊆ PronType.features subj)

-- § 5a: Licit — subject strictly outranks object (data from (77)–(81))
theorem pcc_1_2 : pccLicit .first .second = true := by decide
theorem pcc_1_3el : pccLicit .first .thirdElder = true := by decide
theorem pcc_1_3hu : pccLicit .first .thirdHuman = true := by decide
theorem pcc_1_3an : pccLicit .first .thirdAnimal = true := by decide
theorem pcc_1_3in : pccLicit .first .thirdInanimate = true := by decide
theorem pcc_2_3el : pccLicit .second .thirdElder = true := by decide
theorem pcc_2_3hu : pccLicit .second .thirdHuman = true := by decide
theorem pcc_2_3an : pccLicit .second .thirdAnimal = true := by decide
theorem pcc_2_3in : pccLicit .second .thirdInanimate = true := by decide
theorem pcc_3el_3hu : pccLicit .thirdElder .thirdHuman = true := by decide  -- (79a)
theorem pcc_3el_3an : pccLicit .thirdElder .thirdAnimal = true := by decide
theorem pcc_3el_3in : pccLicit .thirdElder .thirdInanimate = true := by decide
theorem pcc_3hu_3an : pccLicit .thirdHuman .thirdAnimal = true := by decide  -- (80a)
theorem pcc_3hu_3in : pccLicit .thirdHuman .thirdInanimate = true := by decide
theorem pcc_3an_3in : pccLicit .thirdAnimal .thirdInanimate = true := by decide  -- (81a)

-- § 5b: Illicit — object outranks subject (data from (77b), (78b), (79b)–(82))
theorem pcc_2_1 : pccLicit .second .first = false := by decide
theorem pcc_3el_1 : pccLicit .thirdElder .first = false := by decide
theorem pcc_3el_2 : pccLicit .thirdElder .second = false := by decide
theorem pcc_3hu_1 : pccLicit .thirdHuman .first = false := by decide  -- (82)
theorem pcc_3hu_2 : pccLicit .thirdHuman .second = false := by decide
theorem pcc_3hu_3el : pccLicit .thirdHuman .thirdElder = false := by decide  -- (79b)
theorem pcc_3an_1 : pccLicit .thirdAnimal .first = false := by decide
theorem pcc_3an_2 : pccLicit .thirdAnimal .second = false := by decide
theorem pcc_3an_3el : pccLicit .thirdAnimal .thirdElder = false := by decide
theorem pcc_3an_3hu : pccLicit .thirdAnimal .thirdHuman = false := by decide  -- (80b)
theorem pcc_3in_1 : pccLicit .thirdInanimate .first = false := by decide
theorem pcc_3in_2 : pccLicit .thirdInanimate .second = false := by decide
theorem pcc_3in_3el : pccLicit .thirdInanimate .thirdElder = false := by decide
theorem pcc_3in_3hu : pccLicit .thirdInanimate .thirdHuman = false := by decide
theorem pcc_3in_3an : pccLicit .thirdInanimate .thirdAnimal = false := by decide  -- (81b)

-- § 5c: Same-rank — licit under (86) (see header note re absolute vs relative)
theorem pcc_1_1 : pccLicit .first .first = true := by decide
theorem pcc_2_2 : pccLicit .second .second = true := by decide
theorem pcc_3el_3el : pccLicit .thirdElder .thirdElder = true := by decide
theorem pcc_3hu_3hu : pccLicit .thirdHuman .thirdHuman = true := by decide
theorem pcc_3an_3an : pccLicit .thirdAnimal .thirdAnimal = true := by decide
theorem pcc_3in_3in : pccLicit .thirdInanimate .thirdInanimate = true := by decide

-- § 5d: Drift sentry on aggregate licit count
/-- 21 licit subj×obj pairings (15 strict + 6 same-rank). Drift sentry for
    the per-cell theorems above. -/
theorem pcc_licit_count :
    (PronType.all.flatMap fun subj =>
      PronType.all.filter fun obj => pccLicit subj obj).length = 21 := by
  decide

-- ============================================================================
-- § 6: Structural Properties of Feature Containment
-- ============================================================================

/-- Reflexivity: A ⊆ A always, so pccLicit p p = true. -/
theorem pcc_refl : ∀ p : PronType, pccLicit p p = true := by
  intro p; simp [pccLicit]

/-- Transitivity: features p3 ⊆ features p2 and features p2 ⊆ features p1
    imply features p3 ⊆ features p1. -/
theorem pcc_trans : ∀ p1 p2 p3 : PronType,
    pccLicit p1 p2 = true → pccLicit p2 p3 = true → pccLicit p1 p3 = true := by
  intro p1 p2 p3 h12 h23
  simp only [pccLicit, decide_eq_true_eq] at h12 h23 ⊢
  exact h23.trans h12

/-- The Zapotec feature mapping forms a total containment chain. This is
    the domain-specific fact that makes PCC total. -/
theorem zapotec_features_chain : ∀ p1 p2 : PronType,
    PronType.features p1 ⊆ PronType.features p2 ∨
    PronType.features p2 ⊆ PronType.features p1 := by decide

/-- Totality: at least one direction is licit. Follows from the containment
    chain via `Finset.Subset`. -/
theorem pcc_total : ∀ p1 p2 : PronType,
    pccLicit p1 p2 = true ∨ pccLicit p2 p1 = true := by
  intro p1 p2
  simp only [pccLicit, decide_eq_true_eq]
  exact (zapotec_features_chain p1 p2).elim Or.inr Or.inl

/-- Antisymmetry on PronType: mutual licitness implies same pronoun type.
    This requires Zapotec-specific injectivity of the feature mapping
    (the abstract claim is just feature-set equality). -/
theorem pcc_antisymm : ∀ p1 p2 : PronType,
    pccLicit p1 p2 = true → pccLicit p2 p1 = true → p1 = p2 := by decide

-- ============================================================================
-- § 7: Denotation ↔ PCC Correspondence
-- ============================================================================

/-! Within third person, denotation nesting (semantic, from ⊕ composition)
    mirrors PCC licitness (syntactic, from feature containment). The two
    main contributions of the paper — compositional animacy semantics and
    derived PCC — are formally connected: more features → smaller
    denotation → higher on hierarchy → can be subject.

    The three semantic-side facts are `elderPron_sub_humanPron`,
    `humanPron_sub_animalPron`, `animalPron_sub_piDen` (§4c above). The
    syntactic-side facts are `pcc_3el_3hu`, `pcc_3hu_3an`, `pcc_3an_3in`
    (licit) and `pcc_3hu_3el`, `pcc_3an_3hu`, `pcc_3in_3an` (illicit), all
    in §5. Earlier drafts bundled them into a 9-conjunct
    `denotation_pcc_full_chain` aggregator; that was a
    no-aggregate-count-style sentry and is omitted to keep `decide`
    recursion within mathlib defaults. -/

/-- Helper: `{i} ∈ oplus F G` whenever `{i} ∈ F` and `{i} ∈ G`. -/
private lemma singleton_i_mem_oplus
    {F G : Finset (Finset ZapInd)}
    (hF : ({.i} : Finset ZapInd) ∈ F) (hG : ({.i} : Finset ZapInd) ∈ G) :
    ({.i} : Finset ZapInd) ∈ oplus F G := by
  have h : ({.i} : Finset ZapInd) = ({.i} : Finset ZapInd) ∪ ({.i} : Finset ZapInd) :=
    (Finset.union_idempotent _).symm
  rw [h]
  exact mem_oplus_of_mem hF hG

/-- Third-person restriction strictly shrinks the elder pronoun denotation:
    `{i}` is a witness that lives in `elderPron` (via the all-singletons
    decomposition `{i} ∪ {i} ∪ {i} ∪ {i}`) but is filtered out of
    `thirdElderPron` because it contains the speaker. Structural rather
    than card-based to avoid computing two ~63-element Finset
    cardinalities in the kernel. -/
theorem third_restricts_elder :
    (thirdElderPron zd).card < (elderPron zd).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
  intro hEq
  have h_in_elder : ({.i} : Finset ZapInd) ∈ elderPron zd :=
    singleton_i_mem_oplus (by decide)
      (singleton_i_mem_oplus (by decide)
        (singleton_i_mem_oplus (by decide) (by decide)))
  have h_not_in_third : ({.i} : Finset ZapInd) ∉ thirdElderPron zd := by
    show _ ∉ (elderPron zd).filter
      (fun s => zd.speaker ∉ s ∧ zd.addressee ∉ s)
    rw [Finset.mem_filter]
    push_neg
    intro _
    -- speaker = .i, and .i ∈ {.i}
    refine fun h => absurd ?_ h
    show ZapInd.i ∈ ({.i} : Finset ZapInd)
    decide
  exact h_not_in_third (hEq ▸ h_in_elder)

/-- LC produces disjoint third-person pronoun denotations. -/
theorem elder_human_LC_disjoint :
    Disjoint (thirdElderLC zd) (thirdHumanLC zd) := by
  simp only [thirdHumanLC, lexComp]
  exact Finset.disjoint_sdiff

-- (elderDen_sub_humanDen, humanDen_sub_animateDen, animateDen_sub_piDen
-- moved to §4c above where they're consumed by the elderPron_sub_humanPron
-- chain.)

-- ============================================================================
-- § 8: SINGULAR/PLURAL and Composition Order (57, 63)
-- ============================================================================

/-! Person/animacy features compose via ⊕; number features compose via ∩.
    These two modes MUST apply in a specific order: ⊕ first, then ∩. If
    SINGULAR were interleaved within the ⊕ chain, ⊕ would re-introduce
    pluralities by joining the singletons SINGULAR preserved (paper §3.2,
    derivation (63)). This non-commutativity is why person and number
    occupy distinct functional heads. -/

set_option maxRecDepth 16000 in
/-- Correct composition (57): ⊕ all person features, then ∩ SINGULAR.
    First-person singular = {speaker}. -/
theorem correct_1sg :
    singularFilter (oplus (speakerDen zd) (oplus (participantDen zd) (piDen zd))) =
    {({.i} : Finset ZapInd)} := by decide

/-- ⊕ and SINGULAR do not commute. Interleaving SINGULAR within the ⊕
    chain gives different (wrong) results because ⊕ creates new pluralities
    from the singletons SINGULAR preserved. (63). -/
theorem oplus_singular_noncommutative :
    singularFilter (oplus (speakerDen zd) (participantDen zd)) ≠
    oplus (speakerDen zd) (singularFilter (participantDen zd)) := by decide

/-- The wrong order produces plural sums: ⊕ SPEAKER applied AFTER SINGULAR
    creates {speaker, addressee} from singleton {addressee}, undoing
    SINGULAR's filtering. -/
theorem wrong_order_produces_plural :
    ({.i, .u} : Finset ZapInd) ∈
      oplus (speakerDen zd) (singularFilter (participantDen zd)) := by decide

-- ============================================================================
-- § 9: Bridges to Features.Person / Features.Prominence
-- ============================================================================

/-- Map PronType to the coarser 3-way person distinction in
    `Features.Prominence`. All third-person animacy subtypes collapse. -/
def PronType.toPersonLevel : PronType → Features.Prominence.PersonLevel
  | .first  => .first
  | .second => .second
  | _       => .third

/-- PCC respects person prominence: when subject is strictly more prominent
    in person (not just animacy), PCC is licit. -/
theorem pcc_person_refinement : ∀ p1 p2 : PronType,
    p1.toPersonLevel.rank > p2.toPersonLevel.rank → pccLicit p1 p2 = true := by
  decide

/-- Map PronType to binary person features (±participant, ±author). -/
def PronType.toPersonFeatures : PronType → Features.Person.Features
  | .first  => ⟨true, true⟩
  | .second => ⟨true, false⟩
  | _       => ⟨false, false⟩

/-- The two independent decompositions of person agree:
    PronType → PersonFeatures and PronType → PersonLevel → Features. -/
theorem person_features_consistent : ∀ p : PronType,
    p.toPersonFeatures = p.toPersonLevel.toFeatures := by decide

/-- Map third-person pronoun types to AnimacyLevel. Elder and human both
    map to `.human` — elder is a human subtype. SAPs return `none`. -/
def PronType.toAnimacyLevel : PronType → Option Features.Prominence.AnimacyLevel
  | .thirdElder     => some .human
  | .thirdHuman     => some .human
  | .thirdAnimal    => some .animate
  | .thirdInanimate => some .inanimate
  | _               => none

/-- The 4-way Zapotec animacy system REFINES the 3-way typological scale.
    Elder and human collapse at AnimacyLevel.human, but PCC distinguishes
    them. Toosarvandani's central empirical contribution. -/
theorem zapotec_refines_3way :
    PronType.toAnimacyLevel .thirdElder = PronType.toAnimacyLevel .thirdHuman ∧
    pccLicit .thirdElder .thirdHuman = true ∧
    pccLicit .thirdHuman .thirdElder = false := by decide

/-- All PronType person features are well-formed (no [−participant, +author]). -/
theorem prontype_features_wellFormed : ∀ p : PronType,
    p.toPersonFeatures.WellFormed := by decide

end Toosarvandani2023
