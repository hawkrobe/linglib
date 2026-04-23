import Linglib.Fragments.Zapotec.Basic
import Linglib.Features.Person

/-!
# Toosarvandani (2023): The Interpretation and Grammatical Representation of Animacy
@cite{toosarvandani-2023}

Language 99(4): 760–805.

Formalizes the core empirical and theoretical contributions:

1. **Pronoun denotation derivations** — the 4-way animacy pronoun inventory of
   Santiago Laxopa Zapotec (Table 1) derived from nested ⊕ composition with
   Lexical Complementarity.

2. **Heterogeneity** — elder pronouns can refer to heterogeneous groups
   (elder + non-elder human), derived by ⊕ rather than stipulated.

3. **Associativity** — ⊕ is associative: the order of feature composition
   doesn't matter.

4. **PCC paradigm** — animacy-based PCC effects in SLZ derived from feature
   containment (86): "A functional head F Agrees with two pronouns A and B,
   where A is higher than B, iff A has all of the features of B." Verified
   for all 36 combinations, yielding 21 licit pairs (15 strict + 6 same-rank).

5. **Denotation ↔ PCC correspondence** — within third person, denotation
   nesting (semantic) mirrors PCC licitness (syntactic), connecting the
   compositional semantics to the syntactic hierarchy.

6. **SINGULAR/PLURAL composition order** — ⊕ (person/animacy) must precede
   ∩ SINGULAR (number) because ⊕ creates new pluralities that undo
   SINGULAR's filtering. Non-commutativity proved concretely.

7. **Bridges to Core** — PronType maps to `Features.Person.Features` (±participant,
   ±author), `Features.Prominence.PersonLevel`, and `Features.Prominence.AnimacyLevel`.
   The 4-way Zapotec animacy system refines the 3-way typological scale.
-/

namespace Toosarvandani2023

open Minimalism.PhiSemantics
open Fragments.Zapotec

-- ============================================================================
-- § 1: Pronoun Denotation Derivations
-- ============================================================================

/-- The elder pronoun denotation is nonempty. -/
theorem elderPron_nonempty : (elderPron zd).Nonempty := by native_decide

/-- The human pronoun denotation is nonempty. -/
theorem humanPron_nonempty : (humanPron zd).Nonempty := by native_decide

/-- The animal pronoun denotation is nonempty. -/
theorem animalPron_nonempty : (animalPron zd).Nonempty := by native_decide

/-- The inanimate pronoun denotation is nonempty. -/
theorem inanimatePron_nonempty : (inanimatePron zd).Nonempty := by native_decide

-- ============================================================================
-- § 2: Heterogeneity — ⊕ Generates Mixed Groups
-- ============================================================================

/-- An elder+human group `{e, h}` is in the elder pronoun denotation.
    This is the key empirical prediction: elder pronouns can refer to
    heterogeneous groups containing both elders and non-elders.
    @cite{toosarvandani-2023} §4.2. -/
theorem elder_heterogeneous :
    ({.e, .h} : Finset ZapInd) ∈ elderPron zd := by native_decide

/-- An elder+animal group `{e, a}` is in the elder pronoun denotation. -/
theorem elder_with_animal :
    ({.e, .a} : Finset ZapInd) ∈ elderPron zd := by native_decide

/-- A human+animal group `{h, a}` is in the human pronoun after LC
    (in the human denotation but not the elder denotation). -/
theorem human_animal_in_humanLC :
    ({.h, .a} : Finset ZapInd) ∈ thirdHumanLC zd := by native_decide

-- ============================================================================
-- § 3: Containment — Feature Hierarchy Reflected in Denotation Nesting
-- ============================================================================

/-- Elder pronoun ⊂ Human pronoun: with npow-based denotations and ⊕,
    the more marked (elder) denotation is contained in the less marked
    (human) denotation. -/
theorem elderPron_sub_humanPron :
    elderPron zd ⊆ humanPron zd := by native_decide

/-- Human pronoun ⊂ Animal pronoun. -/
theorem humanPron_sub_animalPron :
    humanPron zd ⊆ animalPron zd := by native_decide

/-- Animal pronoun ⊂ π (inanimate pronoun). -/
theorem animalPron_sub_piDen :
    animalPron zd ⊆ piDen zd := by native_decide

/-- SPEAKER ⊂ PARTICIPANT (feature denotation level). -/
theorem speaker_sub_participant :
    speakerDen zd ⊆ participantDen zd := by native_decide

-- ============================================================================
-- § 4: Associativity of ⊕
-- ============================================================================

/-- ⊕ is associative: (F ⊕ G) ⊕ H = F ⊕ (G ⊕ H).
    Verified concretely for the Zapotec domain's animacy denotations.
    @cite{toosarvandani-2023} relies on this for well-formedness of
    nested feature composition. -/
theorem oplus_assoc_elder :
    oplus (oplus (elderDen zd) (humanDen zd)) (animateDen zd) =
    oplus (elderDen zd) (oplus (humanDen zd) (animateDen zd)) := by
  native_decide

-- ============================================================================
-- § 5: PCC — Feature Containment
-- ============================================================================

/-! The PCC (Person Case Constraint) extended with animacy, derived from
    feature containment per @cite{toosarvandani-2023} (86):

    > A functional head F Agrees with two pronouns A and B, where A is
    > higher than B, iff A has all of the features of B.

    Person and animacy features occupy the same structural position (D),
    forming a SINGLE hierarchy. Feature containment — not numeric ranking —
    determines PCC licitness.

    Note: the person-based PCC is empirically ABSOLUTE (any SAP in object
    position is illicit, per footnote 22), while the animacy-based PCC is
    RELATIVE. Condition (86) derives both: SAPs always have more features
    than 3P, so 3P can never contain SAP features. The absolute/relative
    distinction emerges from the feature geometry, not from stipulation. -/

/-- Decompositional φ-features in the nested feature geometry
    D → [π [ANIMATE [HUMAN [ELDER [PARTICIPANT [SPEAKER]]]]]].
    Each feature corresponds to a predicate over the individual domain. -/
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
  complete := by intro x; cases x <;> simp

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
  complete := by intro x; cases x <;> simp

/-- All 6 pronoun types. -/
def PronType.all : List PronType :=
  [.first, .second, .thirdElder, .thirdHuman, .thirdAnimal, .thirdInanimate]

/-- Feature specification per pronoun type.
    SAPs include all animacy features because speaker and addressee are
    at least elder-rank — elderDen includes SAPs per (58). The feature
    sets form a strict containment chain: 1P ⊃ 2P ⊃ 3.EL ⊃ 3.HU ⊃ 3.AN ⊃ 3.IN. -/
def PronType.features : PronType → Finset DFeature
  | .first          => {.speaker, .participant, .elder, .human, .animate, .pi}
  | .second         => {.participant, .elder, .human, .animate, .pi}
  | .thirdElder     => {.elder, .human, .animate, .pi}
  | .thirdHuman     => {.human, .animate, .pi}
  | .thirdAnimal    => {.animate, .pi}
  | .thirdInanimate => {.pi}

/-- PCC licitness via feature containment — (86):
    "A functional head F Agrees with two pronouns A and B, where A is
    higher than B, iff A has all of the features of B."

    Instantiates the parameterized `featureContainmentLicit` from
    `Minimalism.PhiSemantics` with the Zapotec feature mapping. -/
def pccLicit (subj obj : PronType) : Bool :=
  featureContainmentLicit PronType.features subj obj

-- § 5a: Licit — subject strictly outranks object (data from (77)–(81))
theorem pcc_1_2 : pccLicit .first .second = true := by native_decide
theorem pcc_1_3el : pccLicit .first .thirdElder = true := by native_decide
theorem pcc_1_3hu : pccLicit .first .thirdHuman = true := by native_decide
theorem pcc_1_3an : pccLicit .first .thirdAnimal = true := by native_decide
theorem pcc_1_3in : pccLicit .first .thirdInanimate = true := by native_decide
theorem pcc_2_3el : pccLicit .second .thirdElder = true := by native_decide
theorem pcc_2_3hu : pccLicit .second .thirdHuman = true := by native_decide
theorem pcc_2_3an : pccLicit .second .thirdAnimal = true := by native_decide
theorem pcc_2_3in : pccLicit .second .thirdInanimate = true := by native_decide
theorem pcc_3el_3hu : pccLicit .thirdElder .thirdHuman = true := by native_decide  -- (79a)
theorem pcc_3el_3an : pccLicit .thirdElder .thirdAnimal = true := by native_decide
theorem pcc_3el_3in : pccLicit .thirdElder .thirdInanimate = true := by native_decide
theorem pcc_3hu_3an : pccLicit .thirdHuman .thirdAnimal = true := by native_decide  -- (80a)
theorem pcc_3hu_3in : pccLicit .thirdHuman .thirdInanimate = true := by native_decide
theorem pcc_3an_3in : pccLicit .thirdAnimal .thirdInanimate = true := by native_decide  -- (81a)

-- § 5b: Illicit — object outranks subject (data from (77b), (78b), (79b)–(82))
theorem pcc_2_1 : pccLicit .second .first = false := by native_decide
theorem pcc_3el_1 : pccLicit .thirdElder .first = false := by native_decide
theorem pcc_3el_2 : pccLicit .thirdElder .second = false := by native_decide
theorem pcc_3hu_1 : pccLicit .thirdHuman .first = false := by native_decide  -- (82)
theorem pcc_3hu_2 : pccLicit .thirdHuman .second = false := by native_decide
theorem pcc_3hu_3el : pccLicit .thirdHuman .thirdElder = false := by native_decide  -- (79b)
theorem pcc_3an_1 : pccLicit .thirdAnimal .first = false := by native_decide
theorem pcc_3an_2 : pccLicit .thirdAnimal .second = false := by native_decide
theorem pcc_3an_3el : pccLicit .thirdAnimal .thirdElder = false := by native_decide
theorem pcc_3an_3hu : pccLicit .thirdAnimal .thirdHuman = false := by native_decide  -- (80b)
theorem pcc_3in_1 : pccLicit .thirdInanimate .first = false := by native_decide
theorem pcc_3in_2 : pccLicit .thirdInanimate .second = false := by native_decide
theorem pcc_3in_3el : pccLicit .thirdInanimate .thirdElder = false := by native_decide
theorem pcc_3in_3hu : pccLicit .thirdInanimate .thirdHuman = false := by native_decide
theorem pcc_3in_3an : pccLicit .thirdInanimate .thirdAnimal = false := by native_decide  -- (81b)

-- § 5c: Same-rank — always licit under feature containment (86)
theorem pcc_1_1 : pccLicit .first .first = true := by native_decide
theorem pcc_2_2 : pccLicit .second .second = true := by native_decide
theorem pcc_3el_3el : pccLicit .thirdElder .thirdElder = true := by native_decide
theorem pcc_3hu_3hu : pccLicit .thirdHuman .thirdHuman = true := by native_decide
theorem pcc_3an_3an : pccLicit .thirdAnimal .thirdAnimal = true := by native_decide
theorem pcc_3in_3in : pccLicit .thirdInanimate .thirdInanimate = true := by native_decide

-- § 5d: Exhaustive verification
/-- All 36 subj×obj combinations: 21 licit (15 strict + 6 same-rank). -/
theorem pcc_licit_count :
    (PronType.all.flatMap fun subj =>
      PronType.all.filter fun obj => pccLicit subj obj).length = 21 := by
  native_decide

-- ============================================================================
-- § 6: Structural Properties of Feature Containment
-- ============================================================================

/-- Feature containment is reflexive: same-rank is always licit.
    Derived from generic `featureContainment_refl`. -/
theorem pcc_refl : ∀ p : PronType, pccLicit p p = true :=
  fun p => featureContainment_refl PronType.features p

/-- Feature containment is transitive.
    Derived from generic `featureContainment_trans`. -/
theorem pcc_trans : ∀ p1 p2 p3 : PronType,
    pccLicit p1 p2 = true → pccLicit p2 p3 = true → pccLicit p1 p3 = true :=
  fun _ _ _ h12 h23 => featureContainment_trans PronType.features h12 h23

/-- The Zapotec feature mapping forms a total containment chain:
    for any two pronoun types, one's features contain the other's.
    This is the domain-specific fact that makes PCC total. -/
theorem zapotec_features_chain : ∀ p1 p2 : PronType,
    PronType.features p1 ⊆ PronType.features p2 ∨
    PronType.features p2 ⊆ PronType.features p1 := by native_decide

/-- Feature containment is total: for any two pronoun types, at least one
    direction is licit. Derived from generic `featureContainment_total` +
    the Zapotec-specific chain property. -/
theorem pcc_total : ∀ p1 p2 : PronType,
    pccLicit p1 p2 = true ∨ pccLicit p2 p1 = true :=
  featureContainment_total PronType.features zapotec_features_chain

/-- Feature containment is antisymmetric: mutual licitness implies same
    pronoun type. Requires Zapotec-specific injectivity of the feature
    mapping (the generic theorem only gives equal feature sets). -/
theorem pcc_antisymm : ∀ p1 p2 : PronType,
    pccLicit p1 p2 = true → pccLicit p2 p1 = true → p1 = p2 := by native_decide

-- ============================================================================
-- § 7: Denotation ↔ PCC Correspondence
-- ============================================================================

/-! Within third person, the semantic denotation nesting (from ⊕ composition)
    mirrors the syntactic PCC hierarchy (from feature containment). This
    connects the paper's two main contributions: the compositional semantics
    of animacy features and the derived PCC effects.

    More features → smaller denotation → higher on hierarchy → can be subject. -/

/-- Denotation nesting and PCC agree in direction: elderPron ⊆ humanPron
    corresponds to 3.EL licensing 3.HU as object (and not vice versa). -/
theorem denotation_pcc_elder_human :
    elderPron zd ⊆ humanPron zd ∧
    pccLicit .thirdElder .thirdHuman = true ∧
    pccLicit .thirdHuman .thirdElder = false := by native_decide

/-- Full denotation nesting chain corresponds to the PCC hierarchy:
    elderPron ⊆ humanPron ⊆ animalPron ⊆ piDen mirrors
    3.EL > 3.HU > 3.AN > 3.IN. -/
theorem denotation_pcc_full_chain :
    elderPron zd ⊆ humanPron zd ∧
    humanPron zd ⊆ animalPron zd ∧
    animalPron zd ⊆ piDen zd ∧
    pccLicit .thirdElder .thirdHuman = true ∧
    pccLicit .thirdHuman .thirdAnimal = true ∧
    pccLicit .thirdAnimal .thirdInanimate = true ∧
    pccLicit .thirdHuman .thirdElder = false ∧
    pccLicit .thirdAnimal .thirdHuman = false ∧
    pccLicit .thirdInanimate .thirdAnimal = false := by native_decide

-- ============================================================================
-- § 8: Third-Person Restriction and LC
-- ============================================================================

/-- Third-person restriction removes all SAP-containing sums from the
    elder pronoun denotation — the remaining denotation is strictly
    smaller. -/
theorem third_restricts_elder :
    (thirdElderPron zd).card < (elderPron zd).card := by native_decide

/-- LC produces disjoint third-person pronoun denotations: the elder
    and human LC forms share no elements. This follows trivially from
    LC's definition (human LC = human \ elder). -/
theorem elder_human_LC_disjoint :
    Disjoint (thirdElderLC zd) (thirdHumanLC zd) := by
  simp only [thirdHumanLC, lexComp]
  exact Finset.disjoint_sdiff

-- ============================================================================
-- § 9: PersonLevel Bridge
-- ============================================================================

/-- Map pronoun types to the coarser 3-way person distinction used in
    `Features.Prominence`. All third-person animacy subtypes collapse to `.third`. -/
def PronType.toPersonLevel : PronType → Features.Prominence.PersonLevel
  | .first => .first
  | .second => .second
  | _ => .third

/-- PCC correctly refines the person hierarchy: when a pronoun is strictly
    more prominent in person (not just animacy), PCC is always licit. -/
theorem pcc_person_refinement : ∀ p1 p2 : PronType,
    p1.toPersonLevel.rank > p2.toPersonLevel.rank → pccLicit p1 p2 = true := by
  native_decide

-- ============================================================================
-- § 10: Feature Denotation Containment (Atom Level)
-- ============================================================================

/-- ELDER ⊆ HUMAN at the feature denotation level (predicate over atoms).
    Parallels the pronoun-level containment elderPron ⊆ humanPron (§3). -/
theorem elderDen_sub_humanDen :
    elderDen zd ⊆ humanDen zd := by native_decide

/-- HUMAN ⊆ ANIMATE at the feature denotation level. -/
theorem humanDen_sub_animateDen :
    humanDen zd ⊆ animateDen zd := by native_decide

/-- ANIMATE ⊆ π at the feature denotation level. -/
theorem animateDen_sub_piDen' :
    animateDen zd ⊆ piDen zd := by native_decide

-- ============================================================================
-- § 11: SINGULAR/PLURAL and Composition Order
-- ============================================================================

/-! @cite{toosarvandani-2023} §3.2 establishes that person/animacy features
    compose via ⊕ while number features compose via ∩. These two composition
    modes MUST apply in a specific order: ⊕ first, then ∩ SINGULAR/PLURAL.

    If ∩ SINGULAR were interleaved within the ⊕ chain, the ⊕ operator
    would undo SINGULAR's filtering by creating new pluralities from
    the remaining singletons. This non-commutativity is why person and
    number occupy DIFFERENT functional heads in the nominal structure. -/

/-- Correct composition order: ⊕ all person features first, then
    ∩ SINGULAR. First-person singular = {speaker}.
    @cite{toosarvandani-2023} (57). -/
theorem correct_1sg :
    singularFilter (oplus (speakerDen zd) (oplus (participantDen zd) (piDen zd))) =
    {({.i} : Finset ZapInd)} := by native_decide

/-- ⊕ and ∩ SINGULAR do not commute. Interleaving SINGULAR within the
    ⊕ chain gives different (wrong) results because ⊕ creates new
    pluralities from the singletons that SINGULAR preserved.
    @cite{toosarvandani-2023} §3.2. -/
theorem oplus_singular_noncommutative :
    singularFilter (oplus (speakerDen zd) (participantDen zd)) ≠
    oplus (speakerDen zd) (singularFilter (participantDen zd)) := by
  native_decide

/-- The wrong order produces plural sums: ⊕ SPEAKER applied after
    SINGULAR creates {speaker, addressee} from singleton {addressee},
    undoing SINGULAR's filtering. -/
theorem wrong_order_produces_plural :
    ({.i, .u} : Finset ZapInd) ∈
      oplus (speakerDen zd) (singularFilter (participantDen zd)) := by
  native_decide

-- ============================================================================
-- § 12: Bridges to Core
-- ============================================================================

/-- Map PronType to binary person features (±participant, ±author).
    Connects the 6-feature DFeature geometry to the binary person system
    in `Features.Person`. -/
def PronType.toPersonFeatures : PronType → Features.Person.Features
  | .first => ⟨true, true⟩
  | .second => ⟨true, false⟩
  | _ => ⟨false, false⟩

/-- PronType.toPersonFeatures agrees with the PersonLevel route:
    PronType → PersonLevel → Features. The two independent decompositions
    of person are consistent. -/
theorem person_features_consistent : ∀ p : PronType,
    p.toPersonFeatures = p.toPersonLevel.toFeatures := by
  native_decide

/-- Map third-person pronoun types to AnimacyLevel.
    Elder and human both map to `.human` (elder is a human subtype).
    SAPs return `none` — they are typed by person, not animacy. -/
def PronType.toAnimacyLevel : PronType → Option Features.Prominence.AnimacyLevel
  | .thirdElder => some .human
  | .thirdHuman => some .human
  | .thirdAnimal => some .animate
  | .thirdInanimate => some .inanimate
  | _ => none

/-- The 4-way Zapotec animacy system REFINES the 3-way typological scale.
    Elder and human both collapse to AnimacyLevel.human, but PCC
    distinguishes them — a finer distinction invisible to the coarser
    scale. @cite{toosarvandani-2023}'s central empirical contribution. -/
theorem zapotec_refines_3way :
    PronType.toAnimacyLevel .thirdElder = PronType.toAnimacyLevel .thirdHuman ∧
    pccLicit .thirdElder .thirdHuman = true ∧
    pccLicit .thirdHuman .thirdElder = false := by native_decide

/-- All PronType person features are well-formed (no [−participant, +author]). -/
theorem prontype_features_wellFormed : ∀ p : PronType,
    p.toPersonFeatures.wellFormed = true := by native_decide

end Toosarvandani2023
