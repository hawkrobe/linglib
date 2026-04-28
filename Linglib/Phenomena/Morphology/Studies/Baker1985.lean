import Linglib.Core.Morphology.MorphRule

/-!
# @cite{baker-1985}: The Mirror Principle and Morphosyntactic Explanation
@cite{baker-1985}

This study file verifies the Mirror Principle's predictions against
data from Chamorro, Quechua, and Bantu languages, as presented in
@cite{baker-1985}.

## Structure

- **§0**: Mirror-Principle substrate (was `Theories/Morphology/Core/
  MirrorPrinciple.lean`; relocated 0.230.455 — Baker is the founding
  paper, anchor lives here per CLAUDE.md "every file is anchored").
- **§1**: Chamorro — passive, causative, and number agreement
  interactions (§§1, 3.1 of the paper)
- **§2**: Quechua — causative-reciprocal ordering determines
  interpretation (§4.1)
- **§3**: Bantu and Huichol — passive-applicative affix ordering (§4.2)
- **§4**: Cross-linguistic verification of the Agreement
  Restriction (§3.2)
-/

-- ============================================================================
-- §0: Mirror Principle Substrate (Baker 1985)
-- ============================================================================

/-! "Morphological derivations must directly reflect syntactic derivations
(and vice versa)." (@cite{baker-1985} (4)) Each grammatical function
changing rule (GF-rule) — passive, causative, applicative, reflexive/
reciprocal — simultaneously adds an affix to the verb and changes the
grammatical functions of arguments. The Mirror Principle requires the
morphological ordering (affix layering) to match the syntactic ordering
(rule application sequence).

@cite{baker-1985} §6 argues the Mirror Principle should not be a
stipulation but follow from the architecture: in a framework where
GF-rules are a single process with both effects, mirroring is by
construction. Formalized below via `DerivationStep`. -/

namespace Morphology.MirrorPrinciple

open Core.Morphology (MorphCategory)

/-- Grammatical function changing rules (GF-rules). @cite{baker-1985} §§2-4. -/
inductive GFRuleType where
  | passive
  | causative
  | applicative
  | reflexReciprocal
  deriving DecidableEq, Repr, BEq

/-- Map GF-rules to @cite{bybee-1985}'s morphological categories. -/
def GFRuleType.toMorphCategory : GFRuleType → MorphCategory
  | .passive => .voice
  | .causative => .valence
  | .applicative => .valence
  | .reflexReciprocal => .valence

/-- A single step bundling morphological + syntactic effects. By
    bundling, the Mirror Principle holds by construction. -/
structure DerivationStep where
  rule : GFRuleType
  affix : String
  isPrefix : Bool := false
  deriving DecidableEq, Repr, BEq

/-- Steps ordered first-applied (innermost) to last-applied (outermost). -/
abbrev Derivation := List DerivationStep

def ruleOrder (d : Derivation) : List GFRuleType := d.map (·.rule)
def affixOrder (d : Derivation) : List String := d.map (·.affix)

/-- The orderings are isomorphic by construction — the Mirror Principle. -/
theorem mirror_by_construction (d : Derivation) :
    (ruleOrder d).length = (affixOrder d).length := by
  simp [ruleOrder, affixOrder]

inductive AgreementPosition where
  | inner | outer
  deriving DecidableEq, Repr, BEq

inductive GFReference where
  | semantic | surface
  deriving DecidableEq, Repr, BEq

structure AgreementPattern where
  position : AgreementPosition
  reference : GFReference
  deriving DecidableEq, Repr, BEq

/-- Inner position → pre-rule (semantic) GFs; outer → post-rule (surface). -/
def deriveReference : AgreementPosition → GFReference
  | .inner => .semantic
  | .outer => .surface

def AgreementPattern.isAttested (p : AgreementPattern) : Bool :=
  p.reference == deriveReference p.position

theorem inner_semantic_attested :
    (AgreementPattern.mk .inner .semantic).isAttested = true := rfl
theorem outer_surface_attested :
    (AgreementPattern.mk .outer .surface).isAttested = true := rfl
theorem outer_semantic_unattested :
    (AgreementPattern.mk .outer .semantic).isAttested = false := rfl
theorem inner_surface_unattested :
    (AgreementPattern.mk .inner .surface).isAttested = false := rfl

/-- Exactly two of four patterns are attested (Baker (27)). -/
theorem agreement_restriction_count :
    (([⟨.inner, .semantic⟩, ⟨.outer, .semantic⟩,
       ⟨.inner, .surface⟩, ⟨.outer, .surface⟩] :
       List AgreementPattern).filter (·.isAttested)).length
    = 2 := by
  decide

theorem attested_are_27a_and_27d :
    ([⟨.inner, .semantic⟩, ⟨.outer, .semantic⟩,
      ⟨.inner, .surface⟩, ⟨.outer, .surface⟩] :
      List AgreementPattern).filter (·.isAttested)
    = [⟨.inner, .semantic⟩, ⟨.outer, .surface⟩] := by
  decide

theorem derived_reference_attested (pos : AgreementPosition) :
    (AgreementPattern.mk pos (deriveReference pos)).isAttested = true := by
  cases pos <;> rfl

/-- Applicative feeds passive: appl creates the DO that passive promotes. -/
def GFRuleType.Feeds (r1 r2 : GFRuleType) : Prop :=
  r1 = .applicative ∧ r2 = .passive

instance : DecidableRel GFRuleType.Feeds := fun _ _ => by
  unfold GFRuleType.Feeds; exact inferInstance

def feedingOrder (feeder fed : GFRuleType) : List GFRuleType := [feeder, fed]

theorem appl_feeds_passive :
    GFRuleType.Feeds .applicative .passive := ⟨rfl, rfl⟩

theorem appl_pass_predicted :
    feedingOrder .applicative .passive = [.applicative, .passive] := rfl

/-- The morphological domain of the Mirror Principle. @cite{baker-1985} §5. -/
inductive MorphDomain where
  | concatenative | cliticization | nonconcatenative
  deriving DecidableEq, Repr

def MorphDomain.InScope (d : MorphDomain) : Prop := d = .concatenative

instance : DecidablePred MorphDomain.InScope := fun d => by
  unfold MorphDomain.InScope; exact inferInstance

/-- GF-rule morphemes are inside agreement per Bybee's hierarchy. -/
theorem gfRule_inside_agreement (r : GFRuleType) :
    r.toMorphCategory.peripherality < MorphCategory.agreement.peripherality := by
  cases r <;> decide

end Morphology.MirrorPrinciple

namespace Baker1985

open Morphology.MirrorPrinciple

-- ============================================================================
-- §1: Chamorro (Baker §§1, 3.1)
-- ============================================================================

-- ### Chamorro GF-rules and fan- agreement
--
-- Chamorro (Austronesian) has three relevant verbal processes:
-- Number Agreement (man- or fan-) is a prefix registering plurality
-- of the subject; Passive (-in-) is an infix promoting object to
-- subject; Causative (na'-) is a prefix adding a causer as subject.
--
-- The apparent idiosyncrasies of fan- agreement — agreeing with the
-- surface subject in passives but the underlying subject in causatives —
-- are explained by the Mirror Principle: fan-'s position relative to
-- the GF-rule morpheme determines which GFs it references.
--
-- @cite{baker-1985} §§1, 3.1.

section Chamorro

/-- Passive sentence: *fan-in-saolak* 'be spanked (pl)'.

    Morphological structure: [fan [in [saolak]]]
    *fan-* (agreement) is OUTSIDE *-in-* (passive).

    By the Mirror Principle, *fan-* was added after passive,
    so it references the post-passive (surface) subject —
    'the children', the derived subject.

    @cite{baker-1985} (15b), (21). -/
def chamorroPassiveAgreement : AgreementPattern :=
  ⟨.outer, .surface⟩

/-- Causative sentence: *na'-fan-otchu* 'make eat (pl)'.

    Morphological structure: [na' [fan [otchu]]]
    *fan-* (agreement) is INSIDE *na'-* (causative).

    By the Mirror Principle, *fan-* was added before causative,
    so it references the pre-causative (semantic) subject —
    the underlying subject of 'eat'.

    @cite{baker-1985} (15c), (23). -/
def chamorroCausativeAgreement : AgreementPattern :=
  ⟨.inner, .semantic⟩

/-- Both Chamorro agreement patterns are attested. -/
theorem chamorro_passive_attested :
    chamorroPassiveAgreement.isAttested = true := rfl

theorem chamorro_causative_attested :
    chamorroCausativeAgreement.isAttested = true := rfl

/-- Chamorro exhibits both attested patterns in a single language,
    confirming the Agreement Restriction is a property of UG, not a
    language-specific parameter. @cite{baker-1985} §3.1. -/
theorem chamorro_shows_both_attested :
    chamorroPassiveAgreement.isAttested = true ∧
    chamorroCausativeAgreement.isAttested = true :=
  ⟨rfl, rfl⟩

/-- Causative of passive: *na'-fan-s-in-aolak*
    'I had the children spanked by their father.'

    Morphological structure: [na' [fan [in [saolak]]]]
    Derivation order: passive first, then causative.
    *fan-* is between them — added after passive, before causative.
    → References the intermediate subject (post-passive, pre-causative)
    = 'the children' (the derived subject of the passive).

    @cite{baker-1985} (25), (26). -/
def chamorroCausativePassive : Derivation :=
  [{ rule := .passive, affix := "-in-", isPrefix := true },
   { rule := .causative, affix := "na'-", isPrefix := true }]

theorem chamorro_passive_before_causative :
    ruleOrder chamorroCausativePassive = [.passive, .causative] := rfl

end Chamorro

-- ============================================================================
-- §2: Quechua (Baker §4.1)
-- ============================================================================

/-! ### Quechua causative-reciprocal interactions

Quechua shows that causative *-chi* and reciprocal *-naku* can
appear in either order on the verb, with different interpretations
that the Mirror Principle correctly predicts. The difference in
morpheme ordering corresponds to a difference in which arguments
are bound by the reciprocal, which follows from the different
syntactic derivation orders.

@cite{baker-1985} §4.1. -/

section Quechua

/-- Reciprocal inside causative: *maqa-naku-ya-chi-n*
    'He is causing them to beat each other.'

    Morpheme order (inner→outer): root, *-naku* (recip), *-chi* (caus)
    Mirror Principle: reciprocal applied first, then causative.
    → Reciprocal binds agent and patient of root verb
    → Causative adds a new causer
    → Causer causes [reciprocal beating]

    @cite{baker-1985} (39a), (45)–(46). -/
def quechuaRecipInsideCaus : Derivation :=
  [{ rule := .reflexReciprocal, affix := "-naku" },
   { rule := .causative, affix := "-chi" }]

/-- Causative inside reciprocal: *maqa-chi-naku-rka-n*
    'They let someone beat each other.'

    Morpheme order (inner→outer): root, *-chi* (caus), *-naku* (recip)
    Mirror Principle: causative applied first, then reciprocal.
    → Causative adds a causer first
    → Reciprocal then binds the causer and the patient
    → The causers reciprocally [let someone beat them]

    @cite{baker-1985} (39b), (47)–(48). -/
def quechuaCausInsideRecip : Derivation :=
  [{ rule := .causative, affix := "-chi" },
   { rule := .reflexReciprocal, affix := "-naku" }]

/-- Reciprocal-inside-causative: reciprocal applies first. -/
theorem quechua_recip_caus_order :
    ruleOrder quechuaRecipInsideCaus = [.reflexReciprocal, .causative] := rfl

/-- Causative-inside-reciprocal: causative applies first. -/
theorem quechua_caus_recip_order :
    ruleOrder quechuaCausInsideRecip = [.causative, .reflexReciprocal] := rfl

/-- Different morpheme orderings produce different syntactic orderings
    and hence different interpretations. The Mirror Principle links
    all three: morpheme order ↔ syntactic order ↔ interpretation. -/
theorem quechua_orderings_differ :
    ruleOrder quechuaRecipInsideCaus ≠ ruleOrder quechuaCausInsideRecip := by
  native_decide

end Quechua

-- ============================================================================
-- §3: Bantu and Huichol passive-applicative ordering (Baker §4.2)
-- ============================================================================

/-! ### Passive-applicative interactions

When both passive and applicative appear on the same verb, the
applicative morpheme is universally closer to the root. The Mirror
Principle predicts this: applicative creates a new direct object
that passive can then promote to subject, so applicative must
apply first (its affix is inner).

Attested: V-appl-pass
Not attested: *V-pass-appl (for oblique-to-subject promotion)

@cite{baker-1985} §4.2. -/

section PassiveApplicative

/-- Chi-Mwi:ni: *tet-el-el-a* 'bring-appl-asp-pass'
    Applicative *-el* closer to root than passive.
    @cite{baker-1985} (56c). -/
def chiMwini : Derivation :=
  [{ rule := .applicative, affix := "-el" },
   { rule := .passive, affix := "-a" }]

/-- Kinyarwanda: *andik-iish-w-a* 'write-instr-pass-asp'
    Applicative *-iish* closer to root than passive *-w*.
    @cite{baker-1985} (57c). -/
def kinyarwanda : Derivation :=
  [{ rule := .applicative, affix := "-iish" },
   { rule := .passive, affix := "-w" }]

/-- Huichol: *puutinanai-ri-yeri* 'buy-ben-pass'
    Benefactive-applicative *-ri* closer to root than passive *-yeri*.
    @cite{baker-1985} (55). -/
def huichol : Derivation :=
  [{ rule := .applicative, affix := "-ri" },
   { rule := .passive, affix := "-yeri" }]

/-- All three languages show applicative before passive,
    as predicted by the Mirror Principle. -/
theorem all_appl_before_pass :
    ruleOrder chiMwini = [.applicative, .passive] ∧
    ruleOrder kinyarwanda = [.applicative, .passive] ∧
    ruleOrder huichol = [.applicative, .passive] :=
  ⟨rfl, rfl, rfl⟩

/-- All three languages show the order predicted by the feeding
    relationship: applicative feeds passive, so applicative is
    universally inner. -/
theorem all_match_feeding_prediction :
    GFRuleType.Feeds .applicative .passive ∧
    ruleOrder chiMwini = [.applicative, .passive] ∧
    ruleOrder kinyarwanda = [.applicative, .passive] ∧
    ruleOrder huichol = [.applicative, .passive] :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩

/-- Bemba (Bantu) causative-reciprocal: *Naa-mon-eshy-ana*
    'I made Mwape and Mutumba see each other.'

    Bemba uses the Chamorro-type causative (underlying subject
    becomes oblique), unlike Quechua (underlying subject stays
    as object). This leads to different morpheme ordering for
    the same interpretation compared to Quechua — but the Mirror
    Principle still holds: the morpheme ordering reflects the
    syntactic derivation order.

    In Bemba: causative precedes reciprocal morphologically,
    because Bemba's causative changes GFs differently: the
    new causer occupies the object position, so reciprocal
    must apply after causative to bind it.

    @cite{baker-1985} (49), (52). -/
def bembaCausRecip : Derivation :=
  [{ rule := .causative, affix := "-eshy" },
   { rule := .reflexReciprocal, affix := "-ana" }]

theorem bemba_caus_before_recip :
    ruleOrder bembaCausRecip = [.causative, .reflexReciprocal] := rfl

end PassiveApplicative

-- ============================================================================
-- §4: Cross-linguistic Agreement Restriction (Baker §3.2)
-- ============================================================================

/-! ### The Agreement Restriction across languages

@cite{baker-1985} (27) predicts that of four logical possibilities
for combining agreement position and GF reference, only two are
attested cross-linguistically:

| | Semantic GFs | Surface GFs |
|-------|-------------|-------------|
| Inner | ✓ (27a) | ✗ (27c) |
| Outer | ✗ (27b) | ✓ (27d) |

Evidence:
- **(27a)** inner + semantic: Chamorro causative *fan-*, Turkish,
  Sanskrit, Quechua (agreement closer to V, references underlying GFs)
- **(27d)** outer + surface: most agglutinative languages; Chamorro
  passive *fan-* (agreement farther from V, references surface GFs)

No clear cases of (27b) or (27c) have been found.

The Mirror Principle derives this restriction: morphological position
determines derivational timing, and derivational timing determines
which GFs are visible for agreement. -/

section AgreementRestriction

/-- The Mirror Principle correctly derives the attested reference
    for each morphological position. -/
theorem mirror_derives_reference_inner :
    deriveReference .inner = .semantic := rfl

theorem mirror_derives_reference_outer :
    deriveReference .outer = .surface := rfl

/-- Every derived pattern is attested; no stipulation is needed. -/
theorem derived_always_attested (pos : AgreementPosition) :
    (AgreementPattern.mk pos (deriveReference pos)).isAttested = true := by
  cases pos <;> rfl

/-- The Chamorro passive pattern is exactly the derived pattern
    for outer agreement. -/
theorem chamorro_passive_is_derived :
    chamorroPassiveAgreement
    = AgreementPattern.mk .outer (deriveReference .outer) := rfl

/-- The Chamorro causative pattern is exactly the derived pattern
    for inner agreement. -/
theorem chamorro_causative_is_derived :
    chamorroCausativeAgreement
    = AgreementPattern.mk .inner (deriveReference .inner) := rfl

/-- Achenese (Austronesian) provides a test case: verbal agreement
    references the underlying (semantic) subject in both active and
    passive sentences, and Achenese has no overt passive morpheme.
    Since there is no GF-rule morpheme on the verb, the agreement
    morpheme is trivially "inner" (there is nothing for it to be
    outer to), and it references semantic GFs — consistent with
    pattern (27a). @cite{baker-1985} (31). -/
def acheneseAgreement : AgreementPattern :=
  ⟨.inner, .semantic⟩

theorem achenese_attested :
    acheneseAgreement.isAttested = true := rfl

end AgreementRestriction

end Baker1985
