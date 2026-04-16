import Linglib.Theories.Morphology.Core.MirrorPrinciple

/-!
# @cite{baker-1985}: The Mirror Principle and Morphosyntactic Explanation
@cite{baker-1985}

This study file verifies the Mirror Principle's predictions against
data from Chamorro, Quechua, and Bantu languages, as presented in
@cite{baker-1985}.

## Structure

- **§1**: Chamorro — passive, causative, and number agreement
  interactions (§§1, 3.1 of the paper)
- **§2**: Quechua — causative-reciprocal ordering determines
  interpretation (§4.1)
- **§3**: Bantu and Huichol — passive-applicative affix ordering (§4.2)
- **§4**: Cross-linguistic verification of the Agreement
  Restriction (§3.2)
-/

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
    GFRuleType.feeds .applicative .passive = true ∧
    ruleOrder chiMwini = [.applicative, .passive] ∧
    ruleOrder kinyarwanda = [.applicative, .passive] ∧
    ruleOrder huichol = [.applicative, .passive] :=
  ⟨rfl, rfl, rfl, rfl⟩

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
