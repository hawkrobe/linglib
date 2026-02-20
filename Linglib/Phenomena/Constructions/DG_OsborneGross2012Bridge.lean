import Linglib.Theories.Syntax.DependencyGrammar.Formal.CatenalConstruction
import Linglib.Theories.Syntax.ConstructionGrammar.Studies.FillmoreKayOConnor1988
import Linglib.Phenomena.Constructions.Studies.OsborneGross2012.Data

/-!
# Bridge: Osborne & Groß (2012) DG Catenae → CxG Constructions

Connects the dependency trees from `Studies/OsborneGross2012/Data.lean`
to the catena theory from `Catena.lean` and the CxG types from
`ConstructionGrammar.Basic` and `FillmoreKayOConnor1988`.

## Verified Claims

**Claim 1** (p. 176): Every construction type — idioms, LVCs, verb chains,
displacement, comparative correlatives — corresponds to a catena. All 10
example trees are verified. All non-trivial constructions are non-constituent
catenae, demonstrating that the catena concept is needed.

**Claim 2** (p. 176): When a more fixed construct (idiom, LVC) is broken up
by a less fixed one (NP), **both** form catenae. Verified for all 7
V-det-N examples and the CC's two clauses.

## CxG ↔ DG Bridge

Four `CatenalCx` instances covering the full specificity spectrum
(lexicallySpecified → partiallyOpen → fullyAbstract), connecting CxG
`Construction` descriptions to DG catena witnesses.

FKO1988 `IdiomType` classification is bridged to catena verification:
substantive decoding idioms ("kick the bucket") and formal idioms
(the comparative correlative) are both catenae.

## References

- Osborne, T. & Groß, T. (2012). Constructions are catenae. *CogLing* 23(1).
- Fillmore, C. J., Kay, P. & O'Connor, M. C. (1988). Let Alone. *Language* 64(3).
-/

namespace Phenomena.Constructions.Studies.OsborneGross2012.Bridge

open DepGrammar DepGrammar.Catena ConstructionGrammar
open Phenomena.Constructions.Studies.OsborneGross2012
open DepGrammar.CatenalConstruction

-- ============================================================================
-- §1: Per-Datum Catena Verification — Idioms
-- ============================================================================

theorem spillTheBeans_catena :
    isCatena spillTheBeans.deps [0, 2] = true := by native_decide

theorem spillTheBeans_not_constituent :
    isConstituent spillTheBeans.deps 3 [0, 2] = false := by native_decide

theorem giveTheSack_catena :
    isCatena giveTheSack.deps [0, 2] = true := by native_decide

theorem giveTheSack_not_constituent :
    isConstituent giveTheSack.deps 3 [0, 2] = false := by native_decide

theorem kickTheBucket_catena :
    isCatena kickTheBucket.deps [0, 2] = true := by native_decide

theorem kickTheBucket_not_constituent :
    isConstituent kickTheBucket.deps 3 [0, 2] = false := by native_decide

theorem pullSomeStrings_catena :
    isCatena pullSomeStrings.deps [0, 2] = true := by native_decide

theorem pullSomeStrings_not_constituent :
    isConstituent pullSomeStrings.deps 3 [0, 2] = false := by native_decide

-- ============================================================================
-- §2: Per-Datum Catena Verification — LVCs
-- ============================================================================

theorem takeABath_catena :
    isCatena takeABath.deps [0, 2] = true := by native_decide

theorem takeABath_not_constituent :
    isConstituent takeABath.deps 3 [0, 2] = false := by native_decide

theorem haveALook_catena :
    isCatena haveALook.deps [0, 2] = true := by native_decide

theorem haveALook_not_constituent :
    isConstituent haveALook.deps 3 [0, 2] = false := by native_decide

theorem giveAYell_catena :
    isCatena giveAYell.deps [0, 2] = true := by native_decide

theorem giveAYell_not_constituent :
    isConstituent giveAYell.deps 3 [0, 2] = false := by native_decide

-- ============================================================================
-- §3: Per-Datum Catena Verification — Verb Chains
-- ============================================================================

/-- 3-element chain {will, have, helped} = {1,2,3}. -/
theorem verbChain3_catena :
    isCatena heWillHaveHelped.deps [1, 2, 3] = true := by native_decide

theorem verbChain3_not_constituent :
    isConstituent heWillHaveHelped.deps 4 [1, 2, 3] = false := by native_decide

/-- 4-element chain {will, have, been, doing} = {1,2,3,4}. -/
theorem verbChain4_catena :
    isCatena sheWillHaveBeenDoingIt.deps [1, 2, 3, 4] = true := by native_decide

theorem verbChain4_not_constituent :
    isConstituent sheWillHaveBeenDoingIt.deps 6 [1, 2, 3, 4] = false := by native_decide

/-- The full VP {will, have, been, doing, it} = {1,2,3,4,5} is a catena but
    not a constituent — the subject "she" prevents it. -/
theorem fullVP_catena :
    isCatena sheWillHaveBeenDoingIt.deps [1, 2, 3, 4, 5] = true := by native_decide

theorem fullVP_not_constituent :
    isConstituent sheWillHaveBeenDoingIt.deps 6 [1, 2, 3, 4, 5] = false := by native_decide

-- ============================================================================
-- §4: Per-Datum Catena Verification — Displacement
-- ============================================================================

theorem displacement_catena :
    isCatena beansSheSpilled.deps [0, 2] = true := by native_decide

theorem displacement_not_constituent :
    isConstituent beansSheSpilled.deps 3 [0, 2] = false := by native_decide

-- ============================================================================
-- §5: Per-Datum Catena Verification — Comparative Correlative
-- ============================================================================

/-- Protasis = {the, more, you, eat} = {0,1,2,3}. -/
theorem cc_protasis_catena :
    isCatena theMoreTheFatter.deps [0, 1, 2, 3] = true := by native_decide

/-- Apodosis = {the, fatter, you, get} = {4,5,6,7}. -/
theorem cc_apodosis_catena :
    isCatena theMoreTheFatter.deps [4, 5, 6, 7] = true := by native_decide

theorem cc_apodosis_not_constituent :
    isConstituent theMoreTheFatter.deps 8 [4, 5, 6, 7] = false := by native_decide

/-- Protasis IS a constituent (subtree of eat = {eat, you, more, the}). -/
theorem cc_protasis_is_constituent :
    isConstituent theMoreTheFatter.deps 8 [0, 1, 2, 3] = true := by native_decide

/-- Degree markers {the, more} and {the, fatter} each form catenae. -/
theorem cc_degree_markers_catenae :
    isCatena theMoreTheFatter.deps [0, 1] = true ∧
    isCatena theMoreTheFatter.deps [4, 5] = true := by
  constructor <;> native_decide

-- ============================================================================
-- §6: Claim 1 — Constructions Are Catenae (p. 176)
-- ============================================================================

/-- **Claim 1** (Osborne & Groß 2012, p. 176): Constructions are catenae.

    Verified across all five construction types, 10 example trees total. -/
theorem claim1_constructions_are_catenae :
    -- Idioms (4)
    isCatena spillTheBeans.deps [0, 2] = true ∧
    isCatena giveTheSack.deps [0, 2] = true ∧
    isCatena kickTheBucket.deps [0, 2] = true ∧
    isCatena pullSomeStrings.deps [0, 2] = true ∧
    -- LVCs (3)
    isCatena takeABath.deps [0, 2] = true ∧
    isCatena haveALook.deps [0, 2] = true ∧
    isCatena giveAYell.deps [0, 2] = true ∧
    -- Verb chains (2)
    isCatena heWillHaveHelped.deps [1, 2, 3] = true ∧
    isCatena sheWillHaveBeenDoingIt.deps [1, 2, 3, 4] = true ∧
    -- Displacement (1)
    isCatena beansSheSpilled.deps [0, 2] = true ∧
    -- Comparative correlative (2 clauses)
    isCatena theMoreTheFatter.deps [0, 1, 2, 3] = true ∧
    isCatena theMoreTheFatter.deps [4, 5, 6, 7] = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- All non-constituent constructions: these require the catena concept —
    a constituent-based framework cannot represent any of them. -/
theorem all_constructions_not_constituent :
    -- Idioms
    isConstituent spillTheBeans.deps 3 [0, 2] = false ∧
    isConstituent giveTheSack.deps 3 [0, 2] = false ∧
    isConstituent kickTheBucket.deps 3 [0, 2] = false ∧
    isConstituent pullSomeStrings.deps 3 [0, 2] = false ∧
    -- LVCs
    isConstituent takeABath.deps 3 [0, 2] = false ∧
    isConstituent haveALook.deps 3 [0, 2] = false ∧
    isConstituent giveAYell.deps 3 [0, 2] = false ∧
    -- Verb chains
    isConstituent heWillHaveHelped.deps 4 [1, 2, 3] = false ∧
    isConstituent sheWillHaveBeenDoingIt.deps 6 [1, 2, 3, 4] = false ∧
    -- Displacement
    isConstituent beansSheSpilled.deps 3 [0, 2] = false ∧
    -- CC apodosis
    isConstituent theMoreTheFatter.deps 8 [4, 5, 6, 7] = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- §7: Claim 2 — Interleaving Preserves Catena-hood (p. 176)
-- ============================================================================

/-! Claim 2: when a more fixed construct (idiom, LVC) is broken up by a
less fixed one (NP), the words of **both** always form catenae.

In each V-det-N tree, the construction {V, N} = {0, 2} is a catena AND
the intervening NP {det, N} = {1, 2} is also a catena. The NP breaks up
the construction, but catena-hood is preserved for both participants.

For the CC, the protasis and apodosis interleave at the sentence level:
the apodosis depends on the protasis (advcl), yet both form catenae. -/

/-- **Claim 2** (Osborne & Groß 2012, p. 176): When a more fixed construct
    is broken up by a less fixed one, both form catenae.

    Verified for all 7 V-det-N examples (idioms + LVCs) and the CC's
    two clauses. Each pair shows: construction catena ∧ intervening catena. -/
theorem claim2_interleaving_preserves_catenae :
    -- "spill the beans": idiom {0,2} + NP {1,2}
    isCatena spillTheBeans.deps [0, 2] = true ∧
    isCatena spillTheBeans.deps [1, 2] = true ∧
    -- "give the sack": idiom + NP
    isCatena giveTheSack.deps [0, 2] = true ∧
    isCatena giveTheSack.deps [1, 2] = true ∧
    -- "kick the bucket": idiom + NP
    isCatena kickTheBucket.deps [0, 2] = true ∧
    isCatena kickTheBucket.deps [1, 2] = true ∧
    -- "pull some strings": idiom + NP
    isCatena pullSomeStrings.deps [0, 2] = true ∧
    isCatena pullSomeStrings.deps [1, 2] = true ∧
    -- "take a bath": LVC + NP
    isCatena takeABath.deps [0, 2] = true ∧
    isCatena takeABath.deps [1, 2] = true ∧
    -- "have a look": LVC + NP
    isCatena haveALook.deps [0, 2] = true ∧
    isCatena haveALook.deps [1, 2] = true ∧
    -- "give a yell": LVC + NP
    isCatena giveAYell.deps [0, 2] = true ∧
    isCatena giveAYell.deps [1, 2] = true ∧
    -- CC: protasis + apodosis
    isCatena theMoreTheFatter.deps [0, 1, 2, 3] = true ∧
    isCatena theMoreTheFatter.deps [4, 5, 6, 7] = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    <;> native_decide

-- ============================================================================
-- §8: CxG ↔ DG Bridge — CatenalCx Instances
-- ============================================================================

/-! Each construction type is represented as a `CatenalCx`: a CxG
`Construction` description paired with a DG tree and catena proof. -/

def idiomCx : CatenalCx :=
  { construction :=
      { name := "spill the beans"
        form := "V det N (idiomatic)"
        meaning := "divulge secret information"
        specificity := .lexicallySpecified }
    tree := spillTheBeans
    nodes := [0, 2]
    catena := by native_decide }

def lvcCx : CatenalCx :=
  { construction :=
      { name := "take a bath"
        form := "V_light det N"
        meaning := "perform the action denoted by N"
        specificity := .partiallyOpen }
    tree := takeABath
    nodes := [0, 2]
    catena := by native_decide }

def verbChainCx : CatenalCx :=
  { construction :=
      { name := "auxiliary verb chain"
        form := "Aux (Aux)* V"
        meaning := "tense–aspect–mood composition"
        specificity := .fullyAbstract }
    tree := heWillHaveHelped
    nodes := [1, 2, 3]
    catena := by native_decide }

def displacementCx : CatenalCx :=
  { construction :=
      { name := "topicalization"
        form := "XP_topic ... V ... _gap"
        meaning := "foreground XP as discourse topic"
        specificity := .fullyAbstract
        pragmaticFunction := "topic–comment articulation" }
    tree := beansSheSpilled
    nodes := [0, 2]
    catena := by native_decide }

/-- CatenalCx instances cover the full specificity spectrum. -/
theorem catenal_specificity_coverage :
    idiomCx.construction.specificity = .lexicallySpecified ∧
    lvcCx.construction.specificity = .partiallyOpen ∧
    verbChainCx.construction.specificity = .fullyAbstract ∧
    displacementCx.construction.specificity = .fullyAbstract :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §9: Bridge → FKO1988 Idiom Typology
-- ============================================================================

/-! FKO1988's `IdiomType` classification (interpretability × grammaticality ×
formality) is bridged to catena verification. Both ends of the formality
spectrum — substantive idioms and formal idioms — are catenae. -/

open ConstructionGrammar.Studies.FillmoreKayOConnor1988

/-- "kick the bucket" is a substantive decoding idiom in FKO1988's typology. -/
def kickTheBucketIdiomType : IdiomType :=
  { interpretability := .decoding
    grammaticality := .grammatical
    formality := .substantive }

/-- The CC is a formal idiom in FKO1988's typology (§1.2.1). -/
def ccIdiomType : IdiomType :=
  { interpretability := .encoding
    grammaticality := .grammatical
    formality := .formal }

/-- Both substantive and formal idioms are catenae: the idiom classification
    does not affect catena-hood. Substantive idiom {kick, bucket} and formal
    idiom protasis {the, more, you, eat} are both catenae. -/
theorem fko1988_idiom_types_are_catenae :
    -- Substantive idiom: "kick the bucket"
    kickTheBucketIdiomType.formality = .substantive ∧
    isCatena kickTheBucket.deps [0, 2] = true ∧
    -- Formal idiom: CC protasis
    ccIdiomType.formality = .formal ∧
    isCatena theMoreTheFatter.deps [0, 1, 2, 3] = true := by
  refine ⟨rfl, ?_, rfl, ?_⟩ <;> native_decide

/-- Bridge to FKO1988 CC: the `comparativeCorrelative` construction from
    FKO1988 matches the CC tree verified here. Both describe the same
    formal idiom — FKO1988 provides the CxG description, Osborne & Groß
    provide the DG catena analysis. -/
theorem cc_matches_fko1988 :
    comparativeCorrelative.name = "the X-er the Y-er" ∧
    comparativeCorrelative.specificity = .fullyAbstract ∧
    isCatena theMoreTheFatter.deps [0, 1, 2, 3] = true ∧
    isCatena theMoreTheFatter.deps [4, 5, 6, 7] = true := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> native_decide

end Phenomena.Constructions.Studies.OsborneGross2012.Bridge
