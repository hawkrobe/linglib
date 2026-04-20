import Linglib.Core.Dependency.Basic
import Linglib.Theories.Syntax.DependencyGrammar.Formal.CatenalConstruction
import Linglib.Theories.Syntax.ConstructionGrammar.Studies.FillmoreKayOConnor1988

/-!
# Osborne & Groß (2012): Constructions Are Catenae — Data

Dependency trees from Osborne & Groß (2012), "Constructions are catenae:
Construction Grammar meets Dependency Grammar" (*Cognitive Linguistics*
23(1):165–216).

Each tree is a concrete linguistic example analyzed with dependency
structure. The catena proofs connecting these trees to the paper's
theoretical claims are in `DG_OsborneGross2012Bridge.lean`.

## Construction Types

The paper demonstrates catenae across five construction types:
1. **Idioms** (§3): fixed V+N combinations where the idiomatic words
   form a catena skipping the determiner
2. **Light verb constructions** (§4): semantically bleached verb +
   meaningful noun, same dependency pattern as idioms
3. **Verb chains** (§5): auxiliary hierarchies forming connected chains
4. **Displacement** (§7): topicalized element + governor connected
   despite linear separation
5. **Comparative correlative** (§6): each correlative clause forms a catena
-/

namespace Phenomena.Constructions.Studies.OsborneGross2012

open DepGrammar

-- ============================================================================
-- §1: Construction Type Classification
-- ============================================================================

/-- The five construction types analyzed in @cite{osborne-gross-2012}. -/
inductive ConstructionType where
  | idiom                    -- "spill the beans", "kick the bucket"
  | lightVerbConstruction    -- "take a bath", "give a yell"
  | verbChain                -- "will have helped", "will have been doing"
  | displacement             -- "Beans she spilled"
  | comparativeCorrelative   -- "the more you eat the fatter you get"
  deriving Repr, DecidableEq

-- ============================================================================
-- §2: Idioms (Osborne & Groß 2012, §3)
-- ============================================================================

/-- "spill the beans" (p. 181) — idiom {spill, beans} skips determiner.

    Words: spill(0) the(1) beans(2)
    Deps: spill(0) → beans(2:obj), beans(2) → the(1:det)
    Construction nodes: {0, 2} -/
def spillTheBeans : DepTree :=
  { words := [Word.mk' "spill" .VERB, Word.mk' "the" .DET, Word.mk' "beans" .NOUN]
    deps := [⟨0, 2, .obj⟩, ⟨2, 1, .det⟩]
    rootIdx := 0 }

/-- "give the sack" (p. 183) — same V-det-N pattern.

    Words: give(0) the(1) sack(2)
    Deps: give(0) → sack(2:obj), sack(2) → the(1:det)
    Construction nodes: {0, 2} -/
def giveTheSack : DepTree :=
  { words := [Word.mk' "give" .VERB, Word.mk' "the" .DET, Word.mk' "sack" .NOUN]
    deps := [⟨0, 2, .obj⟩, ⟨2, 1, .det⟩]
    rootIdx := 0 }

/-- "kick the bucket" (p. 181) — decoding idiom (FKO1988 §1.1.1).

    Words: kick(0) the(1) bucket(2)
    Deps: kick(0) → bucket(2:obj), bucket(2) → the(1:det)
    Construction nodes: {0, 2} -/
def kickTheBucket : DepTree :=
  { words := [Word.mk' "kick" .VERB, Word.mk' "the" .DET, Word.mk' "bucket" .NOUN]
    deps := [⟨0, 2, .obj⟩, ⟨2, 1, .det⟩]
    rootIdx := 0 }

/-- "pull some strings" (p. 183) — idiom {pull, strings} skips quantifier.

    Cf. `Catena.pulledSomeStrings` for the past-tense variant.

    Words: pull(0) some(1) strings(2)
    Deps: pull(0) → strings(2:obj), strings(2) → some(1:det)
    Construction nodes: {0, 2} -/
def pullSomeStrings : DepTree :=
  { words := [Word.mk' "pull" .VERB, Word.mk' "some" .DET, Word.mk' "strings" .NOUN]
    deps := [⟨0, 2, .obj⟩, ⟨2, 1, .det⟩]
    rootIdx := 0 }

-- ============================================================================
-- §3: Light Verb Constructions (Osborne & Groß 2012, §4)
-- ============================================================================

/-- "take a bath" (p. 187) — LVC {take, bath} skips determiner.

    The verb is semantically bleached; the V+N combination carries
    idiosyncratic meaning not predictable from its parts.

    Words: take(0) a(1) bath(2)
    Deps: take(0) → bath(2:obj), bath(2) → a(1:det)
    Construction nodes: {0, 2} -/
def takeABath : DepTree :=
  { words := [Word.mk' "take" .VERB, Word.mk' "a" .DET, Word.mk' "bath" .NOUN]
    deps := [⟨0, 2, .obj⟩, ⟨2, 1, .det⟩]
    rootIdx := 0 }

/-- "have a look" (p. 187) — same LVC pattern.

    Words: have(0) a(1) look(2)
    Deps: have(0) → look(2:obj), look(2) → a(1:det)
    Construction nodes: {0, 2} -/
def haveALook : DepTree :=
  { words := [Word.mk' "have" .VERB, Word.mk' "a" .DET, Word.mk' "look" .NOUN]
    deps := [⟨0, 2, .obj⟩, ⟨2, 1, .det⟩]
    rootIdx := 0 }

/-- "give a yell" (p. 187) — same LVC pattern.

    Words: give(0) a(1) yell(2)
    Deps: give(0) → yell(2:obj), yell(2) → a(1:det)
    Construction nodes: {0, 2} -/
def giveAYell : DepTree :=
  { words := [Word.mk' "give" .VERB, Word.mk' "a" .DET, Word.mk' "yell" .NOUN]
    deps := [⟨0, 2, .obj⟩, ⟨2, 1, .det⟩]
    rootIdx := 0 }

-- ============================================================================
-- §4: Verb Chains (Osborne & Groß 2012, §5)
-- ============================================================================

/-- "He will have helped" — 3-element verb chain (p. 190).

    In Osborne's DG, auxiliaries form a hierarchical chain (not UD-flat):
    will governs have, have governs helped. The verb chain is a catena but
    NOT a constituent — the subtree of will includes "he".

    Words: he(0) will(1) have(2) helped(3)
    Deps: will(1) → he(0:nsubj), will(1) → have(2:dep), have(2) → helped(3:dep)
    Construction nodes: {1, 2, 3} -/
def heWillHaveHelped : DepTree :=
  { words := [Word.mk' "he" .PRON, Word.mk' "will" .AUX,
              Word.mk' "have" .AUX, Word.mk' "helped" .VERB]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .dep⟩, ⟨2, 3, .dep⟩]
    rootIdx := 1 }

/-- "She will have been doing it" — 4-element verb chain (p. 190, ex. 19b).

    The full chain {will, have, been, doing} = {1,2,3,4} is a catena.
    The subject "she" and object "it" break it up linearly, but the chain
    remains connected in the dependency tree.

    Words: she(0) will(1) have(2) been(3) doing(4) it(5)
    Deps: will(1) → she(0:nsubj), will(1) → have(2:dep),
          have(2) → been(3:dep), been(3) → doing(4:dep),
          doing(4) → it(5:obj)
    Construction nodes: {1, 2, 3, 4} -/
def sheWillHaveBeenDoingIt : DepTree :=
  { words := [Word.mk' "she" .PRON, Word.mk' "will" .AUX,
              Word.mk' "have" .AUX, Word.mk' "been" .AUX,
              Word.mk' "doing" .VERB, Word.mk' "it" .PRON]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .dep⟩, ⟨2, 3, .dep⟩,
             ⟨3, 4, .dep⟩, ⟨4, 5, .obj⟩]
    rootIdx := 1 }

-- ============================================================================
-- §5: Displacement (Osborne & Groß 2012, §7)
-- ============================================================================

/-- "Beans she spilled" — topicalization (p. 200).

    The displaced element "beans" and its governor "spilled" form a catena
    despite being separated by "she" in the linear string. This is also a
    **risen catena** (see Discontinuity.lean): connected in the dependency
    tree but non-contiguous in linear order.

    Words: beans(0) she(1) spilled(2)
    Deps: spilled(2) → beans(0:obj), spilled(2) → she(1:nsubj)
    Construction nodes: {0, 2} -/
def beansSheSpilled : DepTree :=
  { words := [Word.mk' "beans" .NOUN, Word.mk' "she" .PRON,
              Word.mk' "spilled" .VERB]
    deps := [⟨2, 0, .obj⟩, ⟨2, 1, .nsubj⟩]
    rootIdx := 2 }

-- ============================================================================
-- §6: Comparative Correlative (Osborne & Groß 2012, §6)
-- ============================================================================

/-- "The more you eat the fatter you get" — comparative correlative
    (p. 194, ex. 23a).

    The CC is a formal idiom (FKO1988 §1.1.3): a productive syntactic
    pattern with non-compositional semantics. Each correlative clause
    forms a catena, and the apodosis is NOT a constituent.

    Words: the(0) more(1) you(2) eat(3) the(4) fatter(5) you(6) get(7)
    Deps: get(7) → eat(3:advcl),
          eat(3) → you(2:nsubj), eat(3) → more(1:advmod), more(1) → the(0:det),
          get(7) → you(6:nsubj), get(7) → fatter(5:xcomp), fatter(5) → the(4:det)
    Protasis nodes: {0, 1, 2, 3}
    Apodosis nodes: {4, 5, 6, 7} -/
def theMoreTheFatter : DepTree :=
  { words := [Word.mk' "the" .DET, Word.mk' "more" .ADV,
              Word.mk' "you" .PRON, Word.mk' "eat" .VERB,
              Word.mk' "the" .DET, Word.mk' "fatter" .ADJ,
              Word.mk' "you" .PRON, Word.mk' "get" .VERB]
    deps := [⟨7, 3, .advcl⟩,
             ⟨3, 2, .nsubj⟩, ⟨3, 1, .advmod⟩, ⟨1, 0, .det⟩,
             ⟨7, 6, .nsubj⟩, ⟨7, 5, .xcomp⟩, ⟨5, 4, .det⟩]
    rootIdx := 7 }

end Phenomena.Constructions.Studies.OsborneGross2012

/-! ## Bridge content (merged from DG_OsborneGross2012Bridge.lean) -/

/-!
# Bridge: Osborne & Groß (2012) DG Catenae → CxG Constructions
@cite{fillmore-kay-oconnor-1988} @cite{osborne-gross-2012}

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
    comparativeCorrelative.specificity = .partiallyOpen ∧
    isCatena theMoreTheFatter.deps [0, 1, 2, 3] = true ∧
    isCatena theMoreTheFatter.deps [4, 5, 6, 7] = true := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> native_decide

end Phenomena.Constructions.Studies.OsborneGross2012.Bridge
