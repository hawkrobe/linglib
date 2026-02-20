import Linglib.Theories.Syntax.DependencyGrammar.Core.Basic

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

/-- The five construction types analyzed in Osborne & Groß (2012). -/
inductive ConstructionType where
  | idiom                    -- "spill the beans", "kick the bucket"
  | lightVerbConstruction    -- "take a bath", "give a yell"
  | verbChain                -- "will have helped", "will have been doing"
  | displacement             -- "Beans she spilled"
  | comparativeCorrelative   -- "the more you eat the fatter you get"
  deriving Repr, DecidableEq, BEq

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
