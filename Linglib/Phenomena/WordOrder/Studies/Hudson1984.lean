import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.FunctionWords
import Linglib.Theories.Syntax.DependencyGrammar.Core.LexicalRules
import Linglib.Theories.Syntax.DependencyGrammar.Core.NetworkIntegration
import Linglib.Phenomena.WordOrder.SubjectAuxInversion

/-!
# Word Grammar Analysis of Subject-Auxiliary Inversion
@cite{hudson-1984}

Word Grammar handles inversion via subtype inheritance in a word-class
taxonomy (@cite{hudson-1984} pp. 117-118):

1. Verbs take a subject to their left by default
2. Auxiliaries inherit this subject/left specification from `verb`
3. The interrogative auxiliary is a subtype of `auxiliary` that locally
   overrides the subject's direction from left to right
4. Default inheritance does the rest — no special lexical rule needed

The "inverted auxiliary" is not derived by a transformation or lexical
rule that flips a direction. It is simply a different word class — a
subtype of `auxiliary` — with its own word-order specification that
overrides the inherited default.

## End-to-end chain

```
ClauseForm → wordClassForClauseType → englishAuxNet → resolveArgStr → satisfiesArgStr
```

Each tree is licensed (or rejected) by the network, connecting:
- SAI empirical data (SubjectAuxInversion.lean: ex01, ex02, ex04, ex05)
- WG inheritance network (NetworkIntegration.lean: englishAuxNet)
- Licensing predicate (Basic.lean: satisfiesArgStr)
- Fragment lexicon (English/FunctionWords, English/Nouns, etc.)
- Lexical rules (LexicalRules.lean: auxInversionRule)

Reference: @cite{hudson-1990}, @cite{gibson-2025}
-/

namespace Hudson1984

open DepGrammar DepGrammar.WG

-- ============================================================================
-- Words from the Fragment Lexicon
-- ============================================================================

private abbrev what := Fragments.English.Pronouns.what.toWord
private abbrev can := Fragments.English.FunctionWords.can.toWord
private abbrev john := Fragments.English.Nouns.john.toWordSg
private abbrev eat := Fragments.English.Predicates.Verbal.eat.toWordPl
private abbrev pizza := Fragments.English.Nouns.pizza.toWordSg
private abbrev sleep := Fragments.English.Predicates.Verbal.sleep.toWordPl

-- ============================================================================
-- Lexical Entries (derived from Fragment)
-- ============================================================================

/-- "can" - modal auxiliary (non-inverted).
    Features derived from Fragment FunctionWords.can. -/
private def lex_can : LexEntry :=
  { form := can.form
    cat := .AUX
    features := can.features
    argStr := argStr_Aux }

/-- "can" - modal auxiliary (inverted, derived by lexical rule) -/
private def lex_can_inv : LexEntry :=
  auxInversionRule.transform lex_can

-- ============================================================================
-- Example Trees: Intransitive (can + sleep)
-- ============================================================================

/-- "John can sleep" - declarative (subject left of aux)
    John ←subj─ can ─aux→ sleep -/
def johnCanSleepTree : DepTree :=
  { words := [john, can, sleep]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .aux⟩]
    rootIdx := 1 }

/-- "Can John sleep?" - interrogative (subject right of aux)
    can ─subj→ John
     └──aux→ sleep -/
def canJohnSleepTree : DepTree :=
  { words := [can, john, sleep]
    deps := [⟨0, 1, .nsubj⟩, ⟨0, 2, .aux⟩]
    rootIdx := 0 }

-- ============================================================================
-- Example Trees: Transitive (can + eat)
-- ============================================================================

/-- "What can John eat?" - Matrix wh-question (inverted)
    what ←obj─ can ─subj→ John
               └─aux→ eat -/
def whatCanJohnEatTree : DepTree :=
  { words := [what, can, john, eat]
    deps := [⟨1, 2, .nsubj⟩, ⟨1, 3, .aux⟩, ⟨3, 0, .obj⟩]
    rootIdx := 1 }

/-- "*What John can eat?" - Ungrammatical as matrix question
    what ←obj─ eat ←aux─ can ←subj─ John -/
def whatJohnCanEatTree : DepTree :=
  { words := [what, john, can, eat]
    deps := [⟨2, 1, .nsubj⟩, ⟨2, 3, .aux⟩, ⟨3, 0, .obj⟩]
    rootIdx := 2 }

/-- "Can John eat pizza?" - Matrix yes-no question (inverted)
    can ─subj→ John
     └─aux→ eat ─obj→ pizza -/
def canJohnEatPizzaTree : DepTree :=
  { words := [can, john, eat, pizza]
    deps := [⟨0, 1, .nsubj⟩, ⟨0, 2, .aux⟩, ⟨2, 3, .obj⟩]
    rootIdx := 0 }

/-- "*John can eat pizza?" - Ungrammatical as matrix question
    John ←subj─ can ─aux→ eat ─obj→ pizza -/
def johnCanEatPizzaTree : DepTree :=
  { words := [john, can, eat, pizza]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .aux⟩, ⟨2, 3, .obj⟩]
    rootIdx := 1 }

-- ============================================================================
-- §1: Network Licensing (core chain)
-- Each tree is licensed/rejected via wgLicenses = ClauseForm → network → satisfiesArgStr
-- ============================================================================

/-! ### Intransitive trees (can + sleep) -/

/-- "Can John sleep?" is licensed as a matrix question via the network. -/
theorem wg_licenses_inverted_question :
    wgLicenses englishAuxNet canJohnSleepTree 0 .matrixQuestion = true := by
  native_decide

/-- "Can John sleep?" is rejected as a declarative. -/
theorem wg_rejects_inverted_as_declarative :
    wgLicenses englishAuxNet canJohnSleepTree 0 .declarative = false := by
  native_decide

/-- "John can sleep" is licensed as a declarative via the network. -/
theorem wg_licenses_declarative :
    wgLicenses englishAuxNet johnCanSleepTree 1 .declarative = true := by
  native_decide

/-- "John can sleep" is rejected as a matrix question. -/
theorem wg_rejects_declarative_as_question :
    wgLicenses englishAuxNet johnCanSleepTree 1 .matrixQuestion = false := by
  native_decide

/-! ### Wh-question trees (what can John eat) -/

/-- "What can John eat?" is licensed as a matrix question. -/
theorem wg_licenses_wh_question :
    wgLicenses englishAuxNet whatCanJohnEatTree 1 .matrixQuestion = true := by
  native_decide

/-- "*What John can eat?" is rejected as a matrix question. -/
theorem wg_rejects_wh_noninverted :
    wgLicenses englishAuxNet whatJohnCanEatTree 2 .matrixQuestion = false := by
  native_decide

/-! ### Yes-no question trees (can John eat pizza) -/

/-- "Can John eat pizza?" is licensed as a matrix question. -/
theorem wg_licenses_yn_question :
    wgLicenses englishAuxNet canJohnEatPizzaTree 0 .matrixQuestion = true := by
  native_decide

/-- "*John can eat pizza?" is rejected as a matrix question. -/
theorem wg_rejects_yn_noninverted :
    wgLicenses englishAuxNet johnCanEatPizzaTree 1 .matrixQuestion = false := by
  native_decide

-- ============================================================================
-- §2: Lexical-Rule ↔ Network Equivalence
-- The lexical rule auxInversionRule.transform produces an argStr with the
-- same depType+dir as the network-derived interrogative_auxiliary.
-- ============================================================================

/-- The lexical rule's inverted argStr has the same depType+dir projection
as the network-derived interrogative auxiliary argStr. -/
theorem lexrule_matches_network :
    (auxInversionRule.transform lex_can).argStr.slots.map (λ s => (s.depType, s.dir)) =
    (resolveArgStr englishAuxNet "interrogative_auxiliary").slots.map (λ s => (s.depType, s.dir)) := by
  native_decide

/-- Auxiliary inversion rule applies to non-inverted auxiliaries. -/
theorem aux_inv_applies :
    auxInversionRule.applies lex_can = true := rfl

/-- Auxiliary inversion sets the inv feature. -/
theorem aux_inv_sets_inv :
    lex_can_inv.inv = true := rfl

/-- Auxiliary inversion moves subject from left to right. -/
theorem aux_inv_moves_subj :
    lex_can.argStr.slots.head?.map (·.dir) = some .left ∧
    lex_can_inv.argStr.slots.head?.map (·.dir) = some .right :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- §3: Slot-Projection Equivalence (network ↔ manual argStr)
-- satisfiesArgStr only checks depType and dir; the manual argStr_Aux/AuxInv
-- carry extra metadata (required, cat) that is functionally irrelevant.
-- ============================================================================

/-- Network-derived auxiliary slots agree with manual argStr_Aux on
depType and dir (the fields satisfiesArgStr checks). -/
theorem network_aux_slots_match_manual :
    (resolveArgStr englishAuxNet "auxiliary").slots.map (λ s => (s.depType, s.dir)) =
    argStr_Aux.slots.map (λ s => (s.depType, s.dir)) := by native_decide

/-- Same for the interrogative (inverted) auxiliary. -/
theorem network_inv_aux_slots_match_manual :
    (resolveArgStr englishAuxNet "interrogative_auxiliary").slots.map (λ s => (s.depType, s.dir)) =
    argStr_AuxInv.slots.map (λ s => (s.depType, s.dir)) := by native_decide

-- ============================================================================
-- §4: Fragment → Network Chain
-- The Fragment's valence maps to the same depType+dir as the network.
-- ============================================================================

/-- valenceToArgStr .transitive has the same depType+dir projection as the
network-derived transitive word class. -/
theorem fragment_transitive_matches_network :
    (valenceToArgStr .transitive).map (·.slots.map (λ s => (s.depType, s.dir))) =
    some ((resolveArgStr englishAuxNet "transitive").slots.map (λ s => (s.depType, s.dir))) := by
  native_decide

-- ============================================================================
-- §5: SAI Data Connection
-- Our trees correspond to SAI empirical data (ex01, ex02, ex04, ex05).
-- ============================================================================

open Phenomena.WordOrder.SubjectAuxInversion in
/-- Map SAI contexts to whether they require inversion. -/
def saiContextRequiresInversion : SAIContext → Bool
  | .matrixWh => true
  | .matrixYN => true
  | .embedded => false
  | .echo => false
  | .negativeInversion => true
  | .conditionalInversion => true
  | .exclamative => true
  | .soNeither => true
  | .embeddedDialectal => true  -- dialectally, yes
  | .sententialNegation => false
  | .verbRaising => false
  | .tagQuestion => true
  | .vpEllipsis => false
  | .emphatic => false

open Phenomena.WordOrder.SubjectAuxInversion

-- Validate our trees against SAI data sentences and judgments.

-- ex01: "What can John eat?" — grammatical matrix wh-question (inverted)
#guard ex01.sentence == "What can John eat?"
#guard ex01.inverted == true
#guard ex01.acceptability == .grammatical
#guard wgLicenses englishAuxNet whatCanJohnEatTree 1 .matrixQuestion == true

-- ex02: "What John can eat?" — ungrammatical matrix wh-question (not inverted)
#guard ex02.sentence == "What John can eat?"
#guard ex02.inverted == false
#guard ex02.acceptability == .ungrammatical
#guard wgLicenses englishAuxNet whatJohnCanEatTree 2 .matrixQuestion == false

-- ex04: "Can John eat pizza?" — grammatical polar question (inverted)
#guard ex04.sentence == "Can John eat pizza?"
#guard ex04.inverted == true
#guard ex04.acceptability == .grammatical
#guard wgLicenses englishAuxNet canJohnEatPizzaTree 0 .matrixQuestion == true

-- ex05: "John can eat pizza?" — ungrammatical polar question (not inverted)
#guard ex05.sentence == "John can eat pizza?"
#guard ex05.inverted == false
#guard ex05.acceptability == .ungrammatical
#guard wgLicenses englishAuxNet johnCanEatPizzaTree 1 .matrixQuestion == false

/-
## Summary: End-to-End Derivation Chain

```
SAI data (ex01..ex05)
    ↕ sentence/judgment validation (#guard)
ClauseForm (.matrixQuestion / .declarative)
    ↓ wordClassForClauseType
Word class ("interrogative_auxiliary" / "auxiliary")
    ↓ resolveArgStr (default inheritance in englishAuxNet)
ArgStr (nsubj/right + aux/right  or  nsubj/left + aux/right)
    ↓ satisfiesArgStr
Licensed ✓ / Rejected ✗
```

The DG analysis correctly predicts:

| Sentence              | ClauseForm     | Licensed? | SAI datum |
|-----------------------|----------------|-----------|-----------|
| Can John sleep?       | matrixQuestion | ✓         | —         |
| John can sleep        | declarative    | ✓         | —         |
| What can John eat?    | matrixQuestion | ✓         | ex01      |
| *What John can eat?   | matrixQuestion | ✗         | ex02      |
| Can John eat pizza?   | matrixQuestion | ✓         | ex04      |
| *John can eat pizza?  | matrixQuestion | ✗         | ex05      |

The key insight from @cite{hudson-1984} (pp. 117-118): inversion is captured
by treating the interrogative auxiliary as a subtype of auxiliary with a
different subject-position specification. The subject follows the auxiliary
because that is what the interrogative_auxiliary word class says — not
because a lexical rule has flipped a direction.
-/

end Hudson1984
