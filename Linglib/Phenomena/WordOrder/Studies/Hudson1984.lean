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

Reference: @cite{hudson-1990}, @cite{gibson-2025}
-/

namespace Phenomena.WordOrder.Studies.Hudson1984

open DepGrammar

private abbrev what := Fragments.English.Pronouns.what.toWord
private abbrev can := Fragments.English.FunctionWords.can.toWord
private abbrev john := Fragments.English.Nouns.john.toWordSg
private abbrev eat := Fragments.English.Predicates.Verbal.eat.toWordPl
private abbrev pizza := Fragments.English.Nouns.pizza.toWordSg

-- ============================================================================
-- Licensing via Argument Structure
-- ============================================================================

/-- License a sentence based on clause type and word order.
    Uses shared `auxPrecedesSubject`/`subjectPrecedesAux` from Core. -/
def depGrammarLicenses (ws : List Word) (ct : ClauseType) : Bool :=
  match ct with
  | .matrixQuestion => auxPrecedesSubject ws
  | .declarative => subjectPrecedesAux ws || !ws.any (·.cat == .AUX)
  | .embeddedQuestion => subjectPrecedesAux ws
  | .echo => true

-- ============================================================================
-- Example Trees
-- ============================================================================

/-- "What can John eat?" - Matrix wh-question (inverted)
    what ←obj─ can ─subj→ John
               └─aux→ eat
-/
def whatCanJohnEatTree : DepTree :=
  { words := [what, can, john, eat]
    deps := [⟨1, 2, .nsubj⟩, ⟨1, 3, .aux⟩, ⟨3, 0, .obj⟩]
    rootIdx := 1 }

/-- "*What John can eat?" - Ungrammatical as matrix question
    what ←obj─ eat ←aux─ can ←subj─ John
-/
def whatJohnCanEatTree : DepTree :=
  { words := [what, john, can, eat]
    deps := [⟨2, 1, .nsubj⟩, ⟨2, 3, .aux⟩, ⟨3, 0, .obj⟩]
    rootIdx := 2 }

/-- "Can John eat pizza?" - Matrix yes-no question (inverted)
    can ─subj→ John
     └─aux→ eat ─obj→ pizza
-/
def canJohnEatPizzaTree : DepTree :=
  { words := [can, john, eat, pizza]
    deps := [⟨0, 1, .nsubj⟩, ⟨0, 2, .aux⟩, ⟨2, 3, .obj⟩]
    rootIdx := 0 }

/-- "*John can eat pizza?" - Ungrammatical as matrix question
    John ←subj─ can ─aux→ eat ─obj→ pizza
-/
def johnCanEatPizzaTree : DepTree :=
  { words := [john, can, eat, pizza]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .aux⟩, ⟨2, 3, .obj⟩]
    rootIdx := 1 }

-- ============================================================================
-- Licensing Theorems
-- ============================================================================

/-- "What can John eat?" is licensed as a matrix question -/
theorem pair1_grammatical :
    depGrammarLicenses [what, can, john, eat] .matrixQuestion = true := rfl

/-- "What John can eat?" is NOT licensed as a matrix question -/
theorem pair1_ungrammatical :
    depGrammarLicenses [what, john, can, eat] .matrixQuestion = false := rfl

-- ============================================================================
-- Proofs for Pair 2: Matrix yes-no question
-- ============================================================================

/-- "Can John eat pizza?" is licensed as a matrix question -/
theorem pair2_grammatical :
    depGrammarLicenses [can, john, eat, pizza] .matrixQuestion = true := rfl

/-- "John can eat pizza?" is NOT licensed as a matrix question -/
theorem pair2_ungrammatical :
    depGrammarLicenses [john, can, eat, pizza] .matrixQuestion = false := rfl

-- ============================================================================
-- Connection to Argument Structure Analysis
-- ============================================================================

/-- The inverted tree satisfies the inverted argument structure -/
theorem inverted_tree_satisfies_inv_argstr :
    satisfiesArgStr canJohnSleepTree 0 argStr_AuxInv = true := rfl

/-- The non-inverted tree satisfies the non-inverted argument structure -/
theorem noninverted_tree_satisfies_argstr :
    satisfiesArgStr johnCanSleepTree 1 argStr_Aux = true := rfl

/-
The Dependency Grammar analysis correctly predicts:

| Sentence              | ClauseType     | Licensed? | Reason                    |
|-----------------------|----------------|-----------|---------------------------|
| What can John eat?    | matrixQuestion | ✓         | aux < subj (inverted)     |
| What John can eat?    | matrixQuestion | ✗         | subj < aux (not inverted) |
| Can John eat pizza?   | matrixQuestion | ✓         | aux < subj (inverted)     |
| John can eat pizza?   | matrixQuestion | ✗         | subj < aux (not inverted) |

The key insight from @cite{hudson-1984} (pp. 117-118): inversion is captured
by treating the interrogative auxiliary as a subtype of auxiliary with a
different subject-position specification. The subject follows the auxiliary
because that is what the interrogative_auxiliary word class says — not
because a lexical rule has flipped a direction.
-/

-- ============================================================================
-- WG Network Grounding
-- ============================================================================

/-! ### Grounding in Hudson's inheritance network

The lexical-rule analysis above stipulates separate `argStr_Aux` and
`argStr_AuxInv` frames. In @cite{hudson-1984}'s Word Grammar, these are not
independent stipulations — they arise from a single word-class taxonomy
via default inheritance:

1. `verb` specifies that the subject precedes (slot 0 = nsubj/left)
2. `auxiliary` isA `verb`, inheriting subject/left
3. `interrogative_auxiliary` isA `auxiliary`, locally overriding the
   subject's direction to right (subject follows)

The interrogative auxiliary's argument structure is *derived* from the
taxonomy, not stipulated. The theorems below prove this connection. -/

open DepGrammar.WG

/-- The network-derived auxiliary argStr (declarative) has the same
subject and main-verb slots as the manually defined `argStr_Aux`. -/
theorem network_aux_matches_argStr_Aux :
    (resolveArgStr englishAuxNet "auxiliary").slots =
      [{ depType := .nsubj, dir := .left },
       { depType := .aux, dir := .right }] := by native_decide

/-- The network-derived interrogative auxiliary argStr has the same slots
as the manually defined inverted `argStr_AuxInv`. Inversion follows from
subtype inheritance: `interrogative_auxiliary` locally overrides the
subject direction from left to right. -/
theorem network_interrog_aux_matches_argStr_AuxInv :
    (resolveArgStr englishAuxNet "interrogative_auxiliary").slots =
      [{ depType := .nsubj, dir := .right },
       { depType := .aux, dir := .right }] := by native_decide

/-- The inverted tree satisfies the network-derived interrogative auxiliary
arg structure (connecting the network model to `satisfiesArgStr`). -/
theorem inverted_tree_satisfies_network_argstr :
    satisfiesArgStr canJohnSleepTree 0
      (resolveArgStr englishAuxNet "interrogative_auxiliary") = true := by
  native_decide

/-- The non-inverted tree satisfies the network-derived (non-interrogative)
auxiliary arg structure. -/
theorem noninverted_tree_satisfies_network_argstr :
    satisfiesArgStr johnCanSleepTree 1
      (resolveArgStr englishAuxNet "auxiliary") = true := by native_decide

/-- The non-inverted tree does NOT satisfy the interrogative auxiliary's
arg structure — the subject is on the wrong side. -/
theorem noninverted_tree_rejects_interrogative :
    satisfiesArgStr johnCanSleepTree 1
      (resolveArgStr englishAuxNet "interrogative_auxiliary") = false := by
  native_decide

/-- The inverted tree does NOT satisfy the non-interrogative auxiliary's
arg structure. -/
theorem inverted_tree_rejects_declarative :
    satisfiesArgStr canJohnSleepTree 0
      (resolveArgStr englishAuxNet "auxiliary") = false := by native_decide

end Phenomena.WordOrder.Studies.Hudson1984
