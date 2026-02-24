/-!
# Korean Conjunctive (Converbal) Suffixes

Medial clause markers in Korean: conjunctive suffixes on the verb stem that
link clauses in a chain. Korean has no switch-reference morphology; instead,
each conjunctive suffix directly encodes the interclausal semantic relation
(sequential, simultaneous, causal, conditional, concessive, etc.).

Korean converbal constructions are among the most extensively described in the
clause chaining literature. The system is highly productive: new chains can be
extended indefinitely by adding medial clauses with conjunctive suffixes before
the single final (independent) verb.

## Inventory

| Suffix | Meaning | Tense on medial | Negation |
|--------|---------|-----------------|----------|
| -go | sequential/additive 'and, and then' | no | possible |
| -myeonseo | simultaneous 'while' | no | possible |
| -eoseo | causal/sequential 'because, and then' | no | possible |
| -(eu)myeon | conditional 'if, when' | possible | possible |
| -jiman | concessive 'but, although' | possible | possible |
| -dorok | purpose 'so that, until' | no | possible |
| -nikka | causal 'since, because' (evidential) | possible | possible |
| -(eu)ryeo | purpose/intention 'in order to' | no | possible |

## References

- Sohn, H.-M. (1999). The Korean Language. Cambridge University Press.
- Yeon, J. & L. Brown (2011). Korean: A Comprehensive Grammar. Routledge.
-/

namespace Fragments.Korean.MedialVerbs

/-- A Korean conjunctive suffix entry. -/
structure ConjSuffixEntry where
  /-- Suffix form (romanized). -/
  form : String
  /-- Semantic relation gloss. -/
  gloss : String
  /-- Whether tense can be marked on the medial verb with this suffix. -/
  allowsTense : Bool
  /-- Whether independent negation is possible on the medial clause. -/
  allowsNegation : Bool
  deriving Repr, BEq

-- ============================================================================
-- § Suffix inventory
-- ============================================================================

/-- -go: sequential or additive 'and, and then'.
    The most neutral connective — imposes minimal semantic constraint. -/
def go : ConjSuffixEntry :=
  { form := "-go", gloss := "and/and then (sequential/additive)", allowsTense := false, allowsNegation := true }

/-- -myeonseo: simultaneous 'while, as'.
    Requires temporal overlap between medial and following event. -/
def myeonseo : ConjSuffixEntry :=
  { form := "-myeonseo", gloss := "while (simultaneous)", allowsTense := false, allowsNegation := true }

/-- -eoseo: causal or tight sequential 'because, and then'.
    The medial event is either the cause or the immediately preceding event.
    Differs from -go in implying closer connection between events. -/
def eoseo : ConjSuffixEntry :=
  { form := "-eoseo", gloss := "because/and then (causal/sequential)", allowsTense := false, allowsNegation := true }

/-- -(eu)myeon: conditional 'if, when'.
    Can combine with past tense for counterfactual readings. -/
def myeon : ConjSuffixEntry :=
  { form := "-(eu)myeon", gloss := "if/when (conditional)", allowsTense := true, allowsNegation := true }

/-- -jiman: concessive 'but, although'.
    The medial event holds despite the following event. -/
def jiman : ConjSuffixEntry :=
  { form := "-jiman", gloss := "but/although (concessive)", allowsTense := true, allowsNegation := true }

/-- -dorok: purpose or extent 'so that, until'.
    The medial event is the goal or limit of the following event. -/
def dorok : ConjSuffixEntry :=
  { form := "-dorok", gloss := "so that/until (purpose)", allowsTense := false, allowsNegation := true }

/-- -nikka: causal 'since, because' (with evidential overtone).
    Marks the medial event as an established or experienced reason. -/
def nikka : ConjSuffixEntry :=
  { form := "-nikka", gloss := "since/because (causal-evidential)", allowsTense := true, allowsNegation := true }

/-- -(eu)ryeo: purpose/intention 'in order to'.
    The subject intends to bring about the medial event. -/
def ryeo : ConjSuffixEntry :=
  { form := "-(eu)ryeo", gloss := "in order to (purpose/intention)", allowsTense := false, allowsNegation := true }

/-- All conjunctive suffixes. -/
def allSuffixes : List ConjSuffixEntry :=
  [go, myeonseo, eoseo, myeon, jiman, dorok, nikka, ryeo]

-- ============================================================================
-- § Derived properties
-- ============================================================================

/-- Suffixes that allow tense marking on the medial verb. -/
def tensedSuffixes : List ConjSuffixEntry :=
  allSuffixes.filter (·.allowsTense)

/-- Suffixes that disallow tense marking on the medial verb. -/
def untensedSuffixes : List ConjSuffixEntry :=
  allSuffixes.filter (! ·.allowsTense)

-- ============================================================================
-- § Verification theorems
-- ============================================================================

/-- 8 conjunctive suffixes in the inventory. -/
theorem suffix_count : allSuffixes.length = 8 := rfl

/-- Every suffix allows independent negation on the medial clause.
    Korean medial clauses can always be independently negated. -/
theorem all_allow_negation :
    allSuffixes.all (·.allowsNegation) = true := rfl

/-- 3 suffixes allow tense on the medial verb. -/
theorem tensed_count : tensedSuffixes.length = 3 := rfl

/-- 5 suffixes disallow tense on the medial verb. -/
theorem untensed_count : untensedSuffixes.length = 5 := rfl

/-- The tensed/untensed partition exhausts the inventory. -/
theorem tense_partition :
    tensedSuffixes.length + untensedSuffixes.length = allSuffixes.length := rfl

end Fragments.Korean.MedialVerbs
