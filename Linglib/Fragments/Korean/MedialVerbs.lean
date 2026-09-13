import Linglib.Syntax.Clause.Chaining

/-!
# Korean Conjunctive (Converbal) Suffixes
[sohn-1999]

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

The language's clause-chaining system (`chaining`) is read off this inventory where it can be:
the tense and polarity profiles of medial verbs from the suffixes that admit tense and negation,
and the marked relations from the suffixes' relations.
-/

namespace Korean.MedialVerbs

open Clause.Chaining (InterclauseRelation CategoryRetention)

/-- A Korean conjunctive suffix entry. -/
structure ConjSuffixEntry where
  /-- Suffix form (romanized). -/
  form : String
  /-- Semantic relation gloss. -/
  gloss : String
  /-- The interclausal relations the suffix encodes. -/
  relations : List InterclauseRelation
  /-- Whether tense can be marked on the medial verb with this suffix. -/
  allowsTense : Bool
  /-- Whether independent negation is possible on the medial clause. -/
  allowsNegation : Bool
  deriving Repr, BEq

/-! ### Suffix inventory -/

/-- -go: sequential or additive 'and, and then'.
    The most neutral connective — imposes minimal semantic constraint. -/
def go : ConjSuffixEntry :=
  { form := "-go", gloss := "and/and then (sequential/additive)",
    relations := [.sequential, .additive], allowsTense := false, allowsNegation := true }

/-- -myeonseo: simultaneous 'while, as'.
    Requires temporal overlap between medial and following event. -/
def myeonseo : ConjSuffixEntry :=
  { form := "-myeonseo", gloss := "while (simultaneous)", relations := [.simultaneous],
    allowsTense := false, allowsNegation := true }

/-- -eoseo: causal or tight sequential 'because, and then'.
    The medial event is either the cause or the immediately preceding event.
    Differs from -go in implying closer connection between events. -/
def eoseo : ConjSuffixEntry :=
  { form := "-eoseo", gloss := "because/and then (causal/sequential)",
    relations := [.causal, .sequential], allowsTense := false, allowsNegation := true }

/-- -(eu)myeon: conditional 'if, when'.
    Can combine with past tense for counterfactual readings. -/
def myeon : ConjSuffixEntry :=
  { form := "-(eu)myeon", gloss := "if/when (conditional)", relations := [.conditional],
    allowsTense := true, allowsNegation := true }

/-- -jiman: concessive 'but, although'.
    The medial event holds despite the following event. -/
def jiman : ConjSuffixEntry :=
  { form := "-jiman", gloss := "but/although (concessive)", relations := [.concessive],
    allowsTense := true, allowsNegation := true }

/-- -dorok: purpose or extent 'so that, until'.
    The medial event is the goal or limit of the following event. -/
def dorok : ConjSuffixEntry :=
  { form := "-dorok", gloss := "so that/until (purpose)", relations := [.purpose],
    allowsTense := false, allowsNegation := true }

/-- -nikka: causal 'since, because' (with evidential overtone).
    Marks the medial event as an established or experienced reason. -/
def nikka : ConjSuffixEntry :=
  { form := "-nikka", gloss := "since/because (causal-evidential)", relations := [.causal],
    allowsTense := true, allowsNegation := true }

/-- -(eu)ryeo: purpose/intention 'in order to'.
    The subject intends to bring about the medial event. -/
def ryeo : ConjSuffixEntry :=
  { form := "-(eu)ryeo", gloss := "in order to (purpose/intention)", relations := [.purpose],
    allowsTense := false, allowsNegation := true }

/-- All conjunctive suffixes. -/
def allSuffixes : List ConjSuffixEntry :=
  [go, myeonseo, eoseo, myeon, jiman, dorok, nikka, ryeo]

/-! ### Derived properties -/

/-- Suffixes that allow tense marking on the medial verb. -/
def tensedSuffixes : List ConjSuffixEntry :=
  allSuffixes.filter (·.allowsTense)

/-- Suffixes that disallow tense marking on the medial verb. -/
def untensedSuffixes : List ConjSuffixEntry :=
  allSuffixes.filter (! ·.allowsTense)

/-- How far medial verbs retain a category, from the suffixes that admit it. -/
def retention (p : ConjSuffixEntry → Bool) : CategoryRetention :=
  if allSuffixes.all p then .full else if allSuffixes.any p then .restricted else .absent

/-- Korean's clause-chaining system: medial-final chains without switch-reference, each
conjunctive suffix encoding its own relations, tense admitted before some suffixes and
independent negation before all, no agreement, and medial clauses on their own ([sohn-1999];
[sarvasy-aikhenvald-2025] Ch. 1 on Korean's inventory of medial suffixes). -/
def chaining : Clause.Chaining.System where
  direction := .medialFinal
  srSystem := .none
  srTarget := none
  srObligatory := false
  srMarkedness := none
  medialMorph := {
    tense := retention (·.allowsTense)
    agreement := .absent
    mood := .restricted
    polarity := retention (·.allowsNegation)
    aspect := .restricted }
  relationsMarked := (allSuffixes.flatMap (·.relations)).eraseDups
  hasRecapLinkage := false
  hasSummaryLinkage := false
  medialCanStandAlone := true

end Korean.MedialVerbs
