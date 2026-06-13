import Linglib.Syntax.CCG.Interface
import Linglib.Fragments.English.Toy

/-!
# CCG Truth Conditions: Syntax → Semantics Pipeline

The complete CCG → Montague pipeline over the toy fragment: `DerivStep`
encodes combinatory derivations, `catToTy`/`interp` interpret them
compositionally, and each theorem checks that the derived meaning is the
correct truth value in the toy model.
-/

namespace CCG.TruthConditions

open CCG
open Semantics.Montague

-- CCG Derivations for Test Sentences

/-- "John sleeps" - backward application -/
def ccg_john_sleeps : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.lex ⟨"sleeps", IV⟩)

/-- "Mary sleeps" - backward application -/
def ccg_mary_sleeps : DerivStep :=
  .bapp (.lex ⟨"Mary", NP⟩) (.lex ⟨"sleeps", IV⟩)

/-- "John laughs" - backward application -/
def ccg_john_laughs : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.lex ⟨"laughs", IV⟩)

/-- "Mary laughs" - backward application -/
def ccg_mary_laughs : DerivStep :=
  .bapp (.lex ⟨"Mary", NP⟩) (.lex ⟨"laughs", IV⟩)

/-- "John sees Mary" - forward then backward application -/
def ccg_john_sees_mary : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"Mary", NP⟩))

/-- "Mary sees John" - forward then backward application -/
def ccg_mary_sees_john : DerivStep :=
  .bapp (.lex ⟨"Mary", NP⟩) (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"John", NP⟩))

/-- "John eats pizza" - forward then backward application -/
def ccg_john_eats_pizza : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.fapp (.lex ⟨"eats", TV⟩) (.lex ⟨"pizza", NP⟩))

-- Extended Semantic Lexicon (matching the toy model)

/-- Extended lexicon with all entities and predicates -/
def extendedLexicon : SemLexicon ToyEntity Unit := λ word cat =>
  match word, cat with
  -- Proper names
  | "John", .atom .NP => some ⟨NP, ToyEntity.john⟩
  | "Mary", .atom .NP => some ⟨NP, ToyEntity.mary⟩
  | "pizza", .atom .NP => some ⟨NP, ToyEntity.pizza⟩
  | "book", .atom .NP => some ⟨NP, ToyEntity.book⟩
  -- Intransitive verbs
  | "sleeps", .lslash (.atom .S) (.atom .NP) => some ⟨IV, ToyLexicon.sleeps_sem⟩
  | "laughs", .lslash (.atom .S) (.atom .NP) => some ⟨IV, ToyLexicon.laughs_sem⟩
  -- Transitive verbs
  | "sees", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.sees_sem⟩
  | "eats", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.eats_sem⟩
  | "reads", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.reads_sem⟩
  | _, _ => none

/-- Get meaning (as Prop) from CCG derivation -/
def ccgMeaning (d : DerivStep) : Option Prop :=
  getMeaning (d.interp extendedLexicon)

-- Pipeline Theorems: CCG Derives Correct Truth Conditions

/-- CCG correctly predicts "John sleeps" is true -/
theorem ccg_predicts_john_sleeps :
    ccgMeaning ccg_john_sleeps = some True := rfl

/-- CCG correctly predicts "Mary sleeps" is false -/
theorem ccg_predicts_mary_sleeps :
    ccgMeaning ccg_mary_sleeps = some False := rfl

/-- CCG correctly predicts "John laughs" is true -/
theorem ccg_predicts_john_laughs :
    ccgMeaning ccg_john_laughs = some True := rfl

/-- CCG correctly predicts "Mary laughs" is true -/
theorem ccg_predicts_mary_laughs :
    ccgMeaning ccg_mary_laughs = some True := rfl

/-- CCG correctly predicts "John sees Mary" is true -/
theorem ccg_predicts_john_sees_mary :
    ccgMeaning ccg_john_sees_mary = some True := rfl

/-- CCG correctly predicts "Mary sees John" is true -/
theorem ccg_predicts_mary_sees_john :
    ccgMeaning ccg_mary_sees_john = some True := rfl

end CCG.TruthConditions
