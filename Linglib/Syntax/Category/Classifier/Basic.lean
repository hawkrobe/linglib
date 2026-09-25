module

public import Linglib.Morphology.Morph

/-!
# Classifiers

This file defines the word-class record for classifiers and the vocabulary of
[aikhenvald-2000]'s typology of noun categorization devices. `Classifier` is the lexical entry
Fragments store in their inventories: a morph, which is how the classifier attaches and its
form, with its spelling in a native script and its gloss. Which nouns a classifier counts,
whether it is a language's general classifier, and which semantic parameters motivate it are
facts about a whole system or analyses of it, not properties of the entry: a noun records the
classifiers it takes (`ClassifiedNoun`), and a typology's coding of a system lives in the study
that makes it. A device is described by where its morphemes occur and what they characterize,
the locus and the constituent, and its kind (noun class, numeral classifier, verbal classifier,
…) is the classification of that pair by the book's table of scopes (`Kind.ofScope`), never a
stored label: every kind is the classification of some pair (`Kind.ofScope_surjective`), and
noun class is the one kind with two loci, agreement inside and outside the noun phrase
(`Kind.ofScope_eq_some_nounClass_iff`). How a device is realized is likewise read off its
entries where it has them (`Classifier.realization`): the segmental realizations are the
attachment kinds of `Morphology.Morph`, and the book's further devices for marking noun classes
on a noun are the remaining cases of `Realization`.

## Main definitions

* `Classifier` — the lexical entry, a morph with its script and gloss.
* `Classifier.Parameter` — the semantic parameters.
* `Classifier.Scope`, `Classifier.Constituent`, `Classifier.Kind`, `Classifier.Kind.ofScope` —
  the nine kinds of device as the classification of a locus by the constituent it
  characterizes.
* `Classifier.Assignment`, `Classifier.Realization`, `Classifier.realization` — assignment
  principles, realizations, and the realization of an entry.

## References

* [aikhenvald-2000], §1.5, §2.3, §10.5, §11.1, Tables 15.1–15.3
* [corbett-1991]
* [allan-1977]
-/

@[expose] public section

open Morphology (Morph)

/-- A classifier lexical entry: the morph, its attachment kind and form, the form a romanization
where the language has a native script, its spelling in that script, and its gloss. -/
structure Classifier extends Morph where
  /-- The spelling in the native script. -/
  script : Option String := none
  /-- The gloss. -/
  gloss : String := "CL"
  deriving DecidableEq, Repr

namespace Classifier

/-! ### Semantic parameters -/

/-- The semantic parameters noun categorization devices encode, in three large classes —
animacy, physical properties, and function — with kind-specific preferences. Speech register
is distinguished from the referent's social status, since honorific classifiers can index the
style of speech rather than the rank of the referent. -/
inductive Parameter where
  /-- Animate versus inanimate. -/
  | animacy
  /-- Human versus non-human. -/
  | humanness
  /-- Male versus female. -/
  | sex
  /-- The social status or rank of a human referent. -/
  | socialStatus
  /-- The kinship relationship of a human referent. -/
  | kinship
  /-- The speech register (honorific, common, humiliative) rather than the referent's status. -/
  | register
  /-- Shape and dimensionality. -/
  | shape
  /-- Vertical versus horizontal orientation. -/
  | direction
  /-- Differentiation of inside from outside, as between rings and holes. -/
  | interioricity
  /-- Whether an outlined entity is delimited. -/
  | boundedness
  /-- Large versus small. -/
  | size
  /-- Plasticity under manipulation: flexible versus rigid. -/
  | consistency
  /-- Physical state, such as liquid or solid. -/
  | constitution
  /-- The material an object is made of. -/
  | material
  /-- Other inherent, time-stable nature, often realized by classifiers specific to one noun. -/
  | nature
  /-- How an object is used or handled. -/
  | function
  /-- The configuration of objects, such as a coil or a row. -/
  | arrangement
  /-- A quantity of objects, such as a cluster or a flock. -/
  | quanta
  /-- Colour: perceptually salient but never a basis for noun categorization. -/
  | colour
  deriving DecidableEq, Repr

/-! ### Kinds of device, by locus and constituent -/

/-- The morphosyntactic scope a noun categorization device operates in. -/
inductive Scope where
  /-- Inside a head-modifier NP: head-modifier agreement. -/
  | headModifierNP
  /-- Outside the NP: predicate-argument agreement. -/
  | predicateArgument
  /-- The noun itself. -/
  | noun
  /-- A numeral or quantifier NP. -/
  | numeralNP
  /-- A possessive NP. -/
  | possessiveNP
  /-- The clause. -/
  | clause
  /-- An adpositional NP. -/
  | adpositionalNP
  /-- An attributive NP with a deictic. -/
  | attributiveNP
  deriving DecidableEq, Repr

/-- The constituent a noun categorization device characterizes. -/
inductive Constituent where
  /-- The head noun. -/
  | headNoun
  /-- An A/S, S/O, or oblique argument. -/
  | argument
  /-- The possessive relation. -/
  | possessiveRelation
  /-- The possessed noun. -/
  | possessedNoun
  /-- The possessor. -/
  | possessor
  /-- The argument of an adposition. -/
  | adpositionArgument
  deriving DecidableEq, Repr

/-- The nine kinds of noun categorization device, focal points on a continuum individuated by
locus and the constituent characterized. -/
inductive Kind where
  /-- Noun class or gender: a closed obligatory system realized by agreement inside and
  sometimes outside the noun phrase, with an inventory often of two to ten. -/
  | nounClass
  /-- Noun classifier: characterizes the head noun itself, independently of other NP elements,
  as a free form or an affix on the noun. -/
  | nounClassifier
  /-- Numeral classifier: characterizes nouns in numeral and quantifier phrases, as a free form
  or an affix on the numeral, with an often large inventory. -/
  | numeralClassifier
  /-- Relational classifier: characterizes the possessive relation in a possessive NP. -/
  | relationalClassifier
  /-- Possessed classifier: characterizes the possessed noun in a possessive NP. -/
  | possessedClassifier
  /-- Possessor classifier: characterizes the possessor; very rare. -/
  | possessorClassifier
  /-- Verbal classifier: marks agreement on the verb with an S or O argument, as an
  incorporated classifier, an affix, or a suppletive classificatory stem. -/
  | verbalClassifier
  /-- Locative classifier: marks agreement with the head noun in an adpositional NP. -/
  | locativeClassifier
  /-- Deictic classifier: occurs with articles and demonstratives, marking spatial location
  or determination. -/
  | deicticClassifier
  deriving DecidableEq, Repr

/-- The kind of device determined by a locus and the constituent it characterizes: noun classes
inside a head-modifier NP or agreeing with an argument outside it, noun classifiers on the noun,
numeral classifiers in the numeral NP, the three possessive kinds by which part of the
possessive NP they characterize, verbal classifiers agreeing with an argument in the clause,
locative and deictic classifiers in adpositional and attributive NPs. -/
def Kind.ofScope : Scope → Constituent → Option Kind
  | .headModifierNP, .headNoun => some .nounClass
  | .predicateArgument, .argument => some .nounClass
  | .noun, .headNoun => some .nounClassifier
  | .numeralNP, .headNoun => some .numeralClassifier
  | .possessiveNP, .possessiveRelation => some .relationalClassifier
  | .possessiveNP, .possessedNoun => some .possessedClassifier
  | .possessiveNP, .possessor => some .possessorClassifier
  | .clause, .argument => some .verbalClassifier
  | .adpositionalNP, .adpositionArgument => some .locativeClassifier
  | .attributiveNP, .headNoun => some .deicticClassifier
  | _, _ => none

/-- Every kind of device is the classification of some locus and constituent. -/
theorem Kind.ofScope_surjective : ∀ k : Kind, ∃ s c, ofScope s c = some k
  | .nounClass => ⟨.headModifierNP, .headNoun, rfl⟩
  | .nounClassifier => ⟨.noun, .headNoun, rfl⟩
  | .numeralClassifier => ⟨.numeralNP, .headNoun, rfl⟩
  | .relationalClassifier => ⟨.possessiveNP, .possessiveRelation, rfl⟩
  | .possessedClassifier => ⟨.possessiveNP, .possessedNoun, rfl⟩
  | .possessorClassifier => ⟨.possessiveNP, .possessor, rfl⟩
  | .verbalClassifier => ⟨.clause, .argument, rfl⟩
  | .locativeClassifier => ⟨.adpositionalNP, .adpositionArgument, rfl⟩
  | .deicticClassifier => ⟨.attributiveNP, .headNoun, rfl⟩

/-- Noun class is the one kind with two loci: agreement with the head noun inside a
head-modifier NP, and with an argument outside the NP. -/
theorem Kind.ofScope_eq_some_nounClass_iff {s : Scope} {c : Constituent} :
    ofScope s c = some .nounClass ↔
      s = .headModifierNP ∧ c = .headNoun ∨ s = .predicateArgument ∧ c = .argument := by
  cases s <;> cases c <;> simp [ofScope]

/-! ### Assignment and realization -/

/-- The principle by which nouns are assigned to classes or classifiers. -/
inductive Assignment where
  /-- By the meaning of the referent. -/
  | semantic
  /-- By morphological properties of the noun such as declension or derivational affix. -/
  | morphological
  /-- By phonological properties of the noun such as its initial segment or final vowel. -/
  | phonological
  /-- A semantic core with a morphological or phonological overlay. -/
  | mixed
  deriving DecidableEq, Repr

/-- The surface realization of a noun categorization device: a segmental morph, attached on a
side of its host as an affix or a clitic or free, or one of the further devices by which noun
classes are marked on the noun itself. -/
inductive Realization where
  /-- A segmental morph of the given attachment kind. -/
  | morph (kind : Morph.Kind)
  /-- Stem-internal vowel change. -/
  | apophony
  /-- A suppletive stem. -/
  | suppletion
  /-- Stress. -/
  | stress
  /-- Reduplication. -/
  | reduplication
  /-- Noun incorporation. -/
  | nounIncorporation
  /-- A repeater: the noun itself, or part of it, serving as its classifier. -/
  | repeater
  deriving DecidableEq, Repr

/-- The realization of an entry: the attachment kind of its morph. -/
def realization (c : Classifier) : Realization := .morph c.kind

@[simp] theorem realization_mk (m : Morph) (script : Option String) (gloss : String) :
    realization ⟨m, script, gloss⟩ = .morph m.kind :=
  rfl

end Classifier
