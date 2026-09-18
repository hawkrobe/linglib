import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# Corpus word-order data: schema

Typed schema for the word-order data a paper draws from corpora: per-language counts of the
two relative orders of a nominal subject and object, per-language printed statistics of that
order (its Shannon entropy and the mutual information between case marking and syntactic role),
and individually annotated clauses recording the order of object and verb together with the
text type, the object's length, and its animacy. Generated rows live in
`Data/WordOrder/Corpus/<Paper>.lean`, emitted from the canonical `<Paper>.json` by
`scripts/gen_word_order_corpus.py`.

This is data: it imports nothing from `Linglib/` and states no theorems; the order and text-type
enumerations carry the discrete measurable structure so that consumers can take laws over them.
Counts are the dataset's integers; printed statistics are scaled integers, in thousandths of a
bit, at the precision the dataset prints, so that consumers compute over them by `decide`.
Language codes are ISO 639-3 codes as the datasets print them.

## References

* [levshina-etal-2023]
-/

namespace Data.WordOrder.Corpus

/-- The relative order of a nominal subject and a nominal object in a clause. -/
inductive SubjectObject where
  | subjectFirst
  | objectFirst
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace SubjectObject := ⊤
instance : MeasurableSingletonClass SubjectObject := ⟨fun _ ↦ trivial⟩

/-- The relative order of a nominal object and its verb in a clause. -/
inductive ObjectVerb where
  | objectFirst
  | verbFirst
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace ObjectVerb := ⊤
instance : MeasurableSingletonClass ObjectVerb := ⟨fun _ ↦ trivial⟩

/-- The text type of a corpus sample. -/
inductive TextType where
  | conversation
  | fiction
  | news
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace TextType := ⊤
instance : MeasurableSingletonClass TextType := ⟨fun _ ↦ trivial⟩

/-- One language's counts of subject-before-object and object-before-subject clauses in a
corpus. -/
structure SubjectObjectCounts where
  /-- The language name as the dataset prints it. -/
  language : String
  /-- The ISO 639-3 language code. -/
  isoCode : String
  /-- The number of clauses with the subject before the object. -/
  subjectFirst : ℕ
  /-- The number of clauses with the object before the subject. -/
  objectFirst : ℕ
  deriving DecidableEq, Repr

/-- One language's printed statistics of subject–object order in a corpus, the Shannon entropy
of the order and the mutual information between case marking and syntactic role, both in
thousandths of a bit. -/
structure SubjectObjectStatistics where
  /-- The language name as the dataset prints it. -/
  language : String
  /-- The Shannon entropy of subject–object order, in thousandths of a bit. -/
  entropy1000 : ℕ
  /-- The mutual information between case marking and syntactic role, in thousandths of a
  bit. -/
  caseMutualInformation1000 : ℕ
  deriving DecidableEq, Repr

/-- One annotated declarative clause, with its text type and source text, the order of object
and verb, the object's length in words, and whether the object is animate. -/
structure Clause where
  textType : TextType
  /-- The title of the source text as the dataset prints it. -/
  source : String
  order : ObjectVerb
  /-- The length of the object in words. -/
  objectLength : ℕ
  animate : Bool
  deriving DecidableEq, Repr

end Data.WordOrder.Corpus
