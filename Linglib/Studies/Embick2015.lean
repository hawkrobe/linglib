import Linglib.Morphology.DistributedMorphology.ComplexHead
import Linglib.Data.Examples.Embick2015

/-! # Embick 2015: Vocabulary Insertion from the inside out

[embick-2015]'s exposition of Distributed Morphology runs Vocabulary Insertion
over a complex head from the inside out, each morpheme's Q variable replaced
by the most specific applicable exponent, the conditioning context being the
concatenated neighbors once null exponents are pruned. This file runs that
procedure on the book's own material: the Latin verb fragment for *laudāre*
(present, imperfect, perfect, pluperfect) whose Agr exponents look inward at
Asp[perf] and T[+past], the Hungarian plural whose exponent looks outward at
a possessive, and the Korean nominative whose exponent looks inward at the
phonology of the stem, the three directions of conditioning the book
predicts, inward phonological conditioning through the stem's exponent and
outward conditioning through features only.

## Main results

* `latin_rows`: the twenty-four forms of the fragment derive with Pruning of
  the null T[−past].
* `rewriting_loses_m`: if insertion deleted T's features, the first-singular
  -m could not be conditioned by T[+past]; non-deletion is what the fragment
  needs.
* `hungarian_rows`, `korean_rows`: outward synsem and inward phonological
  conditioning.
* `outward_features_only`: at the Hungarian plural, the possessive ahead of it
  is still bare.

## References

[embick-2015], [halle-1997].
-/

namespace Embick2015

open DistributedMorphology
open Data.Examples (LinguisticExample)
open scoped DistributedMorphology.VocabularyItem

namespace Latin

inductive Feature where
  | laud | conjI | v | asp | perf | tense | past | agr
  | first (b : Bool) | second (b : Bool) | pl (b : Bool)
  deriving DecidableEq, Repr

open Feature

/-- The theme vowel as the exponent of v in conjugation I, Asp[perf] -vi, T[+past]
-rā after the perfect and -bā otherwise, T[−past] null, and the Agr exponents:
the perfect set after Asp[perf], -m after T[+past], the defaults elsewhere. -/
def vocab : List (VocabularyItem Feature String) :=
  [⟨⟨[v], [[conjI]], []⟩, "ā"⟩, [asp, perf] ⟷ "vi",
   ⟨⟨[tense, past], [[asp, perf]], []⟩, "rā"⟩, [tense, past] ⟷ "bā", [tense] ⟷ "",
   ⟨⟨[agr, first true, second false, pl false], [[asp, perf]], []⟩, "ī"⟩,
   ⟨⟨[agr, first false, second true, pl false], [[asp, perf]], []⟩, "stī"⟩,
   ⟨⟨[agr, first false, second true, pl true], [[asp, perf]], []⟩, "stis"⟩,
   ⟨⟨[agr, first false, second false, pl true], [[asp, perf]], []⟩, "ērunt"⟩,
   ⟨⟨[agr, first true, second false, pl false], [[tense, past]], []⟩, "m"⟩,
   [agr, first true, second false, pl false] ⟷ "ō",
   [agr, first true, second false, pl true] ⟷ "mus",
   [agr, first false, second true, pl false] ⟷ "s",
   [agr, first false, second true, pl true] ⟷ "tis",
   [agr, first false, second false, pl true] ⟷ "nt",
   [agr, first false, second false, pl false] ⟷ "t"]

inductive Tense where
  | present | imperfect | perfect | pluperfect
  deriving DecidableEq, Repr

/-- The Asp and T morphemes of each tense. -/
def Tense.heads : Tense → List (Morpheme Feature String)
  | .present => [⟨[tense], none, .after⟩]
  | .imperfect => [⟨[tense, past], none, .after⟩]
  | .perfect => [⟨[asp, perf], none, .after⟩, ⟨[tense], none, .after⟩]
  | .pluperfect => [⟨[asp, perf], none, .after⟩, ⟨[tense, past], none, .after⟩]

/-- √LAUD-v-(Asp)-T-Agr. -/
def word (t : Tense) (p₁ p₂ pl : Bool) : ComplexHead Feature String :=
  ⟨⟨[laud, conjI], some "laud", .after⟩,
   ⟨[v], none, .after⟩ :: t.heads ++
     [⟨[agr, first p₁, second p₂, Feature.pl pl], none, .after⟩]⟩

/-- Surface morphs after inside-out insertion with the given discharge. -/
def morphs (dis : ComplexHead.Discharge) (w : ComplexHead Feature String) : List String :=
  (w.insertAll (· = "") vocab .concatenation (λ _ => []) dis).exponents.filter (· ≠ "")

def parseTense : String → Option Tense
  | "present" => some .present
  | "imperfect" => some .imperfect
  | "perfect" => some .perfect
  | "pluperfect" => some .pluperfect
  | _ => none

def parsePerson : String → Option (Bool × Bool)
  | "1" => some (true, false)
  | "2" => some (false, true)
  | "3" => some (false, false)
  | _ => none

/-- A row of the fragment as its word and its morphs. -/
def ofRow (ex : LinguisticExample) : Option (ComplexHead Feature String × List String) := do
  let t ← parseTense (← ex.feature? "tense")
  let (p₁, p₂) ← parsePerson (← ex.feature? "person")
  let pl := (← ex.feature? "number") = "pl"
  pure (word t p₁ p₂ pl, ["m1", "m2", "m3", "m4", "m5"].filterMap ex.feature?)

def rows : List (ComplexHead Feature String × List String) :=
  Examples.all.filterMap ofRow

/-- The twenty-four forms of the fragment, with T[−past] pruned. -/
theorem latin_rows : ∀ r ∈ rows, morphs .nondeletion r.1 = r.2 := by decide

theorem card_rows : rows.length = 24 := by decide

/-- Rewriting T[+past]'s features away at its own insertion leaves Agr the
default -ō: the -m of the imperfect needs non-deletion. -/
theorem rewriting_loses_m :
    morphs .rewriting (word .imperfect true false false) = ["laud", "ā", "bā", "ō"] ∧
      morphs .nondeletion (word .imperfect true false false) = ["laud", "ā", "bā", "m"] := by
  decide

end Latin

namespace Hungarian

inductive Feature where
  | root (s : String) | pl | poss
  deriving DecidableEq, Repr

open Feature

/-- The plural is -ai- before a possessive and -k otherwise. -/
def vocab : List (VocabularyItem Feature String) :=
  [⟨⟨[pl], [], [[poss]]⟩, "ai"⟩, [pl] ⟷ "k", [poss] ⟷ "m"]

def word (r : String) (possessed : Bool) : ComplexHead Feature String :=
  ⟨⟨[root r], some r, .after⟩,
   ⟨[pl], none, .after⟩ :: if possessed then [⟨[poss], none, .after⟩] else []⟩

def plural (w : ComplexHead Feature String) : Option String :=
  (w.insertAll (· = "") vocab .concatenation (λ _ => []) .nondeletion).heads[0]? >>= (·.exp)

def ofRow (ex : LinguisticExample) : Option (ComplexHead Feature String × String) := do
  let possessed := (← ex.feature? "poss") = "yes"
  pure (word (← ex.feature? "root") possessed, ← ex.feature? "plExponent")

def rows : List (ComplexHead Feature String × String) :=
  Examples.all.filterMap ofRow

/-- Outward conditioning by the possessive's features. -/
theorem hungarian_rows : ∀ r ∈ rows, plural r.1 = some r.2 := by decide

/-- When the plural is reached the possessive ahead of it is still bare: what it
sees outward is features, never an exponent. -/
theorem outward_features_only :
    ((word "ruha" true).contextAt (· = "") .concatenation (λ _ => []) 0).rightCtx = [[poss]] := by
  decide

end Hungarian

namespace Korean

inductive Feature where
  | root (s : String) | nom | cFinal | vFinal
  deriving DecidableEq, Repr

open Feature

/-- The nominative is -i after a consonant and -ka after a vowel. -/
def vocab : List (VocabularyItem Feature String) :=
  [⟨⟨[nom], [[cFinal]], []⟩, "i"⟩, ⟨⟨[nom], [[vFinal]], []⟩, "ka"⟩]

/-- The phonological shape of a stem, read off its exponent. -/
def shape : String → List Feature
  | "pap" => [cFinal]
  | "ai" => [vFinal]
  | _ => []

def word (r : String) : ComplexHead Feature String :=
  ⟨⟨[root r], some r, .after⟩, [⟨[nom], none, .after⟩]⟩

def nominative (w : ComplexHead Feature String) : Option String :=
  (w.insertAll (· = "") vocab .concatenation shape .nondeletion).heads[0]? >>= (·.exp)

def ofRow (ex : LinguisticExample) : Option (ComplexHead Feature String × String) := do
  pure (word (← ex.feature? "root"), ← ex.feature? "nomExponent")

def rows : List (ComplexHead Feature String × String) :=
  Examples.all.filterMap ofRow

/-- Inward conditioning by the stem's phonology, visible through its exponent. -/
theorem korean_rows : ∀ r ∈ rows, nominative r.1 = some r.2 := by decide

end Korean

end Embick2015
