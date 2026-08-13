import Linglib.Phonology.Segmental.Defs

/-!
# Vowel hiatus

Two adjacent vowels — a hiatus — are cross-linguistically dispreferred, and
languages repair the configuration, most often at morpheme junctures, by
eliding one of the two vowels ([casali-1997]'s question: which one goes?),
epenthesizing a consonant between them, or fusing them ([casali-2011]).
This file defines the configuration and its elision and epenthesis repairs.

Like `OCP.IsClean`, `Hiatus.Free` is a thin layer over `List.IsChain` — but
over co-vowelhood rather than identity, and string-adjacent rather than
tier-adjacent, so neither constraint instantiates the other and the repairs
differ (elision and epenthesis here; fusion and antigemination there).

## Main definitions

* `Hiatus.Free` / `Hiatus.count` — no vowel–vowel adjacency; the number of
  vowel–vowel adjacencies.
* `Hiatus.Juncture` — hiatus at a morpheme boundary: a vowel-final stem
  meets a vowel-initial suffix.
* `Juncture.epenthesize`, `Juncture.elideV1`, `Juncture.elideV2` — the
  repairs, applicable only to a genuine hiatus configuration.

## Main results

* `Hiatus.free_iff_count_eq_zero` — the ban and the count agree.
* `Juncture.elideV2_eq_stem_iff` — V2 elision merges the suffixed form with
  the bare stem exactly for monosegmental suffixes.
-/

namespace Phonology.Hiatus

/-- A form is **hiatus-free** when no two adjacent segments are both vowels. -/
def Free (fm : List Segment) : Prop :=
  List.IsChain (fun a b => ¬(a.IsVowel ∧ b.IsVowel)) fm

instance : DecidablePred Free := fun fm =>
  inferInstanceAs (Decidable (List.IsChain _ fm))

/-- The number of vowel–vowel adjacencies in a form — the violation count of
the markedness constraint \*Hiatus. -/
def count (fm : List Segment) : ℕ :=
  (fm.zip fm.tail).countP fun p => decide (p.1.IsVowel ∧ p.2.IsVowel)

@[simp] theorem count_nil : count [] = 0 := rfl

@[simp] theorem count_singleton (a : Segment) : count [a] = 0 := rfl

theorem count_cons_cons (a b : Segment) (fm : List Segment) :
    count (a :: b :: fm) =
      count (b :: fm) + if a.IsVowel ∧ b.IsVowel then 1 else 0 := by
  simp [count, List.countP_cons]

/-- The categorical ban and the violation count agree. -/
theorem free_iff_count_eq_zero (fm : List Segment) : Free fm ↔ count fm = 0 := by
  induction fm with
  | nil => simp [Free]
  | cons a t ih =>
      cases t with
      | nil => simp [Free]
      | cons b t' =>
          rw [Free, List.isChain_cons_cons, count_cons_cons, ← Free, ih]
          by_cases h : a.IsVowel ∧ b.IsVowel <;> simp [h]

/-! ### Hiatus at a morpheme juncture -/

/-- Hiatus at a morpheme boundary ([casali-1997]'s hiatus context): a
vowel-final stem `stemBody ++ [v1]` meets a vowel-initial suffix
`v2 :: suffixBody`. The repairs below resolve the `v1`–`v2` adjacency, and
apply only here — a consonant-final stem or consonant-initial suffix never
presents the configuration. -/
structure Juncture where
  /-- The stem minus its final vowel. -/
  stemBody : List Segment
  /-- The stem-final vowel. -/
  v1 : Segment
  /-- The suffix-initial vowel. -/
  v2 : Segment
  /-- The suffix minus its initial vowel. -/
  suffixBody : List Segment
  /-- The stem-final segment is a vowel. -/
  v1_isVowel : v1.IsVowel
  /-- The suffix-initial segment is a vowel. -/
  v2_isVowel : v2.IsVowel

namespace Juncture

variable (j : Juncture)

/-- The stem. -/
def stem : List Segment := j.stemBody ++ [j.v1]

/-- The suffix. -/
def suffix : List Segment := j.v2 :: j.suffixBody

/-- The underlying concatenation, with `v1` and `v2` in hiatus. -/
def input : List Segment := j.stemBody ++ j.v1 :: j.v2 :: j.suffixBody

theorem stem_append_suffix : j.stem ++ j.suffix = j.input := by
  simp [stem, suffix, input]

/-- Consonant epenthesis: insert `c` between the two vowels. -/
def epenthesize (c : Segment) : List Segment :=
  j.stemBody ++ j.v1 :: c :: j.v2 :: j.suffixBody

/-- V1 elision: the stem-final vowel goes. -/
def elideV1 : List Segment := j.stemBody ++ j.suffix

/-- V2 elision: the suffix-initial vowel goes. -/
def elideV2 : List Segment := j.stem ++ j.suffixBody

/-- The faithful concatenation is longer than the bare stem. -/
theorem input_ne_stem : j.input ≠ j.stem := fun h => by
  have := congrArg List.length h
  simp [input, stem] at this

/-- The epenthesized form is longer than the bare stem. -/
theorem epenthesize_ne_stem (c : Segment) : j.epenthesize c ≠ j.stem := fun h => by
  have := congrArg List.length h
  simp [epenthesize, stem] at this

/-- V2 elision merges the suffixed form with the bare stem exactly when the
suffix is monosegmental — the categorical core of suffix-length-conditioned
hiatus resolution. -/
@[simp] theorem elideV2_eq_stem_iff : j.elideV2 = j.stem ↔ j.suffixBody = [] := by
  simp [elideV2]

/-- V1 elision merges the suffixed form with the bare suffix exactly when the
stem is monosegmental. -/
@[simp] theorem elideV1_eq_suffix_iff : j.elideV1 = j.suffix ↔ j.stemBody = [] := by
  simp [elideV1]

end Juncture

end Phonology.Hiatus
