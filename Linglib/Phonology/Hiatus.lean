import Linglib.Phonology.Segmental.Defs

/-!
# Vowel hiatus

Two adjacent vowels — a hiatus — are cross-linguistically dispreferred, and
languages repair the configuration, most often at morpheme junctures, by
eliding one of the two vowels ([casali-1997]'s question: which one goes?),
epenthesizing a consonant between them, or fusing them ([casali-2011]).
This file defines the configuration and the elision and epenthesis repairs
on segment strings.

Like `OCP.IsClean`, `Hiatus.Free` is a thin layer over `List.IsChain` — but
over co-vowelhood rather than identity, and string-adjacent rather than
tier-adjacent, so neither constraint instantiates the other and the repairs
differ (elision and epenthesis here; fusion and antigemination there).

## Main definitions

* `Hiatus.Free` / `Hiatus.count` — no vowel–vowel adjacency; the number of
  vowel–vowel adjacencies.
* `Hiatus.epenthesize`, `Hiatus.elideV1`, `Hiatus.elideV2` — the juncture
  repairs.

## Main results

* `Hiatus.free_iff_count_eq_zero` — the ban and the count agree.
* `Hiatus.elideV2_eq_left_iff` — V2 elision merges the suffixed form with the
  bare stem exactly for monosegmental suffixes.
-/

namespace Phonology.Hiatus

open Phonology

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

/-! ### Juncture repairs -/

/-- Consonant epenthesis at a morpheme juncture: insert `c` between stem and
suffix. -/
def epenthesize (c : Segment) (st suf : List Segment) : List Segment :=
  st ++ c :: suf

/-- V1 elision at a morpheme juncture: the stem-final segment goes. -/
def elideV1 (st suf : List Segment) : List Segment := st.dropLast ++ suf

/-- V2 elision at a morpheme juncture: the suffix-initial segment goes. -/
def elideV2 (st suf : List Segment) : List Segment := st ++ suf.tail

/-- V2 elision merges the suffixed form with the bare stem exactly when the
suffix is monosegmental — the categorical core of suffix-length-conditioned
hiatus resolution. -/
theorem elideV2_eq_left_iff {st suf : List Segment} (hsuf : suf ≠ []) :
    elideV2 st suf = st ↔ suf.length = 1 := by
  cases suf with
  | nil => exact absurd rfl hsuf
  | cons a l => simp [elideV2, List.length_eq_zero_iff]

/-- V1 elision merges the suffixed form with the bare suffix exactly when the
stem is monosegmental. -/
theorem elideV1_eq_right_iff {st suf : List Segment} (hst : st ≠ []) :
    elideV1 st suf = suf ↔ st.length = 1 := by
  constructor
  · intro h
    have hlen := congrArg List.length h
    have h0 : st.length ≠ 0 := fun h' => hst (List.length_eq_zero_iff.1 h')
    simp only [elideV1, List.length_append, List.length_dropLast] at hlen
    omega
  · intro h
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 h
    rfl

end Phonology.Hiatus
