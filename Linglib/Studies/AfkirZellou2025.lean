import Linglib.Fragments.Tarifit.Inventory
import Linglib.Data.Examples.AfkirZellou2025

/-!
# Schwa variation in Tarifit CCəC words

Tarifit triconsonantal verbs in the simple imperative carry a prosodic-template schwa between
the second and third root consonants, and Afkir and Zellou find two further phonetic variants:
a shorter, coarticulating intrusive schwa inside the initial cluster ([Cə̆CəC], about a quarter of
productions), and vowelless forms ([CCC], about five percent), neither of them sensitive to
speaking style. The two schwas are independent processes, the template schwa a targeted segment
whose deletion shortens the word and the intrusive schwa a targetless vocoid. Their distribution
over the thirty-eight target words is tabulated by word, and this file states those tables'
generalizations over the pooled rows, with each word's sonority profile computed from the
fragment's consonant classes (`word?`, `intrusion?`, `vowelless?`).

Two hypotheses about the intrusive schwa are set against each other: repair, on which
insertion should be most frequent in the dispreferred falling-sonority clusters, and the
syllable-planning account of Georgian, on which a vocoid is tolerated only where it boosts the
planned sonority peak, hence in rising clusters. The data side with the second: every rising
cluster shows intrusion at least variably unless its second consonant is voiceless
(`intrusion_of_rising`), the words that never or rarely show intrusion are non-rising or have a
voiceless second consonant (`nonRising_or_voiceless_of_never_rarely`), and the paper's three
flagged exceptions are the only non-rising words with a voiceless second consonant that vary
(`variably_exceptions`). The near-categorical class is exactly the words with medial /r/
(`almostExclusively_iff_c2_r`); it is not the rising class, since on the paper's scale the
pharyngeal outranks the tap and /ʕrəm/ falls.
Vowellessness tracks low sonority: the often-vowelless words have voiceless second and third
consonants, except the flagged /ħkəm/ (`voiceless_of_often_vowelless`), and the never-vowelless
words all carry a voiced consonant there (`voiced_of_never_vowelless`). The regression
estimates, the acoustic measurements, and the perception result that an intrusive vowel aids
discrimination only in falling clusters are reported in the paper without a formal counterpart
here.

## References

* [afkir-zellou-2025]
* [parker-2002]
* [hall-2006]
-/

namespace AfkirZellou2025

open Tarifit Data.Examples

/-- Rate of the intrusive C1ə̆C2 schwa across a word's productions. -/
inductive Intrusion
  | never
  | rarely
  | variably
  | almostExclusively
  deriving DecidableEq, Repr

/-- Rate of vowelless production of a word. -/
inductive Vowelless
  | never
  | rarely
  | often
  deriving DecidableEq, Repr

/-- The target word a row reports, by its transcription. -/
def word? (e : LinguisticExample) : Option TriconWord := words.find? (·.ipa == e.primaryText)

/-- The row's intrusion category. -/
def intrusion? (e : LinguisticExample) : Option Intrusion :=
  match e.feature? "intrusion" with
  | some "never" => some .never
  | some "rarely" => some .rarely
  | some "variably" => some .variably
  | some "almost exclusively" => some .almostExclusively
  | _ => none

/-- The row's vowelless category. -/
def vowelless? (e : LinguisticExample) : Option Vowelless :=
  match e.feature? "vowelless" with
  | some "never" => some .never
  | some "rarely" => some .rarely
  | some "often" => some .often
  | _ => none

/-- Every row names a target word and carries both categories. -/
theorem rows_complete :
    ∀ e ∈ Examples.all, (word? e).isSome ∧ (intrusion? e).isSome ∧ (vowelless? e).isSome := by
  decide

/-! ### The intrusive schwa -/

/-- Intrusion is near-categorical exactly in the words whose second consonant is /r/. -/
theorem almostExclusively_iff_c2_r :
    ∀ e ∈ Examples.all, ∀ w ∈ word? e,
      intrusion? e = some .almostExclusively ↔ w.c2 = .r := by
  decide

/-- A rising cluster shows intrusion at least variably unless its second consonant is
voiceless. -/
theorem intrusion_of_rising :
    ∀ e ∈ Examples.all, ∀ w ∈ word? e, w.Rising →
      intrusion? e = some .variably ∨ intrusion? e = some .almostExclusively ∨
        w.c2.Voiceless := by
  decide

/-- Words that never or rarely show intrusion have a non-rising cluster or a voiceless second
consonant. -/
theorem nonRising_or_voiceless_of_never_rarely :
    ∀ e ∈ Examples.all, (intrusion? e = some .never ∨ intrusion? e = some .rarely) →
      ∀ w ∈ word? e, ¬ w.Rising ∨ w.c2.Voiceless := by
  decide

/-- Variable intrusion goes with a rising cluster or a voiced second consonant, except for the
three words the paper flags. -/
theorem variably_exceptions :
    ∀ e ∈ Examples.all, intrusion? e = some .variably →
      ∀ w ∈ word? e, w.Rising ∨ ¬ w.c2.Voiceless ∨ w ∈ [nqeb, nqer, qtes] := by
  decide

/-! ### Vowelless production -/

/-- Often-vowelless words have voiceless second and third consonants, except /ħkəm/. -/
theorem voiceless_of_often_vowelless :
    ∀ e ∈ Examples.all, vowelless? e = some .often →
      ∀ w ∈ word? e, (w.c2.Voiceless ∧ w.c3.Voiceless) ∨ w = hkem := by
  decide

/-- Never-vowelless words have a voiced second or third consonant. -/
theorem voiced_of_never_vowelless :
    ∀ e ∈ Examples.all, vowelless? e = some .never →
      ∀ w ∈ word? e, ¬ w.c2.Voiceless ∨ ¬ w.c3.Voiceless := by
  decide

end AfkirZellou2025
