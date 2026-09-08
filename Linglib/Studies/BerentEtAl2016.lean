import Linglib.Phonology.OptimalityTheory.Doubling

/-!
# Berent et al. (2016): The double identity of linguistic doubling

Twelve experiments show that the parse of a doubled form XX, banned phonological identity
or preferred morphological reduplication, depends on the morphological context and on the
speaker's first language ([berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016]). With novel
English words doubling is disliked in isolation and preferred once linked to plural meaning
over homogeneous object sets, and sign-naïve English speakers project the same shift onto
novel ASL signs. Across languages, English speakers prefer XX signs as plurals but not as
diminutives, while Hebrew speakers, whose reduplication marks diminution and never
plurality, show no plural preference but favour XX diminutives, a reliable Language ×
Meaning interaction (Table 1). The predictions are categorical: each cell's direction follows
from whether the first language makes REALIZE-MORPH available for the meaning, by positive
or negative transfer, and the framework of `Phonology/OptimalityTheory/Doubling.lean` is
instantiated here with the two first-language grammars.

## References

* [berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016]
* [berent-2026]
-/

open OptimalityTheory.Doubling

namespace BerentEtAl2016

open Constraints OptimalityTheory

/-! ### The two first-language grammars -/

/-- English: plurality is marked morphologically (*dog-s*), diminutives are not productively
(*-let* is not productive), and no function is expressed by reduplication. -/
def englishGrammar : DoublingGrammar :=
  { morphFor := fun | .plurality => true | .diminutive => false
    redupFor := fun | .plurality => false | .diminutive => false }

/-- Hebrew: plurality (*shir* → *shirim* 'song → songs') and diminutives are both marked
morphologically, and reduplication marks diminutives (*kelev* → *klavlav* 'dog → puppy') but
never plurality, which uses suffixation. -/
def hebrewGrammar : DoublingGrammar :=
  { morphFor := fun | .plurality => true | .diminutive => true
    redupFor := fun | .plurality => false | .diminutive => true }

/-! ### Transfer and the dissociation -/

/-- The optimal parse of a doubled form for a first language and a meaning. -/
def optimalParse (g : DoublingGrammar) (f : DoublingFunction) : Finset DoublingParse :=
  (Tableau.ofRanking (l1CandidatesFor g f) (l1RankingFor g f) (l1CandidatesFor_ne g f)).optimal

private theorem candidates_ne (b : Bool) :
    (if b then morphCandidates else phonCandidates) ≠ [] := by
  cases b <;> decide

/-- Reduplication wins exactly where the first language makes REALIZE-MORPH available for
the meaning, and the nonidentical parse otherwise. -/
theorem optimalParse_eq (g : DoublingGrammar) (f : DoublingFunction) :
    optimalParse g f =
      if realizeMorphAvailable g f then {.reduplication} else {.nonidentical} := by
  show (Tableau.ofRanking (if realizeMorphAvailable g f then morphCandidates else phonCandidates)
    (if realizeMorphAvailable g f then morphRanking else phonRanking) (candidates_ne _)).optimal = _
  generalize realizeMorphAvailable g f = b
  cases b <;> decide

/-- REALIZE-MORPH is available to English speakers for plurality alone, no reduplication
contradicting it, and to Hebrew speakers for diminution alone, their reduplication marking
that and not plurality (negative transfer). -/
theorem realizeMorph_available (f : DoublingFunction) :
    (realizeMorphAvailable englishGrammar f = true ↔ f = .plurality) ∧
      (realizeMorphAvailable hebrewGrammar f = true ↔ f = .diminutive) := by
  cases f <;> decide

/-- The 2×2 of Table 1 (experiments 6a, 10a–12a): English speakers reduplicate plurals and not
diminutives, Hebrew speakers diminutives and not plurals. -/
theorem doubling_dissociation (f : DoublingFunction) :
    optimalParse englishGrammar f =
        (if f = .plurality then {.reduplication} else {.nonidentical}) ∧
      optimalParse hebrewGrammar f =
        (if f = .diminutive then {.reduplication} else {.nonidentical}) := by
  cases f <;> decide

end BerentEtAl2016
