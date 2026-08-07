import Linglib.Syntax.DependencyGrammar.Projectivity
import Linglib.Syntax.DependencyGrammar.Length
import Linglib.Data.WALS.Features.F95A
import Linglib.Data.WALS.Features.F96A
import Linglib.Data.UD.Basic
import Linglib.Features.WordOrder
import Linglib.Morphology.Word.Basic

/-!
# Gibson 2025: DLM and the head-direction generalization
[gibson-2025] [dryer-1992] [greenberg-1963] [dryer-haspelmath-2013]

[gibson-2025] argues that dependency length minimization explains the
head-direction generalization of [greenberg-1963] and [dryer-1992]:
languages overwhelmingly prefer consistent (harmonic) head direction
because disharmonic order stretches spine dependencies on recursive
structures, while single-word dependents (his Table 4: adjective-noun,
demonstrative-noun, intensifier-adjective, negator-verb) escape the
pressure because direction does not affect the length of a one-word
attachment. Both halves are worked examples below
(`harmonic_always_shorter`, `single_word_direction_irrelevant`); the
typological half is the harmonic-dominance of his WALS cross-tabulations
(Tables 1–3) and of their substrate-derived counterparts
(`CrossTab.fromWALSCh95`, `CrossTab.fromWALSCh96`).

The `AlignmentCell`/`CrossTab` apparatus is paper-anchored here; its
other consumer is the gradient extension in
`Studies/LevshinaEtAl2023.lean`. Gibson's hand-coded counts differ from
the raw WALS chapters by a handful of languages (his reporting excludes
"Other" rows); cell *pairings* match exactly, and the dominance
conclusion is the same on both.
-/

namespace Gibson2025

open DependencyGrammar
open Morphology (Word)

/-! ### Cross-tabulation apparatus -/

/-- A single cell in a 2×2 head-direction cross-tabulation: the head
    directions of the two construction types being correlated, and the
    language count. -/
structure AlignmentCell where
  dir1 : HeadDirection
  dir2 : HeadDirection
  count : Nat
  deriving Repr, DecidableEq

/-- A cell is harmonic when both constructions take the same head
    direction. -/
def AlignmentCell.IsHarmonic (c : AlignmentCell) : Prop :=
  c.dir1 = c.dir2

instance : DecidablePred AlignmentCell.IsHarmonic := fun c =>
  decEq c.dir1 c.dir2

/-- A 2×2 cross-tabulation of two head-direction-bearing construction
    types (e.g., verb-object × adposition). -/
structure CrossTab where
  name : String
  construction1 : String
  construction2 : String
  hihi : AlignmentCell
  hihf : AlignmentCell
  hfhi : AlignmentCell
  hfhf : AlignmentCell
  deriving Repr

/-- Total count of harmonic (diagonal) cells. -/
def CrossTab.harmonicCount (t : CrossTab) : Nat :=
  t.hihi.count + t.hfhf.count

/-- Total count of disharmonic (off-diagonal) cells. -/
def CrossTab.disharmonicCount (t : CrossTab) : Nat :=
  t.hihf.count + t.hfhi.count

/-- Total number of languages in the table. -/
def CrossTab.totalCount (t : CrossTab) : Nat :=
  t.harmonicCount + t.disharmonicCount

/-- Harmonic pairings strictly outnumber disharmonic. A *raw-count*
    primitive; serious typological generalisations require sample-bias
    correction (cf. [dryer-1992]'s genus method). -/
def CrossTab.IsHarmonicDominant (t : CrossTab) : Prop :=
  t.harmonicCount > t.disharmonicCount

instance : DecidablePred CrossTab.IsHarmonicDominant := fun _ =>
  Nat.decLt _ _

/-! ### Gibson's tables -/

/-- Gibson Table 1: verb-object order × adposition order (981 languages). -/
def voAdposition : CrossTab :=
  { name := "VO × Adposition"
    construction1 := "Verb-Object"
    construction2 := "Adposition"
    hihi := ⟨.headInitial, .headInitial, 454⟩
    hihf := ⟨.headInitial, .headFinal, 41⟩
    hfhi := ⟨.headFinal, .headInitial, 14⟩
    hfhf := ⟨.headFinal, .headFinal, 472⟩ }

/-- Gibson Table 2: verb-object order × subordinator order (456 languages). -/
def voSubordinator : CrossTab :=
  { name := "VO × Subordinator"
    construction1 := "Verb-Object"
    construction2 := "Subordinator"
    hihi := ⟨.headInitial, .headInitial, 302⟩
    hihf := ⟨.headInitial, .headFinal, 2⟩
    hfhi := ⟨.headFinal, .headInitial, 61⟩
    hfhf := ⟨.headFinal, .headFinal, 91⟩ }

/-- Gibson Table 3: verb-object order × relative clause order (665 languages). -/
def voRelativeClause : CrossTab :=
  { name := "VO × Relative clause"
    construction1 := "Verb-Object"
    construction2 := "Relative clause"
    hihi := ⟨.headInitial, .headInitial, 415⟩
    hihf := ⟨.headInitial, .headFinal, 5⟩
    hfhi := ⟨.headFinal, .headInitial, 113⟩
    hfhf := ⟨.headFinal, .headFinal, 132⟩ }

/-- Gibson's three cross-tabulations. -/
def allTables : List CrossTab :=
  [voAdposition, voSubordinator, voRelativeClause]

/-- The head-direction generalization ([greenberg-1963], [dryer-1992]):
    harmonic pairings dominate in every one of Gibson's construction-pair
    tables. -/
theorem head_direction_generalization :
    ∀ t ∈ allTables, t.IsHarmonicDominant := by decide

/-! ### The recursive-embedding worked examples

Gibson's mechanism: "thinks John knows Mary likes cats" in the four
head-direction regimes. Consistent direction keeps every arc short;
mixed direction stretches the spine arcs. -/

/-- Harmonic head-initial. -/
def harmonicHI : Graph 6 :=
  .ofArcs [Word.mk' "thinks" .VERB, Word.mk' "John" .PROPN, Word.mk' "knows" .VERB,
           Word.mk' "Mary" .PROPN, Word.mk' "likes" .VERB, Word.mk' "cats" .NOUN]
    0 [(0, 1, .nsubj), (0, 2, .ccomp), (2, 3, .nsubj), (2, 4, .ccomp), (4, 5, .obj)]

/-- Harmonic head-final (the mirror). -/
def harmonicHF : Graph 6 :=
  .ofArcs [Word.mk' "cats" .NOUN, Word.mk' "likes" .VERB, Word.mk' "Mary" .PROPN,
           Word.mk' "knows" .VERB, Word.mk' "John" .PROPN, Word.mk' "thinks" .VERB]
    5 [(1, 0, .obj), (3, 1, .ccomp), (3, 2, .nsubj), (5, 3, .ccomp), (5, 4, .nsubj)]

/-- Disharmonic: head-initial spine, head-final complements. -/
def disharmonicHF : Graph 6 :=
  .ofArcs [Word.mk' "thinks" .VERB, Word.mk' "John" .PROPN, Word.mk' "Mary" .PROPN,
           Word.mk' "cats" .NOUN, Word.mk' "likes" .VERB, Word.mk' "knows" .VERB]
    0 [(0, 1, .nsubj), (0, 5, .ccomp), (5, 2, .nsubj), (5, 4, .ccomp), (4, 3, .obj)]

/-- Disharmonic: head-final spine, head-initial complements. -/
def disharmonicFH : Graph 6 :=
  .ofArcs [Word.mk' "John" .PROPN, Word.mk' "knows" .VERB, Word.mk' "Mary" .PROPN,
           Word.mk' "likes" .VERB, Word.mk' "cats" .NOUN, Word.mk' "thinks" .VERB]
    5 [(5, 0, .nsubj), (5, 1, .ccomp), (1, 2, .nsubj), (1, 3, .ccomp), (3, 4, .obj)]

example : harmonicHI.IsTree ∧ harmonicHF.IsTree ∧
    disharmonicHF.IsTree ∧ disharmonicFH.IsTree := by decide

/-- All four regimes are projective: the disharmonic ones are longer not
    because of non-projectivity — consistent direction is a separate,
    stronger constraint. -/
example : IsProjective harmonicHI ∧ IsProjective harmonicHF ∧
    IsProjective disharmonicHF ∧ IsProjective disharmonicFH := by decide

/-- Harmonic order is strictly cheaper in both directions, and the mirror
    pair costs exactly the same. -/
theorem harmonic_always_shorter :
    harmonicHI.totalLength < disharmonicHF.totalLength ∧
    harmonicHI.totalLength < disharmonicFH.totalLength ∧
    harmonicHF.totalLength = harmonicHI.totalLength := by decide

/-- Harmonic trees satisfy [behaghel-1932]'s Oberstes Gesetz at
    threshold 2; disharmonic trees do not. -/
example : OberstesGesetz harmonicHI 2 ∧ OberstesGesetz harmonicHF 2 := by decide
example : ¬ OberstesGesetz disharmonicHF 2 ∧ ¬ OberstesGesetz disharmonicFH 2 := by
  decide

/-! ### Single-word dependents escape the pressure (Gibson Table 4)

Adjective-noun, demonstrative-noun, intensifier-adjective, and
negator-verb orders are frequently disharmonic; all four involve
dependents that are typically single words, and a one-word attachment
has the same dependency length in either direction. -/

/-- "very tall": single-word intensifier before its head. -/
def intensifierFinal : Graph 2 :=
  .ofArcs [Word.mk' "very" .ADV, Word.mk' "tall" .ADJ] 1 [(1, 0, .advmod)]

/-- "tall very": the same attachment, head-initial. -/
def intensifierInitial : Graph 2 :=
  .ofArcs [Word.mk' "tall" .ADJ, Word.mk' "very" .ADV] 0 [(0, 1, .advmod)]

/-- A single-word dependent costs the same in either direction — DLM is
    silent exactly where the typology tolerates disharmony. -/
theorem single_word_direction_irrelevant :
    intensifierFinal.totalLength = intensifierInitial.totalLength := by decide

/-! ### Substrate-derived counterparts (WALS Ch 95, Ch 96) -/

/-- Gibson's Table 1 rebuilt from `Data.WALS.F95A.allData`
    ([dryer-haspelmath-2013] Ch 95): the verb-object × adposition
    correlation from raw WALS counts. -/
def CrossTab.fromWALSCh95 : CrossTab :=
  let data := Data.WALS.F95A.allData
  { name := "WALS Ch 95: VO × Adposition"
    construction1 := "Verb-Object"
    construction2 := "Adposition"
    hihi := ⟨.headInitial, .headInitial, (data.filter (·.value == .voAndPrepositions)).length⟩
    hihf := ⟨.headInitial, .headFinal, (data.filter (·.value == .voAndPostpositions)).length⟩
    hfhi := ⟨.headFinal, .headInitial, (data.filter (·.value == .ovAndPrepositions)).length⟩
    hfhf := ⟨.headFinal, .headFinal, (data.filter (·.value == .ovAndPostpositions)).length⟩ }

/-- Gibson's Table 3 rebuilt from `Data.WALS.F96A.allData`
    ([dryer-haspelmath-2013] Ch 96): the verb-object × relative-clause
    correlation from raw WALS counts. NRel is head-initial for the
    noun-relative construction, RelN head-final. -/
def CrossTab.fromWALSCh96 : CrossTab :=
  let data := Data.WALS.F96A.allData
  { name := "WALS Ch 96: VO × Relative clause"
    construction1 := "Verb-Object"
    construction2 := "Relative clause"
    hihi := ⟨.headInitial, .headInitial, (data.filter (·.value == .voAndNrel)).length⟩
    hihf := ⟨.headInitial, .headFinal, (data.filter (·.value == .voAndReln)).length⟩
    hfhi := ⟨.headFinal, .headInitial, (data.filter (·.value == .ovAndNrel)).length⟩
    hfhf := ⟨.headFinal, .headFinal, (data.filter (·.value == .ovAndReln)).length⟩ }

set_option maxRecDepth 8192 in
/-- The substrate-derived Ch 95 table is harmonic-dominant — the same
    conclusion as Gibson's hand-coded Table 1. -/
theorem fromWALSCh95_harmonic_dominant :
    CrossTab.fromWALSCh95.IsHarmonicDominant := by decide

set_option maxRecDepth 8192 in
/-- The substrate-derived Ch 96 table is harmonic-dominant — the same
    conclusion as Gibson's hand-coded Table 3. -/
theorem fromWALSCh96_harmonic_dominant :
    CrossTab.fromWALSCh96.IsHarmonicDominant := by decide

end Gibson2025
