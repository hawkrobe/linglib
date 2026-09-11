import Linglib.Syntax.RelativeClause.Basic
import Linglib.Fragments.English.Relativization
import Linglib.Fragments.Welsh.Relativization
import Linglib.Fragments.Arabic.ModernStandard.Relativization
import Linglib.Fragments.Hebrew.Relativization
import Linglib.Fragments.TobaBatak.Relativization
import Linglib.Fragments.Korean.Relativization
import Linglib.Fragments.Finnish.Relativization
import Linglib.Fragments.Malagasy.Relativization
import Linglib.Fragments.Mandarin.Relativization
import Linglib.Fragments.Basque.Relativization
import Linglib.Fragments.German.Relativization
import Linglib.Fragments.HindiUrdu.Relativization
import Linglib.Fragments.Japanese.Relativization
import Linglib.Fragments.Romance.French.Relativization
import Linglib.Fragments.Slavic.Russian.Relativization
import Linglib.Fragments.Tagalog.Relativization
import Linglib.Fragments.Turkish.Relativization

/-!
# Keenan and Comrie (1977): Noun Phrase Accessibility and Universal Grammar

This file formalizes the Hierarchy Constraints of [keenan-comrie-1977] on the Accessibility
Hierarchy of grammatical positions, subject > direct object > indirect object > oblique >
genitive > object of comparison: a language must relativize subjects, every relative-clause
strategy applies to a continuous segment of the hierarchy, and a strategy may cease at any
lower point (Section 1.2). A strategy is primary when it relativizes subjects, and the paper's
Primary Relativization Constraint, that a primary strategy reaching a low position reaches
every higher one, follows from continuity: the positions a continuous primary strategy covers
form an upper set of the hierarchy order (`isUpperSet_of_isContinuous`, `prc_of_hc2`).

The constraints are then checked on the seventeen languages of Table 1 whose relativization
markers the fragments record (`hc1_verified`, `hc2_verified`); each position from subject to
genitive is attested as the cut-off of a primary strategy, the paper's Section 1.3 argument for
the third constraint (`each_upper_cutoff_attested`); and Toba Batak's gap at direct object
between two continuous strategies shows why the constraints are stated per strategy rather than
per language (`toba_batak_do_gap`). The per-language theorems read Table 1 off the fragments.

## Implementation notes

The hierarchy order is the substrate's `AHPosition` linear order, the subject its top; a
strategy is a fragment `Marker` with the positions it covers, and its continuity is
`Marker.IsContinuous`, order-connectedness of the covered set. Modern Standard Arabic
contributes the two markers Table 1 records rather than the fragment's full inventory, and the
languages the fragments add after 1977 are not consulted.

## References

* [keenan-comrie-1977]
-/

namespace KeenanComrie1977

open RelativeClause

/-! ### The Hierarchy Constraints (Section 1.2) -/

/-- HC₁: some strategy relativizes subjects. -/
def SatisfiesHC1 (markers : List Marker) : Prop := ∃ m ∈ markers, m.IsPrimary

instance (markers : List Marker) : Decidable (SatisfiesHC1 markers) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- HC₂: every strategy covers a continuous segment of the hierarchy. -/
def SatisfiesHC2 (markers : List Marker) : Prop := ∀ m ∈ markers, m.IsContinuous

instance (markers : List Marker) : Decidable (SatisfiesHC2 markers) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The Primary Relativization Constraint: a primary strategy covers an upper set of the
hierarchy, every position above one it reaches. -/
def SatisfiesPRC (markers : List Marker) : Prop :=
  ∀ m ∈ markers, m.IsPrimary → IsUpperSet {p | m.Covers p}

/-- The subject is the top of the hierarchy. -/
theorem le_subject (p : AHPosition) : p ≤ .subject := by cases p <;> decide

/-- A continuous strategy that relativizes subjects covers an upper set: from a covered
position up to the subject everything is covered. -/
theorem isUpperSet_of_isContinuous {m : Marker} (hc : m.IsContinuous) (hp : m.IsPrimary) :
    IsUpperSet {p | m.Covers p} :=
  λ _ b hab ha => hc.out ha hp ⟨hab, le_subject b⟩

/-- The Primary Relativization Constraint follows from HC₂ and the definition of primary, as
the paper derives it. -/
theorem prc_of_hc2 {markers : List Marker} (h : SatisfiesHC2 markers) : SatisfiesPRC markers :=
  λ m hm hp => isUpperSet_of_isContinuous (h m hm) hp

/-- The lowest position a strategy reaches, its cut-off. -/
def cutoff (m : Marker) : Option AHPosition := m.positions.min?

/-- The lowest position any strategy of a language reaches. -/
def lowestCovered (markers : List Marker) : Option AHPosition :=
  (markers.flatMap (·.positions)).min?

/-! ### The sample (Table 1)

The seventeen languages of Table 1 whose markers the fragments record. -/

abbrev english := English.relMarkers
abbrev welsh := Welsh.relMarkers
/-- The two Modern Standard Arabic markers Table 1 records, the definite-headed relative
pronoun with a gap and with a resumptive; the fragment's indefinite-headed asyndetic markers
are not in the paper. -/
abbrev arabic : List Marker :=
  [Arabic.ModernStandard.relAlladhi, Arabic.ModernStandard.relResumptive]
abbrev hebrew := Hebrew.relMarkers
abbrev tobaBatak := TobaBatak.relMarkers
abbrev korean := Korean.relMarkers
abbrev finnish := Finnish.relMarkers
abbrev malagasy := Malagasy.relMarkers
/-- Table 1's Chinese, spoken Pekingese. -/
abbrev mandarin := Mandarin.relMarkers
abbrev basque := Basque.relMarkers
abbrev french := French.relMarkers
abbrev german := German.relMarkers
/-- Table 1's Hindi. -/
abbrev hindi := HindiUrdu.relMarkers
abbrev japanese := Japanese.relMarkers
abbrev russian := Russian.relMarkers
abbrev tagalog := Tagalog.relMarkers
abbrev turkish := Turkish.relMarkers

/-- The sample. -/
def sample : List (List Marker) :=
  [english, welsh, arabic, hebrew, tobaBatak, korean, finnish, malagasy, mandarin, basque,
    french, german, hindi, japanese, russian, tagalog, turkish]

/-- HC₁ holds of every language in the sample. -/
theorem hc1_verified : ∀ markers ∈ sample, SatisfiesHC1 markers := by decide

/-- HC₂ holds of every strategy in the sample. -/
theorem hc2_verified : ∀ markers ∈ sample, SatisfiesHC2 markers := by decide

/-- Hence so does the Primary Relativization Constraint. -/
theorem prc_verified : ∀ markers ∈ sample, SatisfiesPRC markers :=
  λ _ h => prc_of_hc2 (hc2_verified _ h)

/-- Every position from subject to genitive is the cut-off of some primary strategy in the
sample, the Section 1.3 argument that each point of the hierarchy is a possible cut-off; the
paper's witnesses for the object of comparison are not among the fragments. -/
theorem each_upper_cutoff_attested :
    ∀ p ∈ [AHPosition.subject, .directObject, .indirectObject, .oblique, .genitive],
      ∃ markers ∈ sample, ∃ m ∈ markers, m.IsPrimary ∧ cutoff m = some p := by
  decide

/-! ### Toba Batak (Section 1.2.2) -/

/-- Toba Batak relativizes subjects by one strategy and indirect objects through genitives by
another, but direct objects by neither: the gap lies between two continuous strategies, which
is why the constraints govern strategies rather than languages. -/
theorem toba_batak_do_gap : ∀ m ∈ tobaBatak, ¬ m.Covers .directObject := by decide

theorem toba_batak_hc2 : SatisfiesHC2 tobaBatak := by decide

/-! ### Table 1 by language -/

/-- English: the case-free *that* and gap cover subject and direct object, the case-marked
*who*/*whom* the four lower positions. -/
theorem english_full_coverage : english.map (·.positions.length) = [2, 4] := by decide

/-- Welsh (Section 1.3.2): the particle *a* covers subject and direct object, the particle *y*
with a resumptive the lower four. -/
theorem welsh_strategy_split :
    welsh.map (λ m => decide (m.Covers .subject)) = [true, false] ∧
      welsh.map (λ m => decide (m.Covers .indirectObject)) = [false, true] := by
  decide

/-- Modern Standard Arabic: the relative pronoun alone covers the subject only, with a
resumptive the positions below. -/
theorem arabic_primary_su_only :
    arabic.map (λ m => decide (m.Covers .subject)) = [true, false] ∧
      arabic.map (λ m => decide (m.Covers .directObject)) = [false, true] := by
  decide

/-- Malagasy (Section 1.3.1): a single strategy, subjects only. -/
theorem malagasy_su_only : lowestCovered malagasy = some .subject := by decide

/-- Korean (Section 1.3.4): the adnominal verb suffix covers subject through oblique, a
genitive marker the genitive only. -/
theorem korean_primary_su_to_obl :
    korean.map cutoff = [some .oblique, some .genitive] := by decide

/-- Mandarin: the gap covers subject and direct object, retention direct object through object
of comparison, the two overlapping at direct object. -/
theorem mandarin_retention_reaches_ocomp :
    lowestCovered mandarin = some .objComparison ∧
      mandarin.map (λ m => decide (m.Covers .directObject)) = [true, true] := by
  decide

/-- Basque (Section 1.3.3): a single strategy cutting off at indirect object. -/
theorem basque_cutoff_at_io :
    basque.length = 1 ∧ lowestCovered basque = some .indirectObject := by decide

/-- French: the single relative pronoun system covers subject through genitive. -/
theorem french_single_strategy_to_gen :
    french.length = 1 ∧ lowestCovered french = some .genitive := by decide

/-- German ((1) and (2), Section 1.3.1): the relative pronoun covers subject through genitive,
the participial strategy subjects only. -/
theorem german_participial_su_only : german.map (·.positions.length) = [5, 1] := by decide

/-- Hindi: both strategies are primary and reach the genitive. -/
theorem hindi_both_strategies_primary :
    ∀ m ∈ hindi, m.IsPrimary ∧ cutoff m = some .genitive := by decide

/-- Japanese: the gap reaches the genitive. -/
theorem japanese_gap_to_gen : lowestCovered japanese = some .genitive := by decide

/-- Russian: the single declining relative pronoun covers subject through genitive. -/
theorem russian_single_strategy_to_gen :
    russian.length = 1 ∧ lowestCovered russian = some .genitive := by decide

/-- Tagalog (Section 1.3.1): two strategies, each subjects only. -/
theorem tagalog_su_only : ∀ m ∈ tagalog, m.positions = [.subject] := by decide

/-- Turkish: participles cover subject through oblique, retention the positions below. -/
theorem turkish_retention_below_participles :
    lowestCovered turkish = some .objComparison ∧
      turkish.map cutoff = [some .oblique, some .objComparison] := by
  decide

/-- Finnish (Section 1.3.2): the case-marked *joka* is the broader strategy, the participle
covering subject and direct object only, both primary. -/
theorem finnish_plus_case_is_primary :
    finnish.map (·.bearsCaseMarking) = [true, false] ∧ ∀ m ∈ finnish, m.IsPrimary := by
  decide

end KeenanComrie1977
