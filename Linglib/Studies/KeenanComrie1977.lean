import Mathlib.Order.UpperLower.Basic
import Linglib.Syntax.Clause.Relative
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
form an upper set of the hierarchy order (`prc_of_hc2`).

The constraints are then checked on the seventeen languages of Table 1 whose relativization
markers the fragments record (`hc1_verified`, `hc2_verified`), so every primary strategy of the
sample covers the interval from its cut-off up to the subject (`primary_positions_eq_Icc_top`);
each position from subject to genitive is attested as the cut-off of a primary strategy, the
paper's Section 1.3 argument for the third constraint (`each_upper_cutoff_attested`); and Toba
Batak's gap at direct object between two continuous strategies shows why the constraints are
stated per strategy rather than per language (`toba_batak_do_gap`).

## Implementation notes

The hierarchy order is the substrate's `Position` bounded linear order, the subject its top; a
strategy is a fragment `Marker` with the positions it covers, and its continuity is
`Marker.IsContinuous`, order-connectedness of the covered set. Modern Standard Arabic
contributes the two markers Table 1 records rather than the fragment's full inventory, and the
languages the fragments add after 1977 are not consulted.

## References

* [keenan-comrie-1977]
-/

namespace KeenanComrie1977

open RelativeClause Finset

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
  ∀ m ∈ markers, m.IsPrimary → IsUpperSet (m.positions : Set Position)

/-- The Primary Relativization Constraint follows from HC₂ and the definition of primary, as
the paper derives it: a continuous strategy that relativizes subjects covers an upper set. -/
theorem prc_of_hc2 {markers : List Marker} (h : SatisfiesHC2 markers) : SatisfiesPRC markers :=
  fun m hm hp ↦ Set.OrdConnected.isUpperSet_of_top_mem (h m hm) hp

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
  fun _ h ↦ prc_of_hc2 (hc2_verified _ h)

/-- In the sample every primary strategy covers exactly the closed interval from its cut-off up
to the subject, by HC₂ and `Finset.eq_Icc_top_of_ordConnected_coe`: what Table 1 records as a
run of `+` entries ending at the subject. -/
theorem primary_positions_eq_Icc_top :
    ∀ markers ∈ sample, ∀ m ∈ markers, (hp : m.IsPrimary) →
      m.positions = Icc (m.positions.min' ⟨⊤, hp⟩) ⊤ :=
  fun _ h m hm hp ↦ eq_Icc_top_of_ordConnected_coe (hc2_verified _ h m hm) hp

/-- Every position from subject to genitive is the cut-off of some primary strategy in the
sample, which covers exactly the interval from there up to the subject: the Section 1.3 argument
that each point of the hierarchy is a possible cut-off. The paper's witnesses for the object of
comparison are not among the fragments. -/
theorem each_upper_cutoff_attested :
    ∀ p ∈ [Position.subject, .directObject, .indirectObject, .oblique, .genitive],
      ∃ markers ∈ sample, ∃ m ∈ markers, m.positions = Icc p ⊤ := by
  decide

/-! ### Toba Batak (Section 1.2.2) -/

/-- Toba Batak relativizes subjects by one strategy and indirect objects through genitives by
another, but direct objects by neither: the gap lies between two continuous strategies, which
is why the constraints govern strategies rather than languages. -/
theorem toba_batak_do_gap : ∀ m ∈ tobaBatak, .directObject ∉ m.positions := by decide

theorem toba_batak_hc2 : SatisfiesHC2 tobaBatak := by decide

/-! ### Strategies by their relativized position (Section 1.3) -/

/-- Korean (Section 1.3.4): the gap strategy stops at obliques and genitives require a retained
pronoun. -/
theorem korean_genitive_retention : korean.map (·.npRel) = [.gap, .resumptive] := by decide

/-- Finnish (Section 1.3.2): the case-marked *joka* is the broader strategy, the participle
covering subject and direct object only, both primary. -/
theorem finnish_plus_case_is_primary :
    finnish.map (·.bearsCaseMarking) = [true, false] ∧ ∀ m ∈ finnish, m.IsPrimary := by
  decide

end KeenanComrie1977
