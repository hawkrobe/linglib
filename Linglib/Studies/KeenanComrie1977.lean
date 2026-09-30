module

public import Mathlib.Order.UpperLower.Basic
public import Linglib.Core.Order.OrdConnected
public import Linglib.Syntax.Clause.Relative
public import Linglib.Fragments.English.Relativization
public import Linglib.Fragments.Welsh.Relativization
public import Linglib.Fragments.Arabic.ModernStandard.Relativization
public import Linglib.Fragments.Hebrew.Relativization
public import Linglib.Fragments.TobaBatak.Relativization
public import Linglib.Fragments.Korean.Relativization
public import Linglib.Fragments.Finnish.Relativization
public import Linglib.Fragments.Malagasy.Relativization
public import Linglib.Fragments.Mandarin.Relativization
public import Linglib.Fragments.Basque.Relativization
public import Linglib.Fragments.German.Relativization
public import Linglib.Fragments.HindiUrdu.Relativization
public import Linglib.Fragments.Japanese.Relativization
public import Linglib.Fragments.Romance.French.Relativization
public import Linglib.Fragments.Slavic.Russian.Relativization
public import Linglib.Fragments.Tagalog.Relativization
public import Linglib.Fragments.Turkish.Relativization

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

The paper's strategies are derived, not recorded. Two relative clauses are formed by different
strategies when their heads are placed differently or when one is case-coding, presenting an
element that expresses which position is relativized, and the other not (p. 65); a retained
personal pronoun codes case as a relative pronoun does (p. 66). So a strategy is a placement and
a case-coding value (`Strategy`), and the positions it covers in a language are those some
relativizer of the language realizes with an element of that value (`Strategy.positions`).
Table 1's rows follow from the fragments' relativizers: Hebrew's direct object is covered by
both of its strategies (`hebrew_table1`), and Arabic's row is the gap at the subject and
pronoun retention below it (`arabic_table1`).

The constraints are then checked on the seventeen languages of Table 1 whose relativizers the
fragments record (`hc1_verified`, `hc2_verified`), so every primary strategy of the sample covers
the interval from its cut-off up to the subject (`primary_positions_eq_Icc_top`); each position
from subject to genitive is attested as the cut-off of a primary strategy, the paper's Section
1.3 argument for the third constraint (`each_upper_cutoff_attested`); and Toba Batak's gap at
direct object between two continuous strategies shows why the constraints are stated per
strategy rather than per language (`toba_batak_do_gap`). The pattern of pronoun retention
(Section 2.2.2, Table 2) is derived the same way: once a language retains a pronoun at a
position it retains one at every lower position it relativizes (`retention_verified`).

## Implementation notes

The hierarchy order is the substrate's `Position` bounded linear order, the subject its top, and
a strategy's continuity is order-connectedness of the positions it covers. A relative pronoun
agreeing with the head, such as English *who* (p. 65), leaves the relativized position a gap
(`Relativization.NPRel`), so case coding is a property of what occupies that position
(`IsCaseCoding`). Table 1 records Classical Arabic and the fragment Modern Standard Arabic, whose
relativizer covers the row's positions; since the paper considers only definite relative
clauses (p. 64), the sample takes the relativizer of a definite antecedent. The languages the
fragments add after 1977 are not consulted.

## References

* [keenan-comrie-1977]
-/

@[expose] public section

namespace KeenanComrie1977

open Relativization Finset

/-! ### Strategies (Section 1.1) -/

/-- Case coding (p. 65): the element at the relativized position expresses which position it is,
as a relative pronoun marked for it or a retained personal pronoun does (p. 66); a gap
expresses none. -/
def IsCaseCoding (x : NPRel) : Prop := x ≠ .gap

instance : DecidablePred IsCaseCoding := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- An RC-forming strategy (p. 65): relative clauses are formed by different strategies when
their heads are placed differently or one is case-coding and the other not. -/
structure Strategy where
  /-- The placement of the clause relative to its head. -/
  placement : Placement
  /-- Whether the strategy is case-coding, the paper's ±case. -/
  caseCoding : Bool
  deriving DecidableEq, Fintype

namespace Strategy

variable (s : Strategy) (L : List Relativizer)

/-- The positions a language relativizes by a strategy: those some relativizer with its
placement realizes with an element of its case coding. -/
def positions : Finset Position :=
  univ.filter fun p ↦ ∃ r ∈ L, r.placement = s.placement ∧
    ∃ x ∈ r.realize p, decide (IsCaseCoding x) = s.caseCoding

/-- A strategy is primary when it relativizes subjects. -/
def IsPrimary : Prop := ⊤ ∈ s.positions L

instance : Decidable (s.IsPrimary L) := inferInstanceAs (Decidable (_ ∈ _))

end Strategy

/-! ### The Hierarchy Constraints (Section 1.2) -/

/-- HC₁: some strategy relativizes subjects. -/
def SatisfiesHC1 (L : List Relativizer) : Prop := ∃ s : Strategy, s.IsPrimary L

instance (L : List Relativizer) : Decidable (SatisfiesHC1 L) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- HC₂: every strategy covers a continuous segment of the hierarchy. -/
def SatisfiesHC2 (L : List Relativizer) : Prop :=
  ∀ s : Strategy, (s.positions L : Set Position).OrdConnected

instance (L : List Relativizer) : Decidable (SatisfiesHC2 L) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- The Primary Relativization Constraint: a primary strategy covers an upper set of the
hierarchy, every position above one it reaches. -/
def SatisfiesPRC (L : List Relativizer) : Prop :=
  ∀ s : Strategy, s.IsPrimary L → IsUpperSet (s.positions L : Set Position)

/-- The Primary Relativization Constraint follows from HC₂ and the definition of primary, as
the paper derives it: a continuous strategy that relativizes subjects covers an upper set. -/
theorem prc_of_hc2 {L : List Relativizer} (h : SatisfiesHC2 L) : SatisfiesPRC L :=
  fun s hp ↦ Set.OrdConnected.isUpperSet_of_top_mem (h s) hp

/-! ### The sample (Table 1)

The seventeen languages of Table 1 whose relativizers the fragments record. -/

abbrev english := English.Relativization.relativizers
abbrev welsh := Welsh.relativizers
/-- Table 1's Classical Arabic, by the Modern Standard Arabic relativizer of a definite
antecedent, the paper considering only definite restrictive relative clauses (p. 64). -/
abbrev arabic : List Relativizer := [Arabic.ModernStandard.relativizer .definite]
abbrev hebrew := Hebrew.relativizers
abbrev tobaBatak := TobaBatak.relativizers
abbrev korean := Korean.relativizers
abbrev finnish := Finnish.relativizers
abbrev malagasy := Malagasy.relativizers
/-- Table 1's Chinese, spoken Pekingese. -/
abbrev mandarin := Mandarin.relativizers
abbrev basque := Basque.relativizers
abbrev french := French.relativizers
abbrev german := German.relativizers
/-- Table 1's Hindi. -/
abbrev hindi := HindiUrdu.relativizers
abbrev japanese := Japanese.relativizers
abbrev russian := Russian.relativizers
abbrev tagalog := Tagalog.relativizers
abbrev turkish := Turkish.relativizers

/-- The sample. -/
def sample : List (List Relativizer) :=
  [english, welsh, arabic, hebrew, tobaBatak, korean, finnish, malagasy, mandarin, basque,
    french, german, hindi, japanese, russian, tagalog, turkish]

/-- Table 1's Hebrew (p. 77): the −case strategy covers subjects and direct objects and the
+case strategy everything from direct objects down, the direct object shared between them. -/
theorem hebrew_table1 :
    (⟨.postNominal, false⟩ : Strategy).positions hebrew = {.subject, .directObject} ∧
      (⟨.postNominal, true⟩ : Strategy).positions hebrew = Iic .directObject := by
  decide

/-- Table 1's Arabic (p. 76): the −case strategy covers the subject alone and the +case strategy
every other position. -/
theorem arabic_table1 :
    (⟨.postNominal, false⟩ : Strategy).positions arabic = {⊤} ∧
      (⟨.postNominal, true⟩ : Strategy).positions arabic = {⊤}ᶜ := by
  decide

/-- HC₁ holds of every language in the sample. -/
theorem hc1_verified : ∀ L ∈ sample, SatisfiesHC1 L := by decide

/-- HC₂ holds of every strategy in the sample. -/
theorem hc2_verified : ∀ L ∈ sample, SatisfiesHC2 L := by decide

/-- Hence so does the Primary Relativization Constraint. -/
theorem prc_verified : ∀ L ∈ sample, SatisfiesPRC L :=
  fun _ h ↦ prc_of_hc2 (hc2_verified _ h)

/-- In the sample every primary strategy covers exactly the closed interval from its cut-off up
to the subject, by HC₂ and `Finset.eq_Icc_top_of_ordConnected_coe`: what Table 1 records as a
run of `+` entries ending at the subject. -/
theorem primary_positions_eq_Icc_top :
    ∀ L ∈ sample, ∀ s : Strategy, (hp : s.IsPrimary L) →
      s.positions L = Icc ((s.positions L).min' ⟨⊤, hp⟩) ⊤ :=
  fun _ h s hp ↦ eq_Icc_top_of_ordConnected_coe (hc2_verified _ h s) hp

/-- Every position from subject to genitive is the cut-off of some primary strategy in the
sample, which covers exactly the interval from there up to the subject: the Section 1.3 argument
that each point of the hierarchy is a possible cut-off. The paper's witnesses for the object of
comparison are not among the fragments. -/
theorem each_upper_cutoff_attested :
    ∀ p ∈ [Position.subject, .directObject, .indirectObject, .oblique, .genitive],
      ∃ L ∈ sample, ∃ s : Strategy, s.positions L = Icc p ⊤ := by
  decide

/-! ### Toba Batak (Section 1.2.2) -/

/-- Toba Batak relativizes subjects by one strategy and indirect objects through genitives by
another, but direct objects by neither: the gap lies between two continuous strategies, which
is why the constraints govern strategies rather than languages. -/
theorem toba_batak_do_gap : ∀ r ∈ tobaBatak, r.realize .directObject = ∅ := by decide

/-! ### Strategies by their relativized position (Section 1.3) -/

/-- Korean (Section 1.3.4, Table 1 p. 78): the −case strategy stops at obliques and a genitive
requires a retained pronoun. -/
theorem korean_genitive_retention :
    (⟨.preNominal, false⟩ : Strategy).positions korean = Icc .oblique ⊤ ∧
      ∀ r ∈ korean, r.realize .genitive = {.resumptive} := by
  decide

/-- Finnish (Section 1.3.2): the case-coding strategy of *joka* is the broader one, the
participle covering subject and direct object only, both primary. -/
theorem finnish_plus_case_is_primary :
    (⟨.preNominal, false⟩ : Strategy).positions finnish ⊂
        (⟨.postNominal, true⟩ : Strategy).positions finnish ∧
      (⟨.preNominal, false⟩ : Strategy).IsPrimary finnish ∧
      (⟨.postNominal, true⟩ : Strategy).IsPrimary finnish := by
  decide

/-! ### Pronoun retention (Section 2.2.2) -/

/-- A personal pronoun at the relativized position; pronouns of verb agreement are excluded
(p. 92). -/
def IsPronoun (x : NPRel) : Prop :=
  x = .resumptive ∨ x = .resumptiveMovement ∨ x = .resumptiveBound

instance : DecidablePred IsPronoun := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The positions a language relativizes. -/
def relativizable (L : List Relativizer) : Finset Position :=
  univ.filter fun p ↦ ∃ r ∈ L, (r.realize p).Nonempty

/-- The positions at which a language retains a pronoun, its row of Table 2 (p. 93). -/
def retention (L : List Relativizer) : Finset Position :=
  univ.filter fun p ↦ ∃ r ∈ L, ∃ x ∈ r.realize p, IsPronoun x

/-- "Once a language begins to retain pronouns it must do so for as long as relativization is
possible at all" (p. 92). -/
def RetainsDownward (L : List Relativizer) : Prop :=
  ∀ p ∈ retention L, ∀ q ∈ relativizable L, q ≤ p → q ∈ retention L

instance (L : List Relativizer) : Decidable (RetainsDownward L) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Table 2's Arabic (p. 93): pronouns are retained everywhere but the subject. -/
theorem arabic_table2 : retention arabic = {⊤}ᶜ := by decide

/-- Every language of the sample retains pronouns downward. -/
theorem retention_verified : ∀ L ∈ sample, RetainsDownward L := by decide

end KeenanComrie1977
