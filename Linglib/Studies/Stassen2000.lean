module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Order.Basic

/-!
# Stassen (2000): AND-languages and WITH-languages

This file formalizes [stassen-2000]'s typology of noun phrase conjunction, the encoding of a
single event predicated simultaneously of two participants conceived of as separate
individuals, over a sample of 260 languages. The domain is encoded by a coordinate strategy
or a comitative strategy, which contrast in four features: whether the two NPs have the same
structural rank, form a constituent, govern dual or plural agreement, and are linked by an
item distinct from the comitative marker (`Encoding`, `coordinate`, `comitative`). The
features order the encodings from the comitative to the coordinate focal position
(`comitative_le`, `le_coordinate`), with the in-between cases the paper allows for. Nearly
every language has the comitative strategy; a WITH-language has it as its only encoding and
an AND-language has a coordinate strategy as well (`Language.IsWith`, `Language.IsAnd`,
`isAnd_iff_not_isWith`).

AND-languages are diachronically stable and pure WITH-languages rare: WITH-languages drift
towards AND-status by grammaticalizing the comitative encoding, changing its features
towards the coordinate values while the linker stays lexically identical to the comitative
marker (`Grammaticalizes`). The result is a hybrid, which the paper rates as WITH because of
the shared linker (`Hybrid`, `isWith_of_hybrids`), and which becomes coordinate exactly when
the linker differentiates (`hybrid_withMarker`); the lexical identity of the markers is the
criterion the survey of [wals-2013] records. The starting point of the drift is the
language's pattern scheme with the comitative phrase in adverbial position (`scheme`): in a
verb-medial language the subject and the comitative phrase are separated by the verb, so the
constituent that grammaticalization creates presupposes a shift of the comitative phrase to
the subject's side (`svo_not_contiguous`, `shift_contiguous`), whereas verb-final and
verb-initial schemes are contiguous already (`sov_contiguous`, `vso_contiguous`) and can
mark the new constituent only by agreement, where the language has it, or by doubling the
comitative marker on both NPs (`doubled`).

## Implementation notes

The correlational tendencies, that cased and tensed languages tend to AND-status and
WITH-languages to be non-cased and non-tensed, with the AND-cased and WITH-non-cased
combinations the frequent ones, are stated by the paper qualitatively, without a
cross-tabulation, and the areal distribution is descriptive; neither is formalized. The
sample is summarized only as containing roughly twice as many AND-languages as
WITH-languages.

## References

* [stassen-2000]
* [wals-2013]
-/

@[expose] public section

namespace Stassen2000

/-! ### The two strategies -/

/-- The features contrasting the coordinate and comitative strategies, the paper's (83): the
two NPs have the same structural rank, form a constituent, govern dual or plural agreement,
and are linked by an item distinct from the comitative marker. -/
structure Encoding where
  equalRank : Bool
  constituent : Bool
  pluralAgreement : Bool
  distinctMarker : Bool
  deriving DecidableEq, Repr, Fintype

namespace Encoding

/-- The coordinate strategy, the focal position with every feature. -/
def coordinate : Encoding := ⟨true, true, true, true⟩

/-- The comitative strategy, the opposite focal position. -/
def comitative : Encoding := ⟨false, false, false, false⟩

/-- Encodings are ordered feature-wise, from the comitative to the coordinate strategy. -/
protected def LE (e f : Encoding) : Prop :=
  (e.equalRank = true → f.equalRank = true) ∧ (e.constituent = true → f.constituent = true) ∧
    (e.pluralAgreement = true → f.pluralAgreement = true) ∧
    (e.distinctMarker = true → f.distinctMarker = true)

instance : LE Encoding := ⟨Encoding.LE⟩

instance (e f : Encoding) : Decidable (e ≤ f) := by
  change Decidable (Encoding.LE e f); unfold Encoding.LE; infer_instance

instance : PartialOrder Encoding where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLT Encoding := decidableLTOfDecidableLE

theorem comitative_le : ∀ e : Encoding, comitative ≤ e := by decide

theorem le_coordinate : ∀ e : Encoding, e ≤ coordinate := by decide

/-- An encoding is coordinate when it has every feature. -/
def Coordinate (e : Encoding) : Prop := e = coordinate

instance : DecidablePred Coordinate := λ _ => inferInstanceAs (Decidable (_ = _))

/-- A hybrid encoding: above the comitative strategy in some feature, with the linker still
identical to the comitative marker. -/
def Hybrid (e : Encoding) : Prop := comitative < e ∧ e.distinctMarker = false

instance : DecidablePred Hybrid := λ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- A hybrid is not coordinate: its linker is shared with the comitative. -/
theorem not_coordinate_of_hybrid : ∀ e : Encoding, e.Hybrid → ¬ e.Coordinate := by decide

/-- The encoding with its marker feature set. -/
def withMarker (e : Encoding) (b : Bool) : Encoding := { e with distinctMarker := b }

/-- A hybrid becomes coordinate when its linker differentiates from the comitative marker
exactly when it has every other feature: the mixed WITH-languages the paper would call
AND-languages but for the lexical identity. -/
theorem hybrid_withMarker : ∀ e : Encoding, e.Hybrid →
    ((e.withMarker true).Coordinate ↔
      e.equalRank = true ∧ e.constituent = true ∧ e.pluralAgreement = true) := by
  decide

end Encoding

/-- Grammaticalization of the comitative encoding: a step towards the coordinate values in
which the linker stays identical to the comitative marker. -/
def Grammaticalizes (e f : Encoding) : Prop :=
  e ≤ f ∧ e.distinctMarker = false ∧ f.distinctMarker = false

instance (e f : Encoding) : Decidable (Grammaticalizes e f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A step from the comitative strategy that changes some feature yields a hybrid. -/
theorem hybrid_of_grammaticalizes : ∀ f : Encoding,
    Grammaticalizes Encoding.comitative f → f ≠ Encoding.comitative → f.Hybrid := by
  decide

/-! ### AND-languages and WITH-languages -/

/-- A language's strategies for noun phrase conjunction. -/
structure Language where
  encodings : List Encoding

/-- An AND-language has a coordinate strategy. -/
def Language.IsAnd (l : Language) : Prop := ∃ e ∈ l.encodings, e.Coordinate

/-- A WITH-language has only comitative and hybrid strategies. -/
def Language.IsWith (l : Language) : Prop := ∀ e ∈ l.encodings, ¬ e.Coordinate

instance (l : Language) : Decidable l.IsAnd := inferInstanceAs (Decidable (∃ e ∈ _, _))

instance (l : Language) : Decidable l.IsWith := inferInstanceAs (Decidable (∀ e ∈ _, _))

/-- The parameter is binary. -/
theorem isAnd_iff_not_isWith (l : Language) : l.IsAnd ↔ ¬ l.IsWith := by
  simp [Language.IsAnd, Language.IsWith]

/-- The paper's guideline for rating: a language whose every encoding shares the comitative
marker is a WITH-language, however far its hybrids have grammaticalized. -/
theorem isWith_of_hybrids (l : Language)
    (h : ∀ e ∈ l.encodings, e = Encoding.comitative ∨ e.Hybrid) : l.IsWith := by
  intro e he
  rcases h e he with rfl | hh
  · decide
  · exact Encoding.not_coordinate_of_hybrid e hh

/-! ### Pattern schemes -/

/-- The elements of a pattern scheme with an intransitive predicate: the subject, the verb,
and the comitative phrase; with the marker doubled, the subject also carries it. -/
inductive Slot
  | np1
  | verb
  | withNp2
  | withNp1
  deriving DecidableEq, Repr

/-- Basic word orders of the WITH-languages the paper schematizes. -/
inductive WordOrder
  | SVO
  | SOV
  | VSO
  deriving DecidableEq, Repr

/-- The pattern scheme, the paper's (107), (123) and (124): the comitative phrase sits in the
canonical position of adverbial phrases, on the side of the predicate where subjects are. -/
def scheme : WordOrder → List Slot
  | .SVO => [.np1, .verb, .withNp2]
  | .SOV => [.np1, .withNp2, .verb]
  | .VSO => [.verb, .np1, .withNp2]

/-- The two NPs of a scheme are contiguous. -/
def Contiguous (l : List Slot) : Prop :=
  (.np1, .withNp2) ∈ l.zip l.tail ∨ (.withNp2, .np1) ∈ l.zip l.tail

instance : DecidablePred Contiguous := λ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- In a verb-medial scheme the predicate separates the two NPs. -/
theorem svo_not_contiguous : ¬ Contiguous (scheme .SVO) := by decide

theorem sov_contiguous : Contiguous (scheme .SOV) := by decide

theorem vso_contiguous : Contiguous (scheme .VSO) := by decide

/-- The shift of the comitative phrase to preverbal position, the paper's (108): the
comitative phrase is fronted before the verb. -/
def shift (l : List Slot) : List Slot :=
  (l.filter (· ≠ .verb)) ++ l.filter (· = .verb)

/-- After the shift the verb-medial scheme is contiguous, so the string can be reanalyzed as a
constituent. -/
theorem shift_contiguous : Contiguous (shift (scheme .SVO)) := by decide

/-- The doubled scheme, the paper's (125): the comitative marker on both NPs signals their
equal rank in a verb-final language. -/
def doubled : List Slot := [.withNp1, .withNp2, .verb]

end Stassen2000
