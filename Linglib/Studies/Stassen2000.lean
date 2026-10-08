module

public import Linglib.Syntax.WordOrder
public import Mathlib.Data.Finset.Grade

/-!
# Stassen (2000): AND-languages and WITH-languages

This file formalizes [stassen-2000]'s typology of noun phrase conjunction, the encoding of a
single event predicated simultaneously of two participants conceived of as separate
individuals, over a sample of 260 languages. The domain is encoded by a coordinate strategy or
a comitative strategy, which contrast in four features: whether the two NPs have the same
structural rank, form a constituent, govern dual or plural agreement, and are linked by an
item distinct from the comitative marker (`Feature`). An encoding is the set of coordinate
features it has, so the encodings form the Boolean lattice `Finset Feature`: the comitative
strategy is `⊥`, the coordinate strategy `⊤`, and the in-between cases the paper allows for lie
between the two focal positions.

Nearly every language has the comitative strategy. An AND-language also has an encoding with
every coordinate feature relevant to it, and a WITH-language is one that is not an AND-language
(`Language.IsAnd`). Plural agreement is relevant only where verbs agree with their subject
(`Language.relevant`), since the paper's AND-languages include languages without verb agreement
and its pattern schemes distinguish languages with and without it; where verbs agree, an
AND-language is one with the coordinate strategy itself (`Language.isAnd_iff_top_mem`).

AND-languages are diachronically stable and pure WITH-languages rare: WITH-languages
grammaticalize the comitative strategy, moving up the lattice while the linker stays lexically
identical to the comitative marker. The resulting hybrids leave the language a WITH-language
however far they go (`Language.not_isAnd_of_forall_notMem`). The most advanced hybrid has every
relevant feature but the linker and is covered by the coordinate strategy
(`Language.erase_distinctMarker_covBy`); it is the one hybrid that differentiating the linker
turns into a coordinate strategy (`Language.relevant_le_insert_iff`), the mixed WITH-language the
paper would call an AND-language but for the lexical identity of the markers.

The starting point of the drift is the language's pattern scheme, its basic word order with the
comitative phrase in adverbial position (`scheme`). The subject and the comitative phrase are
contiguous exactly when the verb is not medial (`adjacent_scheme_iff`). The constituent that
grammaticalization creates therefore presupposes, in an SVO language, a shift of the comitative
phrase across the verb (`shift`, `adjacent_shift`), which yields the SOV scheme
(`shift_scheme_svo`), whereas verb-final and verb-initial schemes are contiguous already.

## Implementation notes

The paper's schemes (107), (123) and (124) put the comitative phrase where the object stands in
SVO, SOV and VSO order, so `scheme` places it there for every basic order and contiguity is
derived from the order. As in the paper, schemes have intransitive predicates.

The correlational tendencies, that cased and tensed languages tend to AND-status and
WITH-languages to be non-cased and non-tensed, with the AND-cased and WITH-non-cased
combinations the frequent ones, are stated by the paper qualitatively, without a
cross-tabulation, and the areal distribution is descriptive; neither is formalized. The sample
is summarized only as containing roughly twice as many AND-languages as WITH-languages.

## TODO

The paper argues that verb-final and verb-initial WITH-languages without agreement, (123a) and
(124a), can mark the new constituent neither by position nor by agreement, so that they tend to
stay pure WITH-languages, and that some verb-final ones double the comitative marker instead,
(125). Stating this needs the formal means by which each feature is marked.

## References

* [stassen-2000]
-/

@[expose] public section

namespace Stassen2000

open WordOrder

/-! ### Encodings -/

/-- The features of the coordinate strategy, the paper's (83), each opposed to a feature of the
comitative strategy: the two NPs have the same structural rank, form a constituent, govern dual
or plural agreement, and are linked by an item distinct from the comitative marker. An encoding
is the `Finset` of the features it has. -/
inductive Feature
  | equalRank
  | constituent
  | pluralAgreement
  | distinctMarker
  deriving DecidableEq, Repr, Fintype

/-! ### AND-languages and WITH-languages -/

/-- A language: whether its verbs agree with their subject, and its encodings of the domain. -/
structure Language where
  /-- The verbs agree with their subject in person, number and gender. -/
  Agrees : Prop
  [decidableAgrees : Decidable Agrees]
  /-- The encodings of noun phrase conjunction. -/
  encodings : Finset (Finset Feature)

attribute [instance] Language.decidableAgrees

namespace Language

variable (l : Language)

/-- The coordinate features relevant to the language: plural agreement only where its verbs
agree. -/
def relevant : Finset Feature := if l.Agrees then ⊤ else {.pluralAgreement}ᶜ

/-- An AND-language has an encoding with every relevant coordinate feature. -/
def IsAnd : Prop := ∃ e ∈ l.encodings, l.relevant ≤ e

instance : Decidable l.IsAnd := inferInstanceAs (Decidable (∃ e ∈ _, _))

variable {l}

theorem relevant_of_agrees (h : l.Agrees) : l.relevant = ⊤ := by simp [relevant, h]

/-- Where verbs agree, an AND-language is one with the coordinate strategy itself. -/
theorem isAnd_iff_top_mem (h : l.Agrees) : l.IsAnd ↔ ⊤ ∈ l.encodings := by
  simp [IsAnd, relevant_of_agrees h]

theorem distinctMarker_mem_relevant : .distinctMarker ∈ l.relevant := by
  unfold relevant; split_ifs <;> simp

/-- The paper's guideline for rating: a language whose every encoding links with the comitative
marker is a WITH-language, however far its hybrids have grammaticalized. -/
theorem not_isAnd_of_forall_notMem (h : ∀ e ∈ l.encodings, .distinctMarker ∉ e) : ¬ l.IsAnd :=
  fun ⟨e, he, hle⟩ ↦ h e he (hle distinctMarker_mem_relevant)

variable (l) in
/-- The most advanced hybrid, with every relevant feature but the linker, is one feature short of
the coordinate strategy. -/
theorem erase_distinctMarker_covBy : l.relevant.erase .distinctMarker ⋖ l.relevant :=
  Finset.erase_covBy distinctMarker_mem_relevant

/-- Differentiating the linker of a hybrid yields every relevant feature exactly when the hybrid
is the most advanced one. -/
theorem relevant_le_insert_iff {e : Finset Feature} (he : e ≤ l.relevant)
    (hm : .distinctMarker ∉ e) :
    l.relevant ≤ insert .distinctMarker e ↔ e = l.relevant.erase .distinctMarker := by
  rw [Finset.subset_insert_iff]
  exact ⟨fun h ↦ (Finset.subset_erase.2 ⟨he, hm⟩).antisymm h, fun h ↦ h.ge⟩

/-- Without verb agreement, an encoding lacking only plural agreement makes an AND-language, as
the paper's AND-languages without agreement are; where verbs agree, the same encodings make a
WITH-language. -/
example : ({ Agrees := False, encodings := {⊥, {.pluralAgreement}ᶜ} } : Language).IsAnd ∧
    ¬ ({ Agrees := True, encodings := {⊥, {.pluralAgreement}ᶜ} } : Language).IsAnd := by
  decide

end Language

/-! ### Pattern schemes -/

/-- `x` and `y` are adjacent in the arrangement `a`. -/
def Adjacent {α : Type*} {n : ℕ} (a : Arrangement α n) (x y : α) : Prop :=
  (a x : ℕ) + 1 = a y ∨ (a y : ℕ) + 1 = a x

instance {α : Type*} {n : ℕ} (a : Arrangement α n) (x y : α) : Decidable (Adjacent a x y) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Of three elements arranged over three ranks, two are adjacent exactly when the third is not
medial. -/
theorem adjacent_iff {α : Type*} {a : Arrangement α 3} {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : Adjacent a x y ↔ a z ≠ 1 := by
  have := a.injective.ne hxy; have := a.injective.ne hxz; have := a.injective.ne hyz
  have := (a x).isLt; have := (a y).isLt; have := (a z).isLt
  simp only [Adjacent, ne_eq, Fin.ext_iff, Fin.val_one] at *
  omega

/-- The elements of a pattern scheme with an intransitive predicate: the subject, the verb, and
the comitative phrase. -/
inductive Slot
  | subject
  | verb
  | comitative
  deriving DecidableEq, Repr, Fintype

/-- The slots of a scheme as the constituents of a clause, the comitative phrase in the object's
position. -/
def Slot.equivConstituent : Slot ≃ Constituent where
  toFun | .subject => .subject | .verb => .verb | .comitative => .object
  invFun | .subject => .subject | .verb => .verb | .object => .comitative
  left_inv := by decide
  right_inv := by decide

/-- The pattern scheme of a basic word order, the paper's (107), (123) and (124): the comitative
phrase stands in the canonical position of adverbial phrases, which in these schemes is the
object's. -/
def scheme (a : Arrangement Constituent 3) : Arrangement Slot 3 := Slot.equivConstituent.trans a

/-- The subject and the comitative phrase of a scheme are contiguous exactly when the verb is not
medial. -/
theorem adjacent_scheme_iff (a : Arrangement Constituent 3) :
    Adjacent (scheme a) .subject .comitative ↔ a .verb ≠ 1 :=
  adjacent_iff (z := Slot.verb) (by decide) (by decide) (by decide)

/-- In an SVO language the verb separates the two NPs, (107). -/
theorem not_adjacent_scheme_svo : ¬ Adjacent (scheme .svo) .subject .comitative := by decide

/-- SOV and VSO schemes are contiguous already, (123) and (124). -/
theorem adjacent_scheme_sov : Adjacent (scheme .sov) .subject .comitative := by decide

theorem adjacent_scheme_vso : Adjacent (scheme .vso) .subject .comitative := by decide

/-- The shift of the comitative phrase, the paper's (108): the transposition of the verb and the
comitative phrase, which moves the comitative phrase across a medial verb. -/
def shift (s : Arrangement Slot 3) : Arrangement Slot 3 := (Equiv.swap .verb .comitative).trans s

/-- Where the verb is medial, the shift makes the subject and the comitative phrase contiguous,
so that the string can be reanalyzed as a constituent. -/
theorem adjacent_shift {s : Arrangement Slot 3} (h : s .verb = 1) :
    Adjacent (shift s) .subject .comitative :=
  (adjacent_iff (z := Slot.verb) (by decide) (by decide) (by decide)).2 <| by
    simpa [shift, h] using s.injective.ne (show Slot.comitative ≠ .verb by decide)

/-- The shifted SVO scheme is the SOV scheme: (108) has the order of (123). -/
theorem shift_scheme_svo : shift (scheme .svo) = scheme .sov := Equiv.ext (by decide)

end Stassen2000
