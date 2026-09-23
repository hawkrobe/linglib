module

public import Linglib.Data.Examples.Cysouw2003
public import Linglib.Core.Order.UpperLower.Finset
public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Person.Clusivity
public import Linglib.Fragments.English.Pronouns
public import Linglib.Fragments.Tagalog.Pronouns
public import Linglib.Morphology.Paradigm.Morphome

/-!
# Cysouw (2003): The paradigmatic structure of person marking

This file formalizes the paradigmatic structures of [cysouw-2003]. A person paradigm fills
one slot with a closed set of markers over eight referential categories, the three singular
participants and the five attested groups, and its structure is which categories share a
morpheme: a setoid on `Person.Category`, the syncretism of the paradigm's cell-to-form map.
The book's kinds of homophony, its types of the first person complex and its named structures
are properties of that setoid.

Two of the book's generalizations are implicational hierarchies, and each is a lower set of a
chain: horizontal homophony reaches the singular persons from the third upwards, and a paradigm
gives up its oppositions from the first person complex outwards. Every paradigm the book prints
is checked against its classification and against the hierarchies, with the exceptions the
book names.

## Implementation notes

* Cells the book draws as one block carry the same form string, so the syncretism of the
  forms is the book's block notation; fillers such as "(demonstratives)" are kept as printed.
* The named structures are kernels of the book's letter labellings, of which only the kernel
  matters.
* The book's Table 10.3 prints the descriptions of unified-we and only-inclusive swapped;
  Table 3.2 is followed.

## TODO

* Chapter 7's dual paradigms, the Dual Explicitness Hierarchy and the Dual Homophony
  Implication need cells for restricted groups.
* The zero implications of chapter 10 need zero marking read off the forms.

## References

* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
-/

@[expose] public section

namespace Cysouw2003

open Person Morphology

/-- A paradigmatic structure: which of the eight referential categories share a morpheme. -/
abbrev Structure := Setoid Category

/-- The singular categories, ordered by person prominence, the order in which horizontal
homophony reaches them: the third person first, the first person last. -/
abbrev Singular := {c : Category // c.IsSingular}

instance : LinearOrder Singular := LinearOrder.lift' (fun a ↦ a.1.person.prominence) (by decide)

/-- The marking of 'we', the columns of the book's Table 4.2: minimal against augmented
inclusive, inclusive against exclusive, or one form. -/
inductive WeMarking where
  | minimalAugmented | inclusiveExclusive | unified
  deriving DecidableEq, Repr, Fintype

/-- The oppositions a paradigm gives up, in the order the Explicitness Hierarchy says it gives
them up: the two inside the first person complex, then one between groups, then one between
singulars. -/
inductive Opposition where
  | minimalAugmented | inclusiveExclusive | group | singular
  deriving DecidableEq, Repr, Fintype

namespace Opposition

/-- Position in the order of giving up. -/
def rank : Opposition → Fin 4
  | .minimalAugmented => 0
  | .inclusiveExclusive => 1
  | .group => 2
  | .singular => 3

instance : LinearOrder Opposition := LinearOrder.lift' rank (by decide)

end Opposition

namespace Structure

variable (s : Structure)

/-! ### Kinds of homophony -/

/-- Two singular categories share a morpheme. -/
def SingularHomophony : Prop := ∃ a b : Singular, a ≠ b ∧ s a b

/-- A singular category shares a morpheme with a group. -/
def HorizontalHomophony : Prop := ∃ (a : Singular) (b : Category), b.IsGroup ∧ s a b

/-- The singular `a` shares its morpheme with a group of its own person: the first person
with the exclusive or the inclusive, the second with 2+3, the third with 3+3. -/
def HorizontalHomophonyAt (a : Singular) : Prop :=
  ∃ b : Category, b.IsGroup ∧ b.person.coarsen = a.1.person ∧ s a b

/-- A singular category shares a morpheme with a group of another person. -/
def DiagonalHomophony : Prop :=
  ∃ (a : Singular) (b : Category), b.IsGroup ∧ b.person.coarsen ≠ a.1.person ∧ s a b

/-- Two groups share a morpheme, homophony inside the first person complex not counted. -/
def VerticalHomophony : Prop :=
  ∃ a b : Category, a.IsGroup ∧ b.IsGroup ∧ a ≠ b ∧
    ¬ (a.IsFirstPersonComplex ∧ b.IsFirstPersonComplex) ∧ s a b

variable {s} in
/-- Diagonal homophony is horizontal. -/
theorem DiagonalHomophony.horizontalHomophony (h : s.DiagonalHomophony) :
    s.HorizontalHomophony :=
  let ⟨a, b, hb, _, hab⟩ := h; ⟨a, b, hb, hab⟩

/-- A category is specialized when it shares no morpheme with a singular one. -/
def Specialized (c : Category) : Prop := ∀ x : Singular, ¬ s c x

variable [DecidableRel (⇑s)]

instance : Decidable s.SingularHomophony := by unfold SingularHomophony; infer_instance
instance : Decidable s.HorizontalHomophony := by unfold HorizontalHomophony; infer_instance
instance (a : Singular) : Decidable (s.HorizontalHomophonyAt a) := by
  unfold HorizontalHomophonyAt; infer_instance
instance : Decidable s.DiagonalHomophony := by unfold DiagonalHomophony; infer_instance
instance : Decidable s.VerticalHomophony := by unfold VerticalHomophony; infer_instance
instance (c : Category) : Decidable (s.Specialized c) := by unfold Specialized; infer_instance

/-! ### The first person complex -/

/-- The book's letter for a speaker cell: its morpheme class when it is specialized, the
dash, one for every singular morpheme, when it is not. -/
def letter (a : Clusivity.Cell) : Option (Quotient s) :=
  if s.Specialized a then some (Quotient.mk s a) else none

/-- The pattern of the first person complex, the kernel of the letters. -/
abbrev wePattern : Clusivity.Pattern := Setoid.ker s.letter

/-- The structure is of the common type `t`. -/
abbrev HasClusivity (t : Clusivity) : Prop := s.wePattern = t.toPattern

variable {s} in
theorem HasClusivity.unique {t t' : Clusivity} (h : s.HasClusivity t) (h' : s.HasClusivity t') :
    t = t' :=
  Clusivity.toPattern_injective (h.symm.trans h')

/-! ### The Horizontal Homophony Hierarchy -/

/-- The singular categories showing horizontal homophony. -/
def horizontalSingulars : Finset Singular := Finset.univ.filter s.HorizontalHomophonyAt

/-- Horizontal homophony in one person entails it in every less prominent person, so it
appears first in the third person, then the second, then the first; diagonal homophony is
among the exceptions. -/
def RespectsHorizontalHierarchy : Prop :=
  ¬ s.DiagonalHomophony ∧ IsLowerSet (↑s.horizontalSingulars : Set Singular)

instance : Decidable s.RespectsHorizontalHierarchy := by
  unfold RespectsHorizontalHierarchy; infer_instance

variable {s} in
/-- A structure respecting the hierarchy shows horizontal homophony exactly up to its rung. -/
theorem mem_horizontalSingulars_iff (h : s.RespectsHorizontalHierarchy) {a : Singular} :
    a ∈ s.horizontalSingulars ↔ ↑a ≤ s.horizontalSingulars.max :=
  h.2.mem_iff_le_max

/-- The number stages a paradigm without restricted groups can occupy: no singular/group
opposition at all (N1), a consistent one (N2), and neither on the intermediate rungs of the
horizontal hierarchy. -/
def numberStage : Option Number.Stage :=
  if ∀ a, s.HorizontalHomophonyAt a then some .N1
  else if ¬ s.HorizontalHomophony then some .N2 else none

/-! ### The Explicitness Hierarchy -/

/-- The marking of 'we' in a structure, by whether the cells differ, as chapter 4's division
into paradigms with and without an inclusive/exclusive opposition goes (the Ojibwe and Huave
prefixes, whose inclusive is a singular morpheme, are filed under the opposition), and as
any 1+2 against 1+2+3 difference counts as a minimal/augmented inclusive. -/
def weMarking : WeMarking :=
  if ¬ s .speakerAddressee .speakerAddresseeOthers then .minimalAugmented
  else if ¬ s .speakerAddressee .speakerOthers then .inclusiveExclusive else .unified

/-- The structure has given up the opposition: minimal against augmented inclusive unless
'we' is marked so, inclusive against exclusive when 'we' is one form, one between groups when
two groups share a morpheme, one between singulars when two singulars do. -/
def GivesUp : Opposition → Prop
  | .minimalAugmented => s.weMarking ≠ .minimalAugmented
  | .inclusiveExclusive => s.weMarking = .unified
  | .group => s.VerticalHomophony
  | .singular => s.SingularHomophony

instance : DecidablePred s.GivesUp := fun o ↦ by cases o <;> unfold GivesUp <;> infer_instance

/-- The oppositions the structure has given up. -/
def givenUp : Finset Opposition := Finset.univ.filter s.GivesUp

/-- The hierarchy as a constraint on which oppositions a paradigm may give up: those given up
form an initial segment of the order, so singulars merge only where groups already merge, and
groups only once 'we' is one form. -/
def RespectsExplicitnessHierarchy : Prop := IsLowerSet (↑s.givenUp : Set Opposition)

instance : Decidable s.RespectsExplicitnessHierarchy := inferInstanceAs (Decidable (IsLowerSet _))

/-- The rung of a structure on the hierarchy, the last opposition it has given up: the book's
stages of person differentiation P4 (none given up), P3, P2, P1 and P0 (a singular one). -/
def explicitness : WithBot Opposition := s.givenUp.max

variable {s} in
/-- A structure respecting the hierarchy has given up exactly the oppositions up to its rung. -/
theorem mem_givenUp_iff (h : s.RespectsExplicitnessHierarchy) {o : Opposition} :
    o ∈ s.givenUp ↔ ↑o ≤ s.explicitness :=
  h.mem_iff_le_max

end Structure

/-! ### The rare patterns of the first person complex -/

/-- The five rare attested patterns of the first person complex. -/
inductive RarePattern where
  /-- A morpheme for 1+2 and another for 1+2+3 and 1+3 together (Bardi, Kunimaipa, Tiwi). -/
  | pf
  /-- A morpheme for 1+2+3 and another for 1+2 and 1+3 together (Yaouré, Gooniyandi). -/
  | pg
  /-- Minimal and augmented inclusive marked apart, the exclusive by a singular morpheme
  (Tiwi). -/
  | ph
  /-- 1+2 marked by a singular morpheme, 1+2+3 and 1+3 together (Kunimaipa). -/
  | pi
  /-- The inclusive marked by a singular morpheme, the exclusive by its own (Binandere). -/
  | pj
  deriving DecidableEq, Repr, Fintype

namespace RarePattern

/-- The book's letters as morpheme classes, `0` the singular class. -/
def labels : RarePattern → Category → ℕ
  | .pf, .speakerAddressee => 1 | .pf, .speakerAddresseeOthers => 2 | .pf, .speakerOthers => 2
  | .pg, .speakerAddressee => 1 | .pg, .speakerAddresseeOthers => 2 | .pg, .speakerOthers => 1
  | .ph, .speakerAddressee => 1 | .ph, .speakerAddresseeOthers => 2
  | .pi, .speakerAddresseeOthers => 1 | .pi, .speakerOthers => 1
  | .pj, .speakerOthers => 1
  | _, _ => 0

/-- The rare pattern as a setoid on the four cells. -/
abbrev pattern (q : RarePattern) : Clusivity.Pattern := Setoid.ker (q.labels ∘ Subtype.val)

/-- The rare patterns are distinct from each other. -/
theorem pattern_injective : Function.Injective pattern := by
  show ∀ q q' : RarePattern, _ → _; decide +kernel

/-- The rare patterns are distinct from the common types, so ten of the fifteen patterns are
attested. -/
theorem pattern_ne (q : RarePattern) (t : Clusivity) : q.pattern ≠ t.toPattern := by
  revert q t; decide +kernel

end RarePattern

/-! ### The named structures of chapter 4 -/

/-- The structures chapter 4 names after an exemplar: eight common and five semi-common. -/
inductive Kind where
  | latin | sinhalese | berik | maricopa
  | maranao | mandara | tupiGuarani | kwakiutl | sierraPopoluca
  | slave | nezPerce | kombai | omie
  deriving DecidableEq, Repr, Fintype

namespace Kind

/-- Morpheme classes of each named structure; the wildcard covers the three 'we' cells. -/
def labels : Kind → Category → ℕ
  | .latin => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .addresseeOthers => 4 | .others => 5 | _ => 3
  | .sinhalese => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .addresseeOthers => 4 | .others => 2 | _ => 3
  | .berik => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .addresseeOthers => 1 | .others => 2 | _ => 3
  | .maricopa => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .addresseeOthers => 1 | .others => 2 | _ => 0
  | .maranao => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .speakerAddressee => 3 | .speakerAddresseeOthers => 4 | .speakerOthers => 5
    | .addresseeOthers => 6 | .others => 7
  | .mandara => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .speakerOthers => 4 | .addresseeOthers => 5 | .others => 6 | _ => 3
  | .tupiGuarani => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .speakerOthers => 4 | .addresseeOthers => 5 | .others => 2 | _ => 3
  | .kwakiutl => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .speakerOthers => 4 | .addresseeOthers => 1 | .others => 2 | _ => 3
  | .sierraPopoluca => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .speakerOthers => 0 | .addresseeOthers => 1 | .others => 2 | _ => 3
  | .slave => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .addresseeOthers => 3 | .others => 4 | _ => 3
  | .nezPerce => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .addresseeOthers => 4 | .others => 4 | _ => 3
  | .kombai => fun
    | .speaker => 0 | .addressee => 1 | .other => 1
    | .addresseeOthers => 3 | .others => 3 | _ => 2
  | .omie => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .addresseeOthers => 4 | .others => 3 | _ => 3

/-- The names the rows use. -/
def names : List (String × Kind) :=
  [("Latin", .latin), ("Sinhalese", .sinhalese), ("Berik", .berik), ("Maricopa", .maricopa),
   ("Maranao", .maranao), ("Mandara", .mandara), ("Tupí-Guaraní", .tupiGuarani),
   ("Kwakiutl", .kwakiutl), ("Sierra Popoluca", .sierraPopoluca), ("Slave", .slave),
   ("Nez Perce", .nezPerce), ("Kombai", .kombai), ("Omie", .omie)]

/-- The paradigmatic structure of the named kind. -/
abbrev pattern (k : Kind) : Structure := syncretism k.labels

/-- The type of each named structure's first person complex, as the book files them: the
Maricopa type has no 'we', the Sierra Popoluca type only an inclusive, the Maranao type a
minimal/augmented one, the other types with an inclusive/exclusive opposition are
inclusive/exclusive and the rest unified. -/
def clusivity : Kind → Clusivity
  | .maricopa => .noWe
  | .sierraPopoluca => .onlyInclusive
  | .maranao => .minimalAugmented
  | .mandara | .tupiGuarani | .kwakiutl => .inclusiveExclusive
  | .latin | .sinhalese | .berik | .slave | .nezPerce | .kombai | .omie => .unifiedWe

/-- The named structures are distinct. -/
theorem pattern_injective : Function.Injective pattern := by
  show ∀ k l : Kind, _ → _; decide +kernel

/-- Each named structure has the first person complex the book files it under. -/
theorem hasClusivity_pattern (k : Kind) : k.pattern.HasClusivity k.clusivity := by
  revert k; decide +kernel

/-- Every named structure respects the horizontal hierarchy. -/
theorem respectsHorizontalHierarchy_pattern (k : Kind) :
    k.pattern.RespectsHorizontalHierarchy := by
  revert k; decide +kernel

/-- Hierarchy I, with an inclusive/exclusive opposition: Mandara < Tupí-Guaraní < Kwakiutl <
Sierra Popoluca, the last rung the exclusive marked like the speaker. -/
theorem horizontalSingulars_inclusiveExclusive :
    mandara.pattern.horizontalSingulars ⊂ tupiGuarani.pattern.horizontalSingulars ∧
    tupiGuarani.pattern.horizontalSingulars ⊂ kwakiutl.pattern.horizontalSingulars ∧
    kwakiutl.pattern.horizontalSingulars ⊂ sierraPopoluca.pattern.horizontalSingulars := by
  decide +kernel

/-- Hierarchy II, without: Latin < Sinhalese < Berik < Maricopa. -/
theorem horizontalSingulars_unified :
    latin.pattern.horizontalSingulars ⊂ sinhalese.pattern.horizontalSingulars ∧
    sinhalese.pattern.horizontalSingulars ⊂ berik.pattern.horizontalSingulars ∧
    berik.pattern.horizontalSingulars ⊂ maricopa.pattern.horizontalSingulars := by
  decide +kernel

/-- Every named structure respects the explicitness hierarchy. -/
theorem respectsExplicitnessHierarchy_pattern (k : Kind) :
    k.pattern.RespectsExplicitnessHierarchy := by
  revert k; decide +kernel

/-- The columns of the book's cognitive map: vertical homophony (the Slave type) at P1,
unified-we and no-we at P2, inclusive/exclusive and only-inclusive at P3, minimal/augmented
at P4. -/
theorem explicitness_pattern :
    slave.pattern.explicitness = ↑Opposition.group ∧
    latin.pattern.explicitness = ↑Opposition.inclusiveExclusive ∧
    maricopa.pattern.explicitness = ↑Opposition.inclusiveExclusive ∧
    mandara.pattern.explicitness = ↑Opposition.minimalAugmented ∧
    sierraPopoluca.pattern.explicitness = ↑Opposition.minimalAugmented ∧
    maranao.pattern.explicitness = ⊥ := by
  decide +kernel

/-- The rows of the cognitive map: no-we and only-inclusive at N1, the Slave, Latin, Mandara
and Maranao types at N2, and the Sinhalese type between the two. -/
theorem numberStage_pattern :
    maricopa.pattern.numberStage = some .N1 ∧ sierraPopoluca.pattern.numberStage = some .N1 ∧
    (∀ k ∈ [slave, latin, mandara, maranao], k.pattern.numberStage = some .N2) ∧
    sinhalese.pattern.numberStage = none := by
  decide +kernel

end Kind

/-! ### The paradigms of chapters 3 and 4 -/

/-- Morphological status of a paradigm. -/
inductive Marking where
  | independent | inflectional
  deriving DecidableEq, Repr

/-- Chapter 4's frequency classes. -/
inductive Ubiquity where
  | common | semiCommon | rare
  deriving DecidableEq, Repr

/-- A paradigm the book prints, its eight forms and the book's classification of it. -/
structure Row where
  /-- The example id. -/
  id : String
  /-- The form of each cell, block by block. -/
  forms : Category → String
  /-- The chapter printing it. -/
  chapter : ℕ
  /-- Independent or inflectional, where the caption says. -/
  marking : Option Marking
  /-- The named type the book files it under. -/
  kind : Option Kind
  /-- Common, semi-common or rare. -/
  ubiquity : Ubiquity
  /-- The rare 'we' pattern it illustrates. -/
  rare : Option RarePattern

namespace Row

/-- The paradigmatic structure of the row. -/
abbrev syncretism (r : Row) : Structure := Morphology.syncretism r.forms

/-- The row's pattern of the first person complex. -/
abbrev wePattern (r : Row) : Clusivity.Pattern := r.syncretism.wePattern

/-- A feature that may be absent but, when present, must parse. -/
def optional? {α : Type*} (e : Data.Examples.LinguisticExample) (key : String)
    (table : List (String × α)) : Option (Option α) :=
  match e.feature? key with
  | none => some none
  | some s => (table.lookup s).map some

/-- The row of an example. -/
def ofExample? (e : Data.Examples.LinguisticExample) : Option Row := do
  let s1 ← e.feature? "1"
  let s2 ← e.feature? "2"
  let s3 ← e.feature? "3"
  let minIncl ← e.feature? "1+2"
  let augIncl ← e.feature? "1+2+3"
  let excl ← e.feature? "1+3"
  let secondGrp ← e.feature? "2+3"
  let thirdGrp ← e.feature? "3+3"
  let chapter ← e.nat? "chapter"
  let ubiquity ← e.parse? "ubiquity"
    [("common", .common), ("semi-common", .semiCommon), ("rare", .rare)]
  let marking ← optional? e "marking"
    [("independent", .independent), ("inflectional", .inflectional)]
  let kind ← optional? e "kind" Kind.names
  let rare ← optional? e "fpc" [("Pf", .pf), ("Pg", .pg), ("Ph", .ph), ("Pi", .pi), ("Pj", .pj)]
  pure { id := e.id, chapter, ubiquity, marking, kind, rare
         forms := fun
           | .speaker => s1 | .addressee => s2 | .other => s3
           | .speakerAddressee => minIncl | .speakerAddresseeOthers => augIncl
           | .speakerOthers => excl | .addresseeOthers => secondGrp | .others => thirdGrp }

theorem isSome_ofExample : ∀ e ∈ Examples.all, (ofExample? e).isSome := by decide

end Row

/-- The printed paradigms. -/
def rows : List Row := Examples.all.filterMap Row.ofExample?

/-- Every paradigm the book files under a named type has that type's structure. -/
theorem rows_kind : ∀ r ∈ rows, ∀ k, r.kind = some k → r.syncretism = k.pattern := by
  decide +kernel

/-- Every paradigm illustrating a rare pattern has it. -/
theorem rows_rare : ∀ r ∈ rows, ∀ q, r.rare = some q → r.wePattern = q.pattern := by
  decide +kernel

/-- Every chapter-4 paradigm has one of the five common types, chapter 4 having set the rare
patterns aside. -/
theorem rows_hasClusivity :
    ∀ r ∈ rows, r.chapter = 4 → ∃ t, r.syncretism.HasClusivity t := by
  decide +kernel

/-- Addressee inclusion implication I over the printed paradigms, Binandere the one
exception. -/
theorem rows_specializedInclusive_of_specializedExclusive :
    ∀ r ∈ rows, r.rare ≠ some .pj →
      r.wePattern.SpecializedExclusive → r.wePattern.SpecializedInclusive := by
  decide +kernel

theorem binandere :
    ∃ r ∈ rows, r.rare = some .pj ∧ r.wePattern.SpecializedExclusive ∧
      ¬ r.wePattern.SpecializedInclusive := by
  decide +kernel

/-- Addressee inclusion implication II over the printed paradigms. Its exceptions are the
rare patterns that mark the two inclusives apart: (Pf) and (Pg), which the book names, and
(Ph), whose paradigm the book's list overlooks. -/
theorem rows_specializedExclusive_of_splitInclusive :
    ∀ r ∈ rows, (r.rare = none ∨ r.rare = some .pi ∨ r.rare = some .pj) →
      r.wePattern.SplitInclusive → r.wePattern.SpecializedExclusive := by
  decide +kernel

theorem rows_splitInclusive_not_specializedExclusive :
    ∀ r ∈ rows, (r.rare = some .pf ∨ r.rare = some .pg ∨ r.rare = some .ph) →
      r.wePattern.SplitInclusive ∧ ¬ r.wePattern.SpecializedExclusive := by
  decide +kernel

/-- The strong universal 'we' fails: the English inflection has no 'we'. -/
theorem english_inflection_noWe :
    ∃ r ∈ rows, r.id = "cysouw2003_4.68" ∧ r.syncretism.HasClusivity .noWe := by
  decide +kernel

/-- The Homophony Implication over the printed paradigms: singular homophony only in
inflectional paradigms. The two independent-pronoun exceptions the book reports, Qawesqar and
Winnebago, are described in chapter 2 without a printed paradigm. -/
theorem rows_inflectional_of_singularHomophony :
    ∀ r ∈ rows, r.syncretism.SingularHomophony → r.marking = some .inflectional := by
  decide +kernel

/-- The Horizontal Homophony Hierarchy holds of every common and semi-common paradigm; its
exceptions, the diagonal cases among them, are rare. -/
theorem rows_rare_of_not_respectsHorizontalHierarchy :
    ∀ r ∈ rows, ¬ r.syncretism.RespectsHorizontalHierarchy → r.ubiquity = .rare := by
  decide +kernel

/-- Table 4.2's first "nonesuch": under a minimal/augmented inclusive no chapter-4 paradigm
breaks the horizontal hierarchy. -/
theorem rows_respectsHorizontalHierarchy_of_minimalAugmented :
    ∀ r ∈ rows, r.chapter = 4 → r.syncretism.weMarking = .minimalAugmented →
      r.syncretism.RespectsHorizontalHierarchy := by
  decide +kernel

/-- Table 4.2's second "nonesuch": no singular homophony under any inclusive/exclusive
opposition. -/
theorem rows_unified_of_singularHomophony :
    ∀ r ∈ rows, r.chapter = 4 → r.syncretism.SingularHomophony →
      r.syncretism.weMarking = .unified := by
  decide +kernel

/-- The Explicitness Hierarchy holds of every common and semi-common paradigm. -/
theorem rows_rare_of_not_respectsExplicitnessHierarchy :
    ∀ r ∈ rows, ¬ r.syncretism.RespectsExplicitnessHierarchy → r.ubiquity = .rare := by
  decide +kernel

/-- Singular homophony without vertical homophony is rare, the European paradigms. -/
theorem rows_rare_of_singularHomophony_without_vertical :
    ∀ r ∈ rows, r.syncretism.SingularHomophony → ¬ r.syncretism.VerticalHomophony →
      r.ubiquity = .rare := by
  decide +kernel

/-- Vertical homophony under an inclusive/exclusive opposition is rare. -/
theorem rows_rare_of_verticalHomophony_inclusiveExclusive :
    ∀ r ∈ rows, r.syncretism.VerticalHomophony → r.syncretism.weMarking ≠ .unified →
      r.ubiquity = .rare := by
  decide +kernel

/-- The book's exemplars of the five rungs: the Waskia present and the Una undergoer suffixes
have given up a singular and a group opposition, then the Latin, Mandara and Maranao
types. -/
theorem explicitness_rungs :
    ∃ waskia ∈ rows, ∃ una ∈ rows,
      waskia.id = "cysouw2003_4.66" ∧ una.id = "cysouw2003_4.64" ∧
      waskia.syncretism.explicitness = ↑Opposition.singular ∧
      una.syncretism.explicitness = ↑Opposition.group ∧
      Kind.latin.pattern.explicitness = ↑Opposition.inclusiveExclusive ∧
      Kind.mandara.pattern.explicitness = ↑Opposition.minimalAugmented ∧
      Kind.maranao.pattern.explicitness = ⊥ := by
  decide +kernel

/-! ### Two paradigms from the Fragments -/

/-- The English subject forms by referential category: the paradigm of the fragment's
non-accusative pronouns. -/
def englishSubject : Category → Finset String :=
  PersonalPronoun.paradigm (English.Pronouns.pronouns.filter (·.case_ ≠ some .acc))

/-- The English pronouns have the structure of the paradigm the book prints for them. -/
theorem english_pronouns :
    ∃ r ∈ rows, r.id = "cysouw2003_4.19" ∧ syncretism englishSubject = r.syncretism := by
  decide +kernel

/-- Horizontal homophony in the second person only: the English pronouns break the horizontal
hierarchy. -/
theorem english_not_respectsHorizontalHierarchy :
    ¬ Structure.RespectsHorizontalHierarchy (syncretism englishSubject) := by decide +kernel

/-- The Tagalog *ang* series is a Maranao-type paradigm. -/
theorem tagalog_maranao : syncretism Tagalog.ang = Kind.maranao.pattern := by decide +kernel

/-- The Tagalog *ang* series is of the minimal-augmented type. -/
theorem tagalog_minimalAugmented :
    Structure.HasClusivity (syncretism Tagalog.ang) .minimalAugmented := by
  decide +kernel

end Cysouw2003
