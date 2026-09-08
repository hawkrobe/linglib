import Linglib.Data.Examples.Cysouw2003
import Linglib.Features.Number.Basic
import Linglib.Features.Person.Clusivity
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.Tagalog.Pronouns
import Linglib.Morphology.Paradigm.Morphome

/-!
# Cysouw, *The Paradigmatic Structure of Person Marking* (2003)

A person paradigm is a closed set of markers filling one syntagmatic slot, and its
paradigmatic structure is which of its cells share a morpheme. Cysouw replaces the person ×
number grid by eight referential categories, the three singular participants and the five
attested groups 1+2, 1+2+3, 1+3, 2+3 and 3+3, and reads a paradigm's structure off three
kinds of homophony among them: singular, horizontal (a singular with a group) and vertical
(two groups). The three 'we' categories admit fifteen patterns of specialized marking, of
which ten are attested, five common and five rare; the common five obey the addressee
inclusion implications (3.23) and (3.24), which, read as conditions, nest along the four
questions of his Fig. 3.10 into the First Person Hierarchy (3.26). Chapter 4 surveys the
structures of the whole grid, names the common and semi-common ones after exemplar
languages, and states two generalizations over them: horizontal homophony spreads along the
person hierarchy from the third person upwards, the Horizontal Homophony Hierarchies (4.106)
and (4.107), and a paradigm gives up its oppositions in a fixed order, the first person
complex first and singular person last, the Explicitness Hierarchy (4.108).

A paradigmatic structure is a setoid on the eight categories, the syncretism of a paradigm's
cell-to-form map. The kinds of homophony, the 'we' pattern and both hierarchies are
properties of that setoid, and every paradigm printed in chapters 3 and 4 is checked against
the book's own classification and generalizations, with the exceptions the book names:
Binandere against (3.23), the rare 'we' patterns against (3.24), the English pronouns and a
few others against the horizontal hierarchy, and the European singular homophonies and the
paradigms with vertical homophony under an inclusive/exclusive opposition against the
explicitness hierarchy.

## Implementation notes

* Cells the book draws as one block carry the same form string, so the syncretism of the
  forms is the book's block notation; fillers such as "(demonstratives)" are kept as printed.
* The named structures are kernels of labellings, the book's letter notation, of which only
  the kernel matters (his fn. 1, p. 40).
* Table 10.3 prints the descriptions of unified-we and only-inclusive swapped; Table 3.2 is
  followed.

## TODO

* Chapter 7's dual paradigms, the Dual Explicitness Hierarchy (10.8) and the Dual Homophony
  Implication (10.3) need cells for restricted groups.
* The zero implications (10.5) and (10.6) need zero marking read off the forms.

## References

* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
-/

namespace Cysouw2003

open Person Morphology

variable (s : Setoid Category)

/-! ### Kinds of homophony (§2.2, §4.2, §10.1.3) -/

/-- Two singular categories share a morpheme (Fig. 2.1). -/
def SingularHomophony : Prop :=
  ∃ a b : Category, a.IsSingular ∧ b.IsSingular ∧ a ≠ b ∧ s a b

/-- A singular category shares a morpheme with a group (Fig. 4.3). -/
def HorizontalHomophony : Prop := ∃ a b : Category, a.IsSingular ∧ b.IsGroup ∧ s a b

/-- The singular `a` shares its morpheme with a group of its own person: the first person
with the exclusive or the inclusive, the second with 2+3, the third with 3+3 (§10.1.4). -/
def HorizontalHomophonyAt (a : Category) : Prop :=
  ∃ b : Category, b.IsGroup ∧ b.person.coarsen = a.person ∧ s a b

/-- A singular category shares a morpheme with a group of another person (§4.3.6). -/
def DiagonalHomophony : Prop :=
  ∃ a b : Category, a.IsSingular ∧ b.IsGroup ∧ b.person.coarsen ≠ a.person ∧ s a b

/-- Two groups share a morpheme, homophony inside the first person complex not counted
(§10.1.6). -/
def VerticalHomophony : Prop :=
  ∃ a b : Category, a.IsGroup ∧ b.IsGroup ∧ a ≠ b ∧
    ¬ (a.IsFirstPersonComplex ∧ b.IsFirstPersonComplex) ∧ s a b

variable {s} in
/-- Diagonal homophony is horizontal. -/
theorem DiagonalHomophony.horizontalHomophony (h : DiagonalHomophony s) :
    HorizontalHomophony s :=
  let ⟨a, b, ha, hb, _, hab⟩ := h; ⟨a, b, ha, hb, hab⟩

/-! ### The first person complex (§3.5–3.7) -/

/-- A category is specialized when it shares no morpheme with a singular category
(Fig. 3.1's letters against its dashes). -/
def Specialized (c : Category) : Prop := ∀ x : Category, x.IsSingular → ¬ s c x

/-- Fig. 3.1's reading of two speaker cells as alike: both specialized and syncretic, or
neither specialized. -/
def WeRel (a b : Clusivity.Cell) : Prop :=
  (Specialized s a ∧ Specialized s b ∧ s a b) ∨ (¬ Specialized s a ∧ ¬ Specialized s b)

/-- Fig. 3.1's pattern of a structure, its speaker cells grouped by `WeRel`; the dash class is
the speaker's. -/
@[instance_reducible] def wePattern : Clusivity.Pattern where
  r := WeRel s
  iseqv :=
    { refl := λ a => by
        by_cases h : Specialized s a
        · exact .inl ⟨h, h, s.iseqv.refl a⟩
        · exact .inr ⟨h, h⟩
      symm := λ h => h.elim (λ ⟨ha, hb, hab⟩ => .inl ⟨hb, ha, s.iseqv.symm hab⟩)
        (λ ⟨ha, hb⟩ => .inr ⟨hb, ha⟩)
      trans := λ hab hbc => by
        rcases hab with ⟨ha, hb, hab⟩ | ⟨ha, hb⟩ <;>
          rcases hbc with ⟨hb', hc, hbc⟩ | ⟨hb', hc⟩
        · exact .inl ⟨ha, hc, s.iseqv.trans hab hbc⟩
        · exact absurd hb hb'
        · exact absurd hb' hb
        · exact .inr ⟨ha, hc⟩ }

/-- The structure is of the common type `t`. -/
abbrev HasClusivity (t : Clusivity) : Prop := wePattern s = t.toPattern

/-! ### The Horizontal Homophony Hierarchy (§4.7, §10.1.4) -/

/-- Horizontal homophony holds within a person and, in one person, entails it in every less
prominent person, so it appears first in the third person, then the second, then the first
((4.106), (4.107)); diagonal homophony is among the exceptions (§4.7). -/
def RespectsHorizontalHierarchy : Prop :=
  ¬ DiagonalHomophony s ∧
    ∀ a b : Category, a.IsSingular → b.IsSingular → HorizontalHomophonyAt s a →
      b.person.prominence ≤ a.person.prominence → HorizontalHomophonyAt s b

variable {s} in
theorem HasClusivity.unique {t t' : Clusivity} (h : HasClusivity s t) (h' : HasClusivity s t') :
    t = t' :=
  Clusivity.toPattern_injective (h.symm.trans h')

variable [DecidableRel (⇑s)]

instance : Decidable (SingularHomophony s) := by unfold SingularHomophony; infer_instance
instance : Decidable (HorizontalHomophony s) := by unfold HorizontalHomophony; infer_instance
instance (a : Category) : Decidable (HorizontalHomophonyAt s a) := by
  unfold HorizontalHomophonyAt; infer_instance
instance : Decidable (DiagonalHomophony s) := by unfold DiagonalHomophony; infer_instance
instance : Decidable (VerticalHomophony s) := by unfold VerticalHomophony; infer_instance
instance (c : Category) : Decidable (Specialized s c) := by unfold Specialized; infer_instance
instance : DecidableRel (WeRel s) := λ _ _ => by unfold WeRel; infer_instance
instance : DecidableRel (⇑(wePattern s)) := inferInstanceAs (DecidableRel (WeRel s))
instance : Decidable (RespectsHorizontalHierarchy s) := by
  unfold RespectsHorizontalHierarchy; infer_instance

/-- The singular categories showing horizontal homophony. -/
def horizontalSingulars : Finset Category :=
  Finset.univ.filter λ a => a.IsSingular ∧ HorizontalHomophonyAt s a

/-! ### The Explicitness Hierarchy (§4.7, §10.1.7) -/

/-- The marking of 'we', Table 4.2's columns: minimal against augmented inclusive, inclusive
against exclusive, or one form. -/
inductive WeMarking where
  | minimalAugmented | inclusiveExclusive | unified
  deriving DecidableEq, Repr, Fintype

/-- The marking of 'we' in a structure, by whether the cells differ, as chapter 4's division
into paradigms with and without an inclusive/exclusive opposition goes (§4.5–4.6 file the
Ojibwe and Huave prefixes, whose inclusive is a singular morpheme, under the opposition), and
as §4.7 counts any 1+2 against 1+2+3 difference as a minimal/augmented inclusive. -/
def weMarking : WeMarking :=
  if ¬ s .minIncl .augIncl then .minimalAugmented
  else if ¬ s .minIncl .excl then .inclusiveExclusive else .unified

/-- The hierarchy (4.108), (10.7) as a constraint on which oppositions a paradigm may give up:
singulars merge only where groups already merge, and groups merge only once 'we' is one
form. -/
def RespectsExplicitnessHierarchy : Prop :=
  (SingularHomophony s → VerticalHomophony s) ∧ (VerticalHomophony s → weMarking s = .unified)

instance : Decidable (RespectsExplicitnessHierarchy s) := by
  unfold RespectsExplicitnessHierarchy; infer_instance

/-- The rungs of the hierarchy, Fig. 10.9's stages of person differentiation P0–P4: singular
homophony, vertical homophony, and the three markings of 'we'. -/
inductive Explicitness where
  | singularHomophony | verticalHomophony | we (m : WeMarking)
  deriving DecidableEq, Repr, Fintype

namespace Explicitness

/-- Numeric embedding into ℕ preserving the order. -/
def toNat : Explicitness → ℕ
  | .singularHomophony => 0
  | .verticalHomophony => 1
  | .we .unified => 2
  | .we .inclusiveExclusive => 3
  | .we .minimalAugmented => 4

instance : LinearOrder Explicitness := LinearOrder.lift' toNat (by decide)

/-- The order of the rungs ((10.7), Fig. 10.4). -/
theorem hierarchy :
    singularHomophony < verticalHomophony ∧ verticalHomophony < we .unified ∧
      we .unified < we .inclusiveExclusive ∧ we .inclusiveExclusive < we .minimalAugmented := by
  decide

end Explicitness

/-- The rung of a structure on the hierarchy, the lowest opposition it has given up, for a
structure respecting the hierarchy; the others do not fit it (Table 10.4). -/
def explicitness : Option Explicitness :=
  if RespectsExplicitnessHierarchy s then
    some (if SingularHomophony s then .singularHomophony
      else if VerticalHomophony s then .verticalHomophony else .we (weMarking s))
  else none

/-- Fig. 10.8's number stages a paradigm without restricted groups can occupy (§10.2): no
singular/group opposition at all (N1), a consistent one (N2), and neither on the intermediate
rungs of the horizontal hierarchy. -/
def numberStage : Option Number.Stage :=
  if ∀ a : Category, a.IsSingular → HorizontalHomophonyAt s a then some .N1
  else if ¬ HorizontalHomophony s then some .N2 else none

/-- The five rare attested patterns of the first person complex (Fig. 3.7). -/
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

/-- Fig. 3.7's letters as morpheme classes, `0` the singular class. -/
def labels : RarePattern → Category → ℕ
  | .pf, .minIncl => 1 | .pf, .augIncl => 2 | .pf, .excl => 2
  | .pg, .minIncl => 1 | .pg, .augIncl => 2 | .pg, .excl => 1
  | .ph, .minIncl => 1 | .ph, .augIncl => 2
  | .pi, .augIncl => 1 | .pi, .excl => 1
  | .pj, .excl => 1
  | _, _ => 0

/-- The rare pattern as a setoid on the four cells. -/
abbrev pattern (q : RarePattern) : Clusivity.Pattern := Setoid.ker (q.labels ∘ Subtype.val)

/-- The rare patterns are distinct from each other. -/
theorem pattern_injective : Function.Injective pattern := by
  show ∀ q q' : RarePattern, _ → _; decide +kernel

/-- The rare patterns are distinct from the common types, so ten of the fifteen patterns are
attested (Figs. 3.1–3.2). -/
theorem pattern_ne (q : RarePattern) (t : Clusivity) : q.pattern ≠ t.toPattern := by
  revert q t; decide +kernel

end RarePattern

/-! ### The named structures of chapter 4 -/

/-- The structures chapter 4 names after an exemplar: eight common (§4.3.2–5, §4.5.2–4,
§4.5.6) and five semi-common (§4.4.2–4, §4.5.5). -/
inductive Kind where
  | latin | sinhalese | berik | maricopa
  | maranao | mandara | tupiGuarani | kwakiutl | sierraPopoluca
  | slave | nezPerce | kombai | omie
  deriving DecidableEq, Repr, Fintype

namespace Kind

/-- Morpheme classes of each named structure (Figs. 4.9–4.11); the wildcard covers the
three 'we' cells. -/
def labels : Kind → Category → ℕ
  | .latin => λ | .s1 => 0 | .s2 => 1 | .s3 => 2 | .secondGrp => 4 | .thirdGrp => 5 | _ => 3
  | .sinhalese => λ | .s1 => 0 | .s2 => 1 | .s3 => 2 | .secondGrp => 4 | .thirdGrp => 2 | _ => 3
  | .berik => λ | .s1 => 0 | .s2 => 1 | .s3 => 2 | .secondGrp => 1 | .thirdGrp => 2 | _ => 3
  | .maricopa => λ | .s1 => 0 | .s2 => 1 | .s3 => 2 | .secondGrp => 1 | .thirdGrp => 2 | _ => 0
  | .maranao => λ | .s1 => 0 | .s2 => 1 | .s3 => 2 | .minIncl => 3 | .augIncl => 4 | .excl => 5
                  | .secondGrp => 6 | .thirdGrp => 7
  | .mandara => λ | .s1 => 0 | .s2 => 1 | .s3 => 2 | .excl => 4 | .secondGrp => 5
                  | .thirdGrp => 6 | _ => 3
  | .tupiGuarani => λ | .s1 => 0 | .s2 => 1 | .s3 => 2 | .excl => 4 | .secondGrp => 5
                      | .thirdGrp => 2 | _ => 3
  | .kwakiutl => λ | .s1 => 0 | .s2 => 1 | .s3 => 2 | .excl => 4 | .secondGrp => 1
                   | .thirdGrp => 2 | _ => 3
  | .sierraPopoluca => λ | .s1 => 0 | .s2 => 1 | .s3 => 2 | .excl => 0 | .secondGrp => 1
                         | .thirdGrp => 2 | _ => 3
  | .slave => λ | .s1 => 0 | .s2 => 1 | .s3 => 2 | .secondGrp => 3 | .thirdGrp => 4 | _ => 3
  | .nezPerce => λ | .s1 => 0 | .s2 => 1 | .s3 => 2 | .secondGrp => 4 | .thirdGrp => 4 | _ => 3
  | .kombai => λ | .s1 => 0 | .s2 => 1 | .s3 => 1 | .secondGrp => 3 | .thirdGrp => 3 | _ => 2
  | .omie => λ | .s1 => 0 | .s2 => 1 | .s3 => 2 | .secondGrp => 4 | .thirdGrp => 3 | _ => 3

/-- The names the rows use. -/
def names : List (String × Kind) :=
  [("Latin", .latin), ("Sinhalese", .sinhalese), ("Berik", .berik), ("Maricopa", .maricopa),
   ("Maranao", .maranao), ("Mandara", .mandara), ("Tupí-Guaraní", .tupiGuarani),
   ("Kwakiutl", .kwakiutl), ("Sierra Popoluca", .sierraPopoluca), ("Slave", .slave),
   ("Nez Perce", .nezPerce), ("Kombai", .kombai), ("Omie", .omie)]

/-- The paradigmatic structure of the named kind (Figs. 4.9–4.11). -/
abbrev pattern (k : Kind) : Setoid Category := syncretism k.labels

/-- The named structures are distinct. -/
theorem pattern_injective : Function.Injective pattern := by
  show ∀ k l : Kind, _ → _; decide +kernel

/-- Their first person complexes (Fig. 4.4): the Maricopa type has no 'we', the Sierra
Popoluca type only an inclusive, the Maranao type a minimal/augmented one, the other types
with an inclusive/exclusive opposition are inclusive/exclusive and the rest unified. -/
theorem hasClusivity_pattern :
    HasClusivity maricopa.pattern .noWe ∧ HasClusivity sierraPopoluca.pattern .onlyInclusive ∧
    HasClusivity maranao.pattern .minimalAugmented ∧
    (∀ k ∈ [mandara, tupiGuarani, kwakiutl], HasClusivity k.pattern .inclusiveExclusive) ∧
    ∀ k ∈ [latin, sinhalese, berik, slave, nezPerce, kombai, omie],
      HasClusivity k.pattern .unifiedWe := by
  decide +kernel

/-- Every named structure respects the horizontal hierarchy. -/
theorem respectsHorizontalHierarchy_pattern (k : Kind) :
    RespectsHorizontalHierarchy k.pattern := by
  revert k; decide +kernel

/-- Hierarchy I, with an inclusive/exclusive opposition (Fig. 10.2): Mandara < Tupí-Guaraní <
Kwakiutl < Sierra Popoluca, the last rung the exclusive marked like the speaker. -/
theorem horizontalSingulars_inclusiveExclusive :
    horizontalSingulars mandara.pattern ⊂ horizontalSingulars tupiGuarani.pattern ∧
    horizontalSingulars tupiGuarani.pattern ⊂ horizontalSingulars kwakiutl.pattern ∧
    horizontalSingulars kwakiutl.pattern ⊂ horizontalSingulars sierraPopoluca.pattern := by
  decide +kernel

/-- Hierarchy II, without (Fig. 10.3): Latin < Sinhalese < Berik < Maricopa. -/
theorem horizontalSingulars_unified :
    horizontalSingulars latin.pattern ⊂ horizontalSingulars sinhalese.pattern ∧
    horizontalSingulars sinhalese.pattern ⊂ horizontalSingulars berik.pattern ∧
    horizontalSingulars berik.pattern ⊂ horizontalSingulars maricopa.pattern := by
  decide +kernel

/-- Every named structure respects the explicitness hierarchy. -/
theorem respectsExplicitnessHierarchy_pattern (k : Kind) :
    RespectsExplicitnessHierarchy k.pattern := by
  revert k; decide +kernel

/-- Fig. 10.7's columns: vertical homophony (the Slave type) at P1, unified-we and no-we at
P2, inclusive/exclusive and only-inclusive at P3, minimal/augmented at P4. -/
theorem explicitness_pattern :
    explicitness slave.pattern = some .verticalHomophony ∧
    explicitness latin.pattern = some (.we .unified) ∧
    explicitness maricopa.pattern = some (.we .unified) ∧
    explicitness mandara.pattern = some (.we .inclusiveExclusive) ∧
    explicitness sierraPopoluca.pattern = some (.we .inclusiveExclusive) ∧
    explicitness maranao.pattern = some (.we .minimalAugmented) := by
  decide +kernel

/-- Fig. 10.7's rows: no-we and only-inclusive at N1, the Slave, Latin, Mandara and Maranao
types at N2, and the Sinhalese type between the two. -/
theorem numberStage_pattern :
    numberStage maricopa.pattern = some .N1 ∧ numberStage sierraPopoluca.pattern = some .N1 ∧
    (∀ k ∈ [slave, latin, mandara, maranao], numberStage k.pattern = some .N2) ∧
    numberStage sinhalese.pattern = none := by
  decide +kernel

end Kind

/-! ### The paradigms of chapters 3 and 4 -/

/-- Morphological status of a paradigm (§1.2.4). -/
inductive Marking where
  | independent | inflectional
  deriving DecidableEq, Repr

/-- §4.2's frequency classes. -/
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
  /-- The rare 'we' pattern it illustrates (§3.6.6). -/
  rare : Option RarePattern

namespace Row

/-- The paradigmatic structure of the row. -/
abbrev syncretism (r : Row) : Setoid Category := Morphology.syncretism r.forms

/-- The row's pattern of the first person complex. -/
abbrev wePattern (r : Row) : Clusivity.Pattern := Cysouw2003.wePattern r.syncretism

/-- A feature that may be absent but, when present, must parse. -/
private def optional? {α : Type*} (e : Data.Examples.LinguisticExample) (key : String)
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
         forms := λ | .s1 => s1 | .s2 => s2 | .s3 => s3 | .minIncl => minIncl
                    | .augIncl => augIncl | .excl => excl | .secondGrp => secondGrp
                    | .thirdGrp => thirdGrp }

theorem isSome_ofExample : ∀ e ∈ Examples.all, (ofExample? e).isSome := by decide

end Row

/-- The printed paradigms. -/
def rows : List Row := Examples.all.filterMap Row.ofExample?

/-- Every paradigm the book files under a named type has that type's structure. -/
theorem rows_kind : ∀ r ∈ rows, ∀ k, r.kind = some k → r.syncretism = k.pattern := by
  decide +kernel

/-- Every paradigm of §3.6.6 has the rare pattern it illustrates. -/
theorem rows_rare : ∀ r ∈ rows, ∀ q, r.rare = some q → r.wePattern = q.pattern := by
  decide +kernel

/-- Every chapter-4 paradigm has one of the five common types, §4.2 having set the rare
patterns aside. -/
theorem rows_hasClusivity :
    ∀ r ∈ rows, r.chapter = 4 → ∃ t, HasClusivity r.syncretism t := by
  decide +kernel

/-- Addressee inclusion implication I (3.23) over the printed paradigms, Binandere the one
exception. -/
theorem rows_specializedInclusive_of_specializedExclusive :
    ∀ r ∈ rows, r.rare ≠ some .pj →
      r.wePattern.SpecializedExclusive → r.wePattern.SpecializedInclusive := by
  decide +kernel

theorem binandere :
    ∃ r ∈ rows, r.rare = some .pj ∧ r.wePattern.SpecializedExclusive ∧
      ¬ r.wePattern.SpecializedInclusive := by
  decide +kernel

/-- Addressee inclusion implication II (3.24) over the printed paradigms. Its exceptions are
the rare patterns that mark the two inclusives apart: (Pf) and (Pg), which the book names,
and (Ph), whose paradigm (3.20) the book's list overlooks. -/
theorem rows_specializedExclusive_of_splitInclusive :
    ∀ r ∈ rows, (r.rare = none ∨ r.rare = some .pi ∨ r.rare = some .pj) →
      r.wePattern.SplitInclusive → r.wePattern.SpecializedExclusive := by
  decide +kernel

theorem rows_splitInclusive_not_specializedExclusive :
    ∀ r ∈ rows, (r.rare = some .pf ∨ r.rare = some .pg ∨ r.rare = some .ph) →
      r.wePattern.SplitInclusive ∧ ¬ r.wePattern.SpecializedExclusive := by
  decide +kernel

/-- The strong universal 'we' (3.7) fails: the English inflection (4.68) has no 'we'. -/
theorem english_inflection_noWe :
    ∃ r ∈ rows, r.id = "cysouw2003_4.68" ∧ HasClusivity r.syncretism .noWe := by
  decide +kernel

/-- The Homophony Implication (2.14), (10.4) over the printed paradigms: singular homophony
only in inflectional paradigms. The two independent-pronoun exceptions the book reports,
Qawesqar and Winnebago, are described in chapter 2 without a printed paradigm. -/
theorem rows_inflectional_of_singularHomophony :
    ∀ r ∈ rows, SingularHomophony r.syncretism → r.marking = some .inflectional := by
  decide +kernel

/-- The Horizontal Homophony Hierarchy holds of every common and semi-common paradigm; its
exceptions, the diagonal cases among them, are rare (§4.3.6, §4.5.7). -/
theorem rows_rare_of_not_respectsHorizontalHierarchy :
    ∀ r ∈ rows, ¬ RespectsHorizontalHierarchy r.syncretism → r.ubiquity = .rare := by
  decide +kernel

/-- Table 4.2's first "nonesuch": under a minimal/augmented inclusive no chapter-4 paradigm
breaks the horizontal hierarchy. -/
theorem rows_respectsHorizontalHierarchy_of_minimalAugmented :
    ∀ r ∈ rows, r.chapter = 4 → weMarking r.syncretism = .minimalAugmented →
      RespectsHorizontalHierarchy r.syncretism := by
  decide +kernel

/-- Table 4.2's second "nonesuch": no singular homophony under any inclusive/exclusive
opposition. -/
theorem rows_unified_of_singularHomophony :
    ∀ r ∈ rows, r.chapter = 4 → SingularHomophony r.syncretism →
      weMarking r.syncretism = .unified := by
  decide +kernel

/-- The Explicitness Hierarchy holds of every common and semi-common paradigm. -/
theorem rows_rare_of_not_respectsExplicitnessHierarchy :
    ∀ r ∈ rows, ¬ RespectsExplicitnessHierarchy r.syncretism → r.ubiquity = .rare := by
  decide +kernel

/-- Singular homophony without vertical homophony is rare, the European paradigms of §4.3.6
(§4.7). -/
theorem rows_rare_of_singularHomophony_without_vertical :
    ∀ r ∈ rows, SingularHomophony r.syncretism → ¬ VerticalHomophony r.syncretism →
      r.ubiquity = .rare := by
  decide +kernel

/-- Vertical homophony under an inclusive/exclusive opposition is rare (§4.6, Table 4.2). -/
theorem rows_rare_of_verticalHomophony_inclusiveExclusive :
    ∀ r ∈ rows, VerticalHomophony r.syncretism → weMarking r.syncretism ≠ .unified →
      r.ubiquity = .rare := by
  decide +kernel

/-- Fig. 10.4's exemplars occupy the five rungs: the Waskia present (4.66), the Una undergoer
suffixes (4.64), then the Latin, Mandara and Maranao types. -/
theorem explicitness_fig10_4 :
    ∃ waskia ∈ rows, ∃ una ∈ rows,
      waskia.id = "cysouw2003_4.66" ∧ una.id = "cysouw2003_4.64" ∧
      explicitness waskia.syncretism = some .singularHomophony ∧
      explicitness una.syncretism = some .verticalHomophony ∧
      explicitness Kind.latin.pattern = some (.we .unified) ∧
      explicitness Kind.mandara.pattern = some (.we .inclusiveExclusive) ∧
      explicitness Kind.maranao.pattern = some (.we .minimalAugmented) := by
  decide +kernel

/-! ### Two paradigms from the Fragments -/

/-- The English subject pronouns by referential category: the form of the fragment's
non-accusative entry with the category's person, clusivity collapsed, and number. -/
def englishSubject (c : Category) : Option String :=
  (English.pronouns.find? λ e => decide (e.case_ ≠ some .acc ∧
      e.person.map coarsen = some c.person.coarsen ∧
      (e.number = some .singular ↔ c.IsSingular))).map (·.form)

/-- The English pronouns have the structure of (4.19). -/
theorem english_pronouns :
    ∃ r ∈ rows, r.id = "cysouw2003_4.19" ∧ syncretism englishSubject = r.syncretism := by
  decide +kernel

/-- Horizontal homophony in the second person only: the English pronouns break the horizontal
hierarchy (§4.3.6). -/
theorem english_not_respectsHorizontalHierarchy :
    ¬ RespectsHorizontalHierarchy (syncretism englishSubject) := by decide +kernel

/-- The Tagalog *ang* series by referential category. -/
def tagalogAng (c : Category) : Option String :=
  (Tagalog.angSeries.find? λ e => decide (e.category = some c)).map (·.form)

/-- The Tagalog *ang* series is a Maranao-type paradigm (§4.5.2). -/
theorem tagalog_maranao : syncretism tagalogAng = Kind.maranao.pattern := by decide +kernel

end Cysouw2003
