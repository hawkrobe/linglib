import Linglib.Features.Phi.Geometry
import Linglib.Data.Examples.HarleyRitter2002

/-!
# Person and number in pronouns: a feature-geometric analysis

[harley-ritter-2002]: the person and number features of pronouns form a
dependency geometry — Participant with Speaker and Addressee, Individuation
with Group, Minimal, and its dependent Augmented — and a pronoun's content is
a subtree containing the root, so that a complex geometry implies its simpler
subgeometries. The active inventories of Daga, Kalihna, Tonkawa, Chinook,
Yimas, and Boumaa Fijian (§2.3–2.8) give every attested person–number cell a
distinct geometry within the inventory, and the person-only languages Pirahã,
Maxakalí, and Kwakiutl (§4) realize exactly the geometries their inventories
license — at most four first- and second-person pronouns. Pruning a dependent
from a licensed geometry leaves a licensed geometry, whence no dual without
plural, no paucal without dual, no inclusive without second person ((18)), and
no gender in the plural without gender in the singular (Greenberg's Universals
37 and 45, §6.3); Universal 36, gender implies number, is the dependency of
Class on Individuation. Markedness is node count: third person is least marked
and the Fijian first inclusive paucal uses all eight nodes. Acquisition builds
structure top-down, so first person precedes second and singular precedes
plural ((20)).

## Main definitions

* `Lang`, `Lang.active`: the nine languages and the nodes each activates.
* `Row`, `rows`: the pronoun tables, from the paper's example pool.

## Main results

* `active_of_rows`: each inventory is read off its paradigm's contrasts.
* `licenses_rows`, `cell_nodup`: every attested cell is licensed by its
  language's inventory, distinct cells by distinct geometries.
* `person_only_exhaust`, `card_participant_geometries`: Pirahã, Maxakalí, and
  Kwakiutl realize exactly the licensed geometries; the Participant node
  yields four.
* `dual_needs_plural`, `paucal_needs_dual`, `inclusive_needs_second`: (18).
* `gender_needs_number`, `gendered_plural_needs_gendered_singular`,
  `no_gender_only_in_plural`: Universals 36, 37, and 45.
* `third_least_marked`, `fijian_inclusive_paucal`: node-count markedness.
* `first_before_second`, `singular_before_plural`: the acquisition order (20a).
* `maxakali_coopts`: bare Participant and Participant with Speaker fill to the
  same content yet are distinct geometries (§4.1).

## References

* [J. H. Greenberg, *Some universals of grammar*][greenberg-1963]
* [F. Plank and W. Schellinger, *The uneven distribution of genders over
  numbers*][plank-schellinger-1997]
-/

namespace HarleyRitter2002

open Phi.Geometry Data.Examples

/-! ### Languages and their inventories -/

/-- The languages of §2.3–2.8 and §4. -/
inductive Lang where
  | daga | kalihna | tonkawa | chinook | yimas | fijian | piraha | maxakali | kwakiutl
  deriving DecidableEq, Repr, Fintype

/-- The language of a pool row, by Glottocode. -/
def Lang.ofGlottocode : String → Option Lang
  | "daga1275" => some .daga
  | "gali1262" => some .kalihna
  | "tonk1249" => some .tonkawa
  | "chin1286" => some .chinook
  | "yima1243" => some .yimas
  | "fiji1243" => some .fijian
  | "pira1253" => some .piraha
  | "maxa1247" => some .maxakali
  | "kwak1269" => some .kwakiutl
  | _ => none

/-- The nodes each language activates ((12)–(17), (25), (27)): Speaker is
contrastive where there is an inclusive, Minimal where there is a dual,
Augmented where there is a paucal; the person-only languages activate no
Individuation. -/
def Lang.active : Lang → Finset Node
  | .daga => {.referringExpression, .participant, .addressee, .individuation, .group}
  | .kalihna => {.referringExpression, .participant, .speaker, .addressee, .individuation, .group}
  | .tonkawa =>
    {.referringExpression, .participant, .addressee, .individuation, .minimal, .group}
  | .chinook =>
    {.referringExpression, .participant, .speaker, .addressee, .individuation, .minimal, .group}
  | .yimas =>
    {.referringExpression, .participant, .addressee, .individuation, .minimal, .group, .augmented}
  | .fijian =>
    {.referringExpression, .participant, .speaker, .addressee, .individuation, .minimal, .group,
      .augmented}
  | .piraha => {.referringExpression, .participant, .addressee}
  | .maxakali | .kwakiutl => {.referringExpression, .participant, .speaker, .addressee}

theorem active_isLowerSet (l : Lang) : IsLowerSet (↑l.active : Set Node) := by
  cases l <;> decide

/-! ### The pronoun tables -/

/-- A pronoun of the tables: its language, cell, and form. -/
structure Row where
  lang : Lang
  person : Person
  number : Number
  form : String
  deriving DecidableEq, Repr

/-- The person of a pool row, by the tables' labels. -/
def personOfLabel : String → Option Person
  | "1" => some .first
  | "1ex" => some .firstExclusive
  | "1in" => some .firstInclusive
  | "2" => some .second
  | "3" => some .third
  | _ => none

/-- The number of a pool row, by the tables' labels; `none` is number-neutral. -/
def numberOfLabel : String → Option Number
  | "sg" => some .singular
  | "du" => some .dual
  | "pc" => some .paucal
  | "pl" => some .plural
  | "none" => some .general
  | _ => none

/-- Read a row off a pool example. -/
def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let lang ← Lang.ofGlottocode ex.language
  let person ← ex.feature? "person" >>= personOfLabel
  let number ← ex.feature? "number" >>= numberOfLabel
  pure ⟨lang, person, number, ex.primaryText⟩

theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

/-- The pronouns of Tables 3–8 and 13–15. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- A language's pronouns. -/
def Lang.rows (l : Lang) : List Row := HarleyRitter2002.rows.filter (·.lang = l)

/-- The geometry of a row's cell in its language. -/
def Row.cell (r : Row) : Option (Finset Node) := Phi.Geometry.cell r.lang.active r.person r.number

/-- Every attested cell is licensed by its language's inventory. -/
theorem licenses_rows : ∀ r ∈ rows, Licenses r.lang.active r.person r.number := by decide

/-- The inventory is read off the paradigm (§2.4, §3): Addressee is active iff
there is a second person, Speaker iff an inclusive, Minimal iff a dual,
Augmented iff a paucal, and Individuation iff some person distinguishes
numbers — which the person-only languages do not. -/
theorem active_of_rows (l : Lang) :
    (Node.addressee ∈ l.active ↔ ∃ r ∈ l.rows, r.person = .second) ∧
      (Node.speaker ∈ l.active ↔ ∃ r ∈ l.rows, r.person = .firstInclusive) ∧
      (Node.minimal ∈ l.active ↔ ∃ r ∈ l.rows, r.number = .dual) ∧
      (Node.augmented ∈ l.active ↔ ∃ r ∈ l.rows, r.number = .paucal) ∧
      (Node.individuation ∈ l.active ↔
        ∃ r ∈ l.rows, ∃ s ∈ l.rows, r.person = s.person ∧ r.number ≠ s.number) := by
  cases l <;> decide

/-- Within a language, distinct cells receive distinct geometries. -/
theorem cell_nodup (l : Lang) : (l.rows.map Row.cell).Nodup := by
  cases l <;> decide

/-- The person-only languages realize every nonempty lower subset of their
inventory and nothing else (§4, (25), (27)). -/
theorem person_only_exhaust :
    ∀ l ∈ [Lang.piraha, .maxakali, .kwakiutl],
      (l.rows.filterMap Row.cell).toFinset = l.active.lowerSubsets.erase ∅ := by
  decide

/-- A language using only the Participant node has four geometries with it
((26)): no such language has more than four first- and second-person
pronouns. -/
theorem card_participant_geometries :
    (Lang.maxakali.active.lowerSubsets.filter (Node.participant ∈ ·)).card = 4 := by decide

/-! ### Complex geometries imply simpler ones (§2.10, §6.1) -/

variable {A : Finset Node} {p : Person} {n : Number}

/-- Plural is dual with Minimal pruned ((32a)). -/
theorem cell_plural_eq (A : Finset Node) (p : Person) :
    cell A p .plural = (cell A p .dual).map (·.filter fun b => ¬ Node.minimal ≤ b) := by
  cases p <;> by_cases hi : Node.individuation ∈ A <;>
    simp only [cell, personNodes, numberNodes, Option.bind_eq_bind, Option.pure_def, Option.bind,
      hi, ↓reduceIte] <;> decide

/-- Singular is dual with Group pruned, in an inventory with a contrastive
Minimal ((32a)). -/
theorem cell_singular_eq (h : Node.minimal ∈ A) (p : Person) :
    cell A p .singular = (cell A p .dual).map (·.filter fun b => ¬ Node.group ≤ b) := by
  cases p <;> by_cases hi : Node.individuation ∈ A <;>
    simp only [cell, personNodes, numberNodes, Option.bind_eq_bind, Option.pure_def, Option.bind,
      hi, h, ↓reduceIte] <;> decide

/-- Dual is paucal with Augmented pruned. -/
theorem cell_dual_eq (A : Finset Node) (p : Person) :
    cell A p .dual = (cell A p .paucal).map (·.filter fun b => ¬ Node.augmented ≤ b) := by
  cases p <;> by_cases hi : Node.individuation ∈ A <;>
    simp only [cell, personNodes, numberNodes, Option.bind_eq_bind, Option.pure_def, Option.bind,
      hi, ↓reduceIte] <;> decide

/-- Second person is inclusive with Speaker pruned, exclusive inclusive with
Addressee pruned ((32b)). -/
theorem cell_second_eq (A : Finset Node) (n : Number) :
    cell A .second n = (cell A .firstInclusive n).map (·.filter fun b => ¬ Node.speaker ≤ b) ∧
      cell A .firstExclusive n =
        (cell A .firstInclusive n).map (·.filter fun b => ¬ Node.addressee ≤ b) := by
  cases n <;> by_cases hi : Node.individuation ∈ A <;> by_cases hm : Node.minimal ∈ A <;>
    simp only [cell, personNodes, numberNodes, Option.bind_eq_bind, Option.pure_def, Option.bind,
      hi, hm, ↓reduceIte] <;> decide

theorem licenses_of_map_filter {n' : Number} {p' : Person} {a : Node}
    (h : cell A p' n' = (cell A p n).map (·.filter fun b => ¬ a ≤ b)) (hl : Licenses A p n) :
    Licenses A p' n' := by
  obtain ⟨g, hg, hsub⟩ := hl
  exact ⟨_, h ▸ Option.mem_map_of_mem _ hg, (Finset.filter_subset _ _).trans hsub⟩

/-- **(18a)** No dual without plural. -/
theorem dual_needs_plural (h : Licenses A p .dual) : Licenses A p .plural :=
  licenses_of_map_filter (cell_plural_eq A p) h

/-- **(18b)** No paucal without dual. -/
theorem paucal_needs_dual (h : Licenses A p .paucal) : Licenses A p .dual :=
  licenses_of_map_filter (cell_dual_eq A p) h

/-- **(18c)** No inclusive without second person — nor without exclusive. -/
theorem inclusive_needs_second (h : Licenses A .firstInclusive n) :
    Licenses A .second n ∧ Licenses A .firstExclusive n :=
  ⟨licenses_of_map_filter (cell_second_eq A n).1 h, licenses_of_map_filter (cell_second_eq A n).2 h⟩

/-! ### Gender (§6.3) -/

/-- **Universal 36**: gender implies number — Class depends on Individuation. -/
theorem gender_needs_number (hA : IsLowerSet (↑A : Set Node)) (h : Node.nounClass ∈ A) :
    Node.individuation ∈ A :=
  hA (by decide) h

/-- **Universals 37 and 45**: a gendered geometry with Group prunes to a
gendered one without, so gender in the plural implies gender in the singular. -/
theorem gendered_plural_needs_gendered_singular {g : Finset Node} (hg : g ∈ A.lowerSubsets)
    (hc : Node.nounClass ∈ g) :
    (g.filter fun b => ¬ Node.group ≤ b) ∈ A.lowerSubsets ∧
      Node.nounClass ∈ (g.filter fun b => ¬ Node.group ≤ b) ∧
      Node.group ∉ (g.filter fun b => ¬ Node.group ≤ b) :=
  ⟨Finset.filter_not_le_mem_lowerSubsets hg _, Finset.mem_filter.2 ⟨hc, by decide⟩, by simp⟩

/-- The system (45) — gender only in nonsingular numbers — is impossible: an
inventory whose every gendered geometry has Group has no gendered geometry. -/
theorem no_gender_only_in_plural
    (hall : ∀ g ∈ A.lowerSubsets, Node.nounClass ∈ g → Node.group ∈ g) :
    ∀ g ∈ A.lowerSubsets, Node.nounClass ∉ g := fun _ hg hc =>
  have ⟨hg', hc', hng⟩ := gendered_plural_needs_gendered_singular hg hc
  hng (hall _ hg' hc')

/-! ### Markedness (§1.3, §2.3) -/

/-- Third person is the least marked: its geometry lies within every other
person's in the same number. -/
theorem third_least_marked {g g' : Finset Node} (h : cell A .third n = some g)
    (h' : cell A p n = some g') : g ⊆ g' := by
  cases p <;> cases n <;> by_cases hi : Node.individuation ∈ A <;>
    by_cases hm : Node.minimal ∈ A <;>
    simp only [cell, personNodes, numberNodes, Option.bind_eq_bind, Option.pure_def, Option.bind,
      hi, hm, ↓reduceIte, Option.some.injEq,
      reduceCtorEq] at h h' <;> subst h h' <;> decide

/-- In Daga, the first singular is less marked than the first plural — the
default Speaker and Minimal nodes are not counted (§2.3). -/
theorem daga_first_singular_lt_plural :
    ∀ g ∈ cell Lang.daga.active .first .singular, ∀ g' ∈ cell Lang.daga.active .first .plural,
      g.card < g'.card := by
  decide

/-- The most marked pronoun, the Fijian first inclusive paucal, uses all eight
person–number nodes (§2.8). -/
theorem fijian_inclusive_paucal :
    cell Lang.fijian.active .firstInclusive .paucal = some Lang.fijian.active ∧
      Lang.fijian.active.card = 8 := by
  decide

/-! ### Acquisition (§3) -/

/-- First person is acquired before second: its geometry is a proper part
((20a-ii)). -/
theorem first_before_second :
    ∀ g ∈ cell A .first n, ∀ g' ∈ cell A .second n, g ⊂ g' := by
  cases n <;> by_cases hi : Node.individuation ∈ A <;> by_cases hm : Node.minimal ∈ A <;>
    simp only [cell, personNodes, numberNodes, Option.bind_eq_bind, Option.pure_def, Option.bind,
      hi, hm, ↓reduceIte, Option.mem_def,
      Option.some.injEq, forall_eq', reduceCtorEq, false_implies, implies_true] <;> decide

/-- Singular is acquired before plural where Minimal is a default ((20a-iii)). -/
theorem singular_before_plural (hm : Node.minimal ∉ A) (hi : Node.individuation ∈ A) :
    ∀ g ∈ cell A p .singular, ∀ g' ∈ cell A p .plural, g ⊂ g' := by
  cases p <;> simp only [cell, personNodes, numberNodes, Option.bind_eq_bind, Option.pure_def,
    Option.bind, hi, hm, ↓reduceIte, Option.mem_def, Option.some.injEq, forall_eq', reduceCtorEq,
    false_implies, implies_true] <;> decide

/-- Second person and third plural are incomparable, so their order varies
((20b)). -/
theorem second_third_plural_incomparable :
    ∀ g ∈ cell Lang.daga.active .second .singular, ∀ g' ∈ cell Lang.daga.active .third .plural,
      ¬ g ⊆ g' ∧ ¬ g' ⊆ g := by
  decide

/-! ### Empty paradigm space (§4.1) -/

/-- Maxakalí's first singular, the bare Participant node, and its first
exclusive plural, Participant with Speaker, fill to the same content by the
Speaker default yet are distinct geometries — the exclusive plural co-opts the
representation the contrastive Speaker makes available ((27)). -/
theorem maxakali_coopts :
    ∀ g ∈ cell Lang.maxakali.active .first .singular,
      ∀ g' ∈ cell Lang.maxakali.active .firstExclusive .plural,
        g ≠ g' ∧ fillDefaults g = fillDefaults g' := by
  decide

end HarleyRitter2002
