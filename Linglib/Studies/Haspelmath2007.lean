import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Coordination
import Linglib.Fragments.English.Coordination
import Linglib.Fragments.Hausa.Coordination
import Linglib.Fragments.Kannada.Coordination
import Linglib.Fragments.Lango.Coordination
import Linglib.Fragments.Latin.Coordination
import Linglib.Fragments.Tibetan.Coordination
import Linglib.Fragments.Turkish.Coordination
import Linglib.Fragments.Yoruba.Coordination

/-!
# Haspelmath (2007): Coordination

This file formalizes the typology of coordinators in [haspelmath-2007]: the patterns of
coordinator placement in binary coordination, (17), and the two derivations built on them. The
first is diachronic, §1.2: a conjunctive coordinator descends from a comitative modifier 'A with
B' or from an additive focus particle 'A, also B', `DiachronicSource.pattern` gives the pattern
of each source construction, and `coAB_unsourced` derives that the one logically possible
monosyndetic pattern no language attests, co-A B, is the one no source yields. The second is
Table 1.1, §1.4: the full n-ary pattern repeats the binary marking on every coordinand but the
one bare in the binary construction (`full`) and coordinator omission keeps only the last
coordinator (`omitted`); `table_1_1` recovers the table's five rows. `attestations` are the
constructions the chapter cites with their patterns, over which `bisyndetic_normal_postpositive`
states the observation of §1.3 and §2.1 that non-emphatic bisyndesis is postpositive with two
coordinators of the same shape and `prepositive_bisyndetic_emphatic` Stassen's, that
prepositive bisyndesis is an emphatic variant. The emphatic correlatives of (45) are classified
from their forms by `CorrelativeShape.classify`, and Payne's implicational sequence of
coordinand types, §3, is `Contiguous`, with Tinrin the counterexample the chapter records.
The chapter's examples are the rows of `Data/Examples/Haspelmath2007.json`.

## Implementation notes

The chapter's exemplar languages with Fragment coordination entries use them; the others
carry their coordinator inline. Whether a construction is emphatic is recorded only where the
chapter says so, and a diachronic source only where the chapter states one, so Classical
Tibetan *-daŋ*, "a former case-marker", has none. The word-order half of the comitative
derivation, adposition order following modifier order, is taken as the `CoordinatorPosition`
argument of `DiachronicSource.pattern`. The comitative-sourced attestations include Tauya
*-sou*, doubled on both conjuncts, the extension §5.1 notes, so `comitative_patterns` admits
the postpositive bisyndetic pattern beside the two source patterns.

## References

* [haspelmath-2007]
* [stassen-2000]
-/

namespace Haspelmath2007

open Syntax.Coordination

/-! ### Binary patterns, (17) -/

/-- The marking of a coordinand: bare, or carrying a prepositive or a postpositive
coordinator. -/
inductive Slot where
  | bare
  | pre
  | post
  deriving DecidableEq, Repr

/-- The markings of the two coordinands in a binary pattern, (17). -/
def slots : CoordPattern → Slot × Slot
  | .a_co_b => (.bare, .pre)
  | .a'co_b => (.post, .bare)
  | .a_b'co => (.bare, .post)
  | .co'a_b => (.pre, .bare)
  | .co'a_co'b => (.pre, .pre)
  | .a'co_b'co => (.post, .post)
  | .a'co_co'b => (.post, .pre)
  | .co'a_b'co => (.pre, .post)

/-- Monosyndetic coordination is universally asymmetric, §1.2: one coordinand is bare. -/
theorem monosyndetic_bare (p : CoordPattern) (h : p.syndesis = .monosyndetic) :
    (slots p).1 = .bare ∨ (slots p).2 = .bare := by
  cases p <;> first | decide | exact absurd h (by decide)

/-- No source construction has the pattern co-A B, §1.2: the explanation of its absence in
[stassen-2000]'s sample of 260 languages. -/
theorem coAB_unsourced (s : DiachronicSource) (pos : CoordinatorPosition) :
    DiachronicSource.pattern s pos ≠ some .co'a_b := by
  cases s <;> cases pos <;> decide

/-! ### Multiple coordination, Table 1.1 -/

/-- The full n-ary pattern, §1.4: a bisyndetic pattern of one shape marks every coordinand,
and a monosyndetic pattern leaves bare the coordinand bare in the binary construction and
marks every other one as its marked coordinand is marked; the mixed patterns have no full
pattern in the chapter. -/
def full (p : CoordPattern) (n : ℕ) : Option (List Slot) :=
  match slots p with
  | (.bare, s) => some (.bare :: List.replicate (n - 1) s)
  | (s, .bare) => some (List.replicate (n - 1) s ++ [.bare])
  | (s, t) => if s = t then some (List.replicate n s) else none

/-- Keep the last coordinator of a construction read from the end. -/
def keepLastRev : List Slot → List Slot
  | [] => []
  | .bare :: l => .bare :: keepLastRev l
  | s :: l => s :: l.map λ _ => .bare

/-- Coordinator omission, §1.4: all but the last coordinator are eliminated. -/
def omitted (p : CoordPattern) (n : ℕ) : Option (List Slot) :=
  (full p n).map λ l => (keepLastRev l.reverse).reverse

/-- Table 1.1 for four coordinands: the full pattern and the pattern with coordinator omission
of each of the five binary patterns the table lists. -/
theorem table_1_1 :
    full .a_co_b 4 = some [.bare, .pre, .pre, .pre] ∧
      omitted .a_co_b 4 = some [.bare, .bare, .bare, .pre] ∧
    full .a'co_b 4 = some [.post, .post, .post, .bare] ∧
      omitted .a'co_b 4 = some [.bare, .bare, .post, .bare] ∧
    full .a'co_b'co 4 = some [.post, .post, .post, .post] ∧
      omitted .a'co_b'co 4 = some [.bare, .bare, .bare, .post] ∧
    full .co'a_co'b 4 = some [.pre, .pre, .pre, .pre] ∧
      omitted .co'a_co'b 4 = some [.bare, .bare, .bare, .pre] ∧
    full .a_b'co 4 = some [.bare, .post, .post, .post] ∧
      omitted .a_b'co 4 = some [.bare, .bare, .bare, .post] := by
  decide

/-! ### The chapter's attestations -/

/-- A coordinate construction the chapter cites: its coordinator, the second coordinator of a
mixed pattern, the binary pattern, whether the chapter presents the construction as emphatic,
and the diachronic source when the chapter states one. -/
structure Attestation where
  language : String
  coordinator : Coordinator
  second : Option Coordinator := none
  pattern : CoordPattern
  emphatic : Option Bool := none
  source : Option DiachronicSource := none
  deriving Repr

/-- A conjunctive coordinator with no Fragment entry. -/
private def co (form : String) (kind : Morphology.Morph.Kind) : Coordinator :=
  { form, gloss := "and", role := .j, kind }

/-- The constructions of (5), (6), (12), (20)–(37), (59), (77)–(79) and (85). -/
def attestations : List Attestation :=
  [ { language := "Kannada", coordinator := Kannada.Coordination.u, pattern := .a'co_b'co,
      emphatic := some false },
    { language := "English", coordinator := English.Coordination.and_, pattern := .a_co_b,
      emphatic := some false },
    { language := "English", coordinator := co "both" .free,
      second := some English.Coordination.and_, pattern := .co'a_co'b, emphatic := some true },
    { language := "Hausa", coordinator := Hausa.da, pattern := .a_co_b, emphatic := some false,
      source := some .comitative },
    { language := "Lango", coordinator := Lango.Coordination.kede, pattern := .a_co_b,
      emphatic := some false, source := some .comitative },
    { language := "Classical Tibetan", coordinator := Tibetan.Coordination.dang,
      pattern := .a'co_b, emphatic := some false },
    { language := "Latin", coordinator := Latin.Coordination.que, pattern := .a_b'co,
      emphatic := some false },
    { language := "Turkish", coordinator := Turkish.Coordination.de, pattern := .a_b'co },
    { language := "Kanuri", coordinator := co "-a" (.bound .after .affix),
      pattern := .a'co_b'co, emphatic := some false },
    { language := "Yoruba", coordinator := Yoruba.Coordination.ati, pattern := .co'a_co'b,
      emphatic := some true },
    { language := "Yoruba", coordinator := Yoruba.Coordination.ati, pattern := .a_co_b,
      emphatic := some false },
    { language := "Martuthunira", coordinator := co "-thurti" (.bound .after .affix),
      pattern := .a'co_b'co, emphatic := some false },
    { language := "Homeric Greek", coordinator := co "te" (.bound .after .clitic),
      second := some (co "kaì" .free), pattern := .a'co_co'b },
    { language := "Latin", coordinator := Latin.Coordination.et,
      second := some Latin.Coordination.que, pattern := .co'a_b'co, emphatic := some true },
    { language := "Nivkh", coordinator := co "-γo" (.bound .after .affix),
      pattern := .a'co_b'co, emphatic := some false },
    { language := "Polish", coordinator := co "i" .free, pattern := .a_co_b,
      emphatic := some false },
    { language := "Lezgian", coordinator := co "-ni" (.bound .after .affix),
      pattern := .a'co_b, emphatic := some false },
    { language := "West Greenlandic", coordinator := co "=lu" (.bound .after .clitic),
      pattern := .a_b'co, emphatic := some false },
    { language := "Amharic", coordinator := co "-nna" (.bound .after .affix),
      pattern := .a'co_b, emphatic := some false },
    { language := "Ponapean", coordinator := co "oh" .free, pattern := .a_co_b,
      emphatic := some false },
    { language := "Samoan", coordinator := co "ma" .free, pattern := .a_co_b,
      source := some .comitative },
    { language := "Retuarã", coordinator := co "-ka" (.bound .after .affix),
      pattern := .a'co_b, source := some .comitative },
    { language := "Russian", coordinator := co "s" .free, pattern := .a_co_b,
      source := some .comitative },
    { language := "Tauya", coordinator := co "-sou" (.bound .after .affix),
      pattern := .a'co_b'co, emphatic := some false, source := some .comitative } ]

/-- The pattern co-A B is absent from the chapter's attestations, as from Stassen's sample. -/
theorem attested_ne_coAB : ∀ a ∈ attestations, a.pattern ≠ .co'a_b := by decide

/-- Where bisyndesis is the normal, non-emphatic construction, the coordinators are
postpositive and of the same shape, §1.3 and §2.1. -/
theorem bisyndetic_normal_postpositive :
    ∀ a ∈ attestations, a.pattern.syndesis = .bisyndetic → a.emphatic = some false →
      a.pattern = .a'co_b'co ∧ a.second = none := by
  decide

/-- Prepositive bisyndesis occurs only as an emphatic variant of prepositive monosyndesis,
§1.3 after [stassen-2000]. -/
theorem prepositive_bisyndetic_emphatic :
    ∀ a ∈ attestations, a.pattern = .co'a_co'b → a.emphatic = some true := by
  decide

/-- A comitative-sourced coordinator has one of the two source patterns of §1.2 or, doubled on
each conjunct as §5.1 describes, the postpositive bisyndetic one. -/
theorem comitative_patterns :
    ∀ a ∈ attestations, a.source = some .comitative →
      a.pattern = .a_co_b ∨ a.pattern = .a'co_b ∨ a.pattern = .a'co_b'co := by
  decide

/-! ### Emphatic correlatives, (45) -/

/-- The shape of a pair of correlative coordinators against the single coordinator, (45):
both identical to it, only the second identical to it, identical to each other but not to it,
or all three different. -/
inductive CorrelativeShape where
  | bothSingle
  | secondSingle
  | sameNotSingle
  | allDifferent
  deriving DecidableEq, Repr

/-- The shape of a correlative pair, read off the forms. -/
def CorrelativeShape.classify (first second single : String) : CorrelativeShape :=
  if first = single ∧ second = single then .bothSingle
  else if second = single then .secondSingle
  else if first = second then .sameNotSingle
  else .allDifferent

/-- A language's emphatic correlative pair and its single coordinator. -/
structure Correlative where
  language : String
  first : String
  second : String
  single : String
  deriving Repr

/-- The conjunctive rows of (45), with the letter the chapter files each under. -/
def correlatives : List (Correlative × CorrelativeShape) :=
  [ (⟨"Russian", "i", "i", "i"⟩, .bothSingle), (⟨"Italian", "e", "e", "e"⟩, .bothSingle),
    (⟨"Modern Greek", "ke", "ke", "ke"⟩, .bothSingle),
    (⟨"Albanian", "edhe", "edhe", "edhe"⟩, .bothSingle),
    (⟨"English", "both", "and", "and"⟩, .secondSingle),
    (⟨"Irish", "idir", "agus", "agus"⟩, .secondSingle),
    (⟨"Hungarian", "mind", "mind", "és"⟩, .sameNotSingle),
    (⟨"Korean", "-to", "-to", "-hako"⟩, .sameNotSingle),
    (⟨"German", "sowohl", "als auch", "und"⟩, .allDifferent),
    (⟨"Polish", "jak", "tak (i)", "i"⟩, .allDifferent),
    (⟨"Finnish", "sekä", "että", "ja"⟩, .allDifferent),
    (⟨"Indonesian", "baik", "maupun", "dan"⟩, .allDifferent) ]

/-- The letters of (45) are the shapes the forms give. -/
theorem correlatives_classified :
    ∀ c ∈ correlatives, CorrelativeShape.classify c.1.first c.1.second c.1.single = c.2 := by
  decide

/-! ### Payne's implicational sequence, §3 -/

/-- The coordinand types of the sequence S – VP – AP – PP – NP. -/
inductive CoordinandType where
  | s
  | vp
  | ap
  | pp
  | np
  deriving DecidableEq, Fintype, Repr

/-- Position on the sequence. -/
def CoordinandType.rank : CoordinandType → ℕ
  | .s => 0
  | .vp => 1
  | .ap => 2
  | .pp => 3
  | .np => 4

/-- A coordinator's range is a contiguous stretch of the sequence. -/
def Contiguous (r : Finset CoordinandType) : Prop :=
  ∀ a ∈ r, ∀ b ∈ r, ∀ c, a.rank ≤ c.rank → c.rank ≤ b.rank → c ∈ r

instance : DecidablePred Contiguous := λ _ => by unfold Contiguous; infer_instance

/-- The NP against event split of Korean *-(k)wa* and *-ko*, (57), and Turkish *-la* and
*-ıp*, (58): two contiguous ranges. -/
theorem np_event_contiguous : Contiguous {.np} ∧ Contiguous {.vp, .s} := by decide

/-- Tinrin *mê* coordinates sentences and NPs but not VPs, the counterexample to the sequence
the chapter notes. -/
theorem tinrin_not_contiguous : ¬ Contiguous {.s, .np} := by decide

end Haspelmath2007
