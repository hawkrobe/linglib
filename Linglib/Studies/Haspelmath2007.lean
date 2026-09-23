module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Coordinator
public import Linglib.Fragments.English.Coordination
public import Linglib.Fragments.Finnish.Coordination
public import Linglib.Fragments.German.Coordination
public import Linglib.Fragments.Hausa.Coordination
public import Linglib.Fragments.Hungarian.Coordination
public import Linglib.Fragments.Irish.Coordination
public import Linglib.Fragments.Kannada.Coordination
public import Linglib.Fragments.Korean.Coordination
public import Linglib.Fragments.Lango.Coordination
public import Linglib.Fragments.Latin.Coordination
public import Linglib.Fragments.Tibetic.Classical.Coordination
public import Linglib.Fragments.Turkish.Coordination
public import Linglib.Fragments.Yoruba.Coordination

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

The chapter's exemplar languages with Fragment coordination entries use them, in the
attestations and in the correlative pairs of (45), conjunctive and disjunctive; the others
carry their coordinator inline.
A binary pattern is the pair of its coordinands' markings, so syndesis is the number of marked
coordinands, and `marking_agrees_with_side` checks the patterns against the attachment side the
Fragments record for each coordinator. Whether a construction is emphatic is recorded only
where the chapter says so, and a diachronic source only where the chapter states one, so
Classical Tibetan *-daŋ*, "a former case-marker", has none. The word-order half of the comitative
derivation, adposition order following modifier order, is taken as the `CoordinatorPosition`
argument of `DiachronicSource.pattern`. The comitative-sourced attestations include Tauya
*-sou*, doubled on both conjuncts, the extension §5.1 notes, so `comitative_patterns` admits
the postpositive bisyndetic pattern beside the two source patterns.

## References

* [haspelmath-2007]
* [stassen-2000]
-/

@[expose] public section

namespace Haspelmath2007

/-! ### Binary patterns, (17) -/

/-- The marking of a coordinand: bare, or carrying a prepositive coordinator, co-A, or a
postpositive one, A-co. -/
inductive Slot where
  | bare
  | pre
  | post
  deriving DecidableEq, Repr

/-- A binary pattern, (17): the markings of the two coordinands, so that A co-B is
`(.bare, .pre)` and A-co B-co is `(.post, .post)`. -/
abbrev Pattern := Slot × Slot

/-- The number of coordinators in a pattern: none in asyndetic, one in monosyndetic and two in
bisyndetic coordination, §1. -/
def Pattern.syndesis (p : Pattern) : ℕ := [p.1, p.2].countP (· ≠ .bare)

/-- Monosyndetic coordination is universally asymmetric, §1.2: one coordinand is bare. -/
theorem monosyndetic_bare (p : Pattern) (h : p.syndesis = 1) : p.1 = .bare ∨ p.2 = .bare := by
  revert h; rcases p with ⟨_ | _ | _, _ | _ | _⟩ <;> decide

/-- The position of a coordinator relative to its coordinand, §1.2. -/
inductive CoordinatorPosition where
  | prepositive
  | postpositive
  deriving DecidableEq, Repr

/-- The source construction of a conjunctive coordinator, §1.2 and §5.1: a comitative modifier
'A with B' or an additive focus particle 'A, also B'. -/
inductive DiachronicSource where
  | comitative
  | focusParticle
  deriving DecidableEq, Repr

/-- The binary pattern of a source construction, §1.2: a comitative modifier 'A with B' is A-co B
in a language with postpositions and A co-B in one with prepositions, and an additive focus
particle marks the second conjunct, 'A, B too' giving A B-co and 'A, also B' giving A co-B. -/
def DiachronicSource.pattern : DiachronicSource → CoordinatorPosition → Pattern
  | .comitative, .postpositive => (.post, .bare)
  | .comitative, .prepositive => (.bare, .pre)
  | .focusParticle, .postpositive => (.bare, .post)
  | .focusParticle, .prepositive => (.bare, .pre)

/-- No source construction has the pattern co-A B, §1.2: the explanation of its absence in
[stassen-2000]'s sample of 260 languages. -/
theorem coAB_unsourced (s : DiachronicSource) (pos : CoordinatorPosition) :
    s.pattern pos ≠ (.pre, .bare) := by
  cases s <;> cases pos <;> decide

/-! ### Multiple coordination, Table 1.1 -/

/-- The full n-ary pattern, §1.4: a bisyndetic pattern of one shape marks every coordinand,
and a monosyndetic pattern leaves bare the coordinand bare in the binary construction and
marks every other one as its marked coordinand is marked; the mixed patterns have no full
pattern in the chapter. -/
def full (p : Pattern) (n : ℕ) : Option (List Slot) :=
  match p with
  | (.bare, s) => some (.bare :: List.replicate (n - 1) s)
  | (s, .bare) => some (List.replicate (n - 1) s ++ [.bare])
  | (s, t) => if s = t then some (List.replicate n s) else none

/-- Keep the last coordinator of a construction read from the end. -/
def keepLastRev : List Slot → List Slot
  | [] => []
  | .bare :: l => .bare :: keepLastRev l
  | s :: l => s :: l.map fun _ ↦ .bare

/-- Coordinator omission, §1.4: all but the last coordinator are eliminated. -/
def omitted (p : Pattern) (n : ℕ) : Option (List Slot) :=
  (full p n).map fun l ↦ (keepLastRev l.reverse).reverse

/-- Table 1.1 for four coordinands: the full pattern and the pattern with coordinator omission
of each of the five binary patterns the table lists. -/
theorem table_1_1 :
    full (.bare, .pre) 4 = some [.bare, .pre, .pre, .pre] ∧
      omitted (.bare, .pre) 4 = some [.bare, .bare, .bare, .pre] ∧
    full (.post, .bare) 4 = some [.post, .post, .post, .bare] ∧
      omitted (.post, .bare) 4 = some [.bare, .bare, .post, .bare] ∧
    full (.post, .post) 4 = some [.post, .post, .post, .post] ∧
      omitted (.post, .post) 4 = some [.bare, .bare, .bare, .post] ∧
    full (.pre, .pre) 4 = some [.pre, .pre, .pre, .pre] ∧
      omitted (.pre, .pre) 4 = some [.bare, .bare, .bare, .pre] ∧
    full (.bare, .post) 4 = some [.bare, .post, .post, .post] ∧
      omitted (.bare, .post) 4 = some [.bare, .bare, .bare, .post] := by
  decide

/-! ### The chapter's attestations -/

/-- A coordinate construction the chapter cites: its coordinator, the second coordinator of a
mixed pattern, the binary pattern, whether the chapter presents the construction as emphatic,
and the diachronic source when the chapter states one. -/
structure Attestation where
  language : String
  coordinator : Coordinator
  second : Option Coordinator := none
  pattern : Pattern
  emphatic : Option Bool := none
  source : Option DiachronicSource := none
  deriving Repr

/-- A conjunctive coordinator with no Fragment entry. -/
def co (form : String) (kind : Morphology.Morph.Kind) : Coordinator :=
  { form, gloss := "and", role := .conjunctive, kind }

/-- The constructions of (5), (6), (12), (20)–(37), (59), (77)–(79) and (85). -/
def attestations : List Attestation :=
  [ { language := "Kannada", coordinator := Kannada.Coordination.u, pattern := (.post, .post),
      emphatic := some false },
    { language := "English", coordinator := English.Coordination.and_, pattern := (.bare, .pre),
      emphatic := some false },
    { language := "English", coordinator := co "both" .free,
      second := some English.Coordination.and_, pattern := (.pre, .pre), emphatic := some true },
    { language := "Hausa", coordinator := Hausa.da, pattern := (.bare, .pre),
      emphatic := some false, source := some .comitative },
    { language := "Lango", coordinator := Lango.Coordination.kede, pattern := (.bare, .pre),
      emphatic := some false, source := some .comitative },
    { language := "Classical Tibetan", coordinator := ClassicalTibetan.Coordination.dang,
      pattern := (.post, .bare), emphatic := some false },
    { language := "Latin", coordinator := Latin.Coordination.que, pattern := (.bare, .post),
      emphatic := some false },
    { language := "Turkish", coordinator := Turkish.Coordination.de, pattern := (.bare, .post) },
    { language := "Kanuri", coordinator := co "-a" (.bound .after .affix),
      pattern := (.post, .post), emphatic := some false },
    { language := "Yoruba", coordinator := Yoruba.Coordination.ati, pattern := (.pre, .pre),
      emphatic := some true },
    { language := "Yoruba", coordinator := Yoruba.Coordination.ati, pattern := (.bare, .pre),
      emphatic := some false },
    { language := "Martuthunira", coordinator := co "-thurti" (.bound .after .affix),
      pattern := (.post, .post), emphatic := some false },
    { language := "Homeric Greek", coordinator := co "te" (.bound .after .clitic),
      second := some (co "kaì" .free), pattern := (.post, .pre) },
    { language := "Latin", coordinator := Latin.Coordination.et,
      second := some Latin.Coordination.que, pattern := (.pre, .post), emphatic := some true },
    { language := "Nivkh", coordinator := co "-γo" (.bound .after .affix),
      pattern := (.post, .post), emphatic := some false },
    { language := "Polish", coordinator := co "i" .free, pattern := (.bare, .pre),
      emphatic := some false },
    { language := "Lezgian", coordinator := co "-ni" (.bound .after .affix),
      pattern := (.post, .bare), emphatic := some false },
    { language := "West Greenlandic", coordinator := co "=lu" (.bound .after .clitic),
      pattern := (.bare, .post), emphatic := some false },
    { language := "Amharic", coordinator := co "-nna" (.bound .after .affix),
      pattern := (.post, .bare), emphatic := some false },
    { language := "Ponapean", coordinator := co "oh" .free, pattern := (.bare, .pre),
      emphatic := some false },
    { language := "Samoan", coordinator := co "ma" .free, pattern := (.bare, .pre),
      source := some .comitative },
    { language := "Retuarã", coordinator := co "-ka" (.bound .after .affix),
      pattern := (.post, .bare), source := some .comitative },
    { language := "Russian", coordinator := co "s" .free, pattern := (.bare, .pre),
      source := some .comitative },
    { language := "Tauya", coordinator := co "-sou" (.bound .after .affix),
      pattern := (.post, .post), emphatic := some false, source := some .comitative } ]

/-- The marked coordinands of a construction, each with its coordinator: the first coordinator
marks the first marked coordinand, and the second coordinator of a mixed pattern the second. -/
def Attestation.marking (a : Attestation) : List (Slot × Coordinator) :=
  [(a.pattern.1, a.coordinator), (a.pattern.2, a.second.getD a.coordinator)].filter
    (·.1 ≠ .bare)

/-- The patterns agree with the morphology of the coordinators: a coordinator that attaches
after its host is postpositive in every construction, and one that attaches before it
prepositive. -/
theorem marking_agrees_with_side : ∀ a ∈ attestations, ∀ m ∈ a.marking,
    (m.2.kind.side? = some .after → m.1 = .post) ∧
      (m.2.kind.side? = some .before → m.1 = .pre) := by
  decide

/-- The pattern co-A B is absent from the chapter's attestations, as from Stassen's sample. -/
theorem attested_ne_coAB : ∀ a ∈ attestations, a.pattern ≠ (.pre, .bare) := by decide

/-- Where bisyndesis is the normal, non-emphatic construction, the coordinators are
postpositive and of the same shape, §1.3 and §2.1. -/
theorem bisyndetic_normal_postpositive :
    ∀ a ∈ attestations, a.pattern.syndesis = 2 → a.emphatic = some false →
      a.pattern = (.post, .post) ∧ a.second = none := by
  decide

/-- Prepositive bisyndesis occurs only as an emphatic variant of prepositive monosyndesis,
§1.3 after [stassen-2000]. -/
theorem prepositive_bisyndetic_emphatic :
    ∀ a ∈ attestations, a.pattern = (.pre, .pre) → a.emphatic = some true := by
  decide

/-- A comitative-sourced coordinator has one of the two source patterns of §1.2 or, doubled on
each conjunct as §5.1 describes, the postpositive bisyndetic one. -/
theorem comitative_patterns :
    ∀ a ∈ attestations, a.source = some .comitative →
      a.pattern = (.bare, .pre) ∨ a.pattern = (.post, .bare) ∨ a.pattern = (.post, .post) := by
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
def CorrelativeShape.classify (c : Coordinator.Correlative) : CorrelativeShape :=
  if c.first = c.single.form ∧ c.second = c.single.form then .bothSingle
  else if c.second = c.single.form then .secondSingle
  else if c.first = c.second then .sameNotSingle
  else .allDifferent

/-- A disjunctive coordinator with no Fragment entry. -/
def dis (form : String) : Coordinator :=
  { form, gloss := "or", role := .disjunctive, kind := .free }

/-- The rows of (45), each with its language and the letter the chapter files it under. -/
def correlatives : List (String × Coordinator.Correlative × CorrelativeShape) :=
  [ ("Russian", ⟨"i", "i", co "i" .free⟩, .bothSingle),
    ("Italian", ⟨"e", "e", co "e" .free⟩, .bothSingle),
    ("Modern Greek", ⟨"ke", "ke", co "ke" .free⟩, .bothSingle),
    ("Albanian", ⟨"edhe", "edhe", co "edhe" .free⟩, .bothSingle),
    ("Polish", ⟨"albo", "albo", dis "albo"⟩, .bothSingle),
    ("Dutch", ⟨"of", "of", dis "of"⟩, .bothSingle),
    ("Basque", ⟨"ala", "ala", dis "ala"⟩, .bothSingle),
    ("Somali", ⟨"ama", "ama", dis "ama"⟩, .bothSingle),
    ("English", English.Coordination.bothAnd, .secondSingle),
    ("Irish", Irish.Coordination.idirAgus, .secondSingle),
    ("English", English.Coordination.eitherOr, .secondSingle),
    ("German", German.Coordination.entwederOder, .secondSingle),
    ("Finnish", Finnish.Coordination.jokoTai, .secondSingle),
    ("Hungarian", Hungarian.Coordination.mindMind, .sameNotSingle),
    ("Korean", Korean.Coordination.toTo, .sameNotSingle),
    ("Lezgian", ⟨"ja", "ja", dis "waja"⟩, .sameNotSingle),
    ("German", German.Coordination.sowohlAlsAuch, .allDifferent),
    ("Polish", ⟨"jak", "tak (i)", co "i" .free⟩, .allDifferent),
    ("Finnish", Finnish.Coordination.sekaEtta, .allDifferent),
    ("Indonesian", ⟨"baik", "maupun", co "dan" .free⟩, .allDifferent) ]

/-- The letters of (45) are the shapes the forms give. -/
theorem correlatives_classified :
    ∀ r ∈ correlatives, CorrelativeShape.classify r.2.1 = r.2.2 := by
  decide

/-- The correlative coordinators of (45) emphasize a conjunction or a disjunction. -/
theorem correlatives_conjunctive_or_disjunctive : ∀ r ∈ correlatives,
    r.2.1.single.role = .conjunctive ∨ r.2.1.single.role = .disjunctive := by
  decide

/-- Yoruba *àtí … àtí*, the emphatic construction of the attestations, has the shape of
(45a). -/
theorem yoruba_bothSingle :
    CorrelativeShape.classify Yoruba.Coordination.atiAti = .bothSingle := by
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

instance : DecidablePred Contiguous := fun _ ↦ by unfold Contiguous; infer_instance

/-- The NP against event split of Korean *-(k)wa* and *-ko*, (57), and Turkish *-la* and
*-ıp*, (58): two contiguous ranges. -/
theorem np_event_contiguous : Contiguous {.np} ∧ Contiguous {.vp, .s} := by decide

/-- Tinrin *mê* coordinates sentences and NPs but not VPs, the counterexample to the sequence
the chapter notes. -/
theorem tinrin_not_contiguous : ¬ Contiguous {.s, .np} := by decide

end Haspelmath2007
