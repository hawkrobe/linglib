module

public import Linglib.Data.Forms.Stump2006
public import Linglib.Morphology.Paradigm.Linkage
public import Linglib.Morphology.Exponence.Domain
public import Linglib.Fragments.Slavic.Czech.Case
public import Linglib.Fragments.Slavic.Russian.Gender
public import Linglib.Syntax.Number.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.Minimal
public import Mathlib.Tactic.DeriveFintype

/-!
# Stump (2006): Heteroclisis and paradigm linkage

This file formalizes Stump's account of heteroclisis, the property of a lexeme whose
paradigm contains forms built on stems of two or more inflection classes. A rule of paradigm
linkage gives a content cell of a lexeme a form correspondent built on one of the lexeme's
stems: the universal default assigns the root, and narrower language-specific rules override
it by Pāṇini's principle, assigning a coradical, a stem that differs from the root in form or
in inflection class. The paper's rules (5), (14), (15), (17) and (18) realize every form of the
Czech nouns in its Tables 1, 6 and 8, read from the forms data. The paper measures how closely
a heteroclite paradigm's class boundary follows an inflectional category, and claims that the
categories serving as absolute correlates are privileged: every rule of paradigm linkage
sensitive to some category is sensitive to a privileged one.

## Main definitions

* `attested`: the forms of a Czech cell, every matching row of the forms data.
* `Stem`, `Entry`, `inferSoftMasc`: stems individuated by lexeme and declension, lexical
  entries, and the rule of stem inference (18).
* `CellRule`, `rulesFor`, `stemFor`: the rules of paradigm linkage (14), (15) and (17) as
  domain rules, resolved by the Elsewhere engine with the root of rule (5) as the fallback.
* `czRealize`, `czLinkage`: the realization of form cells and the Czech paradigm linkage.
* `degreeNum`, `degree`: the degree of correlation of a category with a class split.
* `IsAbsoluteCorrelate`, `IsMaximalCorrelate`, `IsCloven`, `IsFractured`,
  `IsIntersectiveCorrelate`: the paper's classification of heteroclite paradigms, over any
  cells pairing a case with a number.
* `SensitiveTo`, `Privileged`, `SatisfiesPCR`: the privileged category restriction.
* `sktLinkage`, `matLinkage`: Sanskrit HṚD(AYA) and Russian MAT'.

## Main results

* `realize_matches_tables`: the rules realize every attested form of the nine Czech nouns.
* `heteroclite_iff`, `segments_invariant`, `pramen_suppletive`: PRAMEN, PŘEDSEDA, SLUHA and
  FILOLOG are heteroclite on form-identical stems, and heteroclisis is suppletion.
* `degreeNum_eq_card_iff`: a category is an absolute correlate exactly when the class split
  factors through it.
* `pramen_degrees`, `predseda_degrees`, `sluha_degrees`, `filolog_degrees`: the paper's figures.
* `isAbsoluteCorrelate_of_rules`: rules seeing only a category make it an absolute correlate.
* `pcr`, `not_satisfiesPCR_hypothetical`: the Czech rules satisfy (40), and a case-only rule
  would violate it.
* `fractured_minimal_intersective_privileged`: claim (39) for the Czech nouns.
* `hrd_cloven_by_case`, `mat_suppletive_not_heteroclite`: suppletion with and without
  heteroclisis.

## Implementation notes

The paper writes PŘEDSEDA's root *předseda* and its coradical *předsed*; here both stems have
the segments *předsed*, the hard-feminine endings being segmented after ŽENA's *žen-*. Endings
are read off exemplars, chosen by animacy and a final back obstruent as the tables juxtapose
SLUHA with FILOLOG and MUŽ. Palatalization is witnessed only for *h* and *g*. Rules compete by
domain inclusion, the rendering of Pāṇini's principle, and the universal default (5) is the
root that selection falls back on rather than a listed rule.

## References

* [stump-2006]
* [stump-2001]
-/

@[expose] public section

namespace Stump2006

open Morphology Data.Forms Finset

/-! ### Cells and the attested forms -/

/-- The Czech numbers are the singular and the plural. -/
abbrev CzNumber : Finset Number := {.singular, .plural}

/-- A content cell of a Czech noun pairs a case of the Czech inventory with a number, gender
being constant within a paradigm. -/
abbrev CzCell : Type := Czech.Case.inventory × CzNumber

/-- `CzCell.of c n` is the cell of case `c` and number `n`. -/
def CzCell.of (c : Case) (n : Number) (hc : c ∈ Czech.Case.inventory := by decide)
    (hn : n ∈ CzNumber := by decide) : CzCell :=
  (⟨c, hc⟩, ⟨n, hn⟩)

instance : Nonempty CzCell := ⟨.of .nom .singular⟩

/-- `σ.case` is the case of the cell `σ`. -/
def CzCell.case (σ : CzCell) : Case := σ.1.1

/-- `σ.number` is the number of the cell `σ`. -/
def CzCell.number (σ : CzCell) : Number := σ.2.1

/-- `caseLabels` reads the case codes of the forms data as cases. -/
def caseLabels : List (String × Case) :=
  [("nom", .nom), ("gen", .gen), ("dat", .dat), ("acc", .acc), ("voc", .voc), ("loc", .loc),
    ("ins", .inst)]

/-- `numberLabels` reads the number codes of the forms data as numbers. -/
def numberLabels : List (String × Number) := [("sg", .singular), ("pl", .plural)]

/-- The Czech nouns of Tables 1, 6 and 8 are POKOJ 'room', PRAMEN 'spring', MOST 'bridge',
ŽENA 'woman', PŘEDSEDA 'president', FILOSOF 'philosopher', SLUHA 'servant', FILOLOG
'philologist' and MUŽ 'man'. -/
inductive CzNoun
  | pokoj
  | pramen
  | most
  | zena
  | predseda
  | filosof
  | sluha
  | filolog
  | muz
  deriving DecidableEq, Fintype, Repr

/-- `l.paramId` is the concept that the forms of `l` express in the forms data. -/
def CzNoun.paramId : CzNoun → String
  | .pokoj => "room" | .pramen => "spring" | .most => "bridge" | .zena => "woman"
  | .predseda => "president" | .filosof => "philosopher" | .sluha => "servant"
  | .filolog => "philologist" | .muz => "man"

/-- The attested forms of a cell are the segments of every row of the forms data for the noun
whose case and number codes decode to the cell's, so a cell with two alternants has two. -/
def attested (l : CzNoun) (σ : CzCell) : Finset (List String) :=
  ((Forms.all.filter fun f ↦ f.parameterId == l.paramId &&
      f.columnAs? "Case" caseLabels == some σ.case &&
      f.columnAs? "Number" numberLabels == some σ.number).map Form.segments).toFinset

/-- Every cell has an attested form, so no statement about the attested forms holds for want
of a row. -/
theorem attested_nonempty : ∀ l σ, (attested l σ).Nonempty := by decide +kernel

/-- FILOSOF's dative singular has two alternants, *filosofovi* and *filosofu*. -/
theorem filosof_cellMates : 2 ≤ (attested .filosof (.of .dat .singular)).card := by decide

/-! ### Stems and lexical entries -/

/-- The three declensions the tables juxtapose are the soft masculine, the hard masculine and
the hard feminine. -/
inductive Decl
  | softMasc
  | hardMasc
  | hardFem
  deriving DecidableEq, Fintype, Repr

/-- A stem is individuated, as in the paper, by its lexeme and its inflection class; its form
is the lexeme's, so two stems of one lexeme are class-distinct and form-identical. -/
structure Stem where
  /-- `lexeme` is the noun whose stem this is. -/
  lexeme : CzNoun
  /-- `decl` is the declension the stem inflects in. -/
  decl : Decl
  deriving DecidableEq, Repr

/-- A lexical entry records a noun's stem segments, the declension of its root, whether it
inflects as animate, and whether it belongs to the PRAMEN class of rule (14). -/
structure Entry where
  /-- `lexeme` is the noun the entry describes. -/
  lexeme : CzNoun
  /-- `segments` are the segments of the noun's stems. -/
  segments : List String
  /-- `rootDecl` is the declension of the noun's root. -/
  rootDecl : Decl
  /-- `animate` records whether the noun inflects as animate. -/
  animate : Bool
  /-- `pramenClass` records membership in the PRAMEN class, a lexical stipulation. -/
  pramenClass : Bool
  deriving DecidableEq, Repr

/-- `entry l` is the lexical entry of `l`. PRAMEN's root is soft-masculine (p. 289), PŘEDSEDA's
and SLUHA's are hard-feminine, and these three belong to the PRAMEN class. -/
def entry : CzNoun → Entry
  | .pokoj => ⟨.pokoj, ["p", "o", "k", "o", "j"], .softMasc, false, false⟩
  | .pramen => ⟨.pramen, ["p", "r", "a", "m", "e", "n"], .softMasc, false, true⟩
  | .most => ⟨.most, ["m", "o", "s", "t"], .hardMasc, false, false⟩
  | .zena => ⟨.zena, ["ž", "e", "n"], .hardFem, true, false⟩
  | .predseda => ⟨.predseda, ["p", "ř", "e", "d", "s", "e", "d"], .hardFem, true, true⟩
  | .filosof => ⟨.filosof, ["f", "i", "l", "o", "s", "o", "f"], .hardMasc, true, false⟩
  | .sluha => ⟨.sluha, ["s", "l", "u", "h"], .hardFem, true, true⟩
  | .filolog => ⟨.filolog, ["f", "i", "l", "o", "l", "o", "g"], .hardMasc, true, false⟩
  | .muz => ⟨.muz, ["m", "u", "ž"], .softMasc, true, false⟩

/-- The segments of a stem are those of its lexeme's entry. -/
def Stem.segments (z : Stem) : List String := (entry z.lexeme).segments

/-- The root of a noun, its default stem (n. 8), inflects in the root declension. -/
def Entry.root (e : Entry) : Stem := ⟨e.lexeme, e.rootDecl⟩

/-- A stem is a root when it inflects in its lexeme's root declension. -/
def Stem.IsRoot (z : Stem) : Prop := z.decl = (entry z.lexeme).rootDecl

instance : DecidablePred Stem.IsRoot := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The hard-masculine coradical of a noun of the PRAMEN class is its stem in the
hard-masculine declension. -/
def Entry.hardMascCoradical (e : Entry) : Option Stem :=
  if e.pramenClass then some ⟨e.lexeme, .hardMasc⟩ else none

/-- A noun belongs to the PŘEDSEDA subclass, "a subclass of masculine animate members of the
PRAMEN class" (p. 290), when it is an animate member of the PRAMEN class. -/
def Entry.InPredsedaSubclass (e : Entry) : Prop := e.pramenClass = true ∧ e.animate = true

instance : DecidablePred Entry.InPredsedaSubclass :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The back obstruents of Czech are *k*, *g*, *h* and *ch*. -/
def IsBackObstruent (x : String) : Prop := x ∈ ["k", "g", "h", "ch"]

instance : DecidablePred IsBackObstruent := fun x ↦ inferInstanceAs (Decidable (x ∈ _))

/-- A segment list ends in a back obstruent when its last segment is one. -/
def EndsInBackObstruent (s : List String) : Prop := ∃ x ∈ s.getLast?, IsBackObstruent x

instance : DecidablePred EndsInBackObstruent :=
  fun s ↦ inferInstanceAs (Decidable (∃ x ∈ s.getLast?, _))

/-- `inferSoftMasc` is the Czech rule of stem inference (18) (p. 292), which reads "If lexeme L
has a stem s belonging to the hard-masculine declension and s ends in a back obstruent, then L
has s′ as its soft-masculine coradical, where s′ is like s except that it belongs to the
soft-masculine declension." -/
def inferSoftMasc (z : Stem) : Option Stem :=
  if z.decl = .hardMasc ∧ EndsInBackObstruent z.segments then some { z with decl := .softMasc }
  else none

/-- The hard-masculine stem of a noun is its root if that is hard-masculine, and otherwise its
hard-masculine coradical. -/
def Entry.hardMascStem (e : Entry) : Option Stem :=
  if e.rootDecl = .hardMasc then some e.root else e.hardMascCoradical

/-- The soft-masculine coradical of a noun is the stem that rule (18) infers from its
hard-masculine stem. -/
def Entry.softMascCoradical (e : Entry) : Option Stem := e.hardMascStem.bind inferSoftMasc

/-- Rule (18) supplies a soft-masculine coradical to SLUHA, whose hard-masculine stem is a
coradical, and to FILOLOG, whose hard-masculine stem is its root, and to no other noun. -/
theorem softMascCoradical_isSome_iff :
    ∀ l, (entry l).softMascCoradical.isSome ↔ l = .sluha ∨ l = .filolog := by
  decide

/-- A hard-masculine coradical is a stem of its own noun. -/
theorem Entry.lexeme_of_mem_hardMascCoradical {e : Entry} {z : Stem}
    (hz : z ∈ e.hardMascCoradical) : z.lexeme = e.lexeme := by
  unfold Entry.hardMascCoradical at hz
  split at hz
  · cases hz; rfl
  · cases hz

/-- A soft-masculine coradical is a stem of its own noun. -/
theorem Entry.lexeme_of_mem_softMascCoradical {e : Entry} {z : Stem}
    (hz : z ∈ e.softMascCoradical) : z.lexeme = e.lexeme := by
  obtain ⟨y, hy, hz⟩ := Option.mem_bind_iff.mp hz
  have hy : y.lexeme = e.lexeme := by
    unfold Entry.hardMascStem at hy
    split at hy
    · cases hy; rfl
    · exact e.lexeme_of_mem_hardMascCoradical hy
  unfold inferSoftMasc at hz
  split at hz
  · cases hz; exact hy
  · cases hz

/-! ### Rules of paradigm linkage -/

/-- A rule of paradigm linkage, instantiated for one noun, gives the cells of its domain form
correspondents built on its exponent, a stem. Rules are ordered by Pāṇini's principle, by which
"competition between two or more morphological markings is resolved in favor of the marking
having the narrowest 'meaning'" (n. 5): a rule whose domain is included in another's is the
more specific. -/
abbrev CellRule : Type := Exponence.DomainRule CzCell Stem

/-- `plural` is the set of plural cells, `{plural X}` in the paper's notation. -/
def plural : Finset CzCell := {σ | σ.number = .plural}

/-- `datLocSg` is the set of dative and locative singular cells. -/
def datLocSg : Finset CzCell := {σ | σ.number = .singular ∧ (σ.case = .dat ∨ σ.case = .loc)}

/-- `locPl` is the locative plural cell, `{locative plural X}` in the paper's notation. -/
def locPl : Finset CzCell := {σ | σ.case = .loc ∧ σ.number = .plural}

/-- Rule (14) (p. 289) reads "Where L is a nominal lexeme that belongs to the PRAMEN class and
has s as its hard-masculine coradical, if σ = {plural X}, then the content-cell ⟨L, σ⟩ has
⟨s, σ⟩ as its form-correspondent." -/
def rule14 (e : Entry) : Option CellRule := e.hardMascCoradical.map (⟨plural, ·⟩)

/-- Rule (15) (p. 290) reads "Where L is a nominal lexeme that belongs to the PŘEDSEDA subclass
and has s as its hard-masculine coradical, if σ = {α singular X} and α = dative or locative,
then the content-cell ⟨L, σ⟩ has ⟨s, σ⟩ as its form-correspondent." -/
def rule15 (e : Entry) : Option CellRule :=
  if e.InPredsedaSubclass then e.hardMascCoradical.map (⟨datLocSg, ·⟩) else none

/-- Rule (17) (p. 292) reads "Where L is a nominal lexeme having s as its soft-masculine
coradical, if σ = {locative plural X}, then the content-cell ⟨L, σ⟩ has ⟨s, σ⟩ as its
form-correspondent." -/
def rule17 (e : Entry) : Option CellRule := e.softMascCoradical.map (⟨locPl, ·⟩)

/-- The language-specific rules of paradigm linkage applying to a noun are those of (14), (15)
and (17) whose coradicals and classes the noun has. The universal default (5) is not among
them: it is the root that `Linkage.ofRules` falls back on. -/
def rulesFor (e : Entry) : List CellRule :=
  (rule14 e).toList ++ (rule15 e).toList ++ (rule17 e).toList

/-- `czRules l` are the rules of paradigm linkage of the noun `l`. -/
def czRules (l : CzNoun) : List CellRule := rulesFor (entry l)

/-- `czRoot l` is the root of `l`, the stem that rule (5), the universal default rule of
paradigm linkage (p. 286), gives every cell that none of the rules of `l` reaches. -/
def czRoot (l : CzNoun) : Stem := (entry l).root

/-- The stem of a cell's form correspondent is the one Pāṇini's principle selects, that of an
applicable rule no applicable rule is narrower than, or the root where no rule applies. -/
def stemFor (l : CzNoun) (σ : CzCell) : Stem := Linkage.selectStem czRules czRoot l σ

/-- Every noun's entry describes that noun. -/
@[simp] theorem entry_lexeme (l : CzNoun) : (entry l).lexeme = l := by cases l <;> rfl

/-- Every rule for a noun assigns a stem of that noun. -/
theorem lexeme_stem_of_mem_rulesFor {e : Entry} {r : CellRule} (hr : r ∈ rulesFor e) :
    r.exponent.lexeme = e.lexeme := by
  simp only [rulesFor, List.mem_append, Option.mem_toList] at hr
  rcases hr with (hr | hr) | hr
  · obtain ⟨z, hz, rfl⟩ := Option.mem_map.mp hr
    exact e.lexeme_of_mem_hardMascCoradical hz
  · unfold rule15 at hr
    split at hr
    · obtain ⟨z, hz, rfl⟩ := Option.mem_map.mp hr
      exact e.lexeme_of_mem_hardMascCoradical hz
    · cases hr
  · obtain ⟨z, hz, rfl⟩ := Option.mem_map.mp hr
    exact e.lexeme_of_mem_softMascCoradical hz

/-- A noun's cells are all built on its own stems. -/
theorem stemFor_lexeme (l : CzNoun) (σ : CzCell) : (stemFor l σ).lexeme = l :=
  Linkage.selectStem_induction (fun z ↦ z.lexeme = l) (entry_lexeme l)
    fun _ hr ↦ (lexeme_stem_of_mem_rulesFor hr).trans (entry_lexeme l)

/-! ### Realization -/

/-- Palatalization replaces a stem-final velar, *h* and *g* by *z* as Table 8's *sluzích* and
*filolozích* witness, and *k* by *c* and *ch* by *š*, which the tables do not witness. -/
def palatalize (s : List String) : List String :=
  match s.getLast? with
  | some "h" | some "g" => s.dropLast ++ ["z"]
  | some "k" => s.dropLast ++ ["c"]
  | some "ch" => s.dropLast ++ ["š"]
  | _ => s

/-- `exemplar d a v` is the exemplar of the declension `d` for animacy `a` and a final back
obstruent `v`: POKOJ and MUŽ for the soft masculine, MOST, FILOSOF and FILOLOG for the hard
masculine, and ŽENA for the hard feminine. -/
def exemplar : Decl → Bool → Bool → CzNoun
  | .softMasc, false, _ => .pokoj
  | .softMasc, true, _ => .muz
  | .hardMasc, false, _ => .most
  | .hardMasc, true, false => .filosof
  | .hardMasc, true, true => .filolog
  | .hardFem, _, _ => .zena

/-- Each exemplar's root inflects in the declension it exemplifies. -/
theorem exemplar_rootDecl : ∀ d a v, (entry (exemplar d a v)).rootDecl = d := by decide

/-- Wherever an exemplar inflects on its root, its root's segments begin each of its forms, so
removing them leaves an ending. -/
theorem exemplar_root_isPrefix : ∀ d a v σ, (stemFor (exemplar d a v) σ).IsRoot →
    ∀ w ∈ attested (exemplar d a v) σ, (entry (exemplar d a v)).segments <+: w := by
  decide +kernel

/-- The endings of a declension at a cell are its exemplar's forms there, less the
exemplar's root. -/
def ending (d : Decl) (animate velar : Bool) (σ : CzCell) : Finset (List String) :=
  (attested (exemplar d animate velar) σ).image
    (List.drop (entry (exemplar d animate velar)).segments.length)

/-- The endings of a stem at a cell are its declension's, except that the -u alternating with
-ovi is "restricted to roots belonging to the hard-masculine declension" (n. 14). -/
def Stem.endings (z : Stem) (σ : CzCell) : Finset (List String) :=
  let ends := ending z.decl (entry z.lexeme).animate (decide (EndsInBackObstruent z.segments)) σ
  if ¬ z.IsRoot ∧ ["o", "v", "i"] ∈ ends then ends.erase ["u"] else ends

/-- The base of a stem is its segments, palatalized in the soft-masculine declension. -/
def Stem.base (z : Stem) : List String :=
  if z.decl = .softMasc then palatalize z.segments else z.segments

/-- The form cell `⟨z, σ⟩` is realized as the base of `z` followed by each of its endings. -/
def czRealize (z : Stem) (σ : CzCell) : Finset (List String) := (z.endings σ).image (z.base ++ ·)

/-- The Czech paradigm linkage gives each content cell the stem its rules select, and
preserves its property set. -/
def czLinkage : Linkage CzNoun Stem CzCell CzCell := Linkage.ofRules id czRules czRoot

/-- Each cell's selected stem realizes exactly the attested forms. -/
theorem czRealize_stemFor : ∀ l σ, czRealize (stemFor l σ) σ = attested l σ := by
  decide +kernel

/-- The rules of paradigm linkage realize every form of Tables 1, 6 and 8. -/
theorem realize_matches_tables (l : CzNoun) (σ : CzCell) :
    czLinkage.realized czRealize l σ = {(attested l σ, σ)} :=
  (Linkage.ofFun_realized _ _ czRealize l σ).trans <|
    congrArg (fun w ↦ {(w, σ)}) (czRealize_stemFor l σ)

/-- The hard-masculine coradical of a noun of the PŘEDSEDA subclass realizes the dative and
locative singular with -ovi alone, the prediction of n. 14 that *předsed* and *sluh* lack the
-u alternant. -/
theorem coradical_no_u : ∀ l, (entry l).InPredsedaSubclass → ∀ σ ∈ datLocSg,
    czRealize ⟨l, .hardMasc⟩ σ = {(entry l).segments ++ ["o", "v", "i"]} := by
  decide

/-! ### Heteroclisis -/

/-- `cellClass l σ` is the declension that the cell `σ` of `l` inflects in. -/
def cellClass (l : CzNoun) (σ : CzCell) : Decl := (stemFor l σ).decl

/-- PRAMEN is heteroclite, its paradigm drawing on stems of two declensions. -/
theorem pramen_heteroclite : czLinkage.IsHeteroclite Stem.decl .pramen := by decide

/-- Exactly PRAMEN, PŘEDSEDA, SLUHA and FILOLOG are heteroclite. -/
theorem heteroclite_iff : ∀ l, czLinkage.IsHeteroclite Stem.decl l ↔
    l = .pramen ∨ l = .predseda ∨ l = .sluha ∨ l = .filolog := by
  decide +kernel

/-- Every noun's stems share their segments, so the heteroclite nouns alternate between stems
that differ in declension alone. -/
theorem segments_invariant (l : CzNoun) : czLinkage.IsInvariantAlong Stem.segments l :=
  Linkage.ofFun_isInvariantAlong_iff.mpr fun σ σ' ↦
    show (stemFor l σ).segments = (stemFor l σ').segments by
      simp only [Stem.segments, stemFor_lexeme]

/-- PRAMEN's paradigm "exhibits a kind of stem suppletion" (pp. 282–283), since its two stems,
though phonologically identical, are two stems. -/
theorem pramen_suppletive : czLinkage.IsSuppletive .pramen := pramen_heteroclite.isSuppletive

/-! ### The degree of correlation -/

section Correlation

variable {C V K : Type*} [Fintype C] [Fintype V] [Fintype K] [DecidableEq V] [DecidableEq K]

/-- `degreeNum A cls` is the numerator of the degree of `A`-correlation (p. 309), the sum over
the values `v` of `A` of "the largest number of cells in P that carry the specification v and
inflect as members of the same inflection class". -/
def degreeNum (A : C → V) (cls : C → K) : ℕ :=
  ∑ v, univ.sup fun k ↦ #{σ | A σ = v ∧ cls σ = k}

omit [Fintype V] in
private theorem sup_card_le_card_fiber (A : C → V) (cls : C → K) (v : V) :
    univ.sup (fun k ↦ #{σ | A σ = v ∧ cls σ = k}) ≤ #{σ | A σ = v} :=
  Finset.sup_le fun _ _ ↦ card_le_card fun σ ↦ by simp +contextual

/-- The count never exceeds the number of cells. -/
theorem degreeNum_le_card (A : C → V) (cls : C → K) : degreeNum A cls ≤ Fintype.card C := by
  rw [← card_univ, card_eq_sum_card_fiberwise (f := A) (t := univ) (by simp)]
  exact sum_le_sum fun v _ ↦ sup_card_le_card_fiber A cls v

/-- The count is the number of cells exactly when the class split factors through the
category. -/
theorem degreeNum_eq_card_iff (A : C → V) (cls : C → K) :
    degreeNum A cls = Fintype.card C ↔ cls.FactorsThrough A := by
  rw [← card_univ, card_eq_sum_card_fiberwise (f := A) (t := univ) (by simp), degreeNum,
    sum_eq_sum_iff_of_le fun v _ ↦ sup_card_le_card_fiber A cls v]
  constructor
  · intro h σ τ hστ
    obtain ⟨k, -, hk⟩ := exists_mem_eq_sup univ ⟨cls σ, mem_univ _⟩
      fun k ↦ #{σ' | A σ' = A σ ∧ cls σ' = k}
    have hcard := h (A σ) (mem_univ _)
    rw [hk] at hcard
    have hsub := eq_of_subset_of_card_le (s := {σ' | A σ' = A σ ∧ cls σ' = k})
      (t := {σ' | A σ' = A σ}) (fun x ↦ by simp +contextual) hcard.ge
    have h₁ : σ ∈ ({σ' | A σ' = A σ ∧ cls σ' = k} : Finset C) := hsub ▸ by simp
    have h₂ : τ ∈ ({σ' | A σ' = A σ ∧ cls σ' = k} : Finset C) := hsub ▸ by simp [hστ]
    rw [(by simpa using h₁ : cls σ = k), (by simpa [hστ] using h₂ : cls τ = k)]
  · intro h v _
    refine le_antisymm (sup_card_le_card_fiber A cls v) ?_
    rcases ({σ | A σ = v} : Finset C).eq_empty_or_nonempty with he | ⟨σ, hσ⟩
    · simp [he]
    · refine le_trans (le_of_eq ?_) (le_sup (mem_univ (cls σ)))
      congr 1
      ext τ
      simp only [mem_filter, mem_univ, true_and] at hσ ⊢
      exact ⟨fun hτ ↦ ⟨hτ, h (hτ.trans hσ.symm)⟩, And.left⟩

/-- The degree of `A`-correlation (p. 309) is the count over the number of cells. -/
def degree (A : C → V) (cls : C → K) : ℚ := degreeNum A cls / Fintype.card C

/-- The degree is one exactly when the class split factors through the category. -/
theorem degree_eq_one_iff [Nonempty C] {A : C → V} {cls : C → K} :
    degree A cls = 1 ↔ cls.FactorsThrough A := by
  rw [degree, div_eq_one_iff_eq (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), Nat.cast_inj,
    degreeNum_eq_card_iff]

end Correlation

/-! ### Correlates of heteroclisis

The paper's classification of heteroclite paradigms applies to any cells pairing a case in `A`
with a number in `B`, and to any class map `cls` giving the inflection class of each cell. -/

section Correlates

variable {A B K L E : Type*}

/-- The inflectional categories of a noun are number and case. -/
inductive Category
  | number
  | case
  deriving DecidableEq, Fintype, Repr

/-- `c.proj σ` is the value of the category `c` at the cell `σ`. -/
def Category.proj : Category → A × B → A ⊕ B
  | .number, σ => .inr σ.2
  | .case, σ => .inl σ.1

/-- `c.other` is the category other than `c`. -/
def Category.other : Category → Category
  | .number => .case
  | .case => .number

@[simp] theorem Category.other_other (c : Category) : c.other.other = c := by cases c <;> rfl

/-- A category is an absolute correlate of a paradigm's heteroclisis "if and only if the degree
of A-correlation in that paradigm is 1.0" (p. 309), that is, when the paradigm's class split
factors through the category. -/
def IsAbsoluteCorrelate (c : Category) (cls : A × B → K) : Prop := cls.FactorsThrough c.proj

/-- A paradigm is cloven when it is heteroclite, two of its cells inflecting in distinct
classes, and has an absolute correlate (p. 309). -/
def IsCloven (cls : A × B → K) : Prop :=
  (∃ σ τ, cls σ ≠ cls τ) ∧ ∃ c, IsAbsoluteCorrelate c cls

/-- A paradigm is fractured when it is heteroclite, two of its cells inflecting in distinct
classes, and lacks any absolute correlate (p. 309). -/
def IsFractured (cls : A × B → K) : Prop :=
  (∃ σ τ, cls σ ≠ cls τ) ∧ ∀ c, ¬ IsAbsoluteCorrelate c cls

/-- A class split factoring through both categories is constant. -/
theorem cellClass_eq_of_isAbsoluteCorrelate {cls : A × B → K}
    (hn : IsAbsoluteCorrelate .number cls) (hc : IsAbsoluteCorrelate .case cls) (σ τ : A × B) :
    cls σ = cls τ :=
  (hc (a := σ) (b := (σ.1, τ.2)) rfl).trans (hn rfl)

/-- `projOn S σ` records the values at `σ` of the categories in `S`. -/
def projOn (S : Finset Category) (σ : A × B) : Option A × Option B :=
  (if .case ∈ S then some σ.1 else none, if .number ∈ S then some σ.2 else none)

/-- Categories are intersective correlates of a paradigm's heteroclisis when "for each
well-formed property set τ specified for exactly the categories A₁, . . . , A_n there is a
single inflection class C such that every cell in P realizing τ inflects as a member of C"
(p. 313). -/
def IsIntersectiveCorrelate (cls : A × B → K) (S : Finset Category) : Prop :=
  cls.FactorsThrough (projOn S)

/-- Cells agreeing in more categories agree in fewer. -/
theorem projOn_eq_of_subset {S T : Finset Category} (hST : S ⊆ T) {σ τ : A × B}
    (h : projOn T σ = projOn T τ) : projOn S σ = projOn S τ := by
  simp only [projOn, Prod.mk.injEq] at h ⊢
  refine ⟨?_, ?_⟩
  · by_cases hc : Category.case ∈ S
    · simpa [hc, hST hc] using h.1
    · simp [hc]
  · by_cases hn : Category.number ∈ S
    · simpa [hn, hST hn] using h.2
    · simp [hn]

/-- Adding categories to intersective correlates keeps them intersective correlates. -/
theorem IsIntersectiveCorrelate.mono {cls : A × B → K} {S T : Finset Category}
    (h : IsIntersectiveCorrelate cls S) (hST : S ⊆ T) : IsIntersectiveCorrelate cls T :=
  fun _ _ hστ ↦ h (projOn_eq_of_subset hST hστ)

/-- A single category is an intersective correlate exactly when it is an absolute one. -/
theorem isIntersectiveCorrelate_singleton_iff {cls : A × B → K} {c : Category} :
    IsIntersectiveCorrelate cls {c} ↔ IsAbsoluteCorrelate c cls := by
  have key : ∀ σ τ : A × B, projOn {c} σ = projOn {c} τ ↔ c.proj σ = c.proj τ := by
    intro σ τ; cases c <;> simp [projOn, Category.proj]
  exact ⟨fun h _ _ hστ ↦ h ((key _ _).mpr hστ), fun h _ _ hστ ↦ h ((key _ _).mp hστ)⟩

/-- Both categories together are an intersective correlate of every paradigm. -/
theorem isIntersectiveCorrelate_univ (cls : A × B → K) : IsIntersectiveCorrelate cls univ :=
  fun σ τ h ↦ by
    simp only [projOn, mem_univ, ↓reduceIte, Prod.mk.injEq, Option.some.injEq] at h
    rw [Prod.ext h.1 h.2]

/-- The minimal intersective correlate of a fractured paradigm is the pair of both
categories. -/
theorem minimal_univ_of_isFractured {cls : A × B → K} (h : IsFractured cls) :
    Minimal (IsIntersectiveCorrelate cls) univ := by
  refine ⟨isIntersectiveCorrelate_univ cls, fun S hS _ ↦ ?_⟩
  by_contra hne
  obtain ⟨c, -, hc⟩ := not_subset.mp hne
  refine h.2 c.other (isIntersectiveCorrelate_singleton_iff.mp (hS.mono fun x hx ↦ ?_))
  exact mem_singleton.mpr (by cases x <;> cases c <;> first | rfl | exact absurd hx hc)

/-- A rule is sensitive to the value of a category when its applicability does not factor
through the other category. -/
def SensitiveTo (r : Exponence.DomainRule (A × B) E) (c : Category) : Prop :=
  ¬ (Exponence.Applies r).FactorsThrough c.other.proj

/-- A category is privileged for a family `cls` of class maps, one for each lexeme, when it
serves as an absolute correlate of a cloven paradigm: "the inflectional categories serving as
absolute correlates of heteroclisis in a given language are PRIVILEGED" (p. 315). -/
def Privileged (cls : L → A × B → K) (c : Category) : Prop :=
  ∃ l, IsCloven (cls l) ∧ IsAbsoluteCorrelate c (cls l)

/-- A system of rules satisfies the privileged category restriction (40) (p. 316), which reads
"If a rule of paradigm linkage applies to lexemes belonging to a privileged syntactic category C
and this rule is sensitive to the value of any inflectional category, then it is sensitive to
the value of a privileged inflectional category for members of C." The lexemes `L` are taken to
form one privileged syntactic category, so the antecedent on the syntactic category is left
implicit. -/
def SatisfiesPCR (cls : L → A × B → K) (rules : L → List (Exponence.DomainRule (A × B) E)) :
    Prop :=
  ∀ l, ∀ r ∈ rules l, (∃ c, SensitiveTo r c) → ∃ c, Privileged cls c ∧ SensitiveTo r c

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- A category is a maximal correlate when its degree "is higher than any other inflectional
category's degree of correlation in that paradigm" (p. 309). -/
def IsMaximalCorrelate [Fintype K] [DecidableEq K] (c : Category) (cls : A × B → K) : Prop :=
  ∀ c' ≠ c, degreeNum c'.proj cls < degreeNum c.proj cls

/-- A category is an absolute correlate exactly when its degree of correlation is one. -/
theorem isAbsoluteCorrelate_iff_degree [Fintype K] [DecidableEq K] [Nonempty (A × B)]
    {c : Category} {cls : A × B → K} : IsAbsoluteCorrelate c cls ↔ degree c.proj cls = 1 :=
  degree_eq_one_iff.symm

/-- An absolute correlate of a heteroclite paradigm is its maximal correlate. -/
theorem IsAbsoluteCorrelate.isMaximalCorrelate [Fintype K] [DecidableEq K] {c : Category}
    {cls : A × B → K} (hl : ∃ σ τ, cls σ ≠ cls τ) (h : IsAbsoluteCorrelate c cls) :
    IsMaximalCorrelate c cls := by
  intro c' hc'
  rw [(degreeNum_eq_card_iff _ _).mpr h]
  refine (degreeNum_le_card _ _).lt_of_ne fun hEq ↦ ?_
  have h' : IsAbsoluteCorrelate c' cls := (degreeNum_eq_card_iff _ _).mp hEq
  obtain ⟨σ, τ, hne⟩ := hl
  apply hne
  cases c <;> cases c'
  · exact absurd rfl hc'
  · exact cellClass_eq_of_isAbsoluteCorrelate h h' σ τ
  · exact cellClass_eq_of_isAbsoluteCorrelate h' h σ τ
  · exact absurd rfl hc'

variable [DecidableEq K]

instance (c : Category) (cls : A × B → K) : Decidable (IsAbsoluteCorrelate c cls) :=
  inferInstanceAs (Decidable (∀ σ τ, c.proj σ = c.proj τ → cls σ = cls τ))

instance [Fintype K] (c : Category) (cls : A × B → K) : Decidable (IsMaximalCorrelate c cls) :=
  inferInstanceAs (Decidable (∀ _, _ → _))

instance (cls : A × B → K) : Decidable (IsCloven cls) := inferInstanceAs (Decidable (_ ∧ _))

instance (cls : A × B → K) : Decidable (IsFractured cls) := inferInstanceAs (Decidable (_ ∧ _))

instance (r : Exponence.DomainRule (A × B) E) (c : Category) : Decidable (SensitiveTo r c) :=
  inferInstanceAs (Decidable (¬ _))

instance [Fintype L] (cls : L → A × B → K) (c : Category) : Decidable (Privileged cls c) :=
  inferInstanceAs (Decidable (∃ _, _))

instance [Fintype L] (cls : L → A × B → K) (rules : L → List (Exponence.DomainRule (A × B) E)) :
    Decidable (SatisfiesPCR cls rules) :=
  have (r : Exponence.DomainRule (A × B) E) :
      Decidable ((∃ c, SensitiveTo r c) → ∃ c, Privileged cls c ∧ SensitiveTo r c) :=
    inferInstance
  inferInstanceAs (Decidable (∀ _, _))

end Correlates

/-! ### Correlates of Czech heteroclisis -/

/-- PRAMEN's degree of number correlation is 14/14 and its degree of case correlation .50. -/
theorem pramen_degrees : degree Category.number.proj (cellClass .pramen) = 1 ∧
    degree Category.case.proj (cellClass .pramen) = 1 / 2 := by
  decide +kernel

/-- PŘEDSEDA's degree of number correlation is .86 (= 12/14) and its degree of case
correlation .64. -/
theorem predseda_degrees : degree Category.number.proj (cellClass .predseda) = 6 / 7 ∧
    degree Category.case.proj (cellClass .predseda) = 9 / 14 := by
  decide +kernel

/-- SLUHA's degree of number correlation is .79 (= 11/14) and its degree of case correlation
.57. -/
theorem sluha_degrees : degree Category.number.proj (cellClass .sluha) = 11 / 14 ∧
    degree Category.case.proj (cellClass .sluha) = 4 / 7 := by
  decide +kernel

/-- FILOLOG's degrees of number and of case correlation are both .93 (= 13/14) (p. 313). -/
theorem filolog_degrees : degree Category.number.proj (cellClass .filolog) = 13 / 14 ∧
    degree Category.case.proj (cellClass .filolog) = 13 / 14 := by
  decide +kernel

/-- PRAMEN's paradigm is cloven. -/
theorem pramen_cloven : IsCloven (cellClass .pramen) := by decide

/-- PŘEDSEDA's paradigm is fractured. -/
theorem predseda_fractured : IsFractured (cellClass .predseda) := by decide

/-- SLUHA's paradigm is fractured. -/
theorem sluha_fractured : IsFractured (cellClass .sluha) := by decide

/-- FILOLOG's paradigm is fractured. -/
theorem filolog_fractured : IsFractured (cellClass .filolog) := by decide

/-- Number is a maximal correlate of heteroclisis in the fractured paradigms of PŘEDSEDA and
SLUHA, as (38) (p. 312) has it: "just as number is the absolute correlate of heteroclisis in
the cloven paradigm of Czech PRAMEN, it is likewise the maximal correlate of heteroclisis in the
fractured paradigms of PŘEDSEDA and SLUHA." -/
theorem number_maximal_predseda_sluha :
    IsMaximalCorrelate .number (cellClass .predseda) ∧
      IsMaximalCorrelate .number (cellClass .sluha) := by
  decide

/-- FILOLOG's fractured paradigm has no maximal correlate (p. 313), so (38), by which maximal
correlates of fractured paradigms "tend to be" the absolute correlates of cloven ones, states a
tendency. -/
theorem filolog_no_maximal : ∀ c, ¬ IsMaximalCorrelate c (cellClass .filolog) := by decide

/-! ### Rules sensitive to a category -/

/-- Rules whose applicability sees only `A` make a noun's class split factor through `A`. So
by (41a), number "would be an absolute correlate of heteroclisis in the cloven paradigms of
type-I verbal lexemes" (p. 317). -/
theorem isAbsoluteCorrelate_of_rules {V : Type*} (l : CzNoun) (A : CzCell → V)
    (h : ∀ r ∈ czRules l, (Exponence.Applies r).FactorsThrough A) :
    (fun σ ↦ (stemFor l σ).decl).FactorsThrough A :=
  Linkage.selectStem_factorsThrough Stem.decl fun r hr _ _ hA ↦ Iff.of_eq (h r hr hA)

/-- A category is an absolute correlate of a noun's paradigm when none of its rules is
sensitive to the other category. -/
theorem isAbsoluteCorrelate_of_forall_not_sensitiveTo {c : Category} {l : CzNoun}
    (h : ∀ r ∈ czRules l, ¬ SensitiveTo r c.other) : IsAbsoluteCorrelate c (cellClass l) :=
  isAbsoluteCorrelate_of_rules _ _ fun r hr ↦ by simpa [SensitiveTo] using h r hr

/-- Number is an absolute correlate of PRAMEN's heteroclisis because (14), its one
language-specific rule, is insensitive to case, as is the default (5). -/
theorem pramen_number_absolute : IsAbsoluteCorrelate .number (cellClass .pramen) :=
  isAbsoluteCorrelate_of_forall_not_sensitiveTo (by decide)

/-- Number is a maximal correlate of heteroclisis in PRAMEN's paradigm, as of any paradigm it
is an absolute correlate of. -/
theorem number_maximal_pramen : IsMaximalCorrelate .number (cellClass .pramen) :=
  pramen_number_absolute.isMaximalCorrelate pramen_cloven.1

/-! ### The privileged category restriction -/

/-- Number is privileged for Czech nouns. -/
theorem privileged_number : Privileged cellClass .number :=
  ⟨.pramen, pramen_cloven, pramen_number_absolute⟩

/-- Case is not privileged, for "in Czech, for example, number is the only privileged
inflectional category among the categories relevant for nominal inflection" (p. 316). -/
theorem not_privileged_case : ¬ Privileged cellClass .case := by decide +kernel

/-- The Czech rules satisfy (40), since (14) is sensitive to number and (15) and (17), though
sensitive to case, are "also sensitive to the value of the privileged inflectional category for
nouns" (p. 316). -/
theorem pcr : SatisfiesPCR cellClass czRules := by decide +kernel

/-- `genitive` is the set of genitive cells. -/
def genitive : Finset CzCell := {σ | σ.case = .gen}

/-- A hypothetical system adds to the Czech rules one giving the genitive cells of the
PŘEDSEDA subclass the hard-masculine coradical, a rule sensitive to case alone. It is modelled
on the paper's hypothetical (41) and Table 26, whose type-II rule is sensitive to tense and
person but not number; it leaves PRAMEN, and so the privilege of number, untouched. -/
def hypothetical (e : Entry) : List CellRule :=
  rulesFor e ++
    (if e.InPredsedaSubclass then (e.hardMascCoradical.map (⟨genitive, ·⟩)).toList else [])

/-- The hypothetical system violates (40), so the restriction is not vacuous. -/
theorem not_satisfiesPCR_hypothetical : ¬ SatisfiesPCR cellClass (hypothetical ∘ entry) := by
  decide +kernel

/-- Claim (39) (p. 313) holds for Czech nouns, every fractured paradigm having a privileged
category among its minimal intersective correlates. The claim "is trivially true of fractured
paradigms in which only two inflectional categories are distinguished" (p. 313), as here. -/
theorem fractured_minimal_intersective_privileged {l : CzNoun}
    (h : IsFractured (cellClass l)) :
    ∃ S, Minimal (IsIntersectiveCorrelate (cellClass l)) S ∧ ∃ c ∈ S, Privileged cellClass c :=
  ⟨univ, minimal_univ_of_isFractured h, .number, mem_univ _, privileged_number⟩

/-! ### Sanskrit HṚD(AYA) (Table 4) -/

/-- The Sanskrit cases are the nominative, vocative, accusative, instrumental, dative, ablative,
genitive and locative. -/
abbrev SktCase : Finset Case := {.nom, .voc, .acc, .inst, .dat, .abl, .gen, .loc}

/-- The Sanskrit numbers are the singular, the dual and the plural. -/
abbrev SktNumber : Finset Number := {.singular, .dual, .plural}

/-- A Sanskrit content cell pairs a case with a number. -/
abbrev SktCell : Type := SktCase × SktNumber

instance : Nonempty SktCell := ⟨(⟨.nom, by decide⟩, ⟨.singular, by decide⟩)⟩

/-- The declensions of HṚD(AYA)'s stems are the neuter a-stem and the neuter consonant-stem
declensions. -/
inductive SktDecl
  | aStem
  | consStem
  deriving DecidableEq, Fintype, Repr

/-- HṚD(AYA) has the stems *hṛdaya* and *hṛd*. -/
inductive SktStem
  | hrdaya
  | hrd
  deriving DecidableEq, Fintype, Repr

/-- `z.form` is the form of the stem `z`. -/
def SktStem.form : SktStem → String
  | .hrdaya => "hṛdaya"
  | .hrd => "hṛd"

/-- A stem's declension follows its final segment, for "because hṛdaya is a neuter stem ending in
a, it follows the neuter a-stem declension ..., but because hṛd is a neuter stem ending in a
consonant, it instead follows the neuter consonant-stem declension" (p. 282). -/
def SktStem.decl : SktStem → SktDecl
  | .hrdaya => .aStem
  | .hrd => .consStem

/-- HṚD(AYA) is the one Sanskrit lexeme considered. -/
inductive SktNoun
  | hrdaya
  deriving DecidableEq, Fintype, Repr

/-- The direct cases are the nominative, vocative and accusative. -/
abbrev direct : Finset Case := {.nom, .voc, .acc}

/-- `hrdStem σ` is the stem of the cell `σ`, since "the direct ... case forms of HṚD(AYA) are
built on the stem hṛdaya, while its remaining, oblique case forms are built on the stem hṛd"
(p. 282). -/
def hrdStem (σ : SktCell) : SktStem := if σ.1.1 ∈ direct then .hrdaya else .hrd

/-- `sktLinkage` is the paradigm linkage of HṚD(AYA). -/
def sktLinkage : Linkage SktNoun SktStem SktCell SktCell := Linkage.ofFun id fun _ ↦ hrdStem

/-- HṚD(AYA) is heteroclite. -/
theorem hrd_heteroclite : sktLinkage.IsHeteroclite SktStem.decl .hrdaya := by decide

/-- HṚD(AYA)'s stems also differ in form, its heteroclisis being an effect of stem suppletion,
unlike PRAMEN's (`segments_invariant`). -/
theorem hrd_form_suppletive : sktLinkage.IsHeteroclite SktStem.form .hrdaya := by decide

/-- Case is an absolute correlate of HṚD(AYA)'s heteroclisis and number is not, so its
paradigm is cloven, as the paper counts it (p. 313), and "in Sanskrit, for example, cloven noun
paradigms have case as their absolute correlate" (p. 310). -/
theorem hrd_cloven_by_case :
    degree (fun σ : SktCell ↦ σ.1) (fun σ ↦ (hrdStem σ).decl) = 1 ∧
      degree (fun σ : SktCell ↦ σ.2) (fun σ ↦ (hrdStem σ).decl) ≠ 1 :=
  ⟨degree_eq_one_iff.mpr (by decide), mt degree_eq_one_iff.mp (by decide)⟩

/-! ### Russian MAT' (Table 5) -/

/-- The Russian numbers are the singular and the plural. -/
abbrev RuNumber : Finset Number := {.singular, .plural}

/-- A Russian content cell pairs a case of the six-case core with a number; the prepositional
is the locative. -/
abbrev RuCell : Type := Slavic.Case.coreInventory × RuNumber

/-- MAT' is the one Russian lexeme considered. -/
inductive RuNoun
  | mat
  deriving DecidableEq, Fintype, Repr

/-- MAT' has "a radical stem mat' in the singular direct-case forms and an extended stem
mater' elsewhere" (p. 283). -/
inductive RuStem
  | mat
  | mater
  deriving DecidableEq, Fintype, Repr

/-- Both stems of MAT' follow the third declension (p. 283). -/
def RuStem.decl : RuStem → Russian.Gender.DeclClass
  | .mat => .III
  | .mater => .III

/-- `matLinkage` builds MAT' on *mat'* in the nominative and accusative singular and on
*mater'* elsewhere. -/
def matLinkage : Linkage RuNoun RuStem RuCell RuCell :=
  Linkage.ofFun id fun _ σ ↦
    if σ.2.1 = .singular ∧ (σ.1.1 = .nom ∨ σ.1.1 = .acc) then .mat else .mater

/-- MAT' is suppletive but not heteroclite, for "suppletion in itself does not necessitate
heteroclisis" (p. 283). -/
theorem mat_suppletive_not_heteroclite :
    matLinkage.IsSuppletive .mat ∧ ¬ matLinkage.IsHeteroclite RuStem.decl .mat := by
  decide

end Stump2006
