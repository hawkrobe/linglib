import Linglib.Morphology.Paradigm.Linkage
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma

/-!
# Stump 2006: heteroclisis and paradigm linkage
[stump-2006]

Heteroclisis — a lexeme whose paradigm draws on two or more inflection classes —
regulated by rules of paradigm linkage. The universal default rule (5) links each
content cell `⟨L, σ⟩` to `⟨root L, σ⟩`; a heteroclite lexeme carries an override
(the shape of the Czech rule (14)) routing part of its paradigm to a coradical of
a different class.

**Czech PRAMEN 'spring'** (Table 1, after Heim 1982): singular cells inflect
soft-masculine (like POKOJ 'room'), plural cells hard-masculine (like MOST
'bridge'). The two stems are phonologically identical — [stump-2006] holds that
the paradigm still "exhibits a kind of stem alternation", the stems differing in
class alone; footnote 5 defends class-distinct, form-identical stem alternants
against the No Blur Principle. Formally: the linkage is invariant along the form
projection yet heteroclite along the class projection
(`heteroclisis_without_form_suppletion`), and heteroclisis entails stem
non-invariance (`Linkage.IsHeteroclite.isSuppletive`).

**Sanskrit HR̥D(AYA) 'heart'** (Table 4): direct-case cells are built on
*hr̥daya* (neuter a-stem declension, like ĀSYA), oblique cells on *hr̥d*
(neuter consonant-stem declension) — heteroclisis riding on genuine stem
suppletion, occupying the grid cell PRAMEN leaves empty. Together the two
lexemes witness that form-invariance and class-invariance are independent
below stem invariance.

## Main results

* `realize_matches_table1` — the rule-(5)-plus-override linkage reproduces all
  42 word forms of Table 1 for POKOJ, MOST, and PRAMEN
* `pramen_heteroclite` / `heteroclisis_without_form_suppletion` — PRAMEN is
  heteroclite with phonologically constant stems
* `pramen_stem_alternation` — the entailment instance: PRAMEN's linkage is
  suppletive in the broad sense (two stems) despite form identity
* `hrd_heteroclite_and_form_suppletive` — HR̥D(AYA) is heteroclite *and*
  form-suppletive
* `soft_hard_contrast` — the two declensions PRAMEN juxtaposes ordinarily
  contrast, so its split is detectable cell by cell
-/

namespace Stump2006

open Morphology

/-! ### Czech: the two masculine declensions of Table 1 -/

/-- The two Czech masculine inanimate declensions Table 1 juxtaposes. -/
inductive Decl | softMasc | hardMasc
  deriving DecidableEq, Fintype, Repr

/-- The seven Czech cases, in Table 1's row order. -/
inductive Case | nom | gen | dat | acc | voc | loc | ins
  deriving DecidableEq, Fintype, Repr

/-- Grammatical number. -/
inductive Num | sg | pl
  deriving DecidableEq, Fintype, Repr

/-- A content cell: case and number (masculine gender held constant). -/
structure CzCell where
  case : Case
  num : Num
  deriving DecidableEq, Fintype, Repr

/-- The three lexemes of Table 1. -/
inductive CzNoun | pokoj | most | pramen
  deriving DecidableEq, Fintype, Repr

/-- The stem inventory: one stem each for POKOJ and MOST, and PRAMEN's two
class-distinct coradicals. `pramenS` and `pramenH` are distinct stems sharing a
phonological form — the alternant pair of [stump-2006]'s footnote 5. -/
inductive CzStem | pokoj | most | pramenS | pramenH
  deriving DecidableEq, Fintype, Repr

/-- A stem's phonological form. -/
def CzStem.form : CzStem → String
  | .pokoj => "pokoj"
  | .most => "most"
  | .pramenS => "pramen"
  | .pramenH => "pramen"

/-- A stem's inflection-class membership — the projection heteroclisis is stated
along. -/
def CzStem.decl : CzStem → Decl
  | .pokoj => .softMasc
  | .most => .hardMasc
  | .pramenS => .softMasc
  | .pramenH => .hardMasc

/-- Each lexeme's root, as stipulated lexically (rule (5) reads it off). -/
def root : CzNoun → CzStem
  | .pokoj => .pokoj
  | .most => .most
  | .pramen => .pramenS

/-- The linkage: the universal default rule (5) routes every cell to the root;
PRAMEN's plural cells carry the override of the shape of rule (14), routing them
to the hard-masculine coradical. -/
def czLinkage : Linkage CzNoun CzStem CzCell where
  stems
    | .pramen, ⟨_, .pl⟩ => {.pramenH}
    | n, _ => {root n}
  pm := fun _ σ => σ

/-- The case/number endings of the two declensions, read off Table 1's POKOJ and
MOST columns. -/
def ending : Decl → CzCell → String
  | .softMasc, ⟨.nom, .sg⟩ => "" | .softMasc, ⟨.gen, .sg⟩ => "e"
  | .softMasc, ⟨.dat, .sg⟩ => "i" | .softMasc, ⟨.acc, .sg⟩ => ""
  | .softMasc, ⟨.voc, .sg⟩ => "i" | .softMasc, ⟨.loc, .sg⟩ => "i"
  | .softMasc, ⟨.ins, .sg⟩ => "em"
  | .softMasc, ⟨.nom, .pl⟩ => "e" | .softMasc, ⟨.gen, .pl⟩ => "ů"
  | .softMasc, ⟨.dat, .pl⟩ => "ům" | .softMasc, ⟨.acc, .pl⟩ => "e"
  | .softMasc, ⟨.voc, .pl⟩ => "e" | .softMasc, ⟨.loc, .pl⟩ => "ích"
  | .softMasc, ⟨.ins, .pl⟩ => "i"
  | .hardMasc, ⟨.nom, .sg⟩ => "" | .hardMasc, ⟨.gen, .sg⟩ => "u"
  | .hardMasc, ⟨.dat, .sg⟩ => "u" | .hardMasc, ⟨.acc, .sg⟩ => ""
  | .hardMasc, ⟨.voc, .sg⟩ => "e" | .hardMasc, ⟨.loc, .sg⟩ => "ě"
  | .hardMasc, ⟨.ins, .sg⟩ => "em"
  | .hardMasc, ⟨.nom, .pl⟩ => "y" | .hardMasc, ⟨.gen, .pl⟩ => "ů"
  | .hardMasc, ⟨.dat, .pl⟩ => "ům" | .hardMasc, ⟨.acc, .pl⟩ => "y"
  | .hardMasc, ⟨.voc, .pl⟩ => "y" | .hardMasc, ⟨.loc, .pl⟩ => "ech"
  | .hardMasc, ⟨.ins, .pl⟩ => "y"

/-- Realization of a form cell: the stem's form plus its own declension's
ending — realization rules "are sensitive to a stem's inflection-class
membership" ([stump-2006] §3.1). -/
def czRealize (z : CzStem) (σ : CzCell) : String := z.form ++ ending z.decl σ

/-- Table 1's forms, transcribed verbatim. -/
def table1 : CzNoun → CzCell → String
  | .pokoj, ⟨.nom, .sg⟩ => "pokoj" | .pokoj, ⟨.gen, .sg⟩ => "pokoje"
  | .pokoj, ⟨.dat, .sg⟩ => "pokoji" | .pokoj, ⟨.acc, .sg⟩ => "pokoj"
  | .pokoj, ⟨.voc, .sg⟩ => "pokoji" | .pokoj, ⟨.loc, .sg⟩ => "pokoji"
  | .pokoj, ⟨.ins, .sg⟩ => "pokojem"
  | .pokoj, ⟨.nom, .pl⟩ => "pokoje" | .pokoj, ⟨.gen, .pl⟩ => "pokojů"
  | .pokoj, ⟨.dat, .pl⟩ => "pokojům" | .pokoj, ⟨.acc, .pl⟩ => "pokoje"
  | .pokoj, ⟨.voc, .pl⟩ => "pokoje" | .pokoj, ⟨.loc, .pl⟩ => "pokojích"
  | .pokoj, ⟨.ins, .pl⟩ => "pokoji"
  | .most, ⟨.nom, .sg⟩ => "most" | .most, ⟨.gen, .sg⟩ => "mostu"
  | .most, ⟨.dat, .sg⟩ => "mostu" | .most, ⟨.acc, .sg⟩ => "most"
  | .most, ⟨.voc, .sg⟩ => "moste" | .most, ⟨.loc, .sg⟩ => "mostě"
  | .most, ⟨.ins, .sg⟩ => "mostem"
  | .most, ⟨.nom, .pl⟩ => "mosty" | .most, ⟨.gen, .pl⟩ => "mostů"
  | .most, ⟨.dat, .pl⟩ => "mostům" | .most, ⟨.acc, .pl⟩ => "mosty"
  | .most, ⟨.voc, .pl⟩ => "mosty" | .most, ⟨.loc, .pl⟩ => "mostech"
  | .most, ⟨.ins, .pl⟩ => "mosty"
  | .pramen, ⟨.nom, .sg⟩ => "pramen" | .pramen, ⟨.gen, .sg⟩ => "pramene"
  | .pramen, ⟨.dat, .sg⟩ => "prameni" | .pramen, ⟨.acc, .sg⟩ => "pramen"
  | .pramen, ⟨.voc, .sg⟩ => "prameni" | .pramen, ⟨.loc, .sg⟩ => "prameni"
  | .pramen, ⟨.ins, .sg⟩ => "pramenem"
  | .pramen, ⟨.nom, .pl⟩ => "prameny" | .pramen, ⟨.gen, .pl⟩ => "pramenů"
  | .pramen, ⟨.dat, .pl⟩ => "pramenům" | .pramen, ⟨.acc, .pl⟩ => "prameny"
  | .pramen, ⟨.voc, .pl⟩ => "prameny" | .pramen, ⟨.loc, .pl⟩ => "pramenech"
  | .pramen, ⟨.ins, .pl⟩ => "prameny"

/-- The default-plus-override linkage reproduces every form of Table 1. -/
theorem realize_matches_table1 :
    ∀ (n : CzNoun) (σ : CzCell),
      czLinkage.realize czRealize n σ = {(table1 n σ, σ)} := by decide

/-- The two declensions ordinarily contrast — no case/number cell has them
merely notational variants across the whole ending inventory, and e.g. the
genitive singular separates them outright. PRAMEN's split is therefore
detectable ([stump-2006] on POKOJ vs MOST vs PRAMEN). -/
theorem soft_hard_contrast :
    ending .softMasc ⟨.gen, .sg⟩ ≠ ending .hardMasc ⟨.gen, .sg⟩ := by decide

/-- **PRAMEN is heteroclite**: its correspondents draw on both declensions
([stump-2006] Table 1, rule (14)). -/
theorem pramen_heteroclite : czLinkage.IsHeteroclite CzStem.decl := by decide

/-- **Heteroclisis without form suppletion**: the linkage is invariant along the
form projection — every lexeme's stems are phonologically constant — yet
heteroclite along the class projection. Form-invariance and class-invariance are
independent ([stump-2006] fn. 5, against reading the No Blur Principle as
excluding class-only stem alternants). -/
theorem heteroclisis_without_form_suppletion :
    czLinkage.InvariantAlong CzStem.form ∧ czLinkage.IsHeteroclite CzStem.decl :=
  ⟨by decide, pramen_heteroclite⟩

/-- The entailment instance: PRAMEN's class split makes the linkage suppletive
in the broad sense — two stems — even though no form alternation is audible,
[stump-2006]'s "a kind of stem alternation". -/
theorem pramen_stem_alternation : czLinkage.IsSuppletive :=
  pramen_heteroclite.isSuppletive

/-! ### Sanskrit HR̥D(AYA): heteroclisis riding on stem suppletion (Table 4)

Direct cases (nominative, vocative, accusative) are built on *hr̥daya*, oblique
cases on *hr̥d*; the a-stem *hr̥daya* follows the neuter a-stem declension, the
consonant-stem *hr̥d* the neuter consonant-stem declension. Cells are abstracted
to the direct/oblique split the prose states. -/

/-- The direct/oblique case-class split. -/
inductive CaseClass | direct | oblique
  deriving DecidableEq, Fintype, Repr

/-- The two Sanskrit neuter declensions involved. -/
inductive SktDecl | aStem | consStem
  deriving DecidableEq, Fintype, Repr

/-- HR̥D(AYA)'s two suppletive stems. -/
inductive SktStem | hrdaya | hrd
  deriving DecidableEq, Fintype, Repr

/-- Stem forms (romanized without diacritics in identifiers; forms carry them). -/
def SktStem.form : SktStem → String
  | .hrdaya => "hr̥daya"
  | .hrd => "hr̥d"

/-- Stem class: a-stems decline as a-stems, consonant-stems as consonant-stems
("because hr̥daya is a neuter stem ending in a … because hr̥d is a neuter stem
ending in a consonant", [stump-2006] on Table 4). -/
def SktStem.decl : SktStem → SktDecl
  | .hrdaya => .aStem
  | .hrd => .consStem

/-- The single lexeme HR̥D(AYA). -/
inductive SktNoun | hrdaya
  deriving DecidableEq, Fintype, Repr

/-- The suppletive linkage: direct cells on *hr̥daya*, oblique on *hr̥d*. -/
def sktLinkage : Linkage SktNoun SktStem CaseClass where
  stems := fun _ σ => match σ with | .direct => {.hrdaya} | .oblique => {.hrd}
  pm := fun _ σ => σ

/-- HR̥D(AYA) occupies the doubly-deviant grid cell: heteroclite *and*
form-suppletive — "it is because of this stem suppletion that the paradigm of
HR̥D(AYA) is heteroclite" ([stump-2006] on Table 4). Contrast PRAMEN, heteroclite
with constant form. -/
theorem hrd_heteroclite_and_form_suppletive :
    sktLinkage.IsHeteroclite SktStem.decl ∧
      ¬ sktLinkage.InvariantAlong SktStem.form :=
  ⟨by decide, by decide⟩

end Stump2006
