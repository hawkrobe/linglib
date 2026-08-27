import Linglib.Features.Case.Basic
import Linglib.Syntax.Case.Order
import Linglib.Morphology.Paradigm.Case
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Phonology.OptimalityTheory.Stratal
import Mathlib.Tactic.DeriveFintype
import Linglib.Phonology.Prosody.Foot
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Linglib.Data.Examples.Aitha2026

/-!
# The nouns that say -ni

Telugu nouns show two stem alternations. The strong one (*il-lu* ~ *in-ṭi* 'house') is
contextual allomorphy of the nominalizer n conditioned by [ACC], the feature every
nonnominative case contains under [caha-2009]'s containment ([mcfadden-2018]). The weak
one (*samudr-am* ~ *samudr-āni* 'ocean') only looks like case allomorphy: it violates *ABA,
is triggered by agreement suffixes in nominative contexts, and reads the weight of the next
syllable inside the prosodic word. It is the phonology of one underlying *-am-ni*, derived in
Stratal OT ([kiparsky-2000]) from prespecified stress on the singular suffix *-ni*.

This file defines the Vocabulary Items of the strong alternation (`strongItems`), the weak
generalization (`weakN`), the singular suffix (`numItems`), and the Stem, Word, and Phrase
tableaux with the marks of the paper's (49), (59), (62), (63), (66), and (67) under the
rankings of (64) and (68). `strong_rows` and `weak_rows` check both alternations against
every paradigm cell of the pool; `weak_not_case_function` and `weak_violates_aba` are the
arguments against case conditioning; `oblique_across_quantifier` is the locality contrast;
the `*_optimal` theorems derive both surface forms from *-am-ni*, and the `*_reranked`
theorems are the Word-to-Phrase rerankings of (68).

## References

* [aitha-2026]
* [caha-2009]
* [mcfadden-2018]
* [kiparsky-2000]
-/

namespace Aitha2026

open Morphology.Case.Allomorphy DistributedMorphology Prosody Data.Examples
open scoped DistributedMorphology.VocabularyItem
open Core Constraints OptimalityTheory Core.Optimization Core.Optimization.Evaluation

/-! ### Case -/

/-- The Telugu cases of the paradigms, with the postpositions as P. -/
inductive TeluguCase where
  | nom | acc | gen | dat | p
  deriving DecidableEq, Repr, Fintype

def TeluguCase.toCore : TeluguCase → Case
  | .nom => .nom
  | .acc => .acc
  | .gen => .gen
  | .dat => .dat
  | .p => .loc

/-- A nonnominative case contains [ACC] ((3), [caha-2009]): the natural class
of the oblique. -/
def TeluguCase.IsNonnom (c : TeluguCase) : Prop := Case.IsNonnominative c.toCore

instance (c : TeluguCase) : Decidable c.IsNonnom :=
  inferInstanceAs (Decidable (Case.IsNonnominative c.toCore))

def TeluguCase.ofString : String → Option TeluguCase
  | "nom" => some .nom | "acc" => some .acc | "gen" => some .gen | "dat" => some .dat
  | "p" => some .p | _ => none

/-! ### The strong alternation (§2) -/

/-- The strong roots of (2), by gloss. -/
inductive Root where
  | house | bow | eye | tooth | nest | stream | mouth | plough | ghee | well | town | husband
  deriving DecidableEq, Repr, Fintype

def Root.ofString : String → Option Root
  | "house" => some .house | "bow" => some .bow | "eye" => some .eye | "tooth" => some .tooth
  | "nest" => some .nest | "stream" => some .stream | "mouth" => some .mouth
  | "plough" => some .plough | "ghee" => some .ghee | "well" => some .well | "town" => some .town
  | "husband" => some .husband | _ => none

/-- Features at the n head: the root it attaches to and, in every
nonnominative case, [ACC]. -/
inductive Feature where
  | root (r : Root)
  | acc
  deriving DecidableEq, Repr

/-- The n head's bundle for root `r` in case `c`. -/
def site (r : Root) (c : TeluguCase) : List Feature :=
  .root r :: if c.IsNonnom then [.acc] else []

/-- The items of one exponent: `e` next to each listed root, in the context
of [ACC] when `acc`. -/
def forRoots (roots : List Root) (e : String) (acc : Bool := false) :
    List (VocabularyItem Feature String) :=
  roots.map fun r => (.root r :: if acc then [.acc] else []) ⟷ e

/-- The Vocabulary Items of (4) for the roots of (2): the nominative exponents
next to their roots, and the oblique exponents next to the same roots and
[ACC] — one *-ṭi* entry spanning the *-ru*, *-lu*, *-nu*, *-ḍu*, and *-li*
classes, *-ti* for the *-yi* class, *-i* for the *-u* class. -/
def strongItems : List (VocabularyItem Feature String) :=
  forRoots [.stream, .mouth] "ru" ++ forRoots [.house, .bow] "lu" ++
    forRoots [.eye, .tooth] "nu" ++ forRoots [.nest] "ḍu" ++ forRoots [.plough] "li" ++
    forRoots [.stream, .mouth, .house, .bow, .eye, .tooth, .nest, .plough] "ṭi" true ++
    forRoots [.ghee, .well] "yi" ++ forRoots [.ghee, .well] "ti" true ++
    forRoots [.town, .husband] "u" ++ forRoots [.town, .husband] "i" true

/-- The exponent of n for root `r` in case `c`. -/
def strongN (r : Root) (c : TeluguCase) : Option String := subsetPrinciple strongItems (site r c)

/-- The nominative–nonnominative cut: every nonnominative case takes the
accusative's exponent, by the Elsewhere Condition over [ACC]. -/
theorem strongN_nonnom :
    ∀ (r : Root) (c : TeluguCase), c.IsNonnom → strongN r c = strongN r .acc := by
  decide

/-! ### The weak alternation (§3) -/

/-- What follows the n exponent: its membership in the noun's prosodic word
and the weight of its initial syllable (§3.2). -/
structure Following where
  internal : Bool
  weight : Syllable.Weight
  deriving DecidableEq, Repr

/-- The long form is triggered iff the next syllable is light and inside the
prosodic word; postpositions with light initial syllables ((18)) and the
heavy-initial postposed quantifier ((17)) do not trigger it. -/
def TriggersLong (f : Option Following) : Prop :=
  ∃ m ∈ f, m.internal = true ∧ m.weight = .light

instance (f : Option Following) : Decidable (TriggersLong f) := by
  unfold TriggersLong; infer_instance

/-- The weak n exponent: *-āni* before a word-internal light syllable, *-am*
otherwise. -/
def weakN (f : Option Following) : String := if TriggersLong f then "āni" else "am"

/-! ### The data pool -/

/-- A paradigm cell of the pool: the root class, the case if any, what follows n, the n
exponent, and for singular weak nouns whether the form is long. -/
structure Cell where
  noun : String
  strongRoot : Option Root
  plural : Bool
  case : Option TeluguCase
  following : Option Following
  n : String
  long : Option Bool
  deriving DecidableEq, Repr

/-- The cell an example records, from its `paperFeatures`. -/
def Cell.ofExample (ex : LinguisticExample) : Option Cell := do
  let fs := ex.paperFeatures
  let noun ← fs.lookup "noun"
  let cls ← fs.lookup "class"
  let number ← fs.lookup "number"
  let case ← fs.lookup "case"
  let prwd ← fs.lookup "prwd"
  let weight ← fs.lookup "weight"
  let n ← fs.lookup "n"
  let following ← match prwd, weight with
    | "none", _ => some none
    | "internal", "light" => some (some ⟨true, .light⟩)
    | "internal", "heavy" => some (some ⟨true, .heavy⟩)
    | "external", "light" => some (some ⟨false, .light⟩)
    | "external", "heavy" => some (some ⟨false, .heavy⟩)
    | _, _ => none
  let strongRoot ←
    if cls = "strong" then (fs.lookup "root" >>= Root.ofString).map some else some none
  pure ⟨noun, strongRoot, number = "pl", TeluguCase.ofString case, following, n,
    (fs.lookup "form").map (· = "long")⟩

/-- Every row recording an n exponent is a cell. -/
theorem cell_ofExample_isSome :
    ∀ ex ∈ Examples.all, (ex.feature? "n").isSome → (Cell.ofExample ex).isSome := by decide

/-- The cells of the pool. -/
def cells : List Cell := Examples.all.filterMap Cell.ofExample

/-- The strong cells, with their roots. -/
def strongCells : List (Root × TeluguCase × String) :=
  cells.filterMap fun c => do pure (← c.strongRoot, ← c.case, c.n)

/-- The singular weak cells. -/
def weakCells : List Cell := cells.filter fun c => c.strongRoot = none ∧ ¬ c.plural

/-- **The strong paradigm**: (4) inserts the attested exponent in every strong cell of (1),
(2), and fn. 6 — the agreement suffix, bearing no [ACC], leaves the nominative form. -/
theorem strong_rows : ∀ x ∈ strongCells, strongN x.1 x.2.1 = some x.2.2 := by decide

/-- **The weak generalization**: in every singular weak cell of (6)–(8), (13)–(18), and (34)
the form is long exactly when the following syllable is light and word-internal. -/
theorem weak_rows : ∀ c ∈ weakCells, c.long = some (decide (TriggersLong c.following)) := by
  decide

/-- The nominative short form of (8). -/
def oceanNom : Cell := ⟨"samudram", none, false, some .nom, none, "am", some false⟩

/-- The long form under the 1SG agreement suffix, in a nominative predicate nominal ((13)). -/
def ocean1sg : Cell := ⟨"samudram", none, false, some .nom, some ⟨true, .light⟩, "āni", some true⟩

/-- **Not case allomorphy**: no assignment of a form to each case fits the weak cells, since
the nominative carries both *-am* and *-āni* ((8) with (13)–(16)). -/
theorem weak_not_case_function :
    ¬ ∃ f : Option TeluguCase → Option Bool, ∀ c ∈ weakCells, f c.case = c.long := by
  rintro ⟨f, h⟩
  have h₁ := h oceanNom (by decide)
  have h₂ := h ocean1sg (by decide)
  simp only [oceanNom, ocean1sg] at h₁ h₂
  exact absurd (h₁.symm.trans h₂) (by decide)

/-- **Locality** ((33)–(36)): across a postposed quantifier the strong oblique is licensed
exactly when the overall case is nonnominative. -/
theorem oblique_across_quantifier :
    ∀ row ∈ Examples.all, row.feature? "intervener" = some "quantifier" →
      row.feature? "class" = some "strong" →
      (row.judgment = .acceptable ↔
        (row.feature? "stem" = some "obl" ↔ row.feature? "case" ≠ some "nom")) := by
  decide

/-! ### Paradigm shapes against containment (§3.1) -/

/-- The suffix shapes of the case paradigms (1) and (8): null nominative and genitive, light
*-ni* and *-ki*, and the heavy postposition *-lō*. -/
def caseSuffix : TeluguCase → Option Following
  | .nom => none
  | .acc => some ⟨true, .light⟩
  | .gen => none
  | .dat => some ⟨true, .light⟩
  | .p => some ⟨false, .heavy⟩

/-- The weak paradigm as an allomorphy pattern, short 0 and long 1. -/
def weakPattern : AllomorphyPattern :=
  let code (c : TeluguCase) : Nat := if weakN (caseSuffix c) = "am" then 0 else 1
  ⟨code .nom, code .acc, code .gen, code .dat⟩

/-- The strong paradigm of *illu* as an allomorphy pattern, nominative 0 and oblique 1. -/
def strongPattern : AllomorphyPattern :=
  let code (c : TeluguCase) : Nat := if strongN .house c = strongN .house .nom then 0 else 1
  ⟨code .nom, code .acc, code .gen, code .dat⟩

/-- The weak ABAB paradigm violates *ABA: the nominative form resurfaces in the genitive,
which contains [ACC] ([caha-2009]). -/
theorem weak_violates_aba : weakPattern.ViolatesABA := by decide

/-- The strong ABB paradigm is contiguous on the containment hierarchy. -/
theorem strong_contiguous : strongPattern.IsContiguous := by decide

/-! ### The singular suffix (§4.2) -/

/-- The context of Num: the preceding n exponent is *-am*. -/
inductive NumContext where
  | afterAm
  deriving DecidableEq, Repr

/-- The Vocabulary Items of Num in the singular ((40)): *-ni* after *-am*, null elsewhere —
conditioned inward, as root-out insertion allows. -/
def numItems : List (VocabularyItem NumContext String) := [[.afterAm] ⟷ "ni", [] ⟷ "ø"]

/-- The singular exponent of Num after an n exponent. -/
def numSg (nExponent : String) : Option String :=
  subsetPrinciple numItems (if nExponent = "am" then [.afterAm] else [] : List NumContext)

/-- Weak nouns take *-ni*, strong nouns the null singular: the underlying weak singular is
*samudr-am-ni-K* ((41)). -/
theorem numSg_am : numSg "am" = some "ni" ∧ numSg "lu" = some "ø" := by decide

/-! ### Stem-level phonology (§5.1) -/

/-- The metrical parses of *samudr-am* in (49): final heavy syllable unparsed, three
degenerate feet, or two bimoraic trochees. -/
inductive StemCandidate where
  | unparsedFinal
  | degenerate
  | trochees
  deriving DecidableEq, Repr, Fintype, Inhabited

def StemCandidate.toFooting : StemCandidate → Footing Syllable.Weight
  | .unparsedFinal => [.inl ⟨[.light, .light], 0⟩, .inr .heavy]
  | .degenerate => [.inl ⟨[.light], 0⟩, .inl ⟨[.light], 0⟩, .inl ⟨[.heavy], 0⟩]
  | .trochees => [.inl ⟨[.light, .light], 0⟩, .inl ⟨[.heavy], 0⟩]

/-- FT-BIN(μ) ≫ PARSE-SYL ≫ ALL-FT-LEFT ((46)–(48)), read off each parse's footing. -/
def stemRanking : List (Constraint StemCandidate) :=
  [Footing.ftBin id ∘ StemCandidate.toFooting, Footing.parseSyl ∘ StemCandidate.toFooting,
    Footing.allFtLeft ∘ StemCandidate.toFooting]

/-- (49): the Stem parses as two moraic trochees, (ˈsa.mu)(ˌdram). -/
theorem stem_optimal : (Tableau.ofFintype stemRanking).optimal = {.trochees} := by decide

/-! ### Word- and Phrase-level rankings (§5.2–5.3)

The constraints of the two strata are shared by label; each stratum fixes one order, and
each tableau supplies only its candidates' violation marks (`Tableau.ofOrder`). -/

/-- The constraints of (64) and (68). -/
inductive Con where
  | distZero | alignR | identStress | ftBin | complexCoda | maxMora | max | identLength | onset
  deriving DecidableEq, Repr

/-- The Word-level ranking (64), with ONSET below IDENT-STRESS (§5.2); Hasse siblings are
listed in the order of the paper's tableau columns. -/
def wordOrder : List Con :=
  [.distZero, .alignR, .identStress, .ftBin, .complexCoda, .maxMora, .max, .identLength, .onset]

/-- The Phrase-level ranking (68). -/
def phraseOrder : List Con :=
  [.ftBin, .onset, .identLength, .max, .identStress, .distZero, .alignR, .maxMora]

/-! ### Word-level phonology (§5.2) -/

/-- The candidates for dative *samudr-am-ní-ki* ((59)): keep /mn/; delete /n/ or /m/ with the
mora; delete /m/ or /n/ with compensatory lengthening. -/
inductive WordCandDat where
  | faithful | deleteN | deleteM | deleteMLengthen | deleteNLengthen
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The marks of (59). -/
def WordCandDat.marks : WordCandDat → Con → ℕ
  | .faithful, .distZero => 1
  | .deleteN, .alignR | .deleteN, .maxMora => 1
  | .deleteN, .max => 2
  | .deleteM, .maxMora | .deleteM, .max => 1
  | .deleteMLengthen, .max | .deleteMLengthen, .identLength => 1
  | .deleteNLengthen, .alignR | .deleteNLengthen, .identLength => 1
  | .deleteNLengthen, .max => 2
  | _, _ => 0

/-- (59): the /mn/ contact is repaired by deleting /m/ and lengthening /a/ — the long form
*samudrāniki*. -/
theorem wordDat_optimal :
    (Tableau.ofOrder wordOrder WordCandDat.marks).optimal = {.deleteMLengthen} := by
  decide

/-- The candidates for nominative *samudr-am-ní* ((62)): destress *-ni*; foot it alone; delete
/i/ into a coda cluster; delete /i/ and /m/; or delete /ni/. -/
inductive WordCandNom where
  | destress | degenerateFoot | deleteI | deleteIM | deleteNi
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The marks of (62). -/
def WordCandNom.marks : WordCandNom → Con → ℕ
  | .destress, .identStress => 1
  | .degenerateFoot, .ftBin => 1
  | .deleteI, .complexCoda | .deleteI, .maxMora | .deleteI, .max => 1
  | .deleteIM, .alignR | .deleteIM, .maxMora => 1
  | .deleteIM, .max => 2
  | .deleteNi, .maxMora => 1
  | .deleteNi, .max => 2
  | _, _ => 0

/-- (62): word-final stressed *-ni*, unable to head a binary foot, is deleted — the short form
*samudram*. -/
theorem wordNom_optimal :
    (Tableau.ofOrder wordOrder WordCandNom.marks).optimal = {.deleteNi} := by
  decide

/-- The candidates for *samudr-am-ní-antaṭi-ni* with a postposed quantifier ((63)): destress
*-ni*; foot it alone; delete /i/ into /mn/; delete /i/ and /m/ with /n/ as coda; delete /ni/;
or delete /i/ and /m/ with /n/ resyllabified as onset. -/
inductive WordCandQ where
  | destress | degenerateFoot | deleteI | deleteIM | deleteNi | deleteIMResyllabify
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The marks of (63), with ONSET marked on every candidate whose *an* lacks an onset. -/
def WordCandQ.marks : WordCandQ → Con → ℕ
  | .destress, .identStress | .destress, .onset => 1
  | .degenerateFoot, .ftBin | .degenerateFoot, .onset => 1
  | .deleteI, .distZero | .deleteI, .max => 1
  | .deleteIM, .alignR | .deleteIM, .onset => 1
  | .deleteIM, .max => 2
  | .deleteNi, .onset => 1
  | .deleteNi, .max => 2
  | .deleteIMResyllabify, .identStress => 1
  | .deleteIMResyllabify, .max => 2
  | _, _ => 0

/-- (63): before the heavy *an* the stressed *-ni* is again deleted, leaving the coda /m/
before an onsetless syllable. -/
theorem wordQ_optimal :
    (Tableau.ofOrder wordOrder WordCandQ.marks).optimal = {.deleteNi} := by
  decide

/-- The n exponent each Word-level output leaves. -/
def WordCandNom.nExponent : WordCandNom → String
  | .destress | .degenerateFoot => "amni"
  | .deleteI => "amn"
  | .deleteIM => "an"
  | .deleteNi => "am"

def WordCandDat.nExponent : WordCandDat → String
  | .faithful => "amni"
  | .deleteN => "ami"
  | .deleteM => "ani"
  | .deleteMLengthen => "āni"
  | .deleteNLengthen => "āmi"

/-- The two Word-level winners are the two forms of the generalization `weakN`: the same
underlying *-am-ni* surfaces short before nothing and long before a word-internal light
syllable. -/
theorem word_level_derives_weakN :
    WordCandNom.deleteNi.nExponent = weakN (caseSuffix .nom) ∧
      WordCandDat.deleteMLengthen.nExponent = weakN (caseSuffix .dat) := by
  decide

/-! ### Phrase-level phonology (§5.3) -/

/-- The candidates for *samudram nunci* 'from the ocean' ((66)): delete /m/ with or without
lengthening, delete the postposition's /n/, or keep the /mn/ contact. -/
inductive PhraseCandP where
  | deleteMLengthen | deleteM | deleteN | faithful
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The marks of (66), as printed. -/
def PhraseCandP.marks : PhraseCandP → Con → ℕ
  | .deleteMLengthen, .max => 1
  | .deleteM, .identStress | .deleteM, .max => 1
  | .deleteN, .max | .deleteN, .alignR => 1
  | .faithful, .distZero => 1
  | .faithful, .alignR => 2
  | _, _ => 0

/-- (66): across the postposition boundary the /mn/ contact is kept. -/
theorem phraseP_optimal :
    (Tableau.ofOrder phraseOrder PhraseCandP.marks).optimal = {.faithful} := by
  decide

/-- The candidates for the Word-level output of (63) at the Phrase level ((67)): keep the
onsetless *an*; resyllabify /m/ as its onset; lengthen /a/ and resyllabify; or foot the
shortened *dra* alone. -/
inductive PhraseCandQ where
  | faithful | resyllabify | lengthen | degenerateFoot
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The marks of (67). -/
def PhraseCandQ.marks : PhraseCandQ → Con → ℕ
  | .faithful, .onset => 1
  | .resyllabify, .identStress | .resyllabify, .alignR | .resyllabify, .maxMora => 1
  | .lengthen, .identLength | .lengthen, .alignR => 1
  | .degenerateFoot, .ftBin | .degenerateFoot, .identStress | .degenerateFoot, .alignR
  | .degenerateFoot, .maxMora => 1
  | _, _ => 0

/-- (67): the coda /m/ resyllabifies as the onset of *an*, shifting stress — *samudra.man.ta.ṭi.ni*
without compensatory lengthening. -/
theorem phraseQ_optimal :
    (Tableau.ofOrder phraseOrder PhraseCandQ.marks).optimal = {.resyllabify} := by
  decide

/-! ### Rerankings (68) -/

open OptimalityTheory.Stratal

/-- *DIST-0 and ALIGN-RIGHT outrank MAX at the Word level and are outranked by it at the
Phrase level: consonant deletion at the Word level, retention and resyllabification at the
Phrase level. -/
theorem distZero_alignR_max_reranked :
    Reranked Con.distZero .max wordOrder phraseOrder ∧
      Reranked Con.alignR .max wordOrder phraseOrder := by
  decide

/-- Prosodic faithfulness (IDENT-STRESS, MAX-μ) outranks segmental faithfulness (MAX,
IDENT-LENGTH) at the Word level and is outranked by it at the Phrase level. -/
theorem prosodic_segmental_reranked :
    Reranked Con.identStress .max wordOrder phraseOrder ∧
      Reranked Con.maxMora .identLength wordOrder phraseOrder := by
  decide

/-- IDENT-STRESS outranks ONSET at the Word level and ONSET outranks it at the Phrase level:
the onsetless *an* of (63) is resyllabified only in (67). -/
theorem identStress_onset_reranked : Reranked Con.identStress .onset wordOrder phraseOrder := by
  decide

end Aitha2026
