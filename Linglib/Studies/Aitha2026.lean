import Linglib.Features.Case.Basic
import Linglib.Syntax.Case.Order
import Linglib.Morphology.Paradigm.Case
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Phonology.OptimalityTheory.Stratal
import Linglib.Phonology.Prosody.Foot
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Linglib.Data.Examples.Aitha2026

/-!
# The nouns that say -ni

[aitha-2026] separates two stem alternations in Telugu nouns. The strong
alternation (*il-lu* ~ *in-ṭi* 'house') is contextual allomorphy of the
nominalizer n conditioned by [ACC], the feature every nonnominative case
contains under [caha-2009]'s containment hierarchy ([mcfadden-2018]). The
weak alternation (*samudr-am* ~ *samudr-āni* 'ocean') only looks like case
allomorphy: it violates *ABA, is triggered by agreement suffixes in
nominative contexts, and reads the weight of the next syllable inside the
prosodic word. It is instead the phonology of a single underlying
*-am-ni*, derived in Stratal OT ([kiparsky-2000]) from prespecified stress
on the singular suffix *-ni*.

## Main definitions

* `strongItems`, `strongN`: the Vocabulary Items of (4) over root lists and
  [ACC], and the n exponent they insert.
* `Following`, `weakN`: what follows n and the long/short generalization of
  §3.2 — long iff the next syllable is light and inside the prosodic word.
* `numItems`: the singular suffix *-ni* as an exponent of Num conditioned by
  the preceding *-am* ((40)).
* `stemRanking`, `wordNomRanking`, `wordDatRanking`, `phraseRanking`: the
  tableaux of (49), (62), (59), and (66).

## Main results

* `strong_rows`, `weak_rows`: the items and the generalization reproduce every
  paradigm cell of the data pool.
* `weak_not_case_function`: no assignment of exponents to cases fits the weak
  rows — the nominative carries both forms ((8), (16)).
* `weak_violates_aba`, `strong_contiguous`: the paradigm shapes against
  containment.
* `wordNom_optimal`, `wordDat_optimal`: Word-level phonology deletes
  word-final stressed *-ni* and repairs /mn/ by compensatory lengthening.
* `distZero_demoted`, `alignR_demoted`: the Word-to-Phrase rerankings of
  (68).

## Implementation notes

The Stem-level sandhi of the *-em* and *-ām* subclasses ((52), (55)) and the
quantifier-postposing tableaux ((63), (67)) are not formalized. Tableau
violation marks follow the paper's prose where the tableau images are not
in the text layer.
-/

namespace Aitha2026

open Morphology.Case.Allomorphy DistributedMorphology Prosody Data.Examples
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
  roots.map fun r => ⟨.root r :: if acc then [.acc] else [], e⟩

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

/-- A paradigm cell of the pool: the root class, the case if any, what follows
n, and the n exponent. -/
structure Cell where
  noun : String
  strongRoot : Option Root
  plural : Bool
  case : Option TeluguCase
  following : Option Following
  n : String
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
  pure ⟨noun, strongRoot, number = "pl", TeluguCase.ofString case, following, n⟩

theorem cell_ofExample_isSome : ∀ ex ∈ Examples.all, (Cell.ofExample ex).isSome := by decide

/-- The cells of the pool. -/
def cells : List Cell := Examples.all.filterMap Cell.ofExample

/-- The strong cells, with their roots. -/
def strongCells : List (Root × TeluguCase × String) :=
  cells.filterMap fun c => do pure (← c.strongRoot, ← c.case, c.n)

/-- The singular weak cells. -/
def weakCells : List Cell := cells.filter fun c => c.strongRoot = none ∧ ¬ c.plural

/-- **The strong paradigm**: (4) inserts the attested exponent in every strong
cell of (1), (2), and fn. 6 — the agreement suffix, bearing no [ACC], leaves
the nominative form. -/
theorem strong_rows : ∀ x ∈ strongCells, strongN x.1 x.2.1 = some x.2.2 := by decide

/-- **The weak generalization**: the long form in every singular weak cell of
(8), (13)–(18) is predicted by the following syllable alone. -/
theorem weak_rows : ∀ c ∈ weakCells, weakN c.following = c.n := by decide

/-- The nominative short form of (8). -/
def oceanNom : Cell := ⟨"samudram", none, false, some .nom, none, "am"⟩

/-- The long form under the 1SG agreement suffix, in a nominative predicate
nominal ((13)). -/
def ocean1sg : Cell := ⟨"samudram", none, false, some .nom, some ⟨true, .light⟩, "āni"⟩

/-- **Not case allomorphy**: no assignment of an n exponent to each case fits
the weak cells, since the nominative carries both *-am* and *-āni* ((8) with
(13)–(16)). -/
theorem weak_not_case_function :
    ¬ ∃ f : Option TeluguCase → String, ∀ c ∈ weakCells, f c.case = c.n := by
  rintro ⟨f, h⟩
  have h₁ := h oceanNom (by decide)
  have h₂ := h ocean1sg (by decide)
  simp only [oceanNom, ocean1sg] at h₁ h₂
  exact absurd (h₁.symm.trans h₂) (by decide)

/-! ### Paradigm shapes against containment (§3.1) -/

/-- The suffix shapes of the case paradigms (1) and (8): null nominative and
genitive, light *-ni*/*-ki*, and the heavy postposition *-lō*. -/
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

/-- The strong paradigm of *illu* as an allomorphy pattern, nominative 0 and
oblique 1. -/
def strongPattern : AllomorphyPattern :=
  let code (c : TeluguCase) : Nat := if strongN .house c = strongN .house .nom then 0 else 1
  ⟨code .nom, code .acc, code .gen, code .dat⟩

/-- The weak ABAB paradigm violates *ABA: the nominative form resurfaces in
the genitive, which contains [ACC] ([caha-2009]). -/
theorem weak_violates_aba : weakPattern.ViolatesABA := by decide

/-- The strong ABB paradigm is contiguous on the containment hierarchy. -/
theorem strong_contiguous : strongPattern.IsContiguous := by decide

/-! ### The singular suffix (§4.2) -/

/-- The context of Num: the preceding n exponent is *-am*. -/
inductive NumContext where
  | afterAm
  deriving DecidableEq, Repr

/-- The Vocabulary Items of Num in the singular ((40)): *-ni* after *-am*,
null elsewhere — conditioned inward, as root-out insertion allows. -/
def numItems : List (VocabularyItem NumContext String) := [⟨[.afterAm], "ni"⟩, ⟨[], "ø"⟩]

/-- The singular exponent of Num after an n exponent. -/
def numSg (nExponent : String) : Option String :=
  subsetPrinciple numItems (if nExponent = "am" then [.afterAm] else [])

/-- Weak nouns take *-ni*, strong nouns the null singular: the underlying weak
singular is *samudr-am-ni-K* ((41)). -/
theorem numSg_am : numSg "am" = some "ni" ∧ numSg "lu" = some "ø" := by decide

/-! ### Stem-level phonology (§5.1) -/

/-- The metrical parses of *samudr-am* in (49): final heavy syllable
unparsed, three degenerate feet, or two bimoraic trochees. -/
inductive StemCandidate where
  | unparsedFinal
  | degenerate
  | trochees
  deriving DecidableEq, Repr

def StemCandidate.toFooting : StemCandidate → Footing Syllable.Weight
  | .unparsedFinal => [.inl ⟨[.light, .light], 0⟩, .inr .heavy]
  | .degenerate => [.inl ⟨[.light], 0⟩, .inl ⟨[.light], 0⟩, .inl ⟨[.heavy], 0⟩]
  | .trochees => [.inl ⟨[.light, .light], 0⟩, .inl ⟨[.heavy], 0⟩]

/-- ALL-FT-LEFT ((48)): per foot, the syllables between the left edge of the
domain and the foot. -/
def allFtLeftOf (fc : Footing Syllable.Weight) : Nat :=
  let rec go : Footing Syllable.Weight → Nat → Nat
    | [], _ => 0
    | .inl f :: rest, pos => pos + go rest (pos + f.syllables.length)
    | .inr _ :: rest, pos => go rest (pos + 1)
  go fc 0

/-- FT-BIN(μ) ((46)). -/
def ftBin : Constraint StemCandidate :=
  fun c => (c.toFooting.feet.filter fun f => decide (Foot.moraCount id f ≠ 2)).length

/-- PARSE-SYL ((47)). -/
def parseSyl : Constraint StemCandidate := fun c => c.toFooting.strays.length

def allFtLeft : Constraint StemCandidate := fun c => allFtLeftOf c.toFooting

/-- FT-BIN ≫ PARSE-SYL ≫ ALL-FT-LEFT. -/
def stemRanking : List (Constraint StemCandidate) := [ftBin, parseSyl, allFtLeft]

def stemCandidates : List StemCandidate := [.unparsedFinal, .degenerate, .trochees]

theorem stemCandidates_ne : stemCandidates ≠ [] := by decide

/-- (49): the Stem parses as two moraic trochees, (ˈsa.mu)(ˌdram). -/
theorem stem_optimal :
    (Tableau.ofRanking stemCandidates stemRanking stemCandidates_ne).optimal = {.trochees} := by
  decide

/-! ### Word-level phonology (§5.2) -/

/-- The constraints of §5.2–5.3, as labels shared across strata. -/
inductive Con where
  | distZero | alignR | identStress | ftBin | maxMora | max | identLength | complexCoda
  deriving DecidableEq, Repr

/-- The Word-level candidates for nominative *samudr-am-ní* ((62)): destress
*-ni*; foot it alone; delete /i/ into a coda cluster; delete /i/ and /m/; or
delete /ni/. -/
inductive WordCandNom where
  | destress | degenerateFoot | deleteI | deleteIM | deleteNi
  deriving DecidableEq, Repr

/-- (62): IDENT-STRESS, FT-BIN, *COMPLEXCODA, ALIGN-R ≫ MAX-μ, MAX. -/
def wordNomRanking : List (Con × Constraint WordCandNom) :=
  [ (.identStress, fun | .destress => 1 | _ => 0),
    (.ftBin, fun | .degenerateFoot => 1 | _ => 0),
    (.complexCoda, fun | .deleteI => 1 | _ => 0),
    (.alignR, fun | .deleteIM => 1 | _ => 0),
    (.maxMora, fun | .deleteI => 1 | .deleteIM => 2 | .deleteNi => 1 | _ => 0),
    (.max, fun | .deleteI => 1 | .deleteIM => 2 | .deleteNi => 2 | _ => 0) ]

def wordNomCands : List WordCandNom := [.destress, .degenerateFoot, .deleteI, .deleteIM, .deleteNi]

theorem wordNomCands_ne : wordNomCands ≠ [] := by decide

/-- (62): word-final stressed *-ni*, unable to head a binary foot, is deleted —
the short form *samudram*. -/
theorem wordNom_optimal :
    (Tableau.ofRanking wordNomCands (wordNomRanking.map (·.2)) wordNomCands_ne).optimal =
      {.deleteNi} := by
  decide

/-- The Word-level candidates for dative *samudr-am-ní-ki* ((59)): keep /mn/;
delete /n/ or /m/ with the mora; delete /m/ or /n/ with compensatory
lengthening. -/
inductive WordCandDat where
  | faithful | deleteN | deleteM | deleteMLengthen | deleteNLengthen
  deriving DecidableEq, Repr

/-- (59): *DIST-0, MAX-μ ≫ ALIGN-R ≫ MAX, IDENT-LENGTH. -/
def wordDatRanking : List (Con × Constraint WordCandDat) :=
  [ (.distZero, fun | .faithful => 1 | _ => 0),
    (.maxMora, fun | .deleteN => 1 | .deleteM => 1 | _ => 0),
    (.alignR, fun | .deleteNLengthen => 1 | _ => 0),
    (.max, fun | .faithful => 0 | _ => 1),
    (.identLength, fun | .deleteMLengthen => 1 | .deleteNLengthen => 1 | _ => 0) ]

def wordDatCands : List WordCandDat :=
  [.faithful, .deleteN, .deleteM, .deleteMLengthen, .deleteNLengthen]

theorem wordDatCands_ne : wordDatCands ≠ [] := by decide

/-- (59): the /mn/ contact is repaired by deleting /m/ and lengthening /a/ —
the long form *samudrāniki*. -/
theorem wordDat_optimal :
    (Tableau.ofRanking wordDatCands (wordDatRanking.map (·.2)) wordDatCands_ne).optimal =
      {.deleteMLengthen} := by
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

/-- The two Word-level winners are the two forms of the generalization
`weakN`: the same underlying *-am-ni* surfaces short before nothing and long
before a word-internal light syllable. -/
theorem word_level_derives_weakN :
    WordCandNom.deleteNi.nExponent = weakN (caseSuffix .nom) ∧
      WordCandDat.deleteMLengthen.nExponent = weakN (caseSuffix .dat) := by
  decide

/-! ### Phrase-level phonology (§5.3) -/

/-- The Phrase-level candidates for *samudram nunci* 'from the ocean' ((66)):
delete /m/ with or without lengthening, delete the postposition's /n/, or
keep the /mn/ contact. -/
inductive PhraseCand where
  | deleteMLengthen | deleteM | deleteN | faithful
  deriving DecidableEq, Repr

/-- (66), (68): at the Phrase level MAX outranks *DIST-0 and ALIGN-R, and
segmental faithfulness outranks prosodic faithfulness. -/
def phraseRanking : List (Con × Constraint PhraseCand) :=
  [ (.max, fun | .faithful => 0 | _ => 1),
    (.identLength, fun | .deleteMLengthen => 1 | _ => 0),
    (.distZero, fun | .faithful => 1 | _ => 0),
    (.alignR, fun _ => 0),
    (.identStress, fun _ => 0),
    (.maxMora, fun | .deleteM => 1 | _ => 0) ]

def phraseCands : List PhraseCand := [.deleteMLengthen, .deleteM, .deleteN, .faithful]

theorem phraseCands_ne : phraseCands ≠ [] := by decide

/-- (66): across the postposition boundary the /mn/ contact is kept. -/
theorem phrase_optimal :
    (Tableau.ofRanking phraseCands (phraseRanking.map (·.2)) phraseCands_ne).optimal =
      {.faithful} := by
  decide

/-- *DIST-0 is demoted below MAX from Word to Phrase ((68)). -/
theorem distZero_demoted :
    OptimalityTheory.Stratal.IsDemotedAcross .distZero phraseRanking wordDatRanking := by
  decide

/-- ALIGN-R is demoted below MAX from Word to Phrase ((68)). -/
theorem alignR_demoted :
    OptimalityTheory.Stratal.IsDemotedAcross .alignR phraseRanking wordDatRanking := by
  decide

end Aitha2026
