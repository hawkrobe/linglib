import Linglib.Phonology.Segmental.ElementTheory
import Linglib.Fragments.Tigrinya.Phonology
import Linglib.Fragments.Tigre.Phonology
import Linglib.Data.Examples.FaustLampitelli2026

/-!
# Faust and Lampitelli (2026): Guttural syneresis in Tigrinya and Tigre

This file formalizes [faust-lampitelli-2026]'s analysis of guttural syneresis: in Tigrinya and
Tigre a low vowel in an open syllable before a guttural is syncopated ([sɨmʕ-i] from
/s_mʌʕ-i/, (10), (36)), the way /i/ is before /j/, because gutturals and low vowels share the
element |A| of Element Theory ([kaye-lowenstamm-vergnaud-1985], [backley-2011];
[angoujard-1995] for the gutturals, (20)–(22)) and two adjacent |A|s fuse into one (26). The
analysis runs in Strict CV ([lowenstamm-1996], [scheer-2004]) with the lateral relations of
Government Phonology ([kaye-lowenstamm-vergnaud-1990], [charette-1991],
[scheer-segeral-2001]): `fusion` always applies to a low vowel next to an |A| consonant and
lowers it to [a] ((27), the headed |A| of (21)); `dissociation` empties the fused nucleus iff it
is properly governed by a contentful nucleus and is not the licensor of its own fused domain,
so lowering without syneresis results before a final guttural (27) and after a guttural (28);
`epenthesis` marks the nuclei that must be realized — the initial one, the one licensing a
word-internal guttural (25), the one after a silent empty nucleus — and `realizations` fills
each with the weak vowel or, by trans-guttural harmony, a copy of the vowel across the guttural
((7), (13), (37)). The operations apply in the order "rules apply" gives ([kaye-1992], (30)),
which makes syneresis opaque in (14), (16), (37). `rows_derived` derives every attested form of
(4)–(19) and (31)–(38) from the fragments' roots and the paper's templates
(`Data/Examples/FaustLampitelli2026.json`); `rows_unpredicted` records the forms of (17) and
(39) whose retained position the analysis does not predict (§3.3.3, [buckley-2000]).

## Implementation notes

* A form is a list of CV units; templates are positions (radical, geminable radical, fixed
  segment) with nuclei, instantiated by a fragment root. Gutturals do not geminate (§2.1), so
  a geminable position holding a guttural is a single unit ((12): -sʌʔɨl).
* The prefixes tɨ- and mɨ- carry empty nuclei realized by epenthesis, as in the paper's
  underlying forms (t_-, m_-); the causative ʔʌ- is lexical (19c).
* Among the realizations of a run of empty nuclei the analysis takes the Ethiosemitic option
  C▪C_C▪C (37a): reading left to right, a nucleus after a silent one is realized.
* Trans-guttural harmony "can, but does not have to apply" (§2.1), so `realizations` lists
  every option and `rows_derived` asks that each attested form be among them. Realization
  does not feed fusion again, the paper's first way out of the loop of (37b–d).
* The postvocalic spirantization of b ([nɨβaħ], (10b)) is outside the analysis; β is read as b.
* Not derived: the |I|-syneresis of (8)–(9) and the ejective asymmetry of fn. 8.

## References

* [faust-lampitelli-2026]
* [kaye-lowenstamm-vergnaud-1985]
* [backley-2011]
* [angoujard-1995]
* [lowenstamm-1996]
* [scheer-2004]
* [kaye-lowenstamm-vergnaud-1990]
* [charette-1991]
* [scheer-segeral-2001]
* [kaye-1992]
* [bye-2011]
* [buckley-2000]
-/

namespace FaustLampitelli2026

open Morphology ElementTheory Tigrinya.Phonology Data.Examples

/-! ### Element-theoretic representations (20)–(22) -/

/-- (21)–(22): [ʌ] is |A| and [a] headed |A|; the mid vowels combine |A| with |I| or |U|; the
weak vowel is the realization of an empty nucleus. -/
def vowelET : Vowel → MR
  | .a => MR.headedSimplex .A
  | .aBare => MR.simplex .A
  | .i => MR.headedSimplex .I
  | .u => MR.headedSimplex .U
  | .e => MR.headPlusOp .I .A
  | .o => MR.headPlusOp .U .A
  | .weak => MR.empty

/-- (20): every guttural contains |A|, and the pharyngeals are headed by it. -/
def gutturalET : Guttural → MR
  | .glottalStop => MR.headPlusOp .glottal .A
  | .h => MR.headPlusOp .H .A
  | .pharyngealVoiceless => (MR.numeration {.glottal, .H}).headCompose .A
  | .pharyngealVoiced => (MR.numeration {.glottal, .H, .L}).headCompose .A

theorem gutturalET_hasElement_A : ∀ g : Guttural, (gutturalET g).HasElement .A := by decide

theorem isHead_A_iff_isPharyngeal : ∀ g : Guttural, (gutturalET g).IsHead .A ↔ g.IsPharyngeal := by
  decide

/-- `IsLowA v`: the vowel's melody is |A| alone, the low vowels of (21). The mid vowels carry
|A| in a complex expression, which blocks fusion (§3.2.2). -/
def IsLowA (v : Vowel) : Prop := (vowelET v).elements = {.A}

instance : DecidablePred IsLowA := λ _ => inferInstanceAs (Decidable (_ = _))

theorem isLowA_iff_isLow : ∀ v : Vowel, IsLowA v ↔ v.IsLow := by decide

/-- The vowel with a given melody, if any. -/
def Vowel.ofMR? (m : MR) : Option Vowel :=
  [Vowel.a, .aBare, .i, .u, .e, .o, .weak].find? (vowelET · = m)

/-- The fused |A|, spanning nucleus and consonant, is headed ((21), (27)): a fused vowel is
realized with |A| as its head, so [ʌ] lowers to [a]. -/
def lowered (v : Vowel) : Vowel := (Vowel.ofMR? ((vowelET v).headCompose .A)).getD v

theorem lowered_aBare : lowered .aBare = .a := by decide

/-! ### Strict CV forms -/

/-- A consonantal position: a guttural, or any other consonant by its transcription. -/
inductive Cons where
  | guttural (g : Guttural)
  | plain (s : String)
  deriving DecidableEq, Repr

/-- The consonant written by a root segment. -/
def Cons.ofIPA (s : String) : Cons :=
  match Guttural.ofIPA? s with
  | some g => .guttural g
  | none => .plain s

/-- `c.HasA`: the consonant's melody contains |A|, which every guttural's does (20). Other
consonants carry no representation here: ejectives also lower but never trigger syneresis
(fn. 8). -/
def Cons.HasA : Cons → Prop
  | .guttural g => (gutturalET g).HasElement .A
  | .plain _ => False

instance : DecidablePred Cons.HasA := λ c => by cases c <;> unfold Cons.HasA <;> infer_instance

theorem hasA_guttural (g : Guttural) : (Cons.guttural g).HasA := gutturalET_hasElement_A g

/-- The transcription of a consonant. -/
def Cons.chars : Cons → List Char
  | .guttural g => g.toIPA.toList
  | .plain s => s.toList

/-- A nucleus in the course of a derivation (29): empty, empty but to be realized (▪), or a
lexical vowel, shaded when fused with an adjacent guttural. -/
inductive Nuc where
  | empty
  | mark
  | vowel (v : Vowel) (fused : Bool)
  deriving DecidableEq, Repr

/-- A CV unit ([lowenstamm-1996]). -/
structure CV where
  c : Cons
  v : Nuc
  deriving DecidableEq, Repr

/-- A form: a strict iteration of CV units. -/
abbrev Form := List CV

/-- The nucleus at `i` is contentful, so that it properly governs the nucleus before it (23a). -/
def Contentful (f : Form) (i : Nat) : Prop :=
  match f[i]? with
  | some ⟨_, .vowel _ _⟩ => True
  | _ => False

instance (f : Form) (i : Nat) : Decidable (Contentful f i) := by
  unfold Contentful; split <;> infer_instance

/-- The consonant at `i` contains |A|. -/
def HasAAt (f : Form) (i : Nat) : Prop :=
  match f[i]? with
  | some u => u.c.HasA
  | none => False

instance (f : Form) (i : Nat) : Decidable (HasAAt f i) := by
  unfold HasAAt; split <;> infer_instance

/-- The nucleus at `i` sits inside a geminate. -/
def GeminateInternal (f : Form) (i : Nat) : Prop :=
  match f[i]?, f[i + 1]? with
  | some u, some u' => u.c = u'.c
  | _, _ => False

instance (f : Form) (i : Nat) : Decidable (GeminateInternal f i) := by
  unfold GeminateInternal; split <;> infer_instance

/-! ### The operations of (30) -/

/-- Fusion ((26b), (27b), (28b)): a low vowel next to an |A| consonant — its own onset or the
next — fuses with it and is lowered. Fusion always applies (§3.2.2). -/
def fusion (f : Form) : Form :=
  f.mapIdx λ i u =>
    match u.v with
    | .vowel v false =>
      if IsLowA v ∧ (u.c.HasA ∨ HasAAt f (i + 1)) then ⟨u.c, .vowel (lowered v) true⟩ else u
    | _ => u

/-- Dissociation (26c): a fused nucleus is emptied iff it is properly governed by a contentful
nucleus and is not the licensor of its own fused domain — the guttural is the next onset
(Av + Ac) rather than its own (Ac + Av, (28)). -/
def dissociation (f : Form) : Form :=
  f.mapIdx λ i u =>
    match u.v with
    | .vowel _ true =>
      if HasAAt f (i + 1) ∧ ¬ u.c.HasA ∧ Contentful f (i + 1) then ⟨u.c, .empty⟩ else u
    | _ => u

/-- Epenthesis (30)–(31): the empty nuclei that must be realized. The word-final nucleus and a
nucleus inside a geminate stay empty; the initial nucleus (no initial clusters), the nucleus
licensing a word-internal guttural (25), a nucleus after a silent empty one (no triconsonantal
clusters) and a nucleus before a geminate are realized; every other empty nucleus is governed
and silent. -/
def epenthesis (f : Form) : Form :=
  (f.zipIdx.foldl (init := ([], false)) λ (acc : Form × Bool) (ui : CV × Nat) =>
    match ui.1.v with
    | .empty =>
      if ui.2 + 1 = f.length ∨ GeminateInternal f ui.2 then (acc.1 ++ [ui.1], true)
      else if ui.2 = 0 ∨ ui.1.c.HasA ∨ acc.2 ∨ GeminateInternal f (ui.2 + 1) then
        (acc.1 ++ [⟨ui.1.c, .mark⟩], false)
      else (acc.1 ++ [ui.1], true)
    | _ => (acc.1 ++ [ui.1], false)).1

/-- The derivation in the order "rules apply" gives (30): fusion creates the environment of
dissociation, which creates that of epenthesis. -/
def derive (f : Form) : Form := epenthesis (dissociation (fusion f))

/-- The lexical vowel at `i`, if any. -/
def vowelAt (f : Form) (i : Nat) : Option Vowel :=
  match f[i]? with
  | some ⟨_, .vowel v _⟩ => some v
  | _ => none

/-- The realizations of a nucleus to be realized: the weak vowel, or, by trans-guttural
harmony ((7), (19c)), a copy of the vowel across an adjacent guttural in either direction. -/
def realizeMark (f : Form) (i : Nat) : List (List Char) :=
  (['ɨ'] ::
    ((if 0 < i ∧ HasAAt f i then (vowelAt f (i - 1)).toList else []) ++
      (if HasAAt f (i + 1) then (vowelAt f (i + 1)).toList else [])).map
        (·.toIPA.toList)).dedup

/-- The realizations of the nucleus at `i`. -/
def realizeNuc (f : Form) (i : Nat) : List (List Char) :=
  match f[i]? with
  | some ⟨_, .mark⟩ => realizeMark f i
  | some ⟨_, .vowel v _⟩ => [v.toIPA.toList]
  | _ => [[]]

/-- The transcription of the consonant at `i`. -/
def consAt (f : Form) (i : Nat) : List Char :=
  match f[i]? with
  | some u => u.c.chars
  | none => []

/-- The surface forms of a form: consonants and realized nuclei in order, one form per choice
of realization. -/
def realizations (f : Form) : List (List Char) :=
  (List.range f.length).foldl (init := [[]]) λ acc i =>
    acc.flatMap λ s => (realizeNuc f i).map (s ++ consAt f i ++ ·)

/-- After fusion no unfused low vowel is adjacent to an |A| consonant: fusion always applies
among two adjacent |A|s (§3.2.2). -/
theorem fusion_fuses (f : Form) (i : Nat) (c : Cons) (v : Vowel)
    (h : (fusion f)[i]? = some ⟨c, .vowel v false⟩) :
    ¬ (IsLowA v ∧ (c.HasA ∨ HasAAt f (i + 1))) := by
  simp only [fusion, List.getElem?_mapIdx, Option.map_eq_some_iff] at h
  obtain ⟨u, -, hu⟩ := h
  split at hu
  · split at hu
    · exact absurd (congrArg CV.v hu) (by simp)
    · cases hu
      simp_all
  · cases hu
    simp_all

/-- Dissociation empties exactly the fused nuclei that are governed and not self-licensed
((26c), (28)). -/
theorem dissociation_empty_iff (f : Form) (i : Nat) (u : CV) (h : f[i]? = some u) :
    (dissociation f)[i]? = some ⟨u.c, .empty⟩ ↔
      u.v = .empty ∨ ∃ v, u.v = .vowel v true ∧
        HasAAt f (i + 1) ∧ ¬ u.c.HasA ∧ Contentful f (i + 1) := by
  simp only [dissociation, List.getElem?_mapIdx, h, Option.map_some, Option.some.injEq]
  obtain ⟨c, n⟩ := u
  cases n with
  | empty => simp
  | mark => simp
  | vowel v fused =>
    cases fused
    · simp
    · simp only [Nuc.vowel.injEq, reduceCtorEq, false_or]
      split <;> simp_all

/-! ### Templates and suffixes (§2.1) -/

/-- A templatic position: a radical, a radical geminated where it can be — gutturals cannot
geminate (§2.1, (12)) — or fixed segmental material. -/
inductive Pos where
  | rad (i : Nat)
  | gem (i : Nat)
  | seg (s : String)

/-- A template: positions with their nuclei; Q, T, L are the radicals. -/
abbrev Template := List (Pos × Nuc)

/-- A lexical vowel. -/
abbrev V (v : Vowel) : Nuc := .vowel v false

/-- A template instantiated by a root. -/
def instantiate (t : Template) (r : ConsonantalRoot String) : Option Form :=
  (t.mapM λ (pn : Pos × Nuc) =>
    match pn.1 with
    | .rad i => (r.segments[i]?).map λ s => [CV.mk (Cons.ofIPA s) pn.2]
    | .gem i => (r.segments[i]?).map λ s =>
        let c := Cons.ofIPA s
        if c.HasA then [CV.mk c pn.2] else [CV.mk c .empty, CV.mk c pn.2]
    | .seg s => some [CV.mk (Cons.ofIPA s) pn.2]).map List.flatten

/-- A suffix: a vowel filling the stem-final nucleus, then further CV units. -/
structure Suffix where
  vowel : Option Vowel := none
  rest : List (String × Nuc) := []

/-- A stem with a suffix. -/
def attach (f : Form) (s : Suffix) : Form :=
  (match s.vowel with
    | some v => f.dropLast ++ (f.getLast?.map λ u => [⟨u.c, .vowel v false⟩]).getD []
    | none => f) ++ s.rest.map λ cn => ⟨Cons.ofIPA cn.1, cn.2⟩

/-- The 2nd-person prefix tɨ-, an empty nucleus in the underlying forms of (31)–(39). -/
def prefix2 : Template := [(.seg "t", .empty)]

/-- DEP.PRF QʌTʌL (4). -/
def depPrf : Template := [(.rad 0, V .aBare), (.rad 1, V .aBare), (.rad 2, .empty)]

/-- The type B DEP.PRF QʌTTʌL, with medial gemination (18b). -/
def depPrfB : Template := [(.rad 0, V .aBare), (.gem 1, V .aBare), (.rad 2, .empty)]

/-- The type C DEP.PRF QaTʌL, with [a] after the first radical (18c). -/
def depPrfC : Template := [(.rad 0, V .a), (.rad 1, V .aBare), (.rad 2, .empty)]

/-- PRF QʌTiL (4). -/
def prf : Template := [(.rad 0, V .aBare), (.rad 1, V .i), (.rad 2, .empty)]

/-- IMPRF QʌTTɨL (4), the Tigre 2-IMP.M with its prefix (12). -/
def imprf : Template := [(.rad 0, V .aBare), (.gem 1, V .weak), (.rad 2, .empty)]

/-- 2-IMPRF tɨ-QʌTTɨL ((7), (17)). -/
def imprf2 : Template := prefix2 ++ imprf

/-- The 2-IMPRF without gemination, tɨ-QʌTɨL, as (7c) [ta-ħadɨm] shows it. -/
def imprf2NoGem : Template :=
  prefix2 ++ [(.rad 0, V .aBare), (.rad 1, V .weak), (.rad 2, .empty)]

/-- PASS-PRF tɨ-QʌTiL (17). -/
def passPrf : Template := prefix2 ++ prf

/-- IMP QɨTʌL ((5), (10)). -/
def imp : Template := [(.rad 0, .empty), (.rad 1, V .aBare), (.rad 2, .empty)]

/-- 2-JUSS tɨ-QTʌL ((5)–(6), (31)–(32)). -/
def juss2 : Template := prefix2 ++ imp

/-- The Tigre IMP QaTTɨL of (5a). -/
def impGem : Template := [(.rad 0, V .a), (.gem 1, V .weak), (.rad 2, .empty)]

/-- The Tigre 2-JUSS tɨ-QaTTɨL of (5a). -/
def jussGem2 : Template := prefix2 ++ impGem

/-- The type A gerund mɨQTaL (13). -/
def gerA : Template := [(.seg "m", .empty), (.rad 0, .empty), (.rad 1, V .a), (.rad 2, .empty)]

/-- The type B gerund mɨQTTaL (18b). -/
def gerB : Template := [(.seg "m", .empty), (.rad 0, .empty), (.gem 1, V .a), (.rad 2, .empty)]

/-- The type C gerund mɨQaTaL ((18c), (39b)). -/
def gerC : Template := [(.seg "m", .empty), (.rad 0, V .a), (.rad 1, V .a), (.rad 2, .empty)]

/-- The causative PRF ʔʌQTiL (19c). -/
def caus : Template := [(.seg "ʔ", V .aBare), (.rad 0, .empty), (.rad 1, V .i), (.rad 2, .empty)]

/-- The Tigre PRF-3MSG stem QaTL- (6). -/
def prf3 : Template := [(.rad 0, V .a), (.rad 1, .empty), (.rad 2, .empty)]

/-! ### The paradigms (4)–(19) and the derivations (31)–(39) -/

/-- The languages of the rows. -/
inductive Lang where
  | tigrinya
  | tigre
  deriving DecidableEq, Repr

/-- An attested form with the root, template and suffix that build it, and whether the analysis
predicts it. -/
structure Row where
  lang : Lang
  root : ConsonantalRoot String
  template : Template
  suffix : Option Suffix
  /-- The attested forms, hyphens removed and β read as b. -/
  forms : List (List Char)
  predicted : Bool

def langTable : List (String × Lang) := [("tigr1271", .tigrinya), ("tigr1270", .tigre)]

def tigrinyaRoots : List (String × ConsonantalRoot String) :=
  [("whip", whip), ("hear", hear), ("arrest", arrest), ("pull", pull), ("teach", teach),
   ("slaughter", slaughter), ("escape", escape), ("ask", ask), ("uncover", uncover),
   ("bark", bark), ("hurt", hurt), ("bless", bless), ("arf", arf)]

def tigreRoots : List (String × ConsonantalRoot String) :=
  [("weigh", Tigre.Phonology.weigh), ("leave", Tigre.Phonology.leave),
   ("wash", Tigre.Phonology.wash), ("flee", Tigre.Phonology.flee),
   ("getUp", Tigre.Phonology.getUp), ("whip", Tigre.Phonology.whip),
   ("ask", Tigre.Phonology.ask), ("load", Tigre.Phonology.load),
   ("uncover", Tigre.Phonology.uncover), ("pull", Tigre.Phonology.pull)]

def templateTable : List (String × Template) :=
  [("depPrf", depPrf), ("depPrfB", depPrfB), ("depPrfC", depPrfC), ("prf", prf),
   ("imprf", imprf), ("imprf2", imprf2), ("imprf2NoGem", imprf2NoGem), ("passPrf", passPrf),
   ("imp", imp), ("juss2", juss2),
   ("impGem", impGem), ("jussGem2", jussGem2), ("gerA", gerA), ("gerB", gerB), ("gerC", gerC),
   ("caus", caus), ("prf3", prf3)]

def suffixTable : List (String × Suffix) :=
  [("a", ⟨some .a, []⟩), ("i", ⟨some .i, []⟩), ("u", ⟨some .u, []⟩), ("ʌ", ⟨some .aBare, []⟩),
   ("ej", ⟨some .e, [("j", .empty)]⟩), ("om", ⟨some .o, [("m", .empty)]⟩),
   ("ku", ⟨none, [("k", V .u)]⟩), ("ka", ⟨none, [("k", V .a)]⟩)]

/-- A transcription as compared with the realizations: hyphens removed, β read as b. -/
def transcribe (s : String) : List Char :=
  (s.toList.filter (· ≠ '-')).map λ c => if c = 'β' then 'b' else c

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let lang ← List.lookup ex.language langTable
  let root ← ex.parse? "root" (match lang with | .tigrinya => tigrinyaRoots | .tigre => tigreRoots)
  let template ← ex.parse? "template" templateTable
  pure ⟨lang, root, template, ex.parse? "suffix" suffixTable,
    (ex.primaryText :: ex.alternatives.map Prod.fst).map transcribe,
    ex.feature? "predicted" != some "no"⟩

theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The underlying form of a row: its template instantiated by its root, with its suffix. -/
def Row.stem (r : Row) : Option Form :=
  (instantiate r.template r.root).map λ f => (r.suffix.map (attach f)).getD f

/-- The surface forms the analysis yields for a row. -/
def Row.realizations (r : Row) : List (List Char) :=
  match r.stem with
  | some f => FaustLampitelli2026.realizations (derive f)
  | none => []

theorem rows_stem_isSome : ∀ r ∈ rows, r.stem.isSome := by decide

/-- Every attested form of (4)–(19) and (31)–(38) is a realization of the derivation of its
underlying form. -/
theorem rows_derived : ∀ r ∈ rows, r.predicted → ∀ f ∈ r.forms, f ∈ r.realizations := by
  decide

/-- The forms of (17b–d) and (39): the position the analysis empties is realized in them, which
it does not predict (§3.3.3). -/
theorem rows_unpredicted : ∀ r ∈ rows, ¬ r.predicted → ∀ f ∈ r.forms, f ∉ r.realizations := by
  decide

end FaustLampitelli2026
