import Linglib.Morphology.Realization
import Linglib.Morphology.Morphotactics.CVTemplate
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Linglib.Fragments.Hebrew.ConsonantalRoots
import Linglib.Data.Examples.Arad2005
import Mathlib.Data.List.Destutter
import Mathlib.Tactic.DeriveFintype

/-!
# Arad 2005: roots and patterns in Hebrew

Every Hebrew verb is a consonantal root in one of seven binyanim, while nouns may or may
not carry a nominal pattern. The asymmetry follows from what the patterns are: a nominal
pattern comes with its vowels, a binyan is a CV template with vowel slots and no vowels of its
own, and the vowels a verb surfaces with are the exponent of Voice — a morphosyntactic feature
that must be spelled out, by a rule whose context is the binyan already inserted under v. A
verb therefore needs the template so that Voice has slots to fill; a noun that is pronounceable
on its own needs nothing. The same root takes unrelated meanings in different patterns
(Multiple Contextualized Meaning), whereas a verb formed from an existing noun keeps the
noun's meaning: roots are interpreted at the first category head that merges with them, and
a later head sees only that word. The contrast shows in the phonology too — a noun-derived
verb is built by modifying the noun's own stem, carrying its prefix and its consonant clusters
into the binyan, where a root-derived verb associates bare consonants to the template.

## Main definitions

* `Binyan`, `Binyan.skeleton`: the five verbal templates as slot skeletons; `mishqalim` the
  nominal patterns with their vowels.
* `voiceSpellout`: the Voice vocabulary items in the context of the binyan; `verb` the
  root-derived verb; `denominal` the noun-derived verb by stem modification.
* `rootMeanings`: a root's glosses in a pattern, read off the rows.

## References

* [arad-2005]
* [mccarthy-1981] — root-to-template association
* [bat-el-1994] — stem modification and cluster transfer
-/

namespace Arad2005

open Morphology DistributedMorphology Data.Examples

/-! ### Binyanim as the spell-out of v and Voice (§2.5) -/

/-- A slot of a pattern skeleton, in the book's subscripted notation: a root radical by
index, an open vowel slot, or a fixed segment. -/
inductive Slot where
  | radical (i : ℕ)
  | vowel
  | fixed (s : String) (slot : CVSlot)
  deriving DecidableEq, Repr

/-- A fixed vowel of a pattern. -/
def Slot.isFixedVowel : Slot → Bool
  | .fixed _ .V => true
  | _ => false

/-- A radical position. -/
def Slot.isRadical : Slot → Bool
  | .radical _ => true
  | _ => false

/-- The C or V slot a pattern slot occupies. -/
def Slot.cv : Slot → CVSlot
  | .radical _ => .C
  | .vowel => .V
  | .fixed _ c => c

/-- The five binyan templates (24b): vowel slots without vowels, the prefixes *n-*, *h-*,
*hit-*, and in CVCCVC the geminate slot of the middle radical. -/
inductive Binyan where
  | cvcvc
  | nvccvc
  | cvccvc
  | hvccvc
  | hitcvccvc
  deriving DecidableEq, Repr, Fintype

/-- The skeletons of (3) and (24b). -/
def Binyan.skeleton : Binyan → List Slot
  | .cvcvc => [.radical 0, .vowel, .radical 1, .vowel, .radical 2]
  | .nvccvc => [.fixed "n" .C, .vowel, .radical 0, .radical 1, .vowel, .radical 2]
  | .cvccvc => [.radical 0, .vowel, .radical 1, .radical 1, .vowel, .radical 2]
  | .hvccvc => [.fixed "h" .C, .vowel, .radical 0, .radical 1, .vowel, .radical 2]
  | .hitcvccvc =>
    [.fixed "h" .C, .fixed "i" .V, .fixed "t" .C, .radical 0, .vowel, .radical 1, .radical 1,
      .vowel, .radical 2]

/-- The binyan and Voice value of a numbered pattern, by (3) and (5): the passives are
patterns 4 and 6. -/
def Binyan.ofPattern : String → Option (Binyan × Bool)
  | "1" => some (.cvcvc, true)
  | "2" => some (.nvccvc, true)
  | "3" => some (.cvccvc, true)
  | "4" => some (.cvccvc, false)
  | "5" => some (.hvccvc, true)
  | "6" => some (.hvccvc, false)
  | "7" => some (.hitcvccvc, true)
  | _ => none

/-- Nominal patterns carry their vowels (24a). -/
def mishqalim : List (List Slot) :=
  [[.fixed "m" .C, .fixed "i" .V, .radical 0, .radical 1, .fixed "a" .V, .radical 2],
    [.fixed "m" .C, .fixed "i" .V, .radical 0, .radical 1, .fixed "o" .V, .radical 2],
    [.fixed "m" .C, .fixed "a" .V, .radical 0, .radical 1, .fixed "e" .V, .radical 2],
    [.fixed "t" .C, .fixed "a" .V, .radical 0, .radical 1, .fixed "i" .V, .radical 2],
    [.radical 0, .radical 1, .fixed "a" .V, .radical 2],
    [.radical 0, .fixed "a" .V, .radical 1, .fixed "i" .V, .radical 2]]

/-- The association lines a skeleton dictates: radicals and fixed segments at their positions,
vowels left to right into the vowel slots. -/
def Slot.associations : List Slot → ℕ → ℕ → ℕ → List Association
  | [], _, _, _ => []
  | .radical k :: rest, i, nv, nf => ⟨.root, k, i⟩ :: associations rest (i + 1) nv nf
  | .vowel :: rest, i, nv, nf => ⟨.vocalism, nv, i⟩ :: associations rest (i + 1) (nv + 1) nf
  | .fixed _ _ :: rest, i, nv, nf => ⟨.affix, nf, i⟩ :: associations rest (i + 1) nv (nf + 1)

/-- Fill a skeleton with a root and a vocalism: association by the subscripts. -/
def fill (sk : List Slot) (r : ConsonantalRoot String) (voc : List String) :
    TemplateMatch String where
  root := r
  vocalism := voc
  affix := sk.filterMap fun | .fixed s _ => some s | _ => none
  template := ⟨sk.map Slot.cv⟩
  associations := Slot.associations sk 0 0 0

/-- The features of Voice and of the v exponent it sees. -/
inductive VoiceFeature where
  | active
  | passive
  | binyan (b : Binyan)
  deriving DecidableEq, Repr

/-- The Voice spell-out (25): a vocalism in the context of the binyan inserted under v. -/
def voiceSpellout : List (VocabularyItem VoiceFeature (List String)) :=
  [⟨⟨[.active], [[.binyan .cvcvc]], []⟩, ["a", "a"]⟩,
    ⟨⟨[.active], [[.binyan .nvccvc]], []⟩, ["i", "a"]⟩,
    ⟨⟨[.active], [[.binyan .cvccvc]], []⟩, ["i", "e"]⟩,
    ⟨⟨[.active], [[.binyan .hvccvc]], []⟩, ["i", "i"]⟩,
    ⟨⟨[.active], [[.binyan .hitcvccvc]], []⟩, ["a", "e"]⟩,
    ⟨⟨[.passive], [[.binyan .cvccvc]], []⟩, ["u", "a"]⟩,
    ⟨⟨[.passive], [[.binyan .hvccvc]], []⟩, ["u", "a"]⟩]

/-- The Voice node once v has been realized: its feature, with the binyan as the inner
neighbor. -/
def voiceNode (b : Binyan) (active : Bool) : Neighborhood (List VoiceFeature) :=
  ⟨[if active then .active else .passive], [[.binyan b]], []⟩

/-- The surface string, with Modern Hebrew degemination. -/
def surface (m : TemplateMatch String) : String := String.join (m.spellout.destutter (· ≠ ·))

/-- The fricative allophone of a stop. -/
def fricative : String → String
  | "p" => "f"
  | "b" => "v"
  | "k" => "x"
  | s => s

/-- Spirantization of *p*, *b*, *k* after a vowel, blocked in the geminate slot: *siper*,
not *sifer*. -/
def spirantize (l : List String) : List String :=
  l.zipIdx.map fun p =>
    if 0 < p.2 ∧ l.getD (p.2 - 1) "" ∈ ["a", "e", "i", "o", "u"] ∧ l.getD (p.2 + 1) "" ≠ p.1
    then fricative p.1 else p.1

/-- A root-derived verb: the binyan under v, Voice's vowels by (25) in its context, the root
associated by the skeleton (28), spirantization and degemination at the surface. `none`
where Voice has no exponent. -/
def verb (r : ConsonantalRoot String) (b : Binyan) (active : Bool) : Option String :=
  (subsetPrinciple voiceSpellout (voiceNode b active)).map fun voc =>
    let m := fill b.skeleton r voc
    String.join ((spirantize m.spellout).destutter (· ≠ ·))

/-- The roots of (3) and (6), from the fragment. -/
def rootOfLabel : String → Option (ConsonantalRoot String)
  | "lmd" => some Hebrew.lmd
  | "spr" => some Hebrew.spr
  | "qlt" => some Hebrew.qlt
  | "pll" => some Hebrew.pll
  | "npc" => some Hebrew.npc
  | "xlq" => some Hebrew.xlq
  | "str" => some Hebrew.str
  | "pqd" => some Hebrew.pqd
  | _ => none

/-- The verbs of (3) and (6) are derived: the binyan under v, Voice's vowels in the binyan's
context, spirantization and degemination at the surface. -/
theorem rows_verbs :
    ∀ r ∈ Examples.all, ∀ root ∈ (r.feature? "root" >>= rootOfLabel).toList,
      ∀ bv ∈ (r.feature? "pattern" >>= Binyan.ofPattern).toList,
        verb root bv.1 bv.2 = some r.primaryText := by
  decide +kernel

/-- Voice must be spelled out: every binyan has an active vocalism, and a passive one exactly
in CVCCVC and hVCCVC (25). -/
theorem voice_obligatory :
    (∀ b : Binyan, (subsetPrinciple voiceSpellout (voiceNode b true)).isSome) ∧
      ∀ b : Binyan, (subsetPrinciple voiceSpellout (voiceNode b false)).isSome ↔
        (b = .cvccvc ∨ b = .hvccvc) := by
  decide

/-- One feature, five exponents: [+active] is realized five ways, the choice fixed by the
binyan (25). -/
theorem active_many_to_one :
    ((voiceSpellout.filter (·.site.focus = [.active])).map (·.exponent)).Nodup ∧
      (voiceSpellout.filter (·.site.focus = [.active])).length = 5 := by
  decide

/-- Every binyan has two vowel slots and no vowels of its own; the prefix of hitCVCCVC is its
only fixed vowel (24b). -/
theorem binyanim_vowel_slots :
    ∀ b : Binyan, b.skeleton.count .vowel = 2 ∧
      ∀ p ∈ b.skeleton, p.isFixedVowel → b = .hitcvccvc := by
  decide

/-- Nominal patterns have no vowel slots: their vowels are their own (24a). -/
theorem mishqalim_no_vowel_slots : ∀ p ∈ mishqalim, p.count .vowel = 0 := by decide

/-! ### Noun-derived verbs by stem modification (§2.6, §7.5) -/

/-- A transliterated vowel. -/
def isVowel (c : Char) : Bool := c ∈ ['a', 'e', 'i', 'o', 'u']

/-- The stem of a base word: without a final vowel or the suffix *-et*, which are not part of
the stem (32). -/
def stem (base : String) : List Char :=
  let s := base.toList
  if s.reverse.take 2 = ['t', 'e'] then s.take (s.length - 2)
  else if (s.getLast?.map isVowel).getD false then s.dropLast
  else s

/-- Stray Erasure: only the first and the last vowel of the stem survive resyllabification
into the bisyllabic template. -/
def erase (s : List Char) : List Char :=
  let idx := (s.zipIdx.filter fun p => isVowel p.1).map (·.2)
  s.zipIdx.filterMap fun p =>
    if isVowel p.1 ∧ some p.2 ≠ idx.head? ∧ some p.2 ≠ idx.getLast? then none else some p.1

/-- The consonant clusters of a stem, the vowels between them dropped. -/
def clusters (s : List Char) : List String :=
  s.foldr (fun c acc =>
    if isVowel c then "" :: acc
    else match acc with
      | [] => [String.singleton c]
      | h :: t => (String.singleton c ++ h) :: t) [""]

/-- Emit a skeleton whose radical runs have been collapsed, one cluster per run and one Voice
vowel per slot. -/
def emit : List Slot → List String → List String → Option String
  | [], [], [] => some ""
  | .fixed s _ :: rest, cs, vs => (s ++ ·) <$> emit rest cs vs
  | .vowel :: rest, cs, v :: vs => (v ++ ·) <$> emit rest cs vs
  | .radical _ :: rest, c :: cs, vs => (c ++ ·) <$> emit rest cs vs
  | _, _, _ => none

/-- A noun-derived verb: the base's stem is modified to the binyan's prosody and its vowels
overwritten by Voice's. Clusters are carried into the template whole when they match its
runs of consonant slots; otherwise the consonants are resyllabified one per slot. -/
def denominal (base : String) (b : Binyan) (active : Bool := true) : Option String :=
  (subsetPrinciple voiceSpellout (voiceNode b active)).bind fun voc =>
    let s := erase (stem base)
    let runs := b.skeleton.destutter fun p q => ¬ (p.isRadical ∧ q.isRadical)
    if (clusters s).length = runs.countP (·.isRadical) then emit runs (clusters s) voc
    else if (s.filter fun c => !isVowel c).length = b.skeleton.countP (·.isRadical) then
      some (surface (fill b.skeleton ⟨(s.filter fun c => !isVowel c).map String.singleton⟩ voc))
    else none

/-- The noun-derived verbs of (29), (32), (39), (40), and Ch. 7 (6) are derived from their
bases in the stated pattern: *misgeret* → *misger* with the nominal *m-* carried along,
*transfer* → *trinsfer* with its clusters intact, *xrop* → *xarap* resyllabified into
CVCVC. -/
theorem rows_denominal :
    ∀ r ∈ Examples.all, ∀ base ∈ (r.feature? "base").toList,
      ∀ bv ∈ (r.feature? "pattern" >>= Binyan.ofPattern).toList,
        denominal base bv.1 bv.2 = some r.primaryText := by
  decide +kernel

/-- Every noun-derived verb of the rows is the stem modification of its base into some
binyan. -/
theorem rows_denominal_exists :
    ∀ r ∈ Examples.all, ∀ base ∈ (r.feature? "base").toList,
      ∃ b : Binyan, ∃ active, denominal base b active = some r.primaryText := by
  decide +kernel

/-! ### Multiple Contextualized Meaning (Ch. 3, Ch. 7) -/

/-- The words the rows list for a root in a pattern. -/
def rootForms (root pattern : String) : Finset String :=
  ((Examples.all.filter fun r =>
    r.feature? "root" = some root ∧ r.feature? "pattern" = some pattern).map
      (·.primaryText)).toFinset

/-- The glosses the rows list for a root in a pattern. -/
def rootMeanings (root pattern : String) : Finset String :=
  ((Examples.all.filter fun r =>
    r.feature? "root" = some root ∧ r.feature? "pattern" = some pattern).filterMap
      (·.feature? "gloss")).toFinset

/-- Roots as an interpreted realization system over the book's pattern labels. -/
def roots : Realization.Interpreted String String String String where
  realize := rootForms
  interp := rootMeanings

/-- A root with two glosses in two patterns is allosemous. -/
theorem roots_allosemous {root c c' m m'} (h : m ∈ rootMeanings root c)
    (h' : m' ∈ rootMeanings root c') (hne : m ≠ m') : roots.IsAllosemous root :=
  ⟨c, c', m, h, m', h', hne⟩

/-- √sgr: *sagar* 'close' against *hisgir* 'extradite' (Ch. 7 (5)). -/
theorem sgr_mcm : roots.IsAllosemous "sgr" :=
  roots_allosemous (c := "CaCaC") (c' := "hiCCiC") (m := "close") (m' := "extradite")
    (by decide +kernel) (by decide +kernel) (by decide)

/-- √qlt: *qelet* 'input' against *taqlit* 'a record' (Ch. 7 (4)). -/
theorem qlt_mcm : roots.IsAllosemous "qlt" :=
  roots_allosemous (c := "CeCeC") (c' := "taCCiC") (m := "input") (m' := "a record")
    (by decide +kernel) (by decide +kernel) (by decide)

/-- √xšb: *xašav* 'to think' against *maxšev* 'a computer' (Ch. 7 (3)). -/
theorem xsb_mcm : roots.IsAllosemous "xšb" :=
  roots_allosemous (c := "CaCaC") (c' := "maCCeC") (m := "to think")
    (m' := "a computer, calculator") (by decide +kernel) (by decide +kernel) (by decide)

/-- √šmn: *šemen* 'oil' against *šamenet* 'cream' (Ch. 7 (2)). -/
theorem smn_mcm : roots.IsAllosemous "šmn" :=
  roots_allosemous (c := "CeCeC") (c' := "CaCCeCet") (m := "oil, grease") (m' := "cream")
    (by decide +kernel) (by decide +kernel) (by decide)

end Arad2005
