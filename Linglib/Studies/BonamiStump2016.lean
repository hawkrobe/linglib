import Linglib.Morphology.Paradigm.Function
import Linglib.Morphology.Root.Certificates
import Mathlib.Tactic.DeriveFintype

/-!
# PFM1 worked fragments: Icelandic verbs and Sanskrit nominals
[bonami-stump-2016] [stump-2001] [kiparsky-1973]

Worked fragments for the PFM1 engine of `Morphology/Paradigm/Function.lean`,
transcribing [bonami-stump-2016]'s own examples.

* **Icelandic verbs** (their Table 17.1/17.3): the paradigm function derives
  `PF(⟨KALLA, {ind pst 2sg}⟩) = kallaðir` by pure suffixation `-a`, `-ði`, `-r`
  through Blocks I–III. Basic stem choice resolves the `greip`/`grip`/`gríp`
  conflict for `GRÍPA` by narrowness (the three-cell rule beats the twelve- and
  twenty-seven-cell rules); a strong verb's Block I falls through to the
  Identity Function Default. Umlaut (`kall` ~ `köll`) and the other
  morphophonological metageneralizations are phonological substance and are not
  modelled here, so only umlaut-free cells are decided.
* **Sanskrit** (their Table 17.5, (17)): the portmanteau `-āna` of a
  consonant-final ninth-conjugation root overrides the `-nī`/`-hi` sequence,
  while a vowel-final root defaults to their composition (the Function
  Composition Default); the vocative refers to the nominative's Block-i
  exponent (block-confined syncretism), a schematic case fragment.

All predictions are `decide`-checked realized values; payload equality is never
decided (payloads are form operations).
-/

namespace BonamiStump2016

open Morphology Morphology.Exponence Morphology.PFM

/-! ### Icelandic verbs (Table 17.1, Table 17.3) -/

section Icelandic

/-- The four verbs of the fragment: `KALLA` weak.4.a, `ÆTLA` weak.4.b, `GRÍPA`
strong.1.a, `FLJÚGA` strong.2.b. -/
inductive Verb | kalla | aetla | gripa | fljuga
  deriving DecidableEq, Fintype

/-- Morphosyntactic features (decomposed: person and number separate). -/
inductive Feat | ind | sbjv | imp | prs | pst | p1 | p2 | p3 | sg | pl
  deriving DecidableEq, Fintype

open Verb Feat

/-- Weak conjugation 4 (here all weak verbs of the fragment). -/
def weak : Finset Verb := {kalla, aetla}
/-- Weak conjugation 4.b. -/
def weak4b : Finset Verb := {aetla}
/-- Strong conjugation. -/
def strong : Finset Verb := {gripa, fljuga}

local notation "IFD" => (identityDefault : Rule Verb (Finset Feat) (Action String (Finset Feat)))

/-- Block I: theme-vowel exponence ([bonami-stump-2016]'s Table 17.3). -/
def blockI : Block Verb String (Finset Feat) :=
  [ ⟨weak, {pst, pl}, .const (· ++ "u")⟩,
    ⟨Finset.univ, {sbjv, prs}, .const (· ++ "i")⟩,
    ⟨weak, {}, .const (· ++ "a")⟩,
    IFD ]

/-- Block II: past-tense exponence. -/
def blockII : Block Verb String (Finset Feat) :=
  [ ⟨weak, {pst, sg}, .const (· ++ "ði")⟩,
    ⟨weak, {pst, pl}, .const (· ++ "ðu")⟩,
    IFD ]

/-- Block III: agreement exponence. -/
def blockIII : Block Verb String (Finset Feat) :=
  [ ⟨weak4b, {imp, p2, sg}, .const (· ++ "ðu")⟩,
    ⟨Finset.univ, {imp, p2, sg}, .const id⟩,
    ⟨Finset.univ, {p2, sg}, .const (· ++ "r")⟩,
    ⟨Finset.univ, {ind, prs, p3, sg}, .const (· ++ "r")⟩,
    ⟨Finset.univ, {p1, pl}, .const (· ++ "um")⟩,
    ⟨Finset.univ, {p2, pl}, .const (· ++ "ið")⟩,
    ⟨Finset.univ, {ind, prs, p3, pl}, .const (· ++ "a")⟩,
    ⟨strong, {ind, pst, p2, sg}, .const (· ++ "st")⟩,
    IFD ]

/-- Rules of basic stem choice ([bonami-stump-2016]'s (7)); the `GRÍPA` and
`FLJÚGA` alternants list the umlaut/ablaut stems as data, not string
operations. -/
def iceStems : List (Rule Verb (Finset Feat) String) :=
  [ ⟨{kalla}, {}, "kall"⟩,
    ⟨{aetla}, {}, "ætl"⟩,
    ⟨{gripa}, {ind, pst, sg}, "greip"⟩,
    ⟨{gripa}, {pst}, "grip"⟩,
    ⟨{gripa}, {}, "gríp"⟩,
    ⟨{fljuga}, {ind, pst, sg}, "flaug"⟩,
    ⟨{fljuga}, {ind, pst}, "flug"⟩,
    ⟨{fljuga}, {pst}, "flyg"⟩,
    ⟨{fljuga}, {ind, prs, sg}, "flýg"⟩,
    ⟨{fljuga}, {}, "fljúg"⟩ ]

/-- Within one lexeme's paradigm the covert lexemic index is constant. -/
def iceStem : Finset Feat → Verb := fun _ => kalla

/-- **Flagship** ([bonami-stump-2016]'s (4a), derived through (6)): the second
person singular indicative past of `KALLA` is `kallaðir`, `kall` + `-a` + `-ði`
+ `-r` through Blocks I–III. -/
example :
    paradigmFunction (fun _ => kalla) (stemChoiceOf iceStems (fun _ => ""))
      [blockI, blockII, blockIII] (kalla, {ind, pst, p2, sg})
      = ("kallaðir", {ind, pst, p2, sg}) := by decide

/-- **Stem-choice narrowness** ([bonami-stump-2016]'s discussion of (7)): at
`⟨GRÍPA, {ind pst 1sg}⟩` the three-cell rule for `greip` overrides the
twelve-cell `grip` and twenty-seven-cell `gríp` rules. -/
example : stemChoiceOf iceStems (fun _ => "") (gripa, {ind, pst, p1, sg}) = "greip" := by decide

/-- **Identity Function Default fires**: a strong verb's Block I has no
applicable exponence rule, so the IFD leaves the stem unchanged
(`gríp`, first singular present indicative of `GRÍPA`). -/
example : evalBlock (fun _ => gripa) blockI ("gríp", {ind, prs, p1, sg})
    = ("gríp", {ind, prs, p1, sg}) := by decide

/-- **The Icelandic PFM inventory is atomic-total**: as a `Realization`, the
paradigm function realizes every cell (`paradigmRealization_isTotal`) with a
single form (`_isUnivalent`), and under the stem projection every cell exposes
a nonempty core — the lexeme-index stratum certified by
`Morphology.Root.HasNonemptyCores`. -/
theorem iceParadigm_hasNonemptyCores :
    Morphology.Root.HasNonemptyCores
      (paradigmRealization (fun _ => kalla) (stemChoiceOf iceStems (fun _ => ""))
        [blockI, blockII, blockIII])
      (fun w => {w.1}) :=
  Morphology.Root.hasNonemptyCores_of_extract_nonempty _ _
    (fun _ => Finset.singleton_nonempty _)

end Icelandic

/-! ### Sanskrit portmanteau and Function Composition Default (Table 17.5) -/

section SanskritPortmanteau

/-- Two ninth-conjugation roots: `AŚ` (consonant-final), `KRĪ` (vowel-final). -/
inductive Root | as | kri
  deriving DecidableEq, Fintype

/-- Features of the second-person singular imperative active. -/
inductive SF | p2 | sg | imp | act
  deriving DecidableEq, Fintype

open Root SF

/-- Block i: ninth-conjugation `-nī` ([bonami-stump-2016]'s (20a)). -/
def blockNi : Block Root String (Finset SF) :=
  [ ⟨Finset.univ, {}, .const (· ++ "nī")⟩ ]

/-- Block ii: subject-agreement `-hi` ([bonami-stump-2016]'s (20b)). -/
def blockHi : Block Root String (Finset SF) :=
  [ ⟨Finset.univ, {p2, sg, imp, act}, .const (· ++ "hi")⟩ ]

/-- Portmanteau Block [ii,i]: consonant-final `-āna` ([bonami-stump-2016]'s
(20c)); consonant-finality is carried by the singleton class `{AŚ}`. -/
def blockAna : Block Root String (Finset SF) :=
  [ ⟨{as}, {p2, sg, imp, act}, .const (· ++ "āna")⟩ ]

/-- The consonant-final root `AŚ` takes the portmanteau `-āna`, overriding the
`-nī`/`-hi` sequence ([bonami-stump-2016]'s (22)). -/
example : evalPortmanteau (fun _ => as) blockAna blockHi blockNi ("aś", {p2, sg, imp, act})
    = ("aśāna", {p2, sg, imp, act}) := by decide

/-- The vowel-final root `KRĪ` has no portmanteau rule, so Block [ii,i] defaults
to the composition of Blocks ii and i (the Function Composition Default),
yielding `krīnīhi` ([bonami-stump-2016]'s (23)). -/
example : evalPortmanteau (fun _ => kri) blockAna blockHi blockNi ("krī", {p2, sg, imp, act})
    = ("krīnīhi", {p2, sg, imp, act}) := by decide

end SanskritPortmanteau

/-! ### Sanskrit vocative referral (schematic, (17)) -/

section SanskritReferral

/-- A schematic nominal declension. -/
inductive Noun | dana
  deriving DecidableEq, Fintype

/-- Case and number features. -/
inductive NF | nom | voc | du
  deriving DecidableEq, Fintype

open Noun NF

/-- Retarget a vocative property set to the corresponding nominative. -/
def vocToNom (σ : Finset NF) : Finset NF := insert nom (σ.erase voc)

/-- The case block: a nominative exponence rule and a vocative rule of referral
([bonami-stump-2016]'s (17)), the referral re-consulting the block at the
nominative cell. -/
def caseBlock : Block Noun String (Finset NF) :=
  [ ⟨Finset.univ, {nom}, .const (· ++ "e")⟩,
    ⟨Finset.univ, {voc}, .referral vocToNom⟩ ]

/-- The vocative dual takes the nominative dual's Block-i exponent: a
block-confined syncretism (`dāne`), distinct from a whole-word paradigm-function
clause. -/
example : evalBlock (fun _ => dana) caseBlock ("dān", {voc, du}) = ("dāne", {voc, du}) := by decide

/-- The nominative dual it refers to. -/
example : evalBlock (fun _ => dana) caseBlock ("dān", {nom, du}) = ("dāne", {nom, du}) := by decide

end SanskritReferral

end BonamiStump2016
