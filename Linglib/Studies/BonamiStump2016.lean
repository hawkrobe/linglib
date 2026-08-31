import Linglib.Morphology.Paradigm.Function
import Mathlib.Tactic.DeriveFintype

/-!
# Bonami and Stump 2016: Paradigm Function Morphology

This file formalizes the worked PFM1 fragments of [bonami-stump-2016] on the engine of
`Morphology/Paradigm/Function.lean`: the finite paradigm of four Icelandic verbs (rules of basic
stem choice, three blocks of rules of exponence, the Identity Function Default), the Sanskrit
ninth-conjugation portmanteau with the Function Composition Default, and the Sanskrit vocative
rule of referral.

Morphophonological metageneralizations (umlaut, vowel loss, coalescence) are phonological
substance outside the engine, so only cells they leave untouched are decided; the strong verbs'
ablaut alternants enter as basic stems, as in the chapter.

## Main definitions

* `iceStems`, `blockI`, `blockII`, `blockIII`, `pf` — the Icelandic rules of basic stem choice,
  rules of exponence, and paradigm function
* `blockNi`, `blockHi`, `blockAna` — the Sanskrit `-nī`, `-hi` and portmanteau `-āna` blocks
* `caseBlock` — a Sanskrit case block with the vocative rule of referral

## Main results

* `pf_kalla`, `pf_gripa_imp`, `pf_fljuga`, `pf_gripa_pst` — the chapter's flagship realizations
* `stem_gripa_pst` — narrowness resolves the `greip`/`grip`/`gríp` stem conflict
* `blockIII_narrowness` — the three competing second-singular rules are strictly ordered
* `as_portmanteau`, `kri_composition` — `-āna` overrides `-nī-hi`; a vowel-final root defaults
  to the composition of Blocks ii and i
* `voc_refers_to_nom` — the vocative dual takes the nominative dual's exponent

## References

* [bonami-stump-2016]
* [stump-2001]
-/

namespace BonamiStump2016

open Morphology Morphology.Exponence Morphology.PFM

/-! ### Icelandic verbs -/

section Icelandic

/-- The four verbs of Table 17.1: KALLA (weak.4.a), ÆTLA (weak.4.b), GRÍPA (strong.1.a),
FLJÚGA (strong.2.b). -/
inductive Verb | kalla | aetla | gripa | fljuga
  deriving DecidableEq, Fintype

/-- Morphosyntactic properties; person and number are separate properties, as in the chapter's
`{pst sg}`. -/
inductive Feat | ind | sbjv | imp | prs | pst | p1 | p2 | p3 | sg | pl
  deriving DecidableEq, Fintype

open Verb Feat

local notation "ExpoRule" => PFM.Rule Verb (Finset Feat) (Action String (Finset Feat))
local notation "IFD" => (identityDefault : ExpoRule)

/-- Weak conjugation 4. -/
def weak : Finset Verb := {kalla, aetla}
/-- Weak conjugation 4.b. -/
def weak4b : Finset Verb := {aetla}
/-- The strong conjugations. -/
def strong : Finset Verb := {gripa, fljuga}

/-- Block I of Table 17.3: theme vowels. -/
def blockI : Block Verb String (Finset Feat) :=
  [ ⟨weak, {pst, pl}, .const (· ++ "u")⟩,
    ⟨Finset.univ, {sbjv, prs}, .const (· ++ "i")⟩,
    ⟨weak, {}, .const (· ++ "a")⟩,
    IFD ]

/-- Block II of Table 17.3: past-tense exponence. -/
def blockII : Block Verb String (Finset Feat) :=
  [ ⟨weak, {pst, sg}, .const (· ++ "ði")⟩,
    ⟨weak, {pst, pl}, .const (· ++ "ðu")⟩,
    IFD ]

/-- The weak.4.b imperative `-ðu`. -/
def weak4bImp : ExpoRule := ⟨weak4b, {imp, p2, sg}, .const (· ++ "ðu")⟩
/-- The zero exponent of the second-singular imperative. -/
def zeroImp : ExpoRule := ⟨Finset.univ, {imp, p2, sg}, .const id⟩
/-- The general second-singular `-r`. -/
def rSg2 : ExpoRule := ⟨Finset.univ, {p2, sg}, .const (· ++ "r")⟩

/-- Block III of Table 17.3: agreement and mood exponence. -/
def blockIII : Block Verb String (Finset Feat) :=
  [ weak4bImp, zeroImp, rSg2,
    ⟨Finset.univ, {ind, prs, p3, sg}, .const (· ++ "r")⟩,
    ⟨Finset.univ, {p1, pl}, .const (· ++ "um")⟩,
    ⟨Finset.univ, {p2, pl}, .const (· ++ "ið")⟩,
    ⟨Finset.univ, {ind, prs, p3, pl}, .const (· ++ "a")⟩,
    ⟨strong, {ind, pst, p2, sg}, .const (· ++ "st")⟩,
    IFD ]

/-- Rules of basic stem choice (7); the strong verbs' ablaut alternants are listed as stems. -/
def iceStems : List (PFM.Rule Verb (Finset Feat) String) :=
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

/-- The covert lexemic index (11): every stem in `v`'s paradigm is indexed `v`. -/
def lindex (v : Verb) : String → Verb := fun _ => v

/-- The Icelandic paradigm function (13): basic stem choice, then Blocks I–III. -/
def pf (v : Verb) (σ : Finset Feat) : String × Finset Feat :=
  paradigmFunction (lindex v) (stemChoiceOf iceStems (fun _ => "")) [blockI, blockII, blockIII]
    (v, σ)

/-- (4a): `kallaðir`, derived by (6) as `kall` + `-a` + `-ði` + `-r`. -/
theorem pf_kalla : pf kalla {ind, pst, p2, sg} = ("kallaðir", {ind, pst, p2, sg}) := by decide

/-- (4c): the bare imperative `gríp` — the IFD fires in Blocks I and II, and the zero imperative
exponent preempts `-r` in Block III. -/
theorem pf_gripa_imp : pf gripa {imp, p2, sg} = ("gríp", {imp, p2, sg}) := by decide

/-- (4d): `flaug`, the narrowest stem-choice rule for FLJÚGA followed by the IFD in every block. -/
theorem pf_fljuga : pf fljuga {ind, pst, p1, sg} = ("flaug", {ind, pst, p1, sg}) := by decide

/-- Table 17.1: the strong second-singular past `greipst`, the strong-verb rule preempting `-r`. -/
theorem pf_gripa_pst : pf gripa {ind, pst, p2, sg} = ("greipst", {ind, pst, p2, sg}) := by decide

/-- The conflict among (7c)–(7e) at `⟨GRÍPA, {ind pst 1sg}⟩` resolves to the three-cell rule. -/
theorem stem_gripa_pst :
    stemChoiceOf iceStems (fun _ => "") (gripa, {ind, pst, p1, sg}) = "greip" := by decide

/-- A strong verb's Block I has no applicable rule of exponence, so the IFD leaves the stem. -/
theorem blockI_gripa : evalBlock (lindex gripa) blockI ("gríp", {ind, prs, p1, sg})
    = ("gríp", {ind, prs, p1, sg}) := by decide

/-- The example of (14): `[iii : ⟨ætla, {imp 2sg}⟩] = ⟨ætlaðu, σ⟩`. -/
theorem nar_aetla_imp : evalBlock (lindex aetla) blockIII ("ætla", {imp, p2, sg})
    = ("ætlaðu", {imp, p2, sg}) := by decide

/-- The example of (15): the weak.4.b `-ðu` is narrower than the zero imperative, which is
narrower than `-r`. -/
theorem blockIII_narrowness : weak4bImp < zeroImp ∧ zeroImp < rSg2 := by decide

end Icelandic

/-! ### Sanskrit portmanteau and the Function Composition Default -/

section Portmanteau

/-- Two ninth-conjugation verbs: consonant-final AŚ 'eat' and vowel-final KRĪ 'buy'. -/
inductive NinthVerb | as | kri
  deriving DecidableEq, Fintype

/-- Properties of the second-person singular imperative active. -/
inductive SF | p2 | sg | imp | act
  deriving DecidableEq, Fintype

open NinthVerb SF

/-- Block i, (20a): ninth-conjugation `-nī`. -/
def blockNi : Block NinthVerb String (Finset SF) :=
  [ ⟨Finset.univ, {}, .const (· ++ "nī")⟩ ]

/-- Block ii, (20b): second-singular imperative active `-hi`. -/
def blockHi : Block NinthVerb String (Finset SF) :=
  [ ⟨Finset.univ, {p2, sg, imp, act}, .const (· ++ "hi")⟩ ]

/-- Block [ii,i], (20c): `-āna` after a consonant-final root, consonant-finality carried by the
class `{AŚ}`. -/
def blockAna : Block NinthVerb String (Finset SF) :=
  [ ⟨{as}, {p2, sg, imp, act}, .const (· ++ "āna")⟩ ]

/-- (21) at (22): AŚ takes the portmanteau `-āna` (Table 17.5). -/
theorem as_portmanteau :
    evalPortmanteau (fun _ => as) blockAna blockHi blockNi ("aś", {p2, sg, imp, act})
      = ("aśāna", {p2, sg, imp, act}) := by decide

/-- No portmanteau rule applies at (23). -/
theorem kri_no_portmanteau : applicable blockAna (kri, ({p2, sg, imp, act} : Finset SF)) = [] :=
  rfl

/-- (23): Block [ii,i] defaults to the composition of Blocks ii and i, the Function Composition
Default (24). -/
theorem kri_fcd :
    evalPortmanteau (fun _ => kri) blockAna blockHi blockNi ("krī", {p2, sg, imp, act})
      = evalBlock (fun _ => kri) blockHi
          (evalBlock (fun _ => kri) blockNi ("krī", {p2, sg, imp, act})) :=
  evalPortmanteau_eq_comp_of_not_applies _ _ _ _ _ kri_no_portmanteau

/-- Table 17.5: `krīnīhi`. -/
theorem kri_composition :
    evalPortmanteau (fun _ => kri) blockAna blockHi blockNi ("krī", {p2, sg, imp, act})
      = ("krīnīhi", {p2, sg, imp, act}) := by decide

end Portmanteau

/-! ### Sanskrit vocative referral -/

section Referral

/-- The neuter a-stem DĀNA 'gift' of Table 17.2. -/
inductive Noun | dana
  deriving DecidableEq, Fintype

/-- Case and number properties. -/
inductive NF | nom | voc | du
  deriving DecidableEq, Fintype

open Noun NF

/-- `σ/{nom}` of (17): the property set like `σ` but nominative. -/
def toNom (σ : Finset NF) : Finset NF := insert nom (σ.erase voc)

/-- Block i: a nominative exponent and the vocative rule of referral (17), which re-consults the
block at the nominative cell. -/
def caseBlock : Block Noun String (Finset NF) :=
  [ ⟨Finset.univ, {nom}, .const (· ++ "e")⟩,
    ⟨Finset.univ, {voc}, .referral toNom⟩ ]

/-- The vocative dual takes the nominative dual's exponent: a syncretism confined to Block i,
unlike the whole-word clause (5). -/
theorem voc_refers_to_nom :
    (evalBlock (fun _ => dana) caseBlock ("dān", {voc, du})).1
      = (evalBlock (fun _ => dana) caseBlock ("dān", {nom, du})).1 := by decide

/-- Table 17.2: the vocative dual `dāne`. -/
theorem voc_du : evalBlock (fun _ => dana) caseBlock ("dān", {voc, du}) = ("dāne", {voc, du}) := by
  decide

end Referral

end BonamiStump2016
