import Linglib.Morphology.Paradigm.Function
import Mathlib.Tactic.DeriveFintype

/-!
# Old English HIERAN and Kashmiri morphomic tense
[stump-2020] [bonami-stump-2016] [stump-2016]

Two fragments from [stump-2020]'s survey of Paradigm Function Morphology, run on
the PFM1 engine of `Morphology/Paradigm/Function.lean` and the paradigm-linkage
model of `Morphology/Paradigm/Linkage.lean`.

* **Old English HIERAN 'hear'** (§2.2, Table 3): the finite paradigm's exploded
  segmentation into three affix blocks — past `-d-`, theme vowel, agreement — the
  Identity Function Default filling empty positions. The bare imperative `hīer`
  is the IFD firing through every block. Only the past cells and the
  agreement-suffixed present plural are decided; the present theme-vowel
  conditioning across the full paradigm needs the block rules (10), which the
  source figure does not legibly give.
* **Kashmiri tense** (§3.1, Table 4): the recent, indefinite, and remote
  preterites of Conjugations II and III are realized through four morphomic
  properties 'past a'–'past d' via a non-identity property mapping `pm`. `WUP`
  (Conj II) and `WUPH` (Conj III) inflect alike in the 'past b' cells —
  `wupyōs` (indefinite) and `wuphyōs` (recent) — because `pmII` and `pmIII` send
  different tenses to the same morphome. The composition exercises PFM2's
  content-to-form linkage over PFM1's block cascade, with `pm ≠ id`, so
  `Linkage.realize_eq_paradigmFunction` (which needs `pm = id`) does not apply.

Forms are transcribed from the article's tables; block rules are read off the
exploded segmentations, never recalled. §3.2's rule conflation (the Swahili si-
portmanteau) is out of scope for this fragment; the affirmative `nitasoma` is
included as the plain block cascade that a conflated si- rule would override.
-/

namespace Stump2020

open Morphology Morphology.Exponence Morphology.PFM

/-! ### Old English HIERAN 'hear' (§2.2, Table 3) -/

section OldEnglish

/-- The weak verb HIERAN. -/
inductive Verb | hieran
  deriving DecidableEq, Fintype

/-- Mood, tense, person, and number features (decomposed). -/
inductive Feat | ind | sbj | imp | pres | past | p1 | p2 | p3 | sg | pl
  deriving DecidableEq, Fintype

open Verb Feat

local notation "IFD" => (identityDefault : Rule Verb (Finset Feat) (Action String (Finset Feat)))

/-- Block I (position i): the past-tense formative `-d-`. -/
def blockI : Block Verb String (Finset Feat) :=
  [ ⟨Finset.univ, {past}, .const (· ++ "d")⟩,
    IFD ]

/-- Block II (position ii): the theme vowel — `-o-` in the past plural,
`-e-` elsewhere in the past (the present-tense conditioning is not modelled). -/
def blockII : Block Verb String (Finset Feat) :=
  [ ⟨Finset.univ, {past, pl}, .const (· ++ "o")⟩,
    ⟨Finset.univ, {past}, .const (· ++ "e")⟩,
    IFD ]

/-- Block III (position iii): agreement and mood — `-st` (2sg indicative,
[stump-2020]'s rule (7)), `-þ` (3sg present indicative), `-aþ` (present plural),
`-n` (past plural). -/
def blockIII : Block Verb String (Finset Feat) :=
  [ ⟨Finset.univ, {ind, p2, sg}, .const (· ++ "st")⟩,
    ⟨Finset.univ, {ind, pres, p3, sg}, .const (· ++ "þ")⟩,
    ⟨Finset.univ, {pres, pl}, .const (· ++ "aþ")⟩,
    ⟨Finset.univ, {past, pl}, .const (· ++ "n")⟩,
    IFD ]

/-- The HIERAN paradigm function: stem `hīer` through Blocks I–III. -/
def hieranPF (σ : Finset Feat) : String × Finset Feat :=
  paradigmFunction (fun _ => hieran) (fun _ => "hīer") [blockI, blockII, blockIII] (hieran, σ)

/-- 1sg past indicative: `hīer` + `-d-` + `-e-` = `hīerde`. -/
example : hieranPF {ind, past, p1, sg} = ("hīerde", {ind, past, p1, sg}) := by decide

/-- 3sg past indicative: `hīerde` (theme `-e-`, no agreement suffix). -/
example : hieranPF {ind, past, p3, sg} = ("hīerde", {ind, past, p3, sg}) := by decide

/-- 2sg past indicative: `hīer` + `-d-` + `-e-` + `-st` = `hīerdest`. -/
example : hieranPF {ind, past, p2, sg} = ("hīerdest", {ind, past, p2, sg}) := by decide

/-- Plural past indicative: `hīer` + `-d-` + `-o-` + `-n` = `hīerdon`. -/
example : hieranPF {ind, past, pl} = ("hīerdon", {ind, past, pl}) := by decide

/-- Plural present indicative: `hīer` + `-aþ` = `hīeraþ` (the theme vowel is
elided; elision is phonological and not modelled). -/
example : hieranPF {ind, pres, pl} = ("hīeraþ", {ind, pres, pl}) := by decide

/-- **The Identity Function Default through every block**: the 2sg imperative is
the bare stem `hīer`, no block contributing an exponent. -/
example : hieranPF {imp, p2, sg} = ("hīer", {imp, p2, sg}) := by decide

end OldEnglish

/-! ### Kashmiri morphomic tense (§3.1, Table 4) -/

section Kashmiri

/-- The two intransitive verbs: `WUP` 'burn inside' (Conj II) and `WUPH` 'fly'
(Conj III). -/
inductive KVerb | wup | wuph
  deriving DecidableEq, Fintype

/-- Content tenses (recent, indefinite, remote preterite), morphomic form
properties ('past a'–'past d'), and 1sg masculine agreement. -/
inductive KFeat
  | recentPast | indefPast | remotePast
  | pastA | pastB | pastC | pastD
  | p1 | sg | masc
  deriving DecidableEq, Fintype

open KVerb KFeat

/-- The stem of each verb. -/
def stemOf : KVerb → String
  | wup => "wup"
  | wuph => "wuph"

/-- **Property mapping for Conjugation II** ([stump-2020]'s (15)): recent →
'past a', indefinite → 'past b', remote → 'past c'. -/
def pmII (σ : Finset KFeat) : Finset KFeat :=
  if recentPast ∈ σ then insert pastA (σ.erase recentPast)
  else if indefPast ∈ σ then insert pastB (σ.erase indefPast)
  else if remotePast ∈ σ then insert pastC (σ.erase remotePast)
  else σ

/-- **Property mapping for Conjugation III** ([stump-2020]'s (15)): recent →
'past b', indefinite → 'past c', remote → 'past d'. The one-morphome shift from
`pmII` is what makes the two conjugations' preterites interleave. -/
def pmIII (σ : Finset KFeat) : Finset KFeat :=
  if recentPast ∈ σ then insert pastB (σ.erase recentPast)
  else if indefPast ∈ σ then insert pastC (σ.erase indefPast)
  else if remotePast ∈ σ then insert pastD (σ.erase remotePast)
  else σ

/-- The form paradigm: 1sg masculine exponents for each morphome, read off
Table 4's stem+suffix segmentation (`wupus`, `wupyōs`, `wupyās`, `wuphiyās`). -/
def formBlock : Block KVerb String (Finset KFeat) :=
  [ ⟨Finset.univ, {pastA, p1, sg, masc}, .const (· ++ "us")⟩,
    ⟨Finset.univ, {pastB, p1, sg, masc}, .const (· ++ "yōs")⟩,
    ⟨Finset.univ, {pastC, p1, sg, masc}, .const (· ++ "yās")⟩,
    ⟨Finset.univ, {pastD, p1, sg, masc}, .const (· ++ "iyās")⟩,
    (identityDefault : Rule KVerb (Finset KFeat) (Action String (Finset KFeat))) ]

/-- Realization of a form cell `⟨Z, τ⟩`: the PFM1 paradigm function on the stem
`Z` at the morphomic property set `τ`. -/
def realizeForm (z : String) (τ : Finset KFeat) : String :=
  (paradigmFunction (fun _ => wup) (fun _ => z) [formBlock] (wup, τ)).1

/-- Conjugation II linkage: the single stem, mapped by `pmII`. -/
def linkII : Linkage KVerb String (Finset KFeat) := ⟨fun l _ => stemOf l, pmII⟩

/-- Conjugation III linkage: the single stem, mapped by `pmIII`. -/
def linkIII : Linkage KVerb String (Finset KFeat) := ⟨fun l _ => stemOf l, pmIII⟩

/-- WUP recent past ('past a'): `wupus`. -/
example : linkII.realize realizeForm wup {recentPast, p1, sg, masc}
    = ("wupus", {pastA, p1, sg, masc}) := by decide

/-- WUP indefinite past ('past b'): `wupyōs`. -/
example : linkII.realize realizeForm wup {indefPast, p1, sg, masc}
    = ("wupyōs", {pastB, p1, sg, masc}) := by decide

/-- WUP remote past ('past c'): `wupyās`. -/
example : linkII.realize realizeForm wup {remotePast, p1, sg, masc}
    = ("wupyās", {pastC, p1, sg, masc}) := by decide

/-- WUPH recent past ('past b'): `wuphyōs`. -/
example : linkIII.realize realizeForm wuph {recentPast, p1, sg, masc}
    = ("wuphyōs", {pastB, p1, sg, masc}) := by decide

/-- WUPH indefinite past ('past c'): `wuphyās`. -/
example : linkIII.realize realizeForm wuph {indefPast, p1, sg, masc}
    = ("wuphyās", {pastC, p1, sg, masc}) := by decide

/-- WUPH remote past ('past d'): `wuphiyās`. -/
example : linkIII.realize realizeForm wuph {remotePast, p1, sg, masc}
    = ("wuphiyās", {pastD, p1, sg, masc}) := by decide

/-- **The morphomic mediation** ([stump-2020] §3.1): WUP's indefinite past and
WUPH's recent past have the same form correspondent property set — both 'past b',
1sg masc — even though their tenses differ. This is why they inflect alike
(`-yōs`), the content-to-form mismatch the paradigm-linkage model captures. -/
example : (linkII.corr wup {indefPast, p1, sg, masc}).2
    = (linkIII.corr wuph {recentPast, p1, sg, masc}).2 := by decide

/-- The second interleaving: WUP's remote past and WUPH's indefinite past share
the 'past c' correspondent, inflecting alike (`-yās`). -/
example : (linkII.corr wup {remotePast, p1, sg, masc}).2
    = (linkIII.corr wuph {indefPast, p1, sg, masc}).2 := by decide

end Kashmiri

/-! ### Swahili affirmative future (§3.2, Table 5) -/

section Swahili

/-- The verb SOMA 'read'. -/
inductive SwVerb | soma
  deriving DecidableEq, Fintype

/-- Tense, person, and number features. -/
inductive SwFeat | fut | s1 | sg
  deriving DecidableEq, Fintype

open SwVerb SwFeat

/-- Block −2 (tense): the future prefix `ta-`. -/
def tenseBlock : Block SwVerb String (Finset SwFeat) :=
  [ ⟨Finset.univ, {fut}, .const ("ta" ++ ·)⟩,
    (identityDefault : Rule SwVerb (Finset SwFeat) (Action String (Finset SwFeat))) ]

/-- Block −3 (subject concord): the 1sg prefix `ni-`. -/
def subjBlock : Block SwVerb String (Finset SwFeat) :=
  [ ⟨Finset.univ, {s1, sg}, .const ("ni" ++ ·)⟩,
    (identityDefault : Rule SwVerb (Finset SwFeat) (Action String (Finset SwFeat))) ]

/-- **The plain affirmative cascade**: `soma` prefixed by tense then subject
concord gives `nitasoma` 'I will read'. §3.2's negative `sitasoma` overrides this
by a conflated si- rule, the [stump-2020] direction left to future work. -/
example : paradigmFunction (fun _ => soma) (fun _ => "soma") [tenseBlock, subjBlock]
    (soma, {fut, s1, sg}) = ("nitasoma", {fut, s1, sg}) := by decide

end Swahili

end Stump2020
