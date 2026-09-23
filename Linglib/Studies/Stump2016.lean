module

public import Linglib.Morphology.Paradigm.Function
public import Mathlib.Tactic.DeriveFintype

/-!
# Stump (2016): Inflectional Paradigms

This file formalizes two of the deviations from the canonical content-to-form isomorphism
argued for in [stump-2016], on the paradigm-linkage model of the substrate's
`Morphology.Linkage`. Latin deponent verbs inflect by means of the morphology that
ordinarily expresses a verb's passive forms: the deponent *cōnārī* realizes its active
content cells with the passive personal endings a regular verb like *parāre* uses only for
its passive, and lacks passive-meaning forms. This is a property mapping that crosses the
voice axis: the regular verb's linkage preserves the content cell's property set and is
canonical (`parareLinkage_isCanonical`), while the deponent's replaces active with passive
on every active cell (`conari_deviates_on_every_active_cell`,
`conari_active_realized_by_passive_form`), so that the same active content cell has an
active form correspondent for the one verb and a passive one for the other
(`depon_vs_regular`).

The Kashmiri recent, indefinite and remote preterites of the intransitive conjugations II
and III are realized through four morphomic properties, the past morphomes a to d, by
property mappings that differ by one morphome (`pmII`, `pmIII`): the indefinite past of
WUP and the recent past of WUPH share the past b form correspondent and inflect alike
(`kashmiri_inflect_alike`), as do the remote past of WUP and the indefinite past of WUPH
(`kashmiri_inflect_alike_pastC`). The form cells are realized by the PFM block cascade of
`Morphology.Paradigm.Function`.

## Implementation notes

The Latin cells are abstracted to voice and agreement, with the inflection-class index and
tense, aspect and mood held constant, and no realizations are attached to the Latin
linkages. The Kashmiri forms and their stem-plus-suffix segmentation are the book's
display of Grierson's paradigms, with the first person singular masculine exponents only.

## References

* [stump-2016]
-/

@[expose] public section

namespace Stump2016

open Morphology

/-- Voice: the axis Latin deponency crosses ([stump-2016] §12.1). -/
inductive Voice where
  | active
  | passive
  deriving DecidableEq, Repr

/-- Person–number agreement: the six cells of the imperfective present
indicative ([stump-2016] Tables 12.1–12.2). -/
inductive Agr where
  | s1 | s2 | s3 | p1 | p2 | p3
  deriving DecidableEq, Repr

/-- A morphosyntactic property set, abstracted to the voice axis and the
agreement features relevant to Latin deponency (the inflection-class index and
tense/aspect/mood, held constant across the paradigm below, are elided). -/
structure Cell where
  agr : Agr
  voice : Voice
  deriving DecidableEq, Repr

/-- The two Latin lexemes contrasted: the deponent *cōnārī* and the regular
*parāre*. -/
inductive LatinVerb where
  | conari
  | parare
  deriving DecidableEq, Repr

/-- Their stems. -/
inductive LatinStem where
  | cona
  | para
  deriving DecidableEq, Repr

/-- The **deponent linkage** of *cōnārī*: a single stem and the voice-flipping
property mapping `pm2c` ([stump-2016] §12.1), which sends an active content cell
to a passive form cell. -/
def conariLinkage : Linkage LatinVerb LatinStem Cell where
  stems := λ _ _ => {.cona}
  pm := λ _ σ => { σ with voice := .passive }

/-- The **regular linkage** of *parāre*: a single stem and the identity property
mapping, canonical on the voice axis ([stump-2016] §7.1). -/
def parareLinkage : Linkage LatinVerb LatinStem Cell where
  stems := λ _ _ => {.para}
  pm := λ _ σ => σ

/-- *cōnārī*'s six active content cells ([stump-2016] Table 12.2). -/
def conariContentCells : List Cell :=
  [⟨.s1, .active⟩, ⟨.s2, .active⟩, ⟨.s3, .active⟩,
   ⟨.p1, .active⟩, ⟨.p2, .active⟩, ⟨.p3, .active⟩]

/-- The regular verb's linkage is canonical: property-set preserving (`pm = id`)
and stem invariant ([stump-2016] §7.1, characteristics (2a)–(2b)). -/
theorem parareLinkage_isCanonical : parareLinkage.IsCanonical :=
  Linkage.canonical_isCanonical (λ _ : LatinVerb => LatinStem.para)

/-- The deponent property mapping flips voice on every active cell. -/
theorem conari_pm_flips_voice (l : LatinVerb) (σ : Cell) :
    (conariLinkage.pm l σ).voice = .passive := rfl

/-- The deponent linkage deviates from the canonical isomorphism on every active
content cell: its property mapping moves the cell off its own property set. -/
theorem conari_deviates_on_every_active_cell (l : LatinVerb) (σ : Cell)
    (h : σ.voice = .active) : conariLinkage.pm l σ ≠ σ := by
  intro heq
  have : Voice.passive = Voice.active := h ▸ congrArg Cell.voice heq
  exact absurd this (by decide)

/-- Hence the deponent linkage is not property-preserving, so not canonical. -/
theorem conariLinkage_not_canonical : ¬ conariLinkage.IsCanonical := by
  rintro ⟨-, -, -, -, hpp⟩
  exact conari_deviates_on_every_active_cell .conari ⟨.s1, .active⟩ rfl (hpp _ _)

/-- **The deponency claim**: every active content cell of *cōnārī* has a
*passive* form correspondent — active content realized by passive morphology
([stump-2016] §12.1). -/
theorem conari_active_realized_by_passive_form (l : LatinVerb) (σ : Cell) :
    (conariLinkage.corr l σ).image (·.2.voice) = {.passive} := by
  simp [conariLinkage, Linkage.corr]

/-- Every one of *cōnārī*'s six active content cells crosses the voice axis. -/
theorem conari_all_cells_cross_voice :
    ∀ σ ∈ conariContentCells, conariLinkage.pm .conari σ ≠ σ := by decide

/-- The crisp contrast: on the *same* active content cell, the regular verb's
form correspondent stays active while the deponent's becomes passive — deviation
without any difference in the content-cell space. -/
theorem depon_vs_regular (σ : Cell) (h : σ.voice = .active) :
    (parareLinkage.corr .parare σ).image (·.2.voice) = {.active} ∧
      (conariLinkage.corr .conari σ).image (·.2.voice) = {.passive} :=
  ⟨by simp [parareLinkage, Linkage.corr, h], by simp [conariLinkage, Linkage.corr]⟩

/-! ### Kashmiri morphomic tense (Ch. 8, pp. 217ff) -/

section Kashmiri

open Morphology.Exponence Morphology.PFM

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

/-- **Property mapping for Conjugation II** ([stump-2016] Ch. 8): recent →
'past a', indefinite → 'past b', remote → 'past c'. -/
def pmII (σ : Finset KFeat) : Finset KFeat :=
  if recentPast ∈ σ then insert pastA (σ.erase recentPast)
  else if indefPast ∈ σ then insert pastB (σ.erase indefPast)
  else if remotePast ∈ σ then insert pastC (σ.erase remotePast)
  else σ

/-- **Property mapping for Conjugation III** ([stump-2016] Ch. 8): recent →
'past b', indefinite → 'past c', remote → 'past d'. The one-morphome shift from
`pmII` is what makes the two conjugations' preterites interleave. -/
def pmIII (σ : Finset KFeat) : Finset KFeat :=
  if recentPast ∈ σ then insert pastB (σ.erase recentPast)
  else if indefPast ∈ σ then insert pastC (σ.erase indefPast)
  else if remotePast ∈ σ then insert pastD (σ.erase remotePast)
  else σ

/-- The form paradigm: 1sg masculine exponents for each morphome, read off the
stem+suffix segmentation (`wupus`, `wupyōs`, `wupyās`, `wuphiyās`). -/
def formBlock : Block KVerb String (Finset KFeat) :=
  [ ⟨Finset.univ, {pastA, p1, sg, masc}, .const (· ++ "us")⟩,
    ⟨Finset.univ, {pastB, p1, sg, masc}, .const (· ++ "yōs")⟩,
    ⟨Finset.univ, {pastC, p1, sg, masc}, .const (· ++ "yās")⟩,
    ⟨Finset.univ, {pastD, p1, sg, masc}, .const (· ++ "iyās")⟩,
    (identityDefault : PFM.Rule KVerb (Finset KFeat) (Action String (Finset KFeat))) ]

/-- Realization of a form cell `⟨Z, τ⟩`: the PFM1 paradigm function on the stem
`Z` at the morphomic property set `τ`. -/
def realizeForm (z : String) (τ : Finset KFeat) : String :=
  (paradigmFunction (λ _ => wup) (λ _ => z) [formBlock] (wup, τ)).1

/-- Conjugation II linkage: the single stem, mapped by `pmII`. -/
def linkII : Linkage KVerb String (Finset KFeat) := ⟨λ l _ => {stemOf l}, λ _ => pmII⟩

/-- Conjugation III linkage: the single stem, mapped by `pmIII`. -/
def linkIII : Linkage KVerb String (Finset KFeat) := ⟨λ l _ => {stemOf l}, λ _ => pmIII⟩

/-- WUP recent past ('past a'): `wupus`. -/
example : linkII.realize realizeForm wup {recentPast, p1, sg, masc}
    = {("wupus", {pastA, p1, sg, masc})} := by decide

/-- WUP indefinite past ('past b'): `wupyōs`. -/
example : linkII.realize realizeForm wup {indefPast, p1, sg, masc}
    = {("wupyōs", {pastB, p1, sg, masc})} := by decide

/-- WUP remote past ('past c'): `wupyās`. -/
example : linkII.realize realizeForm wup {remotePast, p1, sg, masc}
    = {("wupyās", {pastC, p1, sg, masc})} := by decide

/-- WUPH recent past ('past b'): `wuphyōs`. -/
example : linkIII.realize realizeForm wuph {recentPast, p1, sg, masc}
    = {("wuphyōs", {pastB, p1, sg, masc})} := by decide

/-- WUPH indefinite past ('past c'): `wuphyās`. -/
example : linkIII.realize realizeForm wuph {indefPast, p1, sg, masc}
    = {("wuphyās", {pastC, p1, sg, masc})} := by decide

/-- WUPH remote past ('past d'): `wuphiyās`. -/
example : linkIII.realize realizeForm wuph {remotePast, p1, sg, masc}
    = {("wuphiyās", {pastD, p1, sg, masc})} := by decide

/-- **The morphomic mediation** ([stump-2016] Ch. 8): WUP's indefinite past and
WUPH's recent past have the same form correspondent property set — both 'past b',
1sg masc — even though their tenses differ. This is why they inflect alike
(`-yōs`), the content-to-form mismatch the paradigm-linkage model captures. -/
theorem kashmiri_inflect_alike :
    (linkII.corr wup {indefPast, p1, sg, masc}).image Prod.snd
      = (linkIII.corr wuph {recentPast, p1, sg, masc}).image Prod.snd := by decide

/-- The second interleaving: WUP's remote past and WUPH's indefinite past share
the 'past c' correspondent, inflecting alike (`-yās`). -/
theorem kashmiri_inflect_alike_pastC :
    (linkII.corr wup {remotePast, p1, sg, masc}).image Prod.snd
      = (linkIII.corr wuph {indefPast, p1, sg, masc}).image Prod.snd := by decide

end Kashmiri

end Stump2016
