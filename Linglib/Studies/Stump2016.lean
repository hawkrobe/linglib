import Linglib.Morphology.Paradigm.Function
import Mathlib.Tactic.DeriveFintype

/-!
# Stump 2016: paradigm-linkage deviations — deponency and morphomic tense
[stump-2016]

Two deviations from the canonical content-to-form isomorphism argued for in
[stump-2016], run on the paradigm-linkage model of
`Morphology/Paradigm/Linkage.lean`.

**Latin deponency** (Ch. 12): deponent verbs "inflect by means of the morphology
that ordinarily serves to express a verb's passive forms" (§12.1). Deponent
*cōnārī* 'try' realizes its active content cells —
*cōnor, cōnāris, cōnātur, cōnāmur, cōnāminī, cōnantur* (imperfective present
indicative, Table 12.2) — with the passive personal endings
(-or, -ris, -tur, -mur, -minī, -ntur) that a regular verb like *parāre*
'prepare' uses only for its passive (*paror, parāris, parātur, …*, Table 12.1);
*cōnārī* lacks passive-meaning forms entirely. This is a property mapping that
crosses the voice axis: a regular verb is subject to the canonical
`pmc(σ) = σ ∪ {c}`, a deponent to `pm2c(σ:{active}) = σ[active/passive] ∪ {c}`
(§12.1), replacing active with passive. Abstracting away the inflection-class
index `c`, the deponent linkage flips voice while the regular verb's preserves
it — *cōnārī*'s linkage deviates from `IsCanonical` on every active cell.

**Kashmiri morphomic tense** (Ch. 8, pp. 217ff): the recent, indefinite, and
remote preterites of intransitive Conjugations II and III are realized through
four morphomic properties 'past a'–'past d' via a non-identity property mapping.
`WUP` (Conj II) and `WUPH` (Conj III) inflect alike in the 'past b' cells —
`wupyōs` (indefinite) and `wuphyōs` (recent) — because `pmII` and `pmIII` send
different tenses to the same morphome. The composition exercises the PFM1 block
cascade of `Morphology/Paradigm/Function.lean` as the form-cell realization, with
`pm ≠ id`, so `Linkage.realize_eq_paradigmFunction` (which needs `pm = id`) does
not apply. Forms are transcribed from Grierson's paradigms as displayed by
[stump-2016]; block rules are read off the stem+suffix segmentation.

## Main declarations

* `conariLinkage`, `parareLinkage` — the deponent and regular linkages
* `parareLinkage_isCanonical` — the regular verb's voice-preserving linkage is
  canonical
* `conari_deviates_on_every_active_cell` — the deponent `pm` moves every active
  content cell off its own property set
* `conari_active_realized_by_passive_form` — every active content cell's form
  correspondent is passive (the deponency claim)
* `depon_vs_regular` — same active content cell: regular → active form,
  deponent → passive form
* `pmII`, `pmIII`, `linkII`, `linkIII` — the two Kashmiri conjugation linkages,
  their tense-to-morphome property mappings differing by one morphome
* `kashmiri_inflect_alike` — WUP's indefinite past and WUPH's recent past share
  the 'past b' form correspondent, the morphomic content-to-form mismatch
-/

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
  stem := fun _ _ => some .cona
  pm := fun _ σ => { σ with voice := .passive }

/-- The **regular linkage** of *parāre*: a single stem and the identity property
mapping, canonical on the voice axis ([stump-2016] §7.1). -/
def parareLinkage : Linkage LatinVerb LatinStem Cell where
  stem := fun _ _ => some .para
  pm := fun _ σ => σ

/-- *cōnārī*'s six active content cells ([stump-2016] Table 12.2). -/
def conariContentCells : List Cell :=
  [⟨.s1, .active⟩, ⟨.s2, .active⟩, ⟨.s3, .active⟩,
   ⟨.p1, .active⟩, ⟨.p2, .active⟩, ⟨.p3, .active⟩]

/-- The regular verb's linkage is canonical: property-set preserving (`pm = id`)
and stem invariant ([stump-2016] §7.1, characteristics (2a)–(2b)). -/
theorem parareLinkage_isCanonical : parareLinkage.IsCanonical :=
  ⟨fun _ _ => rfl,
   fun _ _ _ _ _ h₁ h₂ => (Option.some.inj h₁).symm.trans (Option.some.inj h₂),
   fun _ _ _ _ _ heq => congrArg Prod.snd (Option.some.inj heq),
   fun _ _ => rfl⟩

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
  rintro ⟨-, -, -, hpp⟩
  exact conari_deviates_on_every_active_cell .conari ⟨.s1, .active⟩ rfl (hpp _ _)

/-- **The deponency claim**: every active content cell of *cōnārī* has a
*passive* form correspondent — active content realized by passive morphology
([stump-2016] §12.1). -/
theorem conari_active_realized_by_passive_form (l : LatinVerb) (σ : Cell) :
    (conariLinkage.corr l σ).map (·.2.voice) = some .passive := rfl

/-- Every one of *cōnārī*'s six active content cells crosses the voice axis. -/
theorem conari_all_cells_cross_voice :
    ∀ σ ∈ conariContentCells, conariLinkage.pm .conari σ ≠ σ := by decide

/-- The crisp contrast: on the *same* active content cell, the regular verb's
form correspondent stays active while the deponent's becomes passive — deviation
without any difference in the content-cell space. -/
theorem depon_vs_regular (σ : Cell) (h : σ.voice = .active) :
    (parareLinkage.corr .parare σ).map (·.2.voice) = some .active ∧
      (conariLinkage.corr .conari σ).map (·.2.voice) = some .passive :=
  ⟨congrArg some h, rfl⟩

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
    (identityDefault : Rule KVerb (Finset KFeat) (Action String (Finset KFeat))) ]

/-- Realization of a form cell `⟨Z, τ⟩`: the PFM1 paradigm function on the stem
`Z` at the morphomic property set `τ`. -/
def realizeForm (z : String) (τ : Finset KFeat) : String :=
  (paradigmFunction (fun _ => wup) (fun _ => z) [formBlock] (wup, τ)).1

/-- Conjugation II linkage: the single stem, mapped by `pmII`. -/
def linkII : Linkage KVerb String (Finset KFeat) := ⟨fun l _ => some (stemOf l), fun _ => pmII⟩

/-- Conjugation III linkage: the single stem, mapped by `pmIII`. -/
def linkIII : Linkage KVerb String (Finset KFeat) := ⟨fun l _ => some (stemOf l), fun _ => pmIII⟩

/-- WUP recent past ('past a'): `wupus`. -/
example : linkII.realize realizeForm wup {recentPast, p1, sg, masc}
    = some ("wupus", {pastA, p1, sg, masc}) := by decide

/-- WUP indefinite past ('past b'): `wupyōs`. -/
example : linkII.realize realizeForm wup {indefPast, p1, sg, masc}
    = some ("wupyōs", {pastB, p1, sg, masc}) := by decide

/-- WUP remote past ('past c'): `wupyās`. -/
example : linkII.realize realizeForm wup {remotePast, p1, sg, masc}
    = some ("wupyās", {pastC, p1, sg, masc}) := by decide

/-- WUPH recent past ('past b'): `wuphyōs`. -/
example : linkIII.realize realizeForm wuph {recentPast, p1, sg, masc}
    = some ("wuphyōs", {pastB, p1, sg, masc}) := by decide

/-- WUPH indefinite past ('past c'): `wuphyās`. -/
example : linkIII.realize realizeForm wuph {indefPast, p1, sg, masc}
    = some ("wuphyās", {pastC, p1, sg, masc}) := by decide

/-- WUPH remote past ('past d'): `wuphiyās`. -/
example : linkIII.realize realizeForm wuph {remotePast, p1, sg, masc}
    = some ("wuphiyās", {pastD, p1, sg, masc}) := by decide

/-- **The morphomic mediation** ([stump-2016] Ch. 8): WUP's indefinite past and
WUPH's recent past have the same form correspondent property set — both 'past b',
1sg masc — even though their tenses differ. This is why they inflect alike
(`-yōs`), the content-to-form mismatch the paradigm-linkage model captures. -/
theorem kashmiri_inflect_alike :
    (linkII.corr wup {indefPast, p1, sg, masc}).map Prod.snd
      = (linkIII.corr wuph {recentPast, p1, sg, masc}).map Prod.snd := by decide

/-- The second interleaving: WUP's remote past and WUPH's indefinite past share
the 'past c' correspondent, inflecting alike (`-yās`). -/
theorem kashmiri_inflect_alike_pastC :
    (linkII.corr wup {remotePast, p1, sg, masc}).map Prod.snd
      = (linkIII.corr wuph {indefPast, p1, sg, masc}).map Prod.snd := by decide

end Kashmiri

end Stump2016
