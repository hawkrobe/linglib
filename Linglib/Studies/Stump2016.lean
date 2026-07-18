import Linglib.Morphology.Paradigm.Linkage

/-!
# Stump 2016: Latin deponency as a voice-flipping paradigm linkage
[stump-2016]

Latin deponent verbs are [stump-2016]'s central argument for the
paradigm-linkage hypothesis (Ch. 12): their active forms "inflect by means of
the morphology that ordinarily serves to express a verb's passive forms"
(§12.1). Deponent *cōnārī* 'try' realizes its active content cells —
*cōnor, cōnāris, cōnātur, cōnāmur, cōnāminī, cōnantur* (imperfective present
indicative, Table 12.2) — with the passive personal endings
(-or, -ris, -tur, -mur, -minī, -ntur) that a regular verb like *parāre*
'prepare' uses only for its passive (*paror, parāris, parātur, …*, Table 12.1);
*cōnārī* lacks passive-meaning forms entirely.

In the paradigm-linkage architecture (`Morphology/Paradigm/Linkage.lean`) this
is a property mapping that crosses the voice axis. A regular verb is subject to
the canonical `pmc(σ) = σ ∪ {c}` (property-set preserving on the contentful
features); a deponent is subject to `pm2c(σ:{active}) = σ[active/passive] ∪ {c}`
(§12.1), replacing active with passive. Abstracting away the inflection-class
index `c` (which is orthogonal to the voice mismatch), the deponent linkage's
property mapping flips voice while the regular verb's preserves it. The
theorems below show *cōnārī*'s linkage deviates from `IsCanonical` on every
active cell — its form correspondents are all passive — while sharing the
content-cell space with the regular verb.

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
  stem := fun _ _ => .cona
  pm := fun σ => { σ with voice := .passive }

/-- The **regular linkage** of *parāre*: a single stem and the identity property
mapping, canonical on the voice axis ([stump-2016] §7.1). -/
def parareLinkage : Linkage LatinVerb LatinStem Cell where
  stem := fun _ _ => .para
  pm := id

/-- *cōnārī*'s six active content cells ([stump-2016] Table 12.2). -/
def conariContentCells : List Cell :=
  [⟨.s1, .active⟩, ⟨.s2, .active⟩, ⟨.s3, .active⟩,
   ⟨.p1, .active⟩, ⟨.p2, .active⟩, ⟨.p3, .active⟩]

/-- The regular verb's linkage is canonical: property-set preserving (`pm = id`)
and stem invariant ([stump-2016] §7.1, characteristics (2a)–(2b)). -/
theorem parareLinkage_isCanonical : parareLinkage.IsCanonical :=
  ⟨fun _ => rfl, fun _ => ⟨.para, fun _ => rfl⟩⟩

/-- The deponent property mapping flips voice on every active cell. -/
theorem conari_pm_flips_voice (σ : Cell) :
    (conariLinkage.pm σ).voice = .passive := rfl

/-- The deponent linkage deviates from the canonical isomorphism on every active
content cell: its property mapping moves the cell off its own property set. -/
theorem conari_deviates_on_every_active_cell (σ : Cell) (h : σ.voice = .active) :
    conariLinkage.pm σ ≠ σ := by
  intro heq
  have : Voice.passive = Voice.active := h ▸ congrArg Cell.voice heq
  exact absurd this (by decide)

/-- Hence the deponent linkage is not property-preserving, so not canonical. -/
theorem conariLinkage_not_canonical : ¬ conariLinkage.IsCanonical := by
  rintro ⟨hpp, -⟩
  exact conari_deviates_on_every_active_cell ⟨.s1, .active⟩ rfl (hpp _)

/-- **The deponency claim**: every active content cell of *cōnārī* has a
*passive* form correspondent — active content realized by passive morphology
([stump-2016] §12.1). -/
theorem conari_active_realized_by_passive_form (l : LatinVerb) (σ : Cell) :
    (conariLinkage.corr l σ).2.voice = .passive := rfl

/-- Every one of *cōnārī*'s six active content cells crosses the voice axis. -/
theorem conari_all_cells_cross_voice :
    ∀ σ ∈ conariContentCells, conariLinkage.pm σ ≠ σ := by decide

/-- The crisp contrast: on the *same* active content cell, the regular verb's
form correspondent stays active while the deponent's becomes passive — deviation
without any difference in the content-cell space. -/
theorem depon_vs_regular (σ : Cell) (h : σ.voice = .active) :
    (parareLinkage.corr .parare σ).2.voice = .active ∧
      (conariLinkage.corr .conari σ).2.voice = .passive :=
  ⟨h, rfl⟩

end Stump2016
