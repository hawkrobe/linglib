module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Linglib.Core.Order.PartialRank
public import Linglib.Syntax.Case.Basic
/-!
# The containment order on Case

A case feature carries a containment structure: its value is a downward-closed stack of nested
feature shells, and one value contains another iff its shell stack does ([caha-2009]):
NOM ⊂ ACC ⊂ GEN ⊂ DAT ⊂ LOC. The order is the partial-rank order
`Core.Order.partialOrderOfRank` over the containment rank, so that the cases off the hierarchy,
ERG, ABS, INST and the rest, are incomparable with every other case, and that silence is the
theoretical content. The empirical *ABA syncretism law over it is the framework-neutral
`Morphology.IsContiguous`. The order is certified as the shadow of the shell decomposition
(`cahaLT_iff_kshells_ssubset`), and is a scoped instance (`open scoped Case.Caha`): a
theoretical order is an opt-in commitment, never a global instance on the inventory.
[mcfadden-2018]'s natural classes of nonnominative and oblique cases are read off it.

The directional containment of spatial cases, Place ⊂ Goal ⊂ Source ⊂ Route, is
`Spatial.PathDir`, and the decomposition of spatial cases into localization and direction is in
`Syntax/Case/Spatial.lean`.

## References

* [caha-2009]
* [mcfadden-2018]
* [blake-1994]
* [smith-moskal-xu-kang-bobaljik-2019]
-/

@[expose] public section

namespace Case

open Core.Order (RankLT RankLE)

/-- Caha's containment rank ([caha-2009]). Cases higher on the
    containment hierarchy have representations that include all lower cases.

    [[[[[ NOM ] ACC ] GEN ] DAT ] LOC ]

    Returns `none` for cases not on the containment hierarchy
    (e.g., ERG/ABS in ergative systems, or minor cases whose containment
    structure is less well established). Codomain `Option (Fin 5)` — the
    boundedness is encoded in the type.

    **Encoding caveat.** [caha-2009]'s Universal Case sequence is
    NOM-ACC-GEN-DAT-INST-COM (no LOC); his Russian-specific sequence
    inserts the prepositional/locative between GEN and DAT. The encoding
    below — NOM=0, ACC=1, GEN=2, DAT=3, LOC=4, INST=none — matches
    neither verbatim; it is closer to Blake's typological hierarchy
    ([blake-1994], which Caha argues should coincide with his sequence).
    Caha's own sequences are stated in `Studies/Caha2009.lean`. -/
def containmentRank : Case → Option (Fin 5)
  | .nom => some 0
  | .acc => some 1
  | .gen => some 2
  | .dat => some 3
  | .loc => some 4
  | _ => none

/-- Strict containment on Caha-rank Cases: both must have a rank, and the
    first's must be strictly smaller. False whenever either side is
    off-hierarchy. -/
abbrev cahaLT : Case → Case → Prop := RankLT containmentRank

/-- The Caha containment order. `c₁ ≤ c₂` iff either they are equal, or
    `cahaLT c₁ c₂`. Off-hierarchy cases are reflexively `≤` themselves and
    incomparable with everything else. -/
abbrev cahaLE : Case → Case → Prop := RankLE containmentRank

/-! ### The decomposition behind the order

Caha's claim is structural: each case on the hierarchy *contains* the
representations of the cases below it, as a stack of case shells. The
rank encoding above is the shadow of that decomposition. -/

/-- The shell stack of an on-hierarchy case: the downward-closed set of
    case shells its representation contains ([caha-2009]'s nested
    functional sequence). **Derived** as the down-set `Iic` of the
    containment rank (`Core.Order.rankShells`), not stipulated alongside
    `containmentRank` — so the two cannot drift, and
    `cahaLT_iff_kshells_ssubset` is the structural shadow fact rather than a
    coincidence to be `decide`d. -/
def kshells : Case → Option (Finset (Fin 5)) :=
  Core.Order.rankShells containmentRank

/-- **The order is the shadow of the decomposition**: the containment order
    through the numeric rank coincides with the partial-rank order through the
    shell stacks (`<` on `Finset` is strict inclusion `⊂`). Now an instance of
    the generic `Core.Order.rankLT_iff_rankShells`, since `kshells` *is* the
    rank's down-set decomposition. -/
theorem cahaLT_iff_kshells_ssubset (c₁ c₂ : Case) :
    cahaLT c₁ c₂ ↔ RankLT kshells c₁ c₂ := by
  unfold kshells; exact Core.Order.rankLT_iff_rankShells containmentRank c₁ c₂

/-! ### The Caha order as scoped instances

A feature bears its theoretical order as an opt-in commitment
(`open scoped Case.Caha`), never as a global instance on the
inventory. The instance is `Core.Order.partialOrderOfRank`, so `≤` is
definitionally `cahaLE` and `<` is `cahaLT`. -/

namespace Caha

scoped instance instPartialOrderCaha : PartialOrder Case :=
  Core.Order.partialOrderOfRank containmentRank

scoped instance (c₁ c₂ : Case) : Decidable (c₁ ≤ c₂) :=
  inferInstanceAs (Decidable (cahaLE c₁ c₂))

scoped instance (c₁ c₂ : Case) : Decidable (c₁ < c₂) :=
  inferInstanceAs (Decidable (cahaLT c₁ c₂))

end Caha

open scoped Caha

/-- A case is **nonnominative** iff its representation contains ACC's, i.e.
    `(.acc : Case) ≤ c` in the Caha order. [mcfadden-2018] argues this
    natural class underlies NOM-vs-oblique stem allomorphy: a VI rule
    conditioned on `[ACC]` captures the split found cross-linguistically
    (one of his arguments that the nominative is featurally empty). -/
def IsNonnominative (c : Case) : Prop := (.acc : Case) ≤ c

instance (c : Case) : Decidable (IsNonnominative c) :=
  inferInstanceAs (Decidable ((.acc : Case) ≤ c))

/-- A case is **oblique** iff its representation contains GEN's, i.e.
    `(.gen : Case) ≤ c` in the Caha order — the traditional
    structural-vs-oblique split (NOM/ACC vs GEN and above), stated
    through the containment encoding ([caha-2009] supplies the encoding,
    not the terminology). Ergative-aligned ABS/ERG are off-hierarchy in
    `containmentRank` and so satisfy `¬ IsOblique` (consistent with
    their parallel-to-NOM/ACC structural status). -/
def IsOblique (c : Case) : Prop := (.gen : Case) ≤ c

instance (c : Case) : Decidable (IsOblique c) :=
  inferInstanceAs (Decidable ((.gen : Case) ≤ c))

/-- The four core McFadden-hierarchy cases stratify cleanly between
    non-oblique (NOM, ACC) and oblique (GEN, DAT). -/
theorem isOblique_split_core :
    ¬ IsOblique .nom ∧ ¬ IsOblique .acc ∧ IsOblique .gen ∧ IsOblique .dat := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Ergative-aligned ABS/ERG are not oblique under the Caha hierarchy
    (off-hierarchy → incomparable with GEN). This makes the predicate
    usable for the ergative pronominal paradigms of
    [smith-moskal-xu-kang-bobaljik-2019] (Wardaman, Khinalugh —
    `Studies/SmithMoskalEtAl2019.lean`). -/
theorem isOblique_erg_abs_false :
    ¬ IsOblique .erg ∧ ¬ IsOblique .abs := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### Sanity chain: NOM < ACC < GEN < DAT < LOC -/

example : (.nom : Case) ≤ .acc := by decide
example : (.acc : Case) ≤ .gen := by decide
example : (.gen : Case) ≤ .dat := by decide
example : (.dat : Case) ≤ .loc := by decide

/-- Off-hierarchy cases (ERG) are incomparable with on-hierarchy cases. -/
example : ¬ ((.erg : Case) ≤ .nom) := by decide
example : ¬ ((.nom : Case) ≤ .erg) := by decide

end Case
