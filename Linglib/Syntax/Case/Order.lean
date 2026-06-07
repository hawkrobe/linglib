import Mathlib.Data.Finset.Basic
import Linglib.Core.Order.PartialRank
import Linglib.Features.Case.Basic
/-!
# Caha Containment Order on Case
[caha-2009] [mcfadden-2018]

Caha's containment order on `Case`, as a **scoped** instance
(`open scoped Syntax.Case.Caha` to use `≤`): theoretical orders are
borne by features as opt-in commitments, not as global instances — the
inventory's default is order-free. Each case on the hierarchy literally
*contains* the representations of all cases below it:

    [[[[[ NOM ] ACC ] GEN ] DAT ] LOC ]

Cases without a `containmentRank` (ERG, ABS, INST, COM, …) are silent —
incomparable with on-hierarchy cases under `≤`, except for reflexivity.
That silence is the theoretical content: Caha's hierarchy is silent on
those cases. The order itself is `Core.Order.partialOrderOfRank` —
the partial-rank gadget whose unranked elements are isolated — so
reflexivity/transitivity/antisymmetry come from the substrate, not from
per-hierarchy hand proofs.

`kshells` states the containment claim structurally — each on-hierarchy
case is a downward-closed stack of case shells — and
`cahaLT_iff_kshells_ssubset` certifies that the rank order is its
shadow: the order is derived from the decomposition, not stipulated.

Other orders (Blake's typological frequency in
`Features/Case/Basic.lean`, per-language syncretism graphs) likewise
live as named `def`s or scoped instances rather than competing global
instances on `Case`.
-/

namespace Syntax
namespace Case

open Core.Order (RankLT RankLE)

/-- Caha's containment rank ([caha-2009]). Cases higher on the
    containment hierarchy have representations that include all lower cases.

    [[[[[ NOM ] ACC ] GEN ] DAT ] LOC ]

    Returns `none` for cases not on the containment hierarchy
    (e.g., ERG/ABS in ergative systems, or minor cases whose containment
    structure is less well established).

    **Encoding caveat.** [caha-2009]'s Universal Case sequence is
    NOM-ACC-GEN-DAT-INST-COM (no LOC); his Russian-specific sequence
    inserts the prepositional/locative between GEN and DAT. The encoding
    below — NOM=0, ACC=1, GEN=2, DAT=3, LOC=4, INST=none — matches
    neither verbatim; it is closer to Blake's typological hierarchy
    ([blake-1994], which Caha argues should coincide with his sequence).
    For Slavic 6-case inventories the encoding choice is
    verdict-equivalent; inventories with INST or COM *without* LOC may
    diverge. For paradigm-shape work that needs Caha's actual Slavic
    ordering, see `cahaSlavicRank` below. -/
def containmentRank : _root_.Case → Option Nat
  | .nom => some 0
  | .acc => some 1
  | .gen => some 2
  | .dat => some 3
  | .loc => some 4
  | _ => none

/-- Caha's Slavic-specific Case sequence ([caha-2009]; stated for
    Russian and confirmed for Serbian): NOM – ACC – GEN – PREP/LOC –
    DAT – INS. Differs from `containmentRank` in placing LOC between GEN
    and DAT (not at top) and INST at the top (not off-hierarchy). Use
    this rank for paradigm-shape contiguity claims referencing Caha's
    Slavic data; use `containmentRank` for inventory downward-closure
    verdicts (where the choice is Slavic-equivalent).

    Codomain `Option (Fin 6)`: the six cases of the Slavic noun system
    are all on-hierarchy in Caha's Slavic encoding (hence `Fin 6`); the
    remaining `Case` cells, which are not part of that system, map to
    `none`. -/
def cahaSlavicRank : _root_.Case → Option (Fin 6)
  | .nom  => some 0
  | .acc  => some 1
  | .gen  => some 2
  | .loc  => some 3
  | .dat  => some 4
  | .inst => some 5
  | _     => none

/-- `cahaSlavicRank` and `containmentRank` agree on the four core cases
    (NOM=0, ACC=1, GEN=2 in both) and disagree on LOC/DAT/INST. The
    disagreement is deliberate: `containmentRank` is verdict-equivalent
    on Slavic inventories for downward-closure (`RespectsCahaContainment`),
    while `cahaSlavicRank` is needed for paradigm-shape contiguity claims
    that respect Caha's actual Slavic sequence. -/
theorem cahaSlavicRank_vs_containmentRank :
    cahaSlavicRank .nom = some 0 ∧ containmentRank .nom = some 0 ∧
    cahaSlavicRank .acc = some 1 ∧ containmentRank .acc = some 1 ∧
    cahaSlavicRank .gen = some 2 ∧ containmentRank .gen = some 2 ∧
    cahaSlavicRank .loc = some 3 ∧ containmentRank .loc = some 4 ∧
    cahaSlavicRank .dat = some 4 ∧ containmentRank .dat = some 3 ∧
    cahaSlavicRank .inst = some 5 ∧ containmentRank .inst = none := by
  decide

/-- Strict containment on Caha-rank Cases: both must have a rank, and the
    first's must be strictly smaller. False whenever either side is
    off-hierarchy. -/
abbrev cahaLT : _root_.Case → _root_.Case → Prop := RankLT containmentRank

/-- The Caha containment order. `c₁ ≤ c₂` iff either they are equal, or
    `cahaLT c₁ c₂`. Off-hierarchy cases are reflexively `≤` themselves and
    incomparable with everything else. -/
abbrev cahaLE : _root_.Case → _root_.Case → Prop := RankLE containmentRank

/-! ### The decomposition behind the order

Caha's claim is structural: each case on the hierarchy *contains* the
representations of the cases below it, as a stack of case shells. The
rank encoding above is the shadow of that decomposition. -/

/-- The shell stack of an on-hierarchy case: the downward-closed set of
    case shells its representation contains ([caha-2009]'s nested
    functional sequence, with shells indexed abstractly). Stipulated
    independently of `containmentRank`; `cahaLT_iff_kshells_ssubset`
    certifies the two agree. -/
def kshells : _root_.Case → Option (Finset (Fin 5))
  | .nom => some {0}
  | .acc => some {0, 1}
  | .gen => some {0, 1, 2}
  | .dat => some {0, 1, 2, 3}
  | .loc => some {0, 1, 2, 3, 4}
  | _ => none

/-- **The order is the shadow of the decomposition**: the containment
    order through the numeric rank coincides with the partial-rank order
    through the shell stacks (`<` on `Finset` is strict inclusion `⊂`).
    The rank encoding is certified against the structural containment
    claim, not stipulated alongside it. -/
theorem cahaLT_iff_kshells_ssubset (c₁ c₂ : _root_.Case) :
    cahaLT c₁ c₂ ↔ RankLT kshells c₁ c₂ := by
  revert c₁ c₂; decide

/-! ### The Caha order as scoped instances

A feature bears its theoretical order as an opt-in commitment
(`open scoped Syntax.Case.Caha`), never as a global instance on the
inventory. The instance is `Core.Order.partialOrderOfRank`, so `≤` is
definitionally `cahaLE` and `<` is `cahaLT`. -/

namespace Caha

scoped instance instPartialOrderCaha : PartialOrder _root_.Case :=
  Core.Order.partialOrderOfRank containmentRank

scoped instance (c₁ c₂ : _root_.Case) : Decidable (c₁ ≤ c₂) :=
  inferInstanceAs (Decidable (cahaLE c₁ c₂))

scoped instance (c₁ c₂ : _root_.Case) : Decidable (c₁ < c₂) :=
  inferInstanceAs (Decidable (cahaLT c₁ c₂))

end Caha

open scoped Caha

/-- A case is **nonnominative** iff its representation contains ACC's, i.e.
    `(.acc : Case) ≤ c` in the Caha order. [mcfadden-2018] argues this
    natural class underlies NOM-vs-oblique stem allomorphy: a VI rule
    conditioned on `[ACC]` captures the split found cross-linguistically
    (one of his arguments that the nominative is featurally empty). -/
def IsNonnominative (c : _root_.Case) : Prop := (.acc : _root_.Case) ≤ c

instance (c : _root_.Case) : Decidable (IsNonnominative c) :=
  inferInstanceAs (Decidable ((.acc : _root_.Case) ≤ c))

/-- A case is **oblique** iff its representation contains GEN's, i.e.
    `(.gen : Case) ≤ c` in the Caha order — the traditional
    structural-vs-oblique split (NOM/ACC vs GEN and above), stated
    through the containment encoding ([caha-2009] supplies the encoding,
    not the terminology). Ergative-aligned ABS/ERG are off-hierarchy in
    `containmentRank` and so satisfy `¬ IsOblique` (consistent with
    their parallel-to-NOM/ACC structural status). -/
def IsOblique (c : _root_.Case) : Prop := (.gen : _root_.Case) ≤ c

instance (c : _root_.Case) : Decidable (IsOblique c) :=
  inferInstanceAs (Decidable ((.gen : _root_.Case) ≤ c))

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

example : (.nom : _root_.Case) ≤ .acc := by decide
example : (.acc : _root_.Case) ≤ .gen := by decide
example : (.gen : _root_.Case) ≤ .dat := by decide
example : (.dat : _root_.Case) ≤ .loc := by decide

/-- Off-hierarchy cases (ERG) are incomparable with on-hierarchy cases. -/
example : ¬ ((.erg : _root_.Case) ≤ .nom) := by decide
example : ¬ ((.nom : _root_.Case) ≤ .erg) := by decide

end Case
end Syntax
