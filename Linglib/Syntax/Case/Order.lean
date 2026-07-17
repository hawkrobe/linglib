import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin
import Linglib.Core.Order.PartialRank
import Linglib.Features.Case.Basic
/-!
# Containment orders on Case
[caha-2009] [pantcheva-2011] [mcfadden-2018]

The **object**: a case feature carries a containment structure — its
value is a downward-closed stack of nested feature shells, and one value
*contains* another iff its shell stack does. The order is then the
partial-rank order `Core.Order.partialOrderOfRank` over a shell-rank
(unranked elements isolated), and the empirical *ABA syncretism law over
it is the framework-neutral `Morphology.IsContiguous`
(syncretism targets only adjacent cells). Both the order gadget and the
*ABA predicate name no paper.

This file holds the two case-feature **instances** of that object,
organized by the object, not by author:

* **Nominal containment** ([caha-2009]): NOM ⊂ ACC ⊂ GEN ⊂ DAT ⊂ LOC,
  via `containmentRank`/`kshells`. ERG/ABS/INST/… are off-hierarchy
  (silent — `containmentRank → none`), and that silence is the
  theoretical content.
* **Directional containment** ([pantcheva-2011]): Place ⊂ Goal ⊂ Source
  ⊂ Route on the orthogonal *path* dimension, via `PathDir`/`dirRank`.
  The spatial case cells (`ine`/`ela`/`ill`, `ade`/`abl`/`all`,
  `sup`/`del`/`sub`) decompose as `Region × PathDir` (`spatialDecomp`),
  so cells inert under the nominal hierarchy gain structure.

Both reuse the *same* `partialOrderOfRank` gadget and certify the order
as the shadow of the shell decomposition (`*_iff_kshells_ssubset` /
`*_iff_shells_ssubset`) — derived, not stipulated.

Orders are **scoped** instances (`open scoped Case.Caha`): theoretical
orders are opt-in commitments, never global instances on the inventory.
Declarations live in the root `Case` namespace (the namespace follows the
subject; the file stays in `Syntax/Case/` as nanosyntactic substrate).
-/

namespace Case

open Core.Order (RankLT RankLE)

/-- Caha's containment rank ([caha-2009]). Cases higher on the
    containment hierarchy have representations that include all lower cases.

    [[[[[ NOM ] ACC ] GEN ] DAT ] LOC ]

    Returns `none` for cases not on the containment hierarchy
    (e.g., ERG/ABS in ergative systems, or minor cases whose containment
    structure is less well established). Codomain `Option (Fin 5)` — the
    boundedness is encoded in the type, matching `Case.hierarchyRank`.

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
def containmentRank : Case → Option (Fin 5)
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
def cahaSlavicRank : Case → Option (Fin 6)
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

/-! ### Directional containment ([pantcheva-2011])

The second instance of the containment object, on the orthogonal *path*
dimension: Place ⊂ Goal ⊂ Source ⊂ Route ([pantcheva-2011]'s functional
sequence, ex. 2). A Source path structurally contains a Goal path —
reflected morphologically where the Source marker contains the Goal
marker (Imbabura Quechua Goal `-man` ⊂ Source `-man-da`; Estonian
`-l` ⊂ `-l-le` ⊂ `-l-t`). Unlike the nominal containment, every path
head is on the chain, so the order is total. -/

/-- The path-direction heads, in containment order
    Place ⊂ Goal ⊂ Source ⊂ Route ([pantcheva-2011] ex. 2). -/
inductive PathDir where
  /-- Place: static location (the locative base; no motion). -/
  | place
  /-- Goal: motion *to* (built on Place). -/
  | goal
  /-- Source: motion *from* (built on Goal — the reversal). -/
  | source
  /-- Route: motion *via/through* (built on Source). -/
  | route
  deriving DecidableEq, Repr, Fintype

/-- Containment rank: how many path heads the direction nests.
    Place=0 ⊂ Goal=1 ⊂ Source=2 ⊂ Route=3. -/
def PathDir.rank : PathDir → Fin 4
  | .place => 0
  | .goal => 1
  | .source => 2
  | .route => 3

/-- The shell stack of a path direction: the downward-closed set of path
    heads its structure contains ([pantcheva-2011]'s nested
    [Route [Source [Goal [Place]]]]). **Derived** as the down-set `Iic` of
    `PathDir.rank`, not stipulated alongside it; `lt_iff_shells_ssubset` is
    then the structural shadow fact (mathlib's `Finset.Iic_ssubset_Iic`). -/
def PathDir.shells (d : PathDir) : Finset (Fin 4) := Finset.Iic d.rank

/-- **The order is the shadow of the decomposition**: directional
    containment (strict rank) coincides with strict inclusion of shell
    stacks — the directional analogue of `cahaLT_iff_kshells_ssubset`, here
    just `Finset.Iic_ssubset_Iic` since the shells *are* `Iic` of the rank. -/
theorem PathDir.lt_iff_shells_ssubset (d₁ d₂ : PathDir) :
    d₁.rank < d₂.rank ↔ d₁.shells ⊂ d₂.shells := by
  simp [PathDir.shells]

/-! ### Directional denotation ([pantcheva-2011] Ch. 5)

The `interpret` affordance for the directional dimension. Each path head
denotes a phase profile over the path interval — whether the Figure
occupies the Place-region at the start / middle / end (Pantcheva's `+`/`−`
sequences). Place is stative (located throughout); Goal is a transition
*into* the region (`−−−−−+++++`, ends located, ex. 5); Source is the
**reversal** of Goal (`+++++−−−−−`, starts located, §5.4); Route passes
*through* it (`−−−−+++−−−−`, located in the middle, ex. 10). -/

/-- Whether the Figure occupies the Place-region at the start, middle, and
    end of the path — [pantcheva-2011]'s `+`/`−` phase profile sampled at
    three points. -/
structure PathProfile where
  /-- The Figure is in the Place-region at the path's start. -/
  atStart : Bool
  /-- … at the middle. -/
  atMid : Bool
  /-- … at the end. -/
  atEnd : Bool
  deriving DecidableEq, Repr

/-- Reverse a profile (swap start and end) — the Source head's semantic
    operation ([pantcheva-2011] §5.4). -/
def PathProfile.reverse (p : PathProfile) : PathProfile :=
  ⟨p.atEnd, p.atMid, p.atStart⟩

/-- The denotation of a path direction ([pantcheva-2011] Ch. 5): the phase
    profile of the Figure–Place-region relation. -/
def PathDir.denote : PathDir → PathProfile
  | .place  => ⟨true, true, true⟩        -- stative: located throughout
  | .goal   => ⟨false, false, true⟩      -- −−+ : transition INTO (ex. 5)
  | .source => ⟨true, false, false⟩      -- +−− : reversal of Goal (§5.4)
  | .route  => ⟨false, true, false⟩      -- −+− : through the region (ex. 10)

/-- **Source is the reversal of Goal** ([pantcheva-2011] §5.4): the Source
    head reverses the Goal path. This *grounds* the `*A&¬A` syncretism
    constraint — a single Goal=Source marker would denote a path and its
    reverse, a contradiction (cf. `Studies/Pantcheva2011.lean`). -/
theorem PathDir.source_denote_eq_goal_reverse :
    PathDir.source.denote = PathDir.goal.denote.reverse := rfl

/-- Goal ends in the region; Source starts in it — the mirror-image
    structure of the two mono-transitional paths (§5.4). -/
theorem PathDir.goal_ends_source_starts :
    PathDir.goal.denote.atEnd = true ∧
    PathDir.source.denote.atStart = true := by decide

/-- The path direction a spatial case expresses, if any. Robust across
    the inventory — direction is determinable even on the cells where
    region is conflated (`regionOf` is the partial companion). The
    spatial case cells decompose as `Region × PathDir`. -/
def dirOf : Case → Option PathDir
  | .loc | .ine | .ade | .sup => some .place
  | .ill | .all | .sub => some .goal
  | .ela | .abl | .del => some .source
  | .perl => some .route
  | _ => none

/-! ### The orthogonal Region axis

The `Place`-internal localization Pantcheva does *not* decompose
(interior/surface/exterior), orthogonal to `PathDir`. Spatial case
systems (Finnish, Hungarian, Daghestanian) cross it with direction. -/

/-- The spatial region a case localizes in. Orthogonal to `PathDir`. -/
inductive Region where
  /-- Interior: in/into/out-of (Finnish inessive/illative/elative). -/
  | interior
  /-- Surface: on/onto/off-of (Hungarian superessive/sublative/delative). -/
  | surface
  /-- Exterior: at/to/from (Finnish adessive/allative/ablative). -/
  | exterior
  deriving DecidableEq, Repr, Fintype

/-- Build a spatial case from its `Region × PathDir` decomposition — the
    constructor direction spatial-case fragments consume. The 3 × 3
    region-specific cells; `route` is region-neutral in these
    inventories (`none`). -/
def toCase : Region → PathDir → Option Case
  | .interior, .place => some .ine
  | .interior, .goal => some .ill
  | .interior, .source => some .ela
  | .surface, .place => some .sup
  | .surface, .goal => some .sub
  | .surface, .source => some .del
  | .exterior, .place => some .ade
  | .exterior, .goal => some .all
  | .exterior, .source => some .abl
  | _, .route => none

/-- The region a case localizes in, under the spatial reading. The
    exterior series is `ade`/`all`/`abl` (Finnish's external local
    cases). **Conflation caveat**: `all`/`abl` double as the *general*
    allative/ablative (Latin-type, region-neutral); the spatial
    decomposition reads them as exterior-goal/source, the use the
    analytical split `Features/Case/Basic.lean` anticipates separating.
    `loc` is the genuinely region-neutral general locative (`none`). -/
def regionOf : Case → Option Region
  | .ine | .ela | .ill => some .interior
  | .sup | .del | .sub => some .surface
  | .ade | .all | .abl => some .exterior
  | _ => none

/-- Analyze a spatial case into `Region × PathDir`, where both are
    determinable (lossy on region-conflated cells; the faithful inverse
    of `toCase` on the 3 × 3 region-specific cells). -/
def spatialDecomp (c : Case) : Option (Region × PathDir) :=
  match regionOf c, dirOf c with
  | some r, some d => some (r, d)
  | _, _ => none

/-- `toCase` and `spatialDecomp` are inverse on the region-specific
    cells — the decomposition round-trips where region is not conflated.
    (`route` is region-neutral, hence `none` on both sides.) -/
theorem spatialDecomp_toCase (r : Region) (d : PathDir) :
    (toCase r d).bind spatialDecomp =
      (toCase r d).map (fun _ => (r, d)) := by
  cases r <;> cases d <;> decide

end Case
