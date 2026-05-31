import Linglib.Semantics.Dynamic.Boxes.Syntax

/-!
# Maier (2015), *Parasitic Attitudes*

@cite{maier-2015}'s solution to the @cite{karttunen-1973} attitude-projection
puzzle, formalized as Maier actually states it: **a DRT mechanism**, not a
world-accessibility abstraction.

## The puzzle

@cite{karttunen-1973} (ex. 42) observed that

  "Bill believed Fred had been beating his wife and he hoped Fred would stop"

does not presuppose, for the speaker, that Fred was beating his wife — the
presupposition of *stop* is filtered by the preceding belief. The asymmetry is
sharpest with the additive trigger *too* (Maier's (7a)/(7b)): belief-then-hope
filters, hope-then-belief does not.

## Maier's mechanism (what this file models)

Maier represents an agent's mental state as a single DRS: a **global belief
layer** `K_BEL` with **labeled non-doxastic compartments** (`DES`, `IMG`, `INT`)
embedded *inside* it (his (26), (32)). By the standard DRT accessibility
(subordination) relation, discourse referents introduced in the belief layer are
accessible from an embedded desire compartment, but referents introduced inside
the desire compartment are **not** accessible to the belief layer. That is the
parasitism — realized purely structurally (the labels are not intensional
operators; Maier fn. 11). Karttunen's puzzle is then solved by two operations
(his §5): a sequence of same-agent attitude ascriptions is **merged** into one
mental-state description (his (58)), after which the presupposition triggered in
the desire compartment **binds** (@cite{van-der-sandt-1992}
presupposition-as-anaphora) to the now-accessible believed event (his
(59)→(60)), rather than projecting.

## Main declarations

* `MentalState`, `MentalState.flatten` — a belief layer with embedded labeled
  compartments, flattened to a nested `DRS.box`.
* `parasitic_asymmetry` / `presup_binds_after_merge` — the substrate's `acc`
  (Muskens) gives Maier's accessibility asymmetry; the believed event becomes an
  accessible antecedent for the desire-compartment presupposition only after
  merge.
* `MentalState.merge` — Maier's attitude-merge (his (58)).
* `MentalState.bind` — presupposition resolution by binding to an accessible
  antecedent.
* `presup_resolved_after_binding` — the worked Karttunen derivation ((53)→(60))
  yields a proper DRS, i.e. the cheating presupposition is filtered.

## Substrate gaps (this file is a stress test of the DRT substrate)

Building Maier's mechanism on `Semantics/Dynamic/` surfaced what the DRT
substrate does and does not provide:

* **Strength.** `DRS.acc` (`Boxes/Syntax.lean`, after @cite{muskens-1996})
  on a nested box *already* yields Maier's parasitic accessibility asymmetry —
  no new accessibility relation was needed; `parasitic_asymmetry` is `decide`d
  against it. `isProper` correctly flags unresolved (free) presupposition
  referents.
* **Gap 1 — no labeled attitude compartment.** `DRS.box` is unlabeled and
  there is no `Att(x):K` condition. Modeled paper-locally via `MentalState` /
  `Compartment` + `flatten`; the labels live outside `DRS`.
* **Gap 2 — no attitude-merge.** `dseq` / `LDRS.merge` are flat conjunction /
  concatenation; they do not merge belief layers and like-mode compartments
  separately (Maier (58)). Built here as `MentalState.merge`.
* **Gap 3 — presupposition-as-anaphora binding (partially closed).** The
  renaming primitive now lives in the substrate as `DRS.rename`; what is still
  missing is the van der Sandt bind-*vs*-accommodate resolution
  (`Accommodation.lean` is world-set CCP), so `MentalState.bind` (bind-only,
  antecedent supplied by hand) remains paper-local.
* **Gap 4 — no intensional belief/desire model semantics.** `KRModel` / `interp`
  is extensional first-order DRT; it lacks Maier's contexts (Lewis de se
  triples), the `Dox` / `Bul*` functions, the indexical anchors, and the capture
  conditions (his (33)/(36)/(37)). The structural mechanism is modeled; its
  model-theoretic justification is documented, not built.
* **Gap 5 — LDRT labels are content-layers, not attitude-modes.**
  `ContentLayer` is presupposition/atIssue/implicature; there is no DES/IMG/INT
  attitude-mode label or label algebra for attitude embedding.
-/

namespace Maier2015

open DRS

/-! ### Empirical projection facts -/

/-- A recorded judgment about an attitude-sequence sentence: whether the
embedded presupposition projects to the speaker, whether it is attributed to the
attitude holder, and whether the sentence is acceptable. -/
structure AttitudeSequenceJudgment where
  /-- The sentence being judged. -/
  sentence : String
  /-- Does the presupposition project to the speaker? -/
  presupProjectsToSpeaker : Bool
  /-- Is the presupposition attributed to the attitude holder? -/
  presupProjectsToHolder : Bool
  /-- Is the sentence acceptable? -/
  acceptable : Bool
  deriving Repr

/-- Karttunen's puzzle (ex. 42): a believe-then-hope sequence filters the
presupposition of *stop*, which therefore does not project to the speaker. -/
def believeHopeFiltering : AttitudeSequenceJudgment :=
  { sentence := "Bill believed Fred had been beating his wife and he hoped Fred would stop"
    presupProjectsToSpeaker := false
    presupProjectsToHolder := true
    acceptable := true }

/-- Maier's (7a): belief-then-hope filters the *too*-presupposition, so the
discourse is felicitous. -/
def believeHopeTooFiltering : AttitudeSequenceJudgment :=
  { sentence := "John believes that Mary will come. He hopes that SUE will come too."
    presupProjectsToSpeaker := false
    presupProjectsToHolder := true
    acceptable := true }

/-- Maier's (7b): hope-then-belief does *not* filter the *too*-presupposition,
which projects and renders the discourse infelicitous. The contrast with (7a) is
the asymmetry the parasitic account explains. -/
def hopeBelieveNoFiltering : AttitudeSequenceJudgment :=
  { sentence := "*John hopes that Mary will come. He believes that SUE will come too."
    presupProjectsToSpeaker := true
    presupProjectsToHolder := false
    acceptable := false }

/-- Maier's (22a): the asymmetry extends to purely representational attitudes
(imagine/dream) lacking a preference component — belief-then-imagine filters. -/
def believeImagineFiltering : AttitudeSequenceJudgment :=
  { sentence := "John believes that Mary will come to his party. Last night he imagined that HER SISTER would come too."
    presupProjectsToSpeaker := false
    presupProjectsToHolder := true
    acceptable := true }

/-- Maier's (22b): the reverse order (imagine-then-believe) does not filter. -/
def imagineBelieveNoFiltering : AttitudeSequenceJudgment :=
  { sentence := "*Last night John imagined that Mary would come to his party. He believes that HER SISTER will come too."
    presupProjectsToSpeaker := true
    presupProjectsToHolder := false
    acceptable := false }

/-- All empirical judgments collected in this module. -/
def allJudgments : List AttitudeSequenceJudgment :=
  [ believeHopeFiltering, believeHopeTooFiltering, hopeBelieveNoFiltering,
    believeImagineFiltering, imagineBelieveNoFiltering ]

/-- The filtering cases: a doxastic attitude precedes a parasitic one. -/
def filteringCases : List AttitudeSequenceJudgment :=
  [ believeHopeFiltering, believeHopeTooFiltering, believeImagineFiltering ]

/-- The non-filtering cases: a parasitic attitude precedes a doxastic one. -/
def nonFilteringCases : List AttitudeSequenceJudgment :=
  [ hopeBelieveNoFiltering, imagineBelieveNoFiltering ]

/-- In every filtering case the presupposition stays off the speaker; in every
non-filtering case it projects. This is the asymmetry the mechanism below
derives. -/
theorem projection_asymmetry_data :
    filteringCases.all (·.presupProjectsToSpeaker == false) = true ∧
    nonFilteringCases.all (·.presupProjectsToSpeaker == true) = true := by
  decide

/-! ### Mental-state descriptions (Maier §3.1) -/

/-- Attitude-mode labels for non-doxastic compartments. Per Maier (fn. 11) these
are labels, not intensional operators — they do not affect DRT accessibility,
only which compartment an ascription contributes to under merge.

SUBSTRATE GAP 5: the substrate's `ContentLayer` (presupposition/atIssue/
implicature) is a different axis; there is no attitude-mode label. -/
inductive AttMode
  | des
  | imgn
  | int
  deriving DecidableEq, Repr, BEq

/-- A labeled non-doxastic compartment: an embedded sub-DRS (its own discourse
referents and conditions) under an attitude-mode label. -/
structure Compartment where
  mode : AttMode
  drefs : List Nat
  conds : List DRS

/-- Maier's mental-state description: a global belief layer (discourse referents
+ conditions) with embedded labeled compartments. The structure mirrors his (32)
`K = K_BEL` with `DES-K_DES` embedded.

SUBSTRATE GAP 1: `DRS` has an unlabeled `box` but no labeled compartment or
`Att(x):K` condition, so this structuring lives outside `DRS`. -/
structure MentalState where
  beliefDrefs : List Nat
  beliefConds : List DRS
  compartments : List Compartment

/-- Flatten a mental state to a single `DRS`: the belief box containing the
belief conditions plus, for each compartment, a nested box. Because each
compartment becomes a box *inside* the belief box, the substrate's `acc` makes
belief referents accessible from a compartment but not conversely — Maier's
parasitism, for free. -/
def MentalState.flatten (K : MentalState) : DRS :=
  .box K.beliefDrefs
    (K.beliefConds ++ K.compartments.map (fun c => .box c.drefs c.conds))

/-! ### Attitude merge (Maier §5.2, (58)) -/

/-- Append one compartment's content into another of the same mode. -/
def Compartment.append (c c' : Compartment) : Compartment :=
  { mode := c.mode, drefs := c.drefs ++ c'.drefs, conds := c.conds ++ c'.conds }

/-- Merge two compartment lists by attitude mode: like-mode compartments are
combined, others carried over. -/
def mergeCompartments (cs cs' : List Compartment) : List Compartment :=
  cs'.foldl (fun cur c' =>
    if cur.any (·.mode == c'.mode) then
      cur.map (fun c => if c.mode == c'.mode then c.append c' else c)
    else cur ++ [c']) cs

/-- Maier's attitude-merge (his (58)): combine two partial descriptions of one
agent's mental state by merging the belief layers and merging like-mode
compartments. This is the operation the substrate lacks (Gap 2): `dseq` /
`LDRS.merge` are flat and do not respect the belief/compartment structure. -/
def MentalState.merge (K K' : MentalState) : MentalState :=
  { beliefDrefs := K.beliefDrefs ++ K'.beliefDrefs
    beliefConds := K.beliefConds ++ K'.beliefConds
    compartments := mergeCompartments K.compartments K'.compartments }

/-! ### Presupposition binding (Maier §4.2, van der Sandt) -/

/-- Resolve a presupposition by binding its referent `presup` to an accessible
antecedent: identify the two referents (drop `presup` from the universe) and
rename it to `antecedent` throughout, via the substrate's `DRS.rename`. Licensed
only when `antecedent` is accessible from `presup` (checked separately via
`acc`). -/
def MentalState.bind (presup antecedent : Nat) (K : MentalState) : MentalState :=
  { beliefDrefs := K.beliefDrefs.filter (· != presup)
    beliefConds := K.beliefConds.map (DRS.rename presup antecedent)
    compartments := K.compartments.map (fun c =>
      { mode := c.mode
        drefs := c.drefs.filter (· != presup)
        conds := c.conds.map (DRS.rename presup antecedent) }) }

/-! ### Solving Karttunen's puzzle (Maier §5.3, (53)–(60))

"Sue thinks that Jane has been cheating on her husband. She hopes that Jane will
stop cheating on him."  Relation indices: cheat = 0, stop = 1, sue = 2,
jane = 3, husband = 4. Referents: s = 10, j = 11, h = 12, e = 20 (the believed
cheating event), e' = 21 (the cheating event presupposed by *stop*). -/

/-- After sentence 1: Sue believes there is a cheating event `e`. -/
def sueBelief : MentalState :=
  { beliefDrefs := [10, 11, 12, 20]
    beliefConds := [.atom 2 [10], .atom 3 [11], .atom 4 [12, 11], .atom 0 [11, 20]]
    compartments := [] }

/-- After sentence 2 (in isolation): Sue's desire compartment contains
`stop(j, e')` and the presupposed cheating event `e'`, with no belief-layer
antecedent of its own. -/
def sueHope : MentalState :=
  { beliefDrefs := []
    beliefConds := []
    compartments := [{ mode := .des, drefs := [21], conds := [.atom 1 [11, 21], .atom 0 [11, 21]] }] }

/-- The two ascriptions merged into one mental-state description (Maier (59)). -/
def sueMerged : MentalState := sueBelief.merge sueHope

/-- The merged description after binding the presupposed event `e'` to the
believed event `e` (Maier (60)). -/
def sueBound : MentalState := sueMerged.bind 21 20

/-- Before merge, the believed cheating event does not even occur in the lone
hope description, so the *stop* presupposition has no antecedent to bind to —
only (dispreferred) accommodation is available. -/
theorem believed_event_absent_before_merge :
    occurs 20 sueHope.flatten = false := by decide

/-- After merge, the believed cheating event `e` (20) is accessible from the
desire-compartment presupposition `e'` (21): binding `e' = e` is licensed. This
is the filtering, and it reuses the substrate's `acc` unchanged. -/
theorem presup_binds_after_merge :
    (acc 21 sueMerged.flatten).contains 20 = true := by decide

/-- The dependence is asymmetric (Maier §3.1, fn. 11): the believed event in the
belief layer does *not* see the desire-compartment referent. Belief can filter
desire's presupposition, not conversely. -/
theorem parasitic_asymmetry :
    (acc 20 sueMerged.flatten).contains 21 = false := by decide

/-- After binding, the presupposed cheating referent `e'` (21) no longer occurs:
it has been identified with the believed event `e` (20), so the presupposition is
resolved by binding (filtered), not accommodated or projected (Maier's (60)).

Resolution is witnessed by the disappearance of the presupposed referent: it has
been renamed to the believed event, so it no longer occurs. -/
theorem presup_resolved_after_binding :
    occurs 21 sueBound.flatten = false ∧ occurs 20 sueBound.flatten = true := by
  decide

end Maier2015
