import Linglib.Semantics.Dynamic.DRS.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Maier (2015), *Parasitic Attitudes*

[maier-2015]'s solution to the [karttunen-1973] attitude-projection
puzzle, formalized as Maier actually states it: **a DRT mechanism**, not a
world-accessibility abstraction — now over the faithful model-theoretic DRS core
(`Semantics/Dynamic/DRS/`).

## The puzzle

[karttunen-1973] (ex. 42) observed that

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
the desire compartment **binds** ([van-der-sandt-1992]
presupposition-as-anaphora) to the now-accessible believed event (his
(59)→(60)), rather than projecting.

## Main declarations

* `MentalState`, `MentalState.flatten` — a belief layer with embedded labeled
  compartments, flattened to a `DRS maierLang ℕ`.
* `parasitic_asymmetry` / `presup_binds_after_merge` — the core's decidable
  `DRS.Accessible` gives Maier's accessibility asymmetry; the believed event
  becomes an accessible antecedent for the desire-compartment presupposition only
  after merge.
* `MentalState.merge` — Maier's attitude-merge (his (58)).
* `MentalState.bind` — presupposition resolution by renaming to an accessible
  antecedent (via the core's functorial `Condition.map`).
* `presup_resolved_after_binding` — the worked Karttunen derivation ((53)→(60))
  resolves the cheating presupposition by binding (filtered, not projected).

## Substrate fit (what the faithful core does and does not provide)

* **Accessibility / occurrence.** `DRS.Accessible`/`DRS.accessibleFrom` and
  `DRS.occ` (`DRS/Basic.lean`) are decidable, host-relative, and reproduce Maier's
  parasitic asymmetry — the four theorems below are `decide`d against them.
  (`DRS.Accessible` is the *fixed* notion: an earlier host-free `∃`-over-
  superordinates formulation was vacuous.)
* **Gap 1 — labeled attitude compartment.** Standard DRT (the core) has no
  labeled / operator-free embedded-box condition (Maier fn. 11: `DES` is a label,
  not an operator). Modeled paper-locally via `MentalState`/`Compartment`;
  `flatten` uses `neg` purely as a *subordination device* — `accScope` descends
  into any complex condition identically, so the accessibility geometry the
  theorems test is exactly Maier's, while `neg`'s truth-semantics is immaterial
  (Maier gives the labels no extensional truth-conditions; gap 4).
* **Gap 2 — attitude-merge.** The core `merge`/`toRel_merge` is flat conjunction;
  Maier's belief-and-like-mode-compartment merge (his (58)) is `MentalState.merge`.
* **Gap 3 — presupposition binding.** Renaming is the core's `Condition.map`
  (capture-free since the DRSs are proper — no bespoke capture-aware rename, the
  mathlib `relabel`/`subst` discipline). The van der Sandt bind-vs-accommodate
  choice remains paper-local (bind-only, antecedent supplied by hand).
* **Gap 4 — intensional model semantics.** The core is extensional first-order
  DRT; Maier's contexts (Lewisian de se triples), `Dox`/`Bul*`, indexical anchors
  and capture conditions (his (33)/(36)/(37)) are documented, not built. The
  structural mechanism is modeled.
-/

open FirstOrder DRT

namespace Maier2015

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

/-! ### The DRS language of the Karttunen example (Maier §5.3) -/

/-- Relations of the Karttunen example: `sue`/`jane` (1-ary), `husband` (2-ary,
`husband(h, j)`), event-style `cheat(e, j, h)` (3-ary, event + cheater + victim),
`stop(j, e')` (2-ary, agent + event). -/
inductive MaierRel : ℕ → Type
  | sue : MaierRel 1
  | jane : MaierRel 1
  | husband : MaierRel 2
  | cheat : MaierRel 3
  | stop : MaierRel 2

/-- The first-order language of the example (no functions). -/
def maierLang : Language := ⟨fun _ => Empty, MaierRel⟩

/-- Conditions over `maierLang` with `ℕ` discourse referents. -/
abbrev MCond := Condition maierLang ℕ

/-! ### Mental-state descriptions (Maier §3.1) -/

/-- Attitude-mode labels for non-doxastic compartments. Per Maier (fn. 11) these
are labels, not intensional operators — they do not affect DRT accessibility,
only which compartment an ascription contributes to under merge. -/
inductive AttMode
  | des
  | imgn
  | int
  deriving DecidableEq, Repr, BEq

/-- A labeled non-doxastic compartment: an embedded sub-DRS (its own discourse
referents and conditions) under an attitude-mode label. -/
structure Compartment where
  mode : AttMode
  drefs : List ℕ
  conds : List MCond

/-- Maier's mental-state description: a global belief layer (discourse referents
+ conditions) with embedded labeled compartments. Mirrors his (32) `K = K_BEL`
with `DES-K_DES` embedded. -/
structure MentalState where
  beliefDrefs : List ℕ
  beliefConds : List MCond
  compartments : List Compartment

/-- Flatten a mental state to a single `DRS maierLang ℕ`: the belief box
containing the belief conditions plus, for each compartment, a *subordinate*
sub-box. Because each compartment is embedded inside the belief box, the core's
`accessibleFrom` makes belief referents accessible from a compartment but not
conversely — Maier's parasitism, for free.

Standard DRT (the core) has no labeled / operator-free embedded-box condition
(Maier fn. 11), so `neg` stands in purely as the subordination device: `accScope`
descends into any complex condition identically, so the accessibility geometry the
theorems test is exactly Maier's; `neg`'s truth-semantics is immaterial here. -/
def MentalState.flatten (K : MentalState) : DRS maierLang ℕ :=
  .mk K.beliefDrefs.toFinset
    (K.beliefConds ++ K.compartments.map (fun c => .neg (.mk c.drefs.toFinset c.conds)))

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
compartments. The core's `merge` is flat concatenation (gap 2); this respects the
belief/compartment structure. -/
def MentalState.merge (K K' : MentalState) : MentalState :=
  { beliefDrefs := K.beliefDrefs ++ K'.beliefDrefs
    beliefConds := K.beliefConds ++ K'.beliefConds
    compartments := mergeCompartments K.compartments K'.compartments }

/-! ### Presupposition binding (Maier §4.2, van der Sandt) -/

/-- Resolve a presupposition by binding its referent `presup` to an accessible
antecedent: drop `presup` from the universes and rename it to `antecedent`
throughout, via the core's functorial `Condition.map` (capture-free since the DRS
is proper). Licensed only when `antecedent` is accessible from `presup` (checked
separately via `DRS.Accessible`). -/
def MentalState.bind (presup antecedent : ℕ) (K : MentalState) : MentalState :=
  { beliefDrefs := K.beliefDrefs.filter (· != presup)
    beliefConds := K.beliefConds.map (Condition.map (fun d => if d = presup then antecedent else d))
    compartments := K.compartments.map (fun c =>
      { mode := c.mode
        drefs := c.drefs.filter (· != presup)
        conds := c.conds.map (Condition.map (fun d => if d = presup then antecedent else d)) }) }

/-! ### Solving Karttunen's puzzle (Maier §5.3, (53)–(60))

"Sue thinks that Jane has been cheating on her husband. She hopes that Jane will
stop cheating on him." Referents: s = 10, j = 11, h = 12, e = 20 (the believed
cheating event), e' = 21 (the cheating event presupposed by *stop*). -/

/-- After sentence 1: Sue believes there is a cheating event `e` (Maier (59),
belief layer). -/
def sueBelief : MentalState :=
  { beliefDrefs := [10, 11, 12, 20]
    beliefConds := [.rel .sue ![10], .rel .jane ![11], .rel .husband ![12, 11],
                    .rel .cheat ![20, 11, 12]]
    compartments := [] }

/-- After sentence 2 (in isolation): Sue's desire compartment contains
`stop(j, e')` and the presupposed cheating event `e'`, with no belief-layer
antecedent of its own. -/
def sueHope : MentalState :=
  { beliefDrefs := []
    beliefConds := []
    compartments := [{ mode := .des, drefs := [21],
                       conds := [.rel .stop ![11, 21], .rel .cheat ![21, 11, 12]] }] }

/-- The two ascriptions merged into one mental-state description (Maier (59)). -/
def sueMerged : MentalState := sueBelief.merge sueHope

/-- The merged description after binding the presupposed event `e'` to the
believed event `e` (Maier (60)). -/
def sueBound : MentalState := sueMerged.bind 21 20

/-- Before merge, the believed cheating event does not even occur in the lone
hope description, so the *stop* presupposition has no antecedent to bind to —
only (dispreferred) accommodation is available. -/
theorem believed_event_absent_before_merge : 20 ∉ DRS.occ sueHope.flatten := by decide

/-- After merge, the believed cheating event `e` (20) is accessible from the
desire-compartment presupposition `e'` (21): binding `e' = e` is licensed. This
is the filtering, reusing the core's `DRS.Accessible` unchanged. -/
theorem presup_binds_after_merge : DRS.Accessible sueMerged.flatten 21 20 := by decide

/-- The dependence is asymmetric (Maier §3.1, fn. 11): the believed event in the
belief layer does *not* see the desire-compartment referent. Belief can filter
desire's presupposition, not conversely. -/
theorem parasitic_asymmetry : ¬ DRS.Accessible sueMerged.flatten 20 21 := by decide

/-- After binding, the presupposed cheating referent `e'` (21) no longer occurs:
it has been identified with the believed event `e` (20), so the presupposition is
resolved by binding (filtered), not accommodated or projected (Maier's (60)). -/
theorem presup_resolved_after_binding :
    21 ∉ DRS.occ sueBound.flatten ∧ 20 ∈ DRS.occ sueBound.flatten := by decide

end Maier2015
