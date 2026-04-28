import Linglib.Theories.Discourse.Centering.Basic
import Linglib.Theories.Discourse.Centering.Transition

/-!
# Centering Theory — Rule 2 (Transition Preference) and Variants
@cite{grosz-joshi-weinstein-1995} @cite{brennan-friedman-pollard-1987}
@cite{strube-1998} @cite{poesio-stevenson-eugenio-hitzeman-2004}

@cite{poesio-stevenson-eugenio-hitzeman-2004} §2.3.3 (p. 315-316)
distinguish three formulations of Rule 2:

- **Rule 2 (GJW 95 sequences)**: rank *pair sequences* of transitions
  by sum-of-ranks: CON-CON > RET-RET > SHIFT-SHIFT. This file's
  `pairRank` (extracted from the older `Rules.lean`).

- **Rule 2 (BFP 87 single transitions)**: rank *single transitions*
  with @cite{brennan-friedman-pollard-1987}'s 4-way refinement:
  CON > RET > SSH > RSH (Smooth Shift = Cb stable as Cp; Rough Shift
  = Cb stable but ≠ Cp). The 4-way `BFPTransition` enum lives in
  `Phenomena/Reference/Studies/PoesioEtAl2004.lean` (deferred per
  CLAUDE.md "extract on second consumer" — Rule2BFP87 is currently
  the only substrate-level consumer; promote to `Transition.lean`
  when a second consumer arrives).

- **Rule 2 (Strube 1998 cheap/expensive)**: a transition is *cheap*
  if `CB(U_n) = CP(U_{n-1})` (the previous utterance's preferred
  center predicts the current utterance's CB), *expensive* otherwise.
  Rule 2 prefers cheap transitions over expensive ones. This file's
  `isCheap` predicate.

Following the same "variants as separate `Prop`s/`Def`s with
implication theorems" mathlib pattern as `Rule1.lean`. Per linguistics-
domain-expert audit, the cheap/expensive distinction is **Strube 1998**
solo (COLING-ACL '98, pp. 1251-1257), not Strube & Hahn 1999 — Hahn
co-authored the related information-status work (`Instances/InformationStatus.lean`)
but the cheap/expensive Rule 2 reformulation is Strube alone.

PSDH evaluate all three variants on their corpus. Headline finding:
**Rule 2 (BFP) is verified at the .01 level only with the Information-
Status instantiation and STRUBE-HAHN ranking** (Table 15, §5.1.1) —
the first parameter setting where all three centering claims (Strong
C1, Rule 1, Rule 2) pass simultaneously. Rule 2 (Strube cheap) is
**not verified by any** instantiation PSDH test (cheap-cheap sequences
average ~50 vs expensive-expensive ~250–650 across instantiations).

This file *extracts* the Rule 2 content from the older `Rules.lean`.
With `Rule1.lean` (sibling file) it dissolves `Rules.lean`'s monolithic
structure.
-/

set_option autoImplicit false

namespace Discourse.Centering

variable {E R : Type}

-- ════════════════════════════════════════════════════
-- § 1. Rule 2 (GJW 1995): sequences of transitions
-- ════════════════════════════════════════════════════

/-- @cite{grosz-joshi-weinstein-1995} **Rule 2** (the "sequences"
    formulation per @cite{poesio-stevenson-eugenio-hitzeman-2004}
    §2.3.3): a *pair* of transitions `(t₁, t₂)` is preferred over a
    pair `(s₁, s₂)` when its constituent transitions have higher rank.
    Implemented as sum-of-ranks — the discriminating measure consistent
    with the paper's stated CONT-CONT > RET-RET > SHIFT-SHIFT case
    (`min` is a coarser alternative).

    Per PSDH §4.1.2 (Table 4), this version is "roughly verified" in
    their corpus but with too few sequences to support strong claims:
    only ~28% of sequence pairs involve two of the canonical three
    transitions (CON/RET/SHIFT); the most frequent pair-types are NULL
    (~48%) and Establishment (~19%), neither of which the GJW 95
    formulation classifies. -/
def pairRank (t₁ t₂ : Transition) : Nat := t₁.rank + t₂.rank

theorem rule2_continuations_preferred_over_retentions :
    pairRank .continuation .continuation > pairRank .retaining .retaining := by decide

theorem rule2_retentions_preferred_over_shifts :
    pairRank .retaining .retaining > pairRank .shifting .shifting := by decide

theorem rule2_continuations_preferred_over_shifts :
    pairRank .continuation .continuation > pairRank .shifting .shifting := by decide

-- ════════════════════════════════════════════════════
-- § 2. Rule 2 (Strube 1998): cheap vs expensive
-- ════════════════════════════════════════════════════

/-- @cite{strube-1998} **cheap-vs-expensive** distinction per
    @cite{poesio-stevenson-eugenio-hitzeman-2004} §2.3.3 (p. 316):

    > A transition pair is **cheap** if the CB of the current
    > utterance is correctly predicted by the CP of the previous
    > utterance, that is, if `CB(U_n) = CP(U_{n-1})`. A transition
    > pair is **expensive** if `CB(U_n) ≠ CP(U_{n-1})`.

    Rule 2 (Strube 1998) prefers cheap transitions over expensive
    ones. The intuition: when the speaker's previous utterance had
    `e` as its preferred (highest-ranked) center, processing is
    cheaper if `e` is also the next utterance's CB — the hearer's
    expectation is confirmed.

    Implementation note: takes `prevCp : Option E` as an explicit
    parameter (rather than recomputing `cp` from a third utterance),
    consistent with how `Rule1GJW83` and `classifyTransitionExtended`
    take their "previous" arguments. The "previous CP" is whatever
    the prior `cp prev_prev` returned. -/
def isCheap [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) (prevCp : Option E) : Prop :=
  cb prev cur = prevCp ∧ (cb prev cur).isSome

instance isCheap.decidable [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] (prev : Utterance E R) (cur : U) (prevCp : Option E) :
    Decidable (isCheap prev cur prevCp) :=
  inferInstanceAs (Decidable (cb prev cur = prevCp ∧ (cb prev cur).isSome))

/-- @cite{strube-1998} Rule 2 preference: prefer cheap transitions
    over expensive ones. PSDH find this version is **not verified**
    by any of the parameter instantiations they test (every
    instantiation produces more expensive than cheap transitions —
    cheap-cheap sequence pairs average ~50 vs expensive-expensive
    ~250–650, Table 5 + §5.2.3). -/
def Rule2Strube1998Preferred [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E]
    (prev : Utterance E R) (cur : U) (prevCp : Option E) : Prop :=
  isCheap prev cur prevCp

-- ════════════════════════════════════════════════════
-- § 3. Reference to the BFP 87 single-transition variant
-- ════════════════════════════════════════════════════

/-! **Rule 2 (BFP 87 single transitions)** — `Rule2BFP87Single` —
    requires the 4-way `BFPTransition` enum (CON | RET | SSH | RSH
    where Smooth Shift splits from Rough Shift on whether
    `CB(U_n) = CP(U_n)`). Per the audit's "extract on second consumer"
    discipline, the 4-way enum lives in
    `Phenomena/Reference/Studies/PoesioEtAl2004.lean` as a `private
    structure` until a second consumer (Walker 1989, Brennan 1995,
    or other BFP-style algorithm) motivates promotion to substrate.

    Until then, the BFP 87 ranking can be encoded as a Nat-valued rank
    on the 4-way enum locally in study files. The substrate's existing
    `Transition.rank` (CON > RET > SHIFT) collapses BFP's CON/RET/SSH/RSH
    to CON/RET/SHIFT-or-SHIFT — a coarser but compatible ranking. -/

end Discourse.Centering
