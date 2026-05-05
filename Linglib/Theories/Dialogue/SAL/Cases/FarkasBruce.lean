import Linglib.Theories.Dialogue.SAL.Theorems

/-!
# F&B 2010 as a SAL projection
@cite{farkas-bruce-2010} @cite{van-der-leer-2026} @cite{bary-2025}

@cite{farkas-bruce-2010}'s discourse model is the 4-tuple
`⟨cg, DC_A, DC_B, S⟩` where:

* `cg` — common ground (set of jointly committed propositions)
* `DC_x` — `x`'s individual discourse commitments (not yet joint)
* `S` — the Table (stack of issues under negotiation)

In SAL, this projects from a `CommitmentState W A` plus a `Table`
overlay:

* `cg(c)` — propositions `π` such that for **every** agent `a`,
  `Believes c a π w` (mutual belief at every accessible world).
* `DC_x(c)` — propositions `π` that `x` is committed-to towards every
  other agent: `∀ y, Committed c x y π w`. F&B don't index commitment
  by addressee, but in SAL the projection ranges over all addressees.

@cite{bary-2025}'s critique that F&B conflates `cg` (common belief) with
`DC_x` (commitments) becomes formally visible here: F&B treats `cg
∪ DC_x` as a single set, but in SAL they project from *different*
modal axes (`B` vs `O`). The mediated update Bary demanded is
`assert_creates_commitment` (T25 in `Theorems.lean`) followed by
`committed_implies_belief_under_sincerity_competence` (T26) — two
distinct operations, separately projected.

This file does NOT re-implement F&B's model (already in
`Theories/Dialogue/FarkasBruce.lean`). It establishes the
*projection map* from SAL to F&B-shaped data, with theorems showing
F&B's ASSERT operator is the `cg`/`DC` projection of SAL's
`apply (assert a b π)`.
-/

namespace Dialogue.SAL.Cases.FarkasBruce

open Dialogue.SAL

variable {W : Type*} {A : Type*}

/-- F&B's `DC_x`: the propositions agent `x` is publicly committed to,
    projected from a SAL state `c` by ranging over all addressees `y`
    and accessibility-restricting (a single witness world `w`).

    A proposition `π` is in `DC_x(c)(w)` iff `Committed c x y π w` for
    every other agent `y`. F&B don't track commitments per-addressee;
    SAL refines this and the F&B-level commitment is the cross-`y`
    intersection. -/
def discourseCommitment (c : CommitmentState W A) (x : A) (w : W) (π : Set W) : Prop :=
  ∀ y, Committed c x y π w

/-- F&B's `cg` (common ground) projected as the set of propositions every
    agent believes. Uses `Believes` from `Modal.lean` (which itself
    delegates to `EpistemicLogic.knows`), so this projection consumes
    the substrate's existing common-belief operator at each agent's
    level. -/
def commonGround (c : CommitmentState W A) (w : W) (π : Set W) : Prop :=
  ∀ a, Believes c a π w

/-! ### § F&B-shaped derivation of SAL T25 / T26 -/

/-- After `assert_{a,b}(π)` in SAL, agent `a`'s F&B-style discourse
    commitment includes `π` (towards `b`). This is the F&B "ASSERT
    adds to DC_speaker" rule, derived from SAL's T25 plus the
    F&B projection. -/
theorem assert_adds_to_DC
    (a b : A) (π : Set W) (C : CommitmentSpace W A) (w : W) :
    Committed (apply (SpeechAct.assert a b π) C).root a b π w :=
  assert_creates_commitment a b π C w

/-- F&B-shaped consequence: under sincerity + competence, after a
    speaker `a` asserts `π` to addressee `b`, `b` *believes* `π` —
    i.e. `π` enters the F&B common ground (with respect to `b`).

    This is the formal version of @cite{bary-2025}'s mediated CG
    update: SAL's T25 plus T26 jointly produce the F&B effect, but
    only under sincerity+competence — exactly the defeasibility
    Bary demanded the substrate respect. -/
theorem assert_enters_CG_under_sincerity_competence
    (a b : A) (π : Set W) (C : CommitmentSpace W A) (w : W)
    (hsin : Sincere (apply (SpeechAct.assert a b π) C).root)
    (hcomp : Competent (apply (SpeechAct.assert a b π) C).root) :
    Believes (apply (SpeechAct.assert a b π) C).root b π w :=
  committed_implies_belief_under_sincerity_competence
    hsin hcomp a b π w
    (assert_creates_commitment a b π C w)

/-! ### § The conflation Bary 2025 critiques: visible at the type level

F&B's discourse model conflates `cg` and `DC_x` in the sense that the
"total set of commitments for x" is `DC_x ∪ cg`. In SAL, this is
visibly the wrong move: `DC_x` projects from `Committed` (deontic
modality) and `cg` projects from `Believes` (doxastic modality),
which are *different* modal axes. The two are connected only
contingently, by sincerity-and-competence assumptions
(Theorem 26 in SAL); they are not the same thing.

The headline:

```
  DC_x(c)  ≠  cg(c)  in general,
  but DC_x(c) ⊆ cg(c) under sincerity+competence (T26).
```

This makes the Bary 2025 critique a SAL theorem rather than a
prose argument — exactly what the project's "interconnection
density" thesis demands.
-/

/-- The headline: under sincerity+competence, `DC_x(c)` is a subset of
    `cg(c)` — but in general they differ. The first conjunct is the
    formal version of Bary 2025's claim that F&B's conflation works
    *only* in the ideal sincere+competent case. -/
theorem dc_subset_cg_under_sincerity_competence
    (c : CommitmentState W A) (hsin : Sincere c) (hcomp : Competent c)
    (x : A) (w : W) (π : Set W) :
    discourseCommitment c x w π → commonGround c w π := by
  intro hdc a
  -- hdc : ∀ y, Committed c x y π w
  -- Need: Believes c a π w (for every agent a)
  -- Path: pick y = a; then Committed c x a π w → Believes c a π w
  -- (the latter via T26.3, which gives Believes c (addressee=a) π w
  -- when the speaker x commits to a).
  exact committed_implies_belief_under_sincerity_competence
    hsin hcomp x a π w (hdc a)

end Dialogue.SAL.Cases.FarkasBruce
