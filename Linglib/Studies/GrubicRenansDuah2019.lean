/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Focus.Control
import Linglib.Pragmatics.Expressives.Basic

/-!
# Graded exhaustivity in Akan, Ga and Ngamo

Formalises [grubic-renans-duah-2019]: the exhaustive inference of a
morphosyntactically marked focus construction is *not asserted* in
any of the three languages — it is presupposed in Akan and Ga
(cleft-like, with an existence presupposition) and merely
conversationally implicated in Ngamo (whose marker contributes
background salience, a definiteness component kept as prose here;
their §7). The three analyses are three placements of exhaustivity
across the two meaning dimensions: at-issue ([kiss-1998]-style
*only*-semantics, rejected for these constructions), `ci`
(presupposed), or neither (implicated).

The §5.2.1 diagnostic — negation plus an additive continuation — is
derived: negating overt *only* keeps the prejacent and negates
exhaustivity, so *also* finds its anaphoric antecedent
((36b)/(37b)); negating the marked constructions targets the
prejacent and removes it ((36a)/(37a), the `#also` judgments). Their
§4 contrast findings (Akan/Ga contrastive, Ngamo felicitous all-new)
connect to the `Semantics.Focus.Use` layer and are left as a TODO.
-/

namespace GrubicRenansDuah2019

open Pragmatics.Expressives (TwoDimProp)
open Semantics.Focus (onlyVia)

/-- Who Njelu phoned ((36)). -/
structure CallWorld where
  sama  : Bool
  hawwa : Bool
  deriving DecidableEq, Repr

def calledSama : Set CallWorld := {w | w.sama}
def calledHawwa : Set CallWorld := {w | w.hawwa}

/-- The alternative phoning propositions. -/
def alts : Semantics.Focus.Interpretation.PropFocusValue CallWorld :=
  {calledSama, calledHawwa}

/-- Exhaustivity of the prejacent over the alternatives — the
strong-theory *only* condition. -/
def exh : Set CallWorld := onlyVia alts calledSama

/-- Some alternative holds. -/
def existencePresup : Set CallWorld :=
  {w | w ∈ calledSama ∨ w ∈ calledHawwa}

private theorem calledHawwa_ne_calledSama : calledHawwa ≠ calledSama := by
  intro h
  have hmem : (⟨false, true⟩ : CallWorld) ∈ calledHawwa := rfl
  rw [h] at hmem
  exact absurd hmem Bool.false_ne_true

/-- The Akan/Ga marked construction: prejacent at issue; exhaustivity
and existence presupposed (§5.2.3, §6). -/
def cleftLike : TwoDimProp CallWorld :=
  .withCI (· ∈ calledSama) (fun w => w ∈ exh ∧ w ∈ existencePresup)

/-- The Ngamo marked construction: prejacent at issue; no exhaustivity
or existence presupposition (§5.2.2, §6.1). -/
def backgroundMarked : TwoDimProp CallWorld :=
  .withCI (· ∈ calledSama) (fun _ => True)

/-- Overt *only* ((36b)/(37b)): prejacent projects, exhaustivity is
at issue. -/
def onlyStyle : TwoDimProp CallWorld :=
  .withCI (· ∈ exh) (· ∈ calledSama)

/-- Negating overt *only* licenses the additive continuation: with the
prejacent projected and exhaustivity negated, some distinct
alternative held — *also* has its antecedent ((36b)/(37b)). -/
theorem negated_only_licenses_also (w : CallWorld)
    (hne : ¬ onlyStyle.atIssue w) (hp : w ∈ calledSama) :
    w ∈ calledHawwa := by
  by_contra hh
  exact hne fun q hq hwq => by
    rcases hq with rfl | rfl
    · rfl
    · exact absurd hwq hh

/-- Negating the marked constructions targets the prejacent, removing
the additive particle's antecedent — the `#also` judgments of
(36a)/(37a). Exhaustivity is not asserted (§5.2.1), against a
[kiss-1998]-style *only*-semantics for these constructions. -/
theorem negated_marked_blocks_also (w : CallWorld)
    (h : ¬ cleftLike.atIssue w) : w ∉ calledSama := h

/-- Ngamo's exhaustive inference is cancellable — a conversational
implicature (§5.2.2): the construction's full content is consistent
with a non-exhaustive world. -/
theorem ngamo_exhaustivity_cancellable :
    ∃ w, backgroundMarked.atIssue w ∧ backgroundMarked.ci w ∧ w ∉ exh :=
  ⟨⟨true, true⟩, rfl, trivial,
    fun h => calledHawwa_ne_calledSama (h calledHawwa (Or.inr rfl) rfl)⟩

/-- Akan/Ga exhaustivity projects and cannot be cancelled — a
presupposition (§5.2.3): no world satisfies the construction while
falsifying exhaustivity. -/
theorem cleft_exhaustivity_uncancellable :
    ¬ ∃ w, cleftLike.atIssue w ∧ cleftLike.ci w ∧ w ∉ exh :=
  fun ⟨_, _, ⟨hexh, _⟩, hnot⟩ => hnot hexh

/-- Ngamo triggers no existence presupposition; Akan and Ga do (§6):
the Ngamo construction is defined at a world where no alternative
holds, the cleft-like one is not. -/
theorem existence_contrast :
    (∃ w, backgroundMarked.ci w ∧ w ∉ existencePresup) ∧
    (∀ w, cleftLike.ci w → w ∈ existencePresup) :=
  ⟨⟨⟨false, false⟩, trivial,
      fun h => h.elim (absurd · Bool.false_ne_true)
        (absurd · Bool.false_ne_true)⟩,
    fun _ h => h.2⟩

end GrubicRenansDuah2019
