import Linglib.Semantics.Questions.Basic
import Linglib.Semantics.Questions.Hamblin

/-!
# Highlighting
[roelofsen-vangool-2010] [roelofsen-farkas-2015]
[simons-tonhauser-beaver-roberts-2010] [krifka-2017]

A *highlighted* proposition is one that has been made salient by a recent
utterance and that addresses the current question under discussion (QUD).
The notion was introduced by [roelofsen-vangool-2010] for disjunctive
questions (the affirmative disjunct is highlighted and feeds the polarity
particle response in [roelofsen-farkas-2015]). It generalises in
[krifka-2017] and the verum-marker literature
(e.g. [martinez-vera-2026]) to a discourse-management primitive
shared across focus, biased polar questions, and verum strategies.

## What this module provides

- `HighlightingContext W` — bundles a set of salient propositions with
  the current QUD.
- `AddressesQUD` — a proposition is comparable to a QUD alternative,
  the simplest [simons-tonhauser-beaver-roberts-2010] version of
  "contextually entails an answer".
- `Highlighted` — the conjunction `salient ∧ addresses-QUD`. This is
  exactly the [martinez-vera-2026] (38) presupposition.
- [roelofsen-farkas-2015] polarity particles `agree`/`reverse`
  with a `commitment` projection.

Consumers (verum studies, biased polar question studies, evidential
discourse studies) import this file rather than re-stipulating the
predicate locally.

## Known unmigrated consumers (deferred)

This substrate landed alongside [martinez-vera-2026]'s formalisation;
existing files that use highlighting-shaped notions but have not yet been
migrated:

* `Semantics/Attitudes/Preferential.lean` — `HighlightingClauseType`
  + `highlightedValue` for Pruitt-Roelofsen 2011 / Uegaki 2022 hope-whether.
* `Studies/FarkasRoelofsen2017.lean` — paper-side
  highlighted-alternative prose; F&R 2015 is the substrate's own anchor.
* `Semantics/Questions/Singleton.lean` — `IsSingleton` documents itself in
  [roelofsen-farkas-2015] terminology but is a different abstraction
  (property of a `Question`, not a discourse context).
* `Semantics/Questions/Bias.lean` — `OriginalBias` /
  `ContextualEvidence` cover adjacent ground (prior-discourse bias) with
  a different shape; bridge not yet written.

Migration to consume `Highlighting.HighlightingContext` is queued for
follow-up work; landing the substrate first lets the new MartinezVera2026
study consume it without forcing an immediate four-file refactor.
-/

namespace Semantics.Highlighting

/-- A highlighting context: the set of propositions made salient by recent
    utterances, paired with the QUD they should address. -/
structure HighlightingContext (W : Type*) where
  /-- Propositions made salient by recent utterances. -/
  salient : Set (Set W)
  /-- The current question under discussion. -/
  qud : Question W

variable {W : Type*}

/-- A proposition `p` *addresses* a question `q` iff it is comparable to
    some alternative — entailing it or being entailed by it. The simplest
    Set-valued version of [simons-tonhauser-beaver-roberts-2010]'s
    "contextually entails an answer". -/
def AddressesQUD (q : Question W) (p : Set W) : Prop :=
  ∃ a ∈ q.alt, p ⊆ a ∨ a ⊆ p

/-- [martinez-vera-2026] (38): proposition `p` is **highlighted** in
    context `c` iff it has been made salient by an utterance and addresses
    the current QUD. -/
def Highlighted (c : HighlightingContext W) (p : Set W) : Prop :=
  p ∈ c.salient ∧ AddressesQUD c.qud p

theorem highlighted_imp_salient {c : HighlightingContext W} {p : Set W}
    (h : Highlighted c p) : p ∈ c.salient := h.1

theorem highlighted_imp_addressesQUD {c : HighlightingContext W} {p : Set W}
    (h : Highlighted c p) : AddressesQUD c.qud p := h.2

instance (c : HighlightingContext W) (p : Set W)
    [Decidable (p ∈ c.salient)] [Decidable (AddressesQUD c.qud p)] :
    Decidable (Highlighted c p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The empty highlighting context: no salient propositions, the trivial
    QUD that is resolved by anything. -/
def empty : HighlightingContext W :=
  { salient := ∅, qud := Question.declarative Set.univ }

/-- A highlighting context built from a single salient proposition that
    declaratively resolves its own QUD. -/
def singleton (p : Set W) : HighlightingContext W :=
  { salient := {p}, qud := Question.declarative p }

/-- Add a proposition to the salient set without touching the QUD. -/
def addSalient (c : HighlightingContext W) (p : Set W) : HighlightingContext W :=
  { c with salient := insert p c.salient }

@[simp] theorem mem_salient_addSalient (c : HighlightingContext W) (p q : Set W) :
    q ∈ (addSalient c p).salient ↔ q = p ∨ q ∈ c.salient := by
  simp [addSalient]

@[simp] theorem qud_addSalient (c : HighlightingContext W) (p : Set W) :
    (addSalient c p).qud = c.qud := rfl

@[simp] theorem salient_singleton (p : Set W) :
    (singleton p : HighlightingContext W).salient = {p} := rfl

@[simp] theorem qud_singleton (p : Set W) :
    (singleton p : HighlightingContext W).qud = Question.declarative p := rfl

/-! ### [roelofsen-farkas-2015]: polarity particles -/

/-- [roelofsen-farkas-2015]'s polarity-particle response slot.

    `agree` (English `yes`, German `ja`, Romance `sí/oui`) confirms the
    highlighted proposition; `reverse` (English `no`, German `nein`,
    Romance `no/non`) commits to its (set-theoretic) complement.

    The two-cell taxonomy is the cross-linguistic minimum; English/German
    elaborate it with intonation, Polish/Czech and Mandarin add further
    morphology — extensions live in study files, not here. -/
inductive ResponseParticle where
  | agree
  | reverse
  deriving DecidableEq, Repr, Inhabited

/-- The proposition committed to by a polarity-particle response, given a
    highlighted proposition `p`. `agree` projects to `p`; `reverse`
    projects to `pᶜ` (set-theoretic complement). -/
def ResponseParticle.commitment (r : ResponseParticle) (p : Set W) : Set W :=
  match r with
  | .agree   => p
  | .reverse => pᶜ

@[simp] theorem ResponseParticle.commitment_agree (p : Set W) :
    ResponseParticle.commitment .agree p = p := rfl

@[simp] theorem ResponseParticle.commitment_reverse (p : Set W) :
    ResponseParticle.commitment .reverse p = pᶜ := rfl

/-- The two response particles disagree on every world: `agree` commits to
    `p`, `reverse` commits to `pᶜ`, and these partition `Set.univ`. -/
theorem ResponseParticle.commitment_inter_eq_empty (p : Set W) :
    ResponseParticle.commitment .agree p ∩
      ResponseParticle.commitment .reverse p = ∅ := by
  simp

end Semantics.Highlighting
