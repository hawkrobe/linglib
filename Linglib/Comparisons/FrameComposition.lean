import Linglib.Theories.Semantics.TypeTheoretic.DFrame
import Linglib.Theories.Syntax.HPSG.Core.Basic

/-!
# Frame Composition: Unification vs. Function Application
@cite{pollard-sag-1994} @cite{loebner-2021}

linglib has multiple frame-like structures — ThematicFrame (neo-Davidsonian
role bundles), HPSG Sign (typed feature structures), Frame2 (TTR records) —
each with its own composition mechanism.

Löbner (2021) claims these are all instances of D-frames, and that their
composition should be understood as frame unification. This module makes the
structural identity explicit and shows where unification and Montague FA
make different predictions.

## Key Comparisons

**ThematicFrame is a D-frame.** Its fields (agent, patient, theme, ...)
are functional attributes mapping entities to event participation.
The `agent_unique` axiom in ThematicAxioms is exactly Löbner's
functional-attribute constraint: each event has *at most one* agent.

**HPSG feature sharing is frame unification.** The Head Feature
Principle (HFP) requires the phrase's HEAD features to equal the
head daughter's HEAD features — identity unification.

**FA vs unification for compounds.** Montague FA requires one daughter
to be a function over the other's type. For N-N compounds ("plastic bag"),
neither constituent is naturally "the function." Frame unification handles
this directly: the modifier fills an attribute slot. Predicate Modification
(PM) is a restricted form of unification — it conjoins two ⟨e,t⟩ predicates
but cannot target a *specific* attribute the way unification does.

-/

namespace Comparisons.FrameComposition

open Semantics.TypeTheoretic

-- ════════════════════════════════════════════════════
-- § 1. HPSG Head Features as D-Frame
-- ════════════════════════════════════════════════════

/-- HPSG head feature names as frame attributes. -/
inductive HeadAttr where
  | vform | inv | aux
  deriving DecidableEq, Repr, BEq

/-- Head feature values as a sum type (heterogeneous → homogeneous). -/
inductive HeadVal where
  | vform : HPSG.VForm → HeadVal
  | inv : HPSG.Inv → HeadVal
  | aux : Bool → HeadVal
  deriving DecidableEq, Repr, BEq

/-- Project HPSG HeadFeatures into a D-frame.
    Each feature becomes a functional attribute (exactly one value). -/
def headFeaturesToDFrame (hf : HPSG.HeadFeatures) :
    DFrame HeadAttr HeadVal where
  central := .vform hf.vform
  get
    | .vform => some (.vform hf.vform)
    | .inv   => some (.inv hf.inv)
    | .aux   => some (.aux hf.aux)

/-- All head feature attributes are defined (total frame). -/
theorem headFeatures_total (hf : HPSG.HeadFeatures) (a : HeadAttr) :
    (headFeaturesToDFrame hf).get a ≠ none := by
  cases a <;> simp [headFeaturesToDFrame]

/-- The Head Feature Principle says the phrase's HEAD = the head
    daughter's HEAD. In frame terms: unifying a frame with itself
    is identity. This is trivially compatible — no conflict possible. -/
theorem hfp_is_trivial_unification (hf : HPSG.HeadFeatures) (a : HeadAttr) :
    ((headFeaturesToDFrame hf).unify (headFeaturesToDFrame hf)).get a =
    (headFeaturesToDFrame hf).get a := by
  cases a <;> rfl

-- ════════════════════════════════════════════════════
-- § 2. Unification vs FA for Compounds
-- ════════════════════════════════════════════════════

/-- Frame unification explains *which attribute* a modifier fills.

    PM would just conjoin "is a bag" ∧ "is plastic" — but it doesn't
    explain why MATERIAL (not SHAPE or USE) is the relevant dimension.
    Frame unification makes the semantic contribution of each constituent
    explicit: the modifier fills exactly the MATERIAL slot, leaving
    SHAPE and USE unchanged. -/
theorem unification_targets_specific_attr :
    plasticBag.get .material = some .plastic ∧
    plasticBag.get .shape = bagFrame.get .shape ∧
    plasticBag.get .use = bagFrame.get .use := ⟨rfl, rfl, rfl⟩

/-- Unification is order-sensitive on the central node: the *head*
    determines what the compound "refers to." "plastic bag" refers
    to a bag (not to plastic). -/
theorem head_determines_reference :
    plasticBag.central = bagFrame.central ∧
    plasticBag.central ≠ plasticMod.central := ⟨rfl, by decide⟩

-- ════════════════════════════════════════════════════
-- § 3. Perspective Shift across Word Classes
-- ════════════════════════════════════════════════════

/-- Löbner's insight (§3.1.1): words from different syntactic categories
    (*price* N, *cheap* Adj, *cost* V) can share one conceptual
    frame, differing only in perspective (central node).

    In Montague semantics, these three words are unrelated lambda
    terms (a relational noun, a modifier, a transitive verb) with
    no shared structure. In frame semantics, the shared structure
    is explicit and the type difference is *derived* from perspective. -/
theorem cross_categorial_sharing :
    (∀ (a : PriceAttr), priceNoun.get a = cheapAdj.get a) ∧
    priceNoun.central ≠ cheapAdj.central :=
  ⟨fun a => by cases a <;> rfl, by decide⟩

end Comparisons.FrameComposition
