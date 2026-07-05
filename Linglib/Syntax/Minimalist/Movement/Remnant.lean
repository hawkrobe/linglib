import Linglib.Syntax.Minimalist.Phase.Basic

/-!
# Remnant XP Movement
[koopman-1997] [aboh-dyakonova-2009] [van-urk-2024]

A constituent X′ moves to Spec,FocP (or Spec,CP) **after** some
sub-constituent Y has independently moved out of X′. The fronted X′
is a *remnant* of the original XP — what's left after Y evacuated.
The classic empirical signature is **predicate doubling**: the verb
appears twice — once at the head of its own movement chain (e.g. in T)
and once inside the fronted remnant VP (where its trace is spelled
out for recoverability).

## Where this substrate is consumed

Remnant-XP movement is referenced informally across multiple existing
Studies files; this substrate centralizes the construct so that the
reasoning is shared rather than re-stipulated:

- [koopman-1997] (originator): predicate clefts in Vata (Kru)
  and Nweh (Grassfields Bantu) — VP fronts after V→T head movement.
- [aboh-dyakonova-2009]: predicate doubling and parallel chains
  in {Gungbe} and across {Kwa}.
- [harizanov-gribanova-2017] / [harizanov-gribanova-2019]:
  alternative analysis (postsyntactic amalgamation), formalized in
  `Studies/HarizanovGribanova2019Amalgamation.lean`
  with the syntactic-vs-PF dichotomy.
- [van-urk-2024]: cross-linguistic constraints on predicate
  fronting; alternative substantive proposals.
- [sande-clem-dabkowski-2026]: Guébie particle-fronting in
  predicate clefts — the fronted constituent is the remnant VP after
  V → v → T head movement and object shift, leaving only the particle
  in the remnant.
- [cole-hermon-2008] (informal use): {Toba Batak} VoiceP raising
  + remnant movement in `Studies/ColeHermon2008.lean`.
- [erlewine-2018] (informal use): predicate fronting in
  `Studies/Erlewine2018.lean`.

TODO: migrate informal consumers to import this substrate. The
extraction-without-migration pattern follows mathlib practice — the
substrate lands now and consumers migrate incrementally.

## Design

`RemnantFronting` records three pieces:
- `frontedXP`: the larger constituent that lands in Spec,Foc/CP
- `evacuatedHeads`: the sub-constituents (typically heads) that moved
  out of `frontedXP` *before* it fronted
- `landingSite`: where `frontedXP` lands

`properRemnant` is the structural predicate that the fronted XP no
longer literally contains the evacuated heads as overt material — the
characteristic property of "remnant" movement, which distinguishes it
from non-remnant XP fronting (where the whole XP, contents intact,
moves).

For verb-doubling derivations, the evacuated head (V) leaves a trace
inside the fronted XP that may be spelled out for recoverability.
[landau-2006] argues this recoverability requirement is purely
phonological; [koopman-1997] and [harizanov-gribanova-2017]
take it to be a syntactic chain property. The substrate does not
adjudicate — the predicate `properRemnant` is silent on whether the
trace is overt.

## What this substrate does NOT do

It does not (yet) provide a typed bridge to `HeadDisplacement` (the
syntactic-vs-PF dichotomy in `HarizanovGribanova2019Amalgamation`),
nor does it state cross-linguistic generalizations about which
constructions license remnant fronting. Those are downstream Studies
content. The substrate is intentionally minimal — just enough to type
the construct so per-paper analyses share vocabulary.

## Relationship to `Movement/Smuggling.lean`

Sibling file `Smuggling.lean` ([collins-2005]) covers a different
XP-movement variant: a constituent YP containing XP moves *with* XP
inside it to a position c-commanding an intervener W (smuggling XP
past W). Remnant fronting is the converse: a sub-element Y has been
evacuated *before* the larger constituent fronts. They share the
structural feature "large XP moves" but differ in whether the
sub-constituent has been extracted (remnant) or remains inside
(smuggling). The substrates are not unified because the structural
preconditions differ; consumers should pick the one that matches
their analysis. SCD 2026's predicate-fronting is remnant; Collins
2005's passive-via-smuggling is smuggling.
-/

namespace Minimalist.Movement

open SyntacticObject

-- ============================================================================
-- § 1: Remnant Fronting Record
-- ============================================================================

/-- A remnant XP movement: `frontedXP` lands at `landingSite` after
    `evacuatedHeads` have moved out of it. -/
structure RemnantFronting where
  /-- The larger constituent that fronts (typically VP, vP, VoiceP,
      or — under [harizanov-gribanova-2017] — AspP). -/
  frontedXP : SyntacticObject
  /-- Heads that moved out of `frontedXP` before it fronted (typically
      V, sometimes also Object). Listed in evacuation order. -/
  evacuatedHeads : List SyntacticObject
  /-- Landing position of `frontedXP` (typically Spec,FocP or Spec,CP). -/
  landingSite : SyntacticObject

-- ============================================================================
-- § 2: Proper Remnant Predicate
-- ============================================================================

/-- Structural definition of a *proper* remnant: every head listed in
    `evacuatedHeads` originally sat inside `frontedXP` (so it actually
    evacuated; vacuous evacuations don't count).

    This is the substrate-side commitment that justifies the term
    "remnant" — the fronted XP is the original XP minus the evacuated
    sub-constituents. The predicate is silent on whether the evacuated
    heads' traces are spelled out (verb doubling vs. silent copy) — that
    is a per-construction choice. -/
def properRemnant (rf : RemnantFronting) : Prop :=
  ∀ h ∈ rf.evacuatedHeads, contains rf.frontedXP h

instance (rf : RemnantFronting) : Decidable (properRemnant rf) := by
  unfold properRemnant; infer_instance

-- ============================================================================
-- § 3: Predicate Doubling Schema ([koopman-1997])
-- ============================================================================

/-- A predicate-doubling derivation: V undergoes head movement to T (or
    higher), and the remnant VP — containing V's trace, possibly
    pronounced — fronts to Spec,CP. The pronounced lower copy is what
    yields surface verb doubling.

    This is the canonical Koopman-1997 schema instantiated in Vata,
    Nweh, and (per [sande-clem-dabkowski-2026]) Guébie. -/
structure PredicateDoubling extends RemnantFronting where
  /-- The verbal head V whose movement creates the doubling. -/
  verb : SyntacticObject
  /-- V is among the evacuated heads (otherwise this isn't doubling). -/
  verb_evacuated : verb ∈ evacuatedHeads
  /-- The verb's trace inside `frontedXP` is pronounced (= verb doubling).
      Per [landau-2006] this is a phonological recoverability
      requirement; per [koopman-1997] and [harizanov-gribanova-2017]
      it reflects syntactic chain pronunciation rules. The substrate
      records the empirical fact without taking sides. -/
  trace_pronounced : Bool

/-- Verb doubling implies the verb evacuated, hence by `properRemnant`
    sat originally inside the fronted XP. -/
theorem predicateDoubling_verb_in_frontedXP
    (pd : PredicateDoubling) (h : properRemnant pd.toRemnantFronting) :
    contains pd.frontedXP pd.verb :=
  h pd.verb pd.verb_evacuated

end Minimalist.Movement
