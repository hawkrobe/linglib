/-!
# Atomic Lexical Entailments and Roots

@cite{beavers-koontz-garboden-2020}

Lexical entailments are the atomic claims a verbal root makes about
the events it describes and the participants in those events.
Following @cite{beavers-koontz-garboden-2020}, we treat these as
*structured atoms* rather than as a fixed feature vector.

A **root** is a finite collection of such atoms. The root's
B&K-G feature signature (±state, ±manner, ±result, ±cause) is then a
*derived* predicate over the entailment set, not a separately stipulated
classification — exposing both the Bifurcation Thesis of Roots and
Manner/Result Complementarity (@cite{rappaport-hovav-levin-2010}) as
testable conjectures rather than architectural commitments.

## Relation to existing infrastructure

- `EntailmentProfile` (Dowty's 10-tuple) collapses argument-level
  entailments into a flat record. Useful for Argument Selection but too
  coarse to express B&K-G's networks of root entailments.
- `EventStructure.Template` (state/activity/achievement/accomplishment/
  motionContact) is the *output* of root × template composition. The
  templatic *heads* (`v_act`, `v_become`, `v_cause`) that compose into
  these full templates live in `Roots/Template.lean`.
-/

namespace Semantics.Verb.Roots

-- ════════════════════════════════════════════════════
-- § 1. Atomic Entailments
-- ════════════════════════════════════════════════════

/-- An atomic claim a root can make. The four B&K-G features
    (±state, ±manner, ±result, ±cause) correspond to the *kinds* of
    atoms present in a root's entailment set.

    The remaining atoms (volitional, sentient, motion, contact)
    cover Dowty's proto-role components that are independent of the
    state/manner/result/cause cut. -/
inductive LexEntailment where
  /-- Attributes a static property (state-kind atom). -/
  | hasState     (label : String)
  /-- Specifies the manner in which the action is performed. -/
  | hasManner    (label : String)
  /-- Entails change of state to the labelled result. -/
  | becomesState (label : String)
  /-- Entails a causing event. Nullary because B&K-G's typology is
      neutral about *what* causes — only that there is a cause.
      The cause-type distinction (internal vs external,
      @cite{bohnemeyer-2004}) is carried separately by
      `Semantics.Verb.EventStructure.CausationType`. -/
  | hasCause
  /-- The agent acts intentionally. -/
  | volitional
  /-- The agent is sentient. -/
  | sentient
  /-- An entity changes location. -/
  | motion
  /-- Two entities are in physical contact. -/
  | contact
  deriving DecidableEq, Repr

namespace LexEntailment

/-- Is the atom a state-attribution? -/
def isState : LexEntailment → Bool
  | hasState _ => true
  | _ => false

/-- Is the atom a manner specification? -/
def isManner : LexEntailment → Bool
  | hasManner _ => true
  | _ => false

/-- Is the atom a change-of-state entailment? -/
def isBecome : LexEntailment → Bool
  | becomesState _ => true
  | _ => false

/-- Is the atom a causation entailment? -/
def isCause : LexEntailment → Bool
  | hasCause => true
  | _ => false

end LexEntailment

-- ════════════════════════════════════════════════════
-- § 2. Roots
-- ════════════════════════════════════════════════════

/-- A verbal root: a name and a list of atomic entailments it imposes.

    The list is the root's *base* entailment set — the atoms asserted
    directly. A closure operation (B&K-G's networks of entailments
    where one atom may entail another) is layered on top in
    `Roots/Closure.lean`. -/
structure Root where
  name : String
  entailments : List LexEntailment
  deriving DecidableEq, Repr

namespace Root

/-- The root entails attribution of some state. -/
def hasState  (r : Root) : Bool := r.entailments.any LexEntailment.isState

/-- The root specifies some manner. -/
def hasManner (r : Root) : Bool := r.entailments.any LexEntailment.isManner

/-- The root entails some change of state (B&K-G "result"). -/
def hasResult (r : Root) : Bool := r.entailments.any LexEntailment.isBecome

/-- The root entails causation. -/
def hasCause  (r : Root) : Bool := r.entailments.any LexEntailment.isCause

end Root

end Semantics.Verb.Roots
