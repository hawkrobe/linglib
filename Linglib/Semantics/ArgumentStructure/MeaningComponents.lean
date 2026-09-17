/-!
# Meaning components

The decomposition of verb meaning that [levin-1993]'s Introduction diagnoses by diathesis
alternations: a change of state (the middle and causative/inchoative alternations), contact
(body-part possessor ascension), motion (the conative alternation, with contact) and causation
(the causative/inchoative alternation, with a change of state), on which *break*, *cut*, *hit*
and *touch* take four distinct vectors. `instrumentSpec` records the instrument *cut* verbs
specify and `mannerSpec` a lexicalized manner; `fuse` is the library's componentwise
composition of a verb's components with a construction's, an approximation and not
[goldberg-1995]'s unification. Root-level entailments, which [beavers-koontz-garboden-2020]
distinguish from these surface components, are `Root.Kinds`.

## References

* [levin-1993]
* [beavers-koontz-garboden-2020]
* [goldberg-1995]
-/

namespace ArgumentStructure

/-- Binary meaning components that define [levin-1993] verb classes.

    These describe **surface** verb behavior, not root-level entailments.
    [beavers-koontz-garboden-2020] argue that surface CoS and causation
    can come from either the template or the root; see `Root.Kinds`
    in `Semantics/Root/Kinds.lean` for the
    root-level decomposition.

    Diagnosed by participation in diathesis alternations:
    - `changeOfState`: middle alternation, causative/inchoative alternation
    - `contact`: body-part possessor ascension alternation
    - `motion`: conative alternation (with contact)
    - `causation`: causative/inchoative alternation (with changeOfState)

    The four canonical classes from Levin's Introduction:
    - *break* = [+CoS, −contact, −motion, +causation]
    - *cut* = [+CoS, +contact, +motion, +causation]
    - *hit* = [−CoS, +contact, +motion, −causation]
    - *touch* = [−CoS, +contact, −motion, −causation]

    Additional binary features (from class descriptions in Part II):
    - `instrumentSpec`: verb specifies instrument/means (cut vs. break)
    - `mannerSpec`: verb specifies manner of action

    UNVERIFIED: Levin Part II page references for instrumentSpec/mannerSpec
    cited from memory. -/
structure MeaningComponents where
  changeOfState : Bool
  contact : Bool
  motion : Bool
  causation : Bool
  instrumentSpec : Bool := false
  mannerSpec : Bool := false
  deriving DecidableEq, Repr

namespace MeaningComponents

/-- The Introduction's vectors for *break*, *cut*, *hit* and *touch*. -/
def break_ : MeaningComponents := ⟨true, false, false, true, false, false⟩
def cut : MeaningComponents := ⟨true, true, true, true, true, false⟩
def hit : MeaningComponents := ⟨false, true, true, false, false, false⟩
def touch : MeaningComponents := ⟨false, true, false, false, false, false⟩
/-- No components, the identity of `fuse`. -/
def none : MeaningComponents := ⟨false, false, false, false, false, false⟩

/-- Componentwise OR. The formaliser's chosen approximation of
    construction-on-verb composition; not equivalent to Goldberg's
    actual constructional unification (see file docstring). -/
def fuse (a b : MeaningComponents) : MeaningComponents :=
  { changeOfState := a.changeOfState || b.changeOfState
  , contact := a.contact || b.contact
  , motion := a.motion || b.motion
  , causation := a.causation || b.causation
  , instrumentSpec := a.instrumentSpec || b.instrumentSpec
  , mannerSpec := a.mannerSpec || b.mannerSpec }

instance : Append MeaningComponents where
  append := fuse

theorem fuse_none_left (mc : MeaningComponents) : none.fuse mc = mc := by
  cases mc; simp [fuse, none]

theorem fuse_none_right (mc : MeaningComponents) : mc.fuse none = mc := by
  cases mc; simp [fuse, none, Bool.or_false]

theorem fuse_comm (a b : MeaningComponents) : a.fuse b = b.fuse a := by
  cases a; cases b; simp [fuse, Bool.or_comm]

end MeaningComponents

end ArgumentStructure
