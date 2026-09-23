module

public import Linglib.Semantics.ArgumentStructure.LevinProperty

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
`MeaningComponents.predictedAlternation` is the Introduction's prediction of an alternation
from a verb's components, a hypothesis whose standing against Part II is a matter for the
studies, and the lemmas after it say how fusion interacts with the prediction: fusion without
instrument specificity never removes a predicted alternation, and instrument specificity
alone blocks one.

## References

* [levin-1993]
* [beavers-koontz-garboden-2020]
* [goldberg-1995]
-/

@[expose] public section

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

/-! ### The Introduction's alternation prediction -/

/-- The Introduction's prediction of an alternation from meaning components, for the
alternations it discusses: the causative/inchoative alternation needs a change of state and
causation without instrument specificity, the middle a change of state, the conative contact
and motion, body-part possessor ascension contact, an instrument subject causation without
instrument specificity, and a resultative a change of state without instrument specificity.
Every other property is class-specific rather than component-derived. -/
def predictedAlternation : MeaningComponents → LevinProperty → Bool
  | mc, .causativeInchoative => mc.changeOfState && mc.causation && !mc.instrumentSpec
  | mc, .middle => mc.changeOfState
  | mc, .conative => mc.contact && mc.motion
  | mc, .bodyPartPossessorAscension => mc.contact
  | mc, .instrumentSubject => mc.causation && !mc.instrumentSpec
  | mc, .resultative => mc.changeOfState && !mc.instrumentSpec
  | _, _ => false

end MeaningComponents

/-! ### Fusion and the prediction -/

/-- Fusing an instrument-free verb with instrument-free components contributing a change of
state and causation predicts the four instrument-sensitive alternations. -/
theorem fuse_cos_caus_enables (v c : MeaningComponents)
    (hCoS : c.changeOfState = true) (hCaus : c.causation = true)
    (hInstV : v.instrumentSpec = false) (hInstC : c.instrumentSpec = false) :
    let f := v.fuse c
    f.predictedAlternation .causativeInchoative = true ∧
    f.predictedAlternation .middle = true ∧
    f.predictedAlternation .instrumentSubject = true ∧
    f.predictedAlternation .resultative = true := by
  rcases v with ⟨cos, con, mot, caus, inst, man⟩
  simp_all [MeaningComponents.fuse, MeaningComponents.predictedAlternation]

/-- Fusing a verb without instrument specificity or causation with components contributing a
change of state but no causation predicts the middle and the resultative but neither the
causative/inchoative alternation nor an instrument subject. -/
theorem fuse_cos_only_partial (v c : MeaningComponents)
    (hCoS : c.changeOfState = true) (hNoCaus : c.causation = false)
    (hNoCausV : v.causation = false)
    (hInstV : v.instrumentSpec = false) (hInstC : c.instrumentSpec = false) :
    let f := v.fuse c
    f.predictedAlternation .middle = true ∧
    f.predictedAlternation .resultative = true ∧
    f.predictedAlternation .causativeInchoative = false ∧
    f.predictedAlternation .instrumentSubject = false := by
  rcases v with ⟨cos, con, mot, caus, inst, man⟩
  simp_all [MeaningComponents.fuse, MeaningComponents.predictedAlternation]

/-- Instrument specificity blocks the causative/inchoative alternation, the instrument subject
and the resultative. -/
theorem instrumentSpec_blocks (mc : MeaningComponents)
    (h : mc.instrumentSpec = true) :
    mc.predictedAlternation .causativeInchoative = false ∧
    mc.predictedAlternation .instrumentSubject = false ∧
    mc.predictedAlternation .resultative = false := by
  rcases mc with ⟨cos, con, mot, caus, inst, man⟩
  simp_all [MeaningComponents.predictedAlternation]

/-- Instrument specificity blocks after any fusion, since fusion keeps it. -/
theorem instrumentSpec_blocks_after_fuse (v c : MeaningComponents)
    (h : v.instrumentSpec = true) :
    (v.fuse c).predictedAlternation .causativeInchoative = false ∧
    (v.fuse c).predictedAlternation .instrumentSubject = false ∧
    (v.fuse c).predictedAlternation .resultative = false := by
  rcases v with ⟨cos, con, mot, caus, inst, man⟩
  simp_all [MeaningComponents.fuse, MeaningComponents.predictedAlternation]

/-- An instrument-free fusion never removes a predicted alternation. -/
theorem fuse_alternation_monotone (v c : MeaningComponents) (alt : LevinProperty)
    (h_no_inst : c.instrumentSpec = false)
    (h_bare : v.predictedAlternation alt = true) :
    (v.fuse c).predictedAlternation alt = true := by
  rcases v with ⟨cos, con, mot, caus, inst, man⟩
  rcases c with ⟨cos', con', mot', caus', inst', man'⟩
  cases alt <;> simp_all [MeaningComponents.predictedAlternation, MeaningComponents.fuse]

/-- Fusion keeps instrument specificity. -/
theorem instrumentSpec_persists (v c : MeaningComponents)
    (h : v.instrumentSpec = true) :
    (v.fuse c).instrumentSpec = true := by
  simp [MeaningComponents.fuse, h]

/-- Fusion is not monotone in general: components adding instrument specificity can block an
alternation the verb alone predicts. -/
theorem fuse_not_generally_monotone :
    ∃ (v c : MeaningComponents) (alt : LevinProperty),
      v.predictedAlternation alt = true ∧
      (v.fuse c).predictedAlternation alt = false :=
  ⟨⟨true, false, false, true, false, false⟩,
   ⟨false, false, false, false, true, false⟩,
   .causativeInchoative, rfl, rfl⟩

/-- Instrument specificity is the only blocker: a verb predicted to alternate alone but not
after fusion has acquired it. -/
theorem fuse_blocks_only_via_instrumentSpec (v c : MeaningComponents)
    (alt : LevinProperty)
    (h_bare : v.predictedAlternation alt = true)
    (h_fused : (v.fuse c).predictedAlternation alt = false) :
    (v.fuse c).instrumentSpec = true := by
  rcases v with ⟨cos, con, mot, caus, inst, man⟩
  rcases c with ⟨cos', con', mot', caus', inst', man'⟩
  cases alt <;> simp_all [MeaningComponents.predictedAlternation, MeaningComponents.fuse]

end ArgumentStructure
