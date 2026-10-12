module

public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.Basic

/-!
# Argument selection by inclusion

Following Grimm and Davis and Koenig, subject selection compares the Proto-Agent and
Proto-Patient parts of two profiles by inclusion rather than by count: an argument outranks
another for subjecthood when its Proto-Agent entailments strictly include the other's, and
Proto-Patient inclusion decides when neither Proto-Agent part strictly includes the other.
Dowty's own principle, which counts the parts, is in `Studies/Dowty1991.lean`.

## Main definitions

* `OutranksForSubject`: the Argument Selection Principle by inclusion.

## References

* [grimm-2011]
* [davis-koenig-2000]
* [dowty-1991]
-/

@[expose] public section

namespace ArgumentStructure

variable (subj obj : EntailmentProfile)

/-- The Argument Selection Principle by inclusion ([grimm-2011], [davis-koenig-2000]): `subj`
outranks `obj` for subjecthood when its Proto-Agent entailments strictly include `obj`'s, or
when neither Proto-Agent part strictly includes the other and `obj`'s Proto-Patient entailments
strictly include `subj`'s. Causation priority is structural: `{causation, independentExistence}`
strictly includes `{independentExistence}` yet is incomparable with
`{sentience, independentExistence}`. -/
def OutranksForSubject : Prop :=
  obj.protoAgent ⊂ subj.protoAgent ∨
    (¬ subj.protoAgent ⊂ obj.protoAgent ∧ subj.protoPatient ⊂ obj.protoPatient)

instance : Decidable (OutranksForSubject subj obj) := by
  unfold OutranksForSubject; infer_instance

end ArgumentStructure
