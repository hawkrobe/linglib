import Linglib.Studies.KonnellyCowper2020
import Linglib.Data.Examples.Arnold2026

/-!
# Arnold 2026: two kinds of singular *they*

Singular *they* covers two uses with opposite pragmatic conditions. Underspecified *they*,
attested since Middle English, is used when the speaker intends an underspecified
representation of the referent — quantified, indefinite, epicene, or simply not developed in
common ground — and its criterion is discourse specificity rather than gender, since it occurs
with gendered referents too. Personal *they*, mainstream only since about 2018, is used
because the referent's personal pronouns are *they/them*, a fact that must be in common
ground and that tends to come with an elaborated representation. The two share their form
and their lack of a gender feature, so a grammatical account of the kind Konnelly and Cowper
give does not separate them: at their first stage *they* is unavailable for any referent of known
gender, at the second it needs an ungendered lexical entry for the referent, and at the third
it is unconstrained, whichever kind is intended.

## Main definitions

* `Kind`, `Kind.condition`: the two kinds and the discourse condition each requires of a
  referent's `Representation`.

## References

* [arnold-2026]
* [konnelly-cowper-2020] — the three-stage grammatical account
* [balhorn-2004] — the history of underspecified *they*
-/

namespace Arnold2026

open Data.Examples KonnellyCowper2020

/-- The two kinds of singular *they*. -/
inductive Kind
  | underspecified
  | personal
  deriving DecidableEq, Repr

/-- The kind a row records. -/
def Kind.parse? : String → Option Kind
  | "underspecified" => some .underspecified
  | "personal" => some .personal
  | _ => none

/-- A referent as the discourse portrays it: whether its representation is elaborated, and
whether its personal pronouns are known in common ground to be *they/them*. -/
structure Representation where
  elaborated : Bool
  theyThem : Bool
  deriving DecidableEq, Repr

/-- The representation a row records. -/
def Representation.ofRow (r : LinguisticExample) : Representation :=
  ⟨r.feature? "representation" = some "elaborated", r.feature? "pronouns" = some "they/them"⟩

/-- The pragmatic condition of each kind: underspecified *they* wants a thin representation,
personal *they* wants the referent's pronouns known. -/
def Kind.condition : Kind → Representation → Prop
  | .underspecified, r => r.elaborated = false
  | .personal, r => r.theyThem = true

instance (k : Kind) (r : Representation) : Decidable (k.condition r) := by
  cases k <;> dsimp only [Kind.condition] <;> infer_instance

/-- No representation satisfies both conditions unless the pronouns are known of a thinly
represented referent — which knowing them precludes. -/
theorem conditions_opposed (r : Representation) (hu : Kind.underspecified.condition r)
    (hp : Kind.personal.condition r) : r = ⟨false, true⟩ := by
  cases r; simp_all [Kind.condition]

/-- Every example meets the condition of its kind, apart from the stage-3 production the paper
flags as a would-be counterexample. -/
theorem rows_conditions :
    ∀ r ∈ Examples.all, r.feature? "counterexample" = none →
      ∀ k ∈ (r.feature? "kind" >>= Kind.parse?).toList, k.condition (Representation.ofRow r) := by
  decide +kernel

/-- Underspecified *they* occurs with gendered referents: every Table 1 example has a referent
of known gender. -/
theorem rows_gendered_referents :
    ∀ r ∈ Examples.all, r.source.paperLabel = "Table 1" →
      r.feature? "kind" = some "underspecified" ∧ r.feature? "referentGender" = some "known" := by
  decide +kernel

/-- Personal *they* is used for elaborated representations in every example, though its
criterion mentions only the pronouns. -/
theorem rows_personal_elaborated :
    ∀ r ∈ Examples.all, r.feature? "kind" = some "personal" →
      (Representation.ofRow r).elaborated = true := by
  decide +kernel

/-- On the grammatical account the two kinds do not differ: *they* for a referent of known
gender is blocked at stage 1, needs an ungendered lexical entry at stage 2, and is free at
stage 3. -/
theorem stages_do_not_separate_kinds :
    genderObligatoryFor .referentialKnownGender .stage1 = true ∧
      genderObligatoryFor .ungenderedProperName .stage2 = false ∧
      genderObligatoryFor .referentialKnownGender .stage3 = false := ⟨rfl, rfl, rfl⟩

end Arnold2026
