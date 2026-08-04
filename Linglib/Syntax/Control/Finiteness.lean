/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# The Calculus of Control

[landau-2004]'s calculus, as codified in [landau-2013] ((6)/(178)): each
clausal head — I and C — carries a `⟨T, Agr⟩` feature specification, and a
head both of whose features are positive assigns `[+R]`, licensing an
independent referential subject. Control is the *elsewhere* case. Mutual
cancellation ([landau-2013] fn. 6): when C is `[+T, +Agr]` as well as I,
R-assignment cancels and OC re-emerges — the Hebrew subjunctive effect,
inexpressible on a flat tense scale. [landau-2004]'s scale of finiteness (`ClauseClass`) abbreviates
`⟨T, Agr⟩` specifications, and `ClauseClass.HasOC` is derived from the
calculus via `ClauseClass.toSpec`.

## Main definitions

- `Control.FeatureSpec`, `Control.Head`, `Control.Spec`
- `Control.Spec.HasControl`: control as the elsewhere condition
- `Control.ClauseClass`: the scale of finiteness, with derived
  `ClauseClass.HasOC`
-/

namespace Control

/-- A `⟨T, Agr⟩` feature specification on a clausal head ([landau-2004];
    [landau-2013] (6)). -/
structure FeatureSpec where
  /-- Semantic tense, `[±T]`. -/
  tense : Bool
  /-- Agreement, `[±Agr]`. -/
  agr : Bool
  deriving DecidableEq, Repr

/-- A head is R-assigning when both features are positive: it licenses an
    independent referential subject ([landau-2013] (178)). -/
def FeatureSpec.RAssigning (h : FeatureSpec) : Prop :=
  h.tense ∧ h.agr

instance (h : FeatureSpec) : Decidable h.RAssigning :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The two clausal heads carrying `⟨T, Agr⟩` specifications. -/
inductive Head where
  /-- The inflectional head. -/
  | I
  /-- The complementizer head. -/
  | C
  deriving DecidableEq, Repr

/-- A clause's control-relevant specification: `⟨T, Agr⟩` on each head. -/
abbrev Spec : Type := Head → FeatureSpec

/-- Control is the elsewhere case ([landau-2013] (178) with fn. 6): an
    R-assigning I destroys control unless C is R-assigning too — mutual
    cancellation. -/
def Spec.HasControl (s : Spec) : Prop :=
  (s .I).RAssigning → (s .C).RAssigning

instance (s : Spec) : Decidable s.HasControl :=
  inferInstanceAs (Decidable (_ → _))

/-- Mutual cancellation: a fully specified C restores OC in a fully finite
    clause — Hebrew subjunctives ([landau-2013] fn. 6). -/
theorem Spec.hasControl_of_c_rAssigning {s : Spec} (h : (s .C).RAssigning) :
    s.HasControl :=
  fun _ => h

/-! ### Clause classes -/

/-- [landau-2004]'s scale positions, in [ostrove-2026]'s terminology:
    C-subjunctives are `[−T]` complements (OC whatever the Agr value),
    F-subjunctives `[+T]` complements (OC unless `[+Agr]`, per the OC-NC
    generalization), and `finite` the fully finite remainder. The positions are tense cells,
    not mood or finiteness categories — `[−T]` covers bare infinitives
    and untensed subjunctives alike, and OC occurs in inflected
    complements. [landau-2015] subsumes the `[±T]` split under
    attitude/nonattitude (the tier reading lives with
    `Studies/Landau2015.lean`). -/
inductive ClauseClass where
  /-- `[−T]` complement: OC at any Agr value -/
  | cSubjunctive
  /-- `[+T]` complement: OC unless `[+Agr]` -/
  | fSubjunctive
  /-- Fully finite: `[+T, +Agr]` on I. No control unless C is fully
      specified too (mutual cancellation, `Spec.hasControl_of_c_rAssigning`) -/
  | finite
  deriving DecidableEq, Repr

/-- The scale position determined by the two clause-typology observables
    of [ostrove-2026]-style fragments: unrestricted TAM marks a fully
    finite clause; among the TAM-restricted clauses, independent tense
    separates `[+T]` from `[−T]` ([landau-2004]'s feature, diagnosed by
    temporal mismatch). Per-language scale maps derive from this single
    classifier rather than restating the case table. -/
def ClauseClass.ofFiniteness (unrestrictedTAM independentTense : Bool) : ClauseClass :=
  if unrestrictedTAM then .finite
  else if independentTense then .fSubjunctive else .cSubjunctive

/-- The `⟨T, Agr⟩` specification a scale position abbreviates, at a given
    Agr value: `[±T]` on I per the position, C unspecified. The scale cannot
    express a fully specified C — mutual cancellation needs the calculus
    directly. -/
def ClauseClass.toSpec (c : ClauseClass) (agr : Bool) : Spec
  | .I => ⟨c ≠ .cSubjunctive, if c = .finite then true else agr⟩
  | .C => ⟨false, false⟩

/-- OC is realized in a clause class iff the calculus leaves control at its
    specification: the elsewhere condition on `toSpec`. -/
def ClauseClass.HasOC (c : ClauseClass) (agr : Bool) : Prop :=
  (c.toSpec agr).HasControl

instance (c : ClauseClass) (agr : Bool) : Decidable (c.HasOC agr) :=
  inferInstanceAs (Decidable (Spec.HasControl _))

/-- OC obtains exactly on C-subjunctives (any Agr) and `[−Agr]`
    F-subjunctives. -/
theorem ClauseClass.hasOC_iff (c : ClauseClass) (agr : Bool) :
    c.HasOC agr ↔ c = .cSubjunctive ∨ (c = .fSubjunctive ∧ agr = false) := by
  cases c <;> cases agr <;> decide

end Control
