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
inexpressible on a flat tense scale. `Control.ClauseClass.HasOC` is derived
from this calculus via `ClauseClass.toSpec` (`Syntax/Control/Tier.lean`).

## Main definitions

- `Control.FeatureSpec`, `Control.Head`, `Control.Spec`
- `Control.Spec.HasControl`: control as the elsewhere condition
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

end Control
