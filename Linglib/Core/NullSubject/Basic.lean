/-!
# Null Subjects: Pro-Drop and Overt PRO @cite{ostrove-2026}

Framework-agnostic typological parameter: whether a language permits
null thematic subjects (*pro*-drop) and whether the subject of an
obligatory-control clause must be overt.

This file is in `Core/` because the *parameter* is theory-neutral —
any syntactic framework (Minimalism, HPSG, LFG, Construction Grammar)
must engage with it. Theory-laden *explanations* of the parameter
(rich-agreement licensing, the EPP, topic drop, etc.) belong in
`Theories/Syntax/<framework>/`. Theory-laden *bridges* — e.g. a
function that derives `hasOvertPRO` from a Minimalist minimal-pronoun
inventory — likewise live with the theory they presuppose
(`Theories/Syntax/Minimalism/MinimalPronoun.lean`).

## The implicational universal

> If a language requires the subject of obligatory control clauses
> (i.e., PRO) to be overt, then that language will not allow
> *pro*-drop. (@cite{ostrove-2026})

This is a one-way implication: non-*pro*-drop does *not* entail overt
PRO. English is non-*pro*-drop but has null PRO; Mixtec (SMPM) and Gã
have overt PRO and are non-*pro*-drop; Italian has null PRO and is
*pro*-drop. The fourth cell — overt PRO + *pro*-drop — is predicted
absent.

## Layering

This file holds the *coarse* two-Boolean view (`ProDropProfile`).
The *fine* per-person/per-context view (`SubjectAssignment`) lives in
`Universals.lean`, which projects down to `ProDropProfile` and reuses
the `Satisfies` definition here. Defining the universal once at the
coarse layer and lifting it to the fine layer keeps the typological
content singly authored.
-/

namespace Core.NullSubject

/-- A language's pro-drop / overt-PRO profile. The two Booleans are the
    typological observables; @cite{ostrove-2026}'s implicational
    universal is a constraint on which combinations are predicted to
    occur. -/
structure ProDropProfile where
  /-- Whether the language permits null thematic subjects in finite
      clauses (*pro*-drop). -/
  allowsProDrop : Bool
  /-- Whether the subject of an obligatory-control clause must be
      realized overtly (overt PRO). -/
  hasOvertPRO   : Bool
  deriving DecidableEq, Repr

namespace ProDropProfile

/-- @cite{ostrove-2026}'s implicational universal as a `Prop`: overt
    PRO entails non-*pro*-drop. Stated as a Prop so it composes with
    other logical predicates; `Decidable` instance below makes it
    evaluable by `decide`. -/
def Satisfies (p : ProDropProfile) : Prop :=
  p.hasOvertPRO = true → p.allowsProDrop = false

instance (p : ProDropProfile) : Decidable p.Satisfies := by
  unfold Satisfies; infer_instance

/-- If PRO is null, the universal is satisfied vacuously (its
    antecedent is false). -/
theorem satisfies_of_not_overt_pro (p : ProDropProfile)
    (h : p.hasOvertPRO = false) : p.Satisfies := by
  intro h'; exact absurd (h ▸ h') (by decide)

/-- If PRO is overt and the language is non-*pro*-drop, the
    universal's consequent already holds, so the implication does too. -/
theorem satisfies_of_overt_pro_no_prodrop (p : ProDropProfile)
    (hD : p.allowsProDrop = false) : p.Satisfies := fun _ => hD

/-- Contrapositive: a *pro*-drop language cannot have overt PRO. This
    is the practically useful direction of the universal — given that
    a language is *pro*-drop, it predicts the absence of overt PRO. -/
theorem prodrop_excludes_overt_pro (p : ProDropProfile)
    (h : p.Satisfies) (hD : p.allowsProDrop = true) :
    p.hasOvertPRO = false := by
  cases hO : p.hasOvertPRO with
  | false => rfl
  | true  => exact absurd (h hO) (hD ▸ by decide)

end ProDropProfile

/-- The four cells of the typology. The fourth (overt PRO + *pro*-drop)
    is predicted absent by @cite{ostrove-2026}'s universal. Names use
    mathlib-style camelCase. -/
inductive Typology where
  /-- Null PRO + non-*pro*-drop (e.g., English). -/
  | nullPRONoProDrop
  /-- Null PRO + *pro*-drop (e.g., Italian). -/
  | nullPROProDrop
  /-- Overt PRO + non-*pro*-drop (e.g., SMPM, Gã, Büli). -/
  | overtPRONoProDrop
  /-- Overt PRO + *pro*-drop — predicted absent. -/
  | overtPROProDrop
  deriving DecidableEq, Repr

/-- Whether a typological cell is attested under the universal. The
    only forbidden cell is `overtPROProDrop`. -/
def Typology.isAttested : Typology → Bool
  | .overtPROProDrop => false
  | _                => true

namespace ProDropProfile

/-- Classify a profile into one of the four typological cells. -/
def classify (p : ProDropProfile) : Typology :=
  match p.hasOvertPRO, p.allowsProDrop with
  | false, false => .nullPRONoProDrop
  | false, true  => .nullPROProDrop
  | true,  false => .overtPRONoProDrop
  | true,  true  => .overtPROProDrop

/-- A profile satisfies the universal iff its typological cell is
    attested. This is the typology-as-finite-enumeration restatement
    of `Satisfies`. -/
theorem satisfies_iff_attested (p : ProDropProfile) :
    p.Satisfies ↔ p.classify.isAttested = true := by
  cases hO : p.hasOvertPRO <;> cases hD : p.allowsProDrop <;>
    simp [Satisfies, classify, Typology.isAttested, hO, hD]

end ProDropProfile

end Core.NullSubject
