/-
# Kripke's Modal Argument and the Scope-Rigidity Equivalence

Kripke (1980) *Naming and Necessity*, Lecture I.

The central formalization: rigidity is equivalent to scope-invariance.
A designator is rigid if and only if de re (wide scope) and de dicto
(narrow scope) readings coincide for all predicates.

This explains the core linguistic observation: names eliminate the
de re / de dicto ambiguity that descriptions create. "Nixon might have
lost" is unambiguous; "The president might have lost" is ambiguous.

## Main Results

- `rigid_iff_scope_invariant`: **Rigidity ↔ Scope-Invariance** (main theorem)
- `nonrigid_creates_ambiguity`: non-rigidity → ∃ predicate witnessing ambiguity
- `modal_argument`: rigid name ≠ non-rigid description
- `essential_rigid_necessary`: essential properties are preserved by rigid designators
- `rigidification_not_synonymy`: dthat rescues rigidity but destroys meaning-identity

Pure intension algebra (`varying_not_rigid`, `rigid_neq_nonrigid`,
`rigid_allOrNothing`, `nonrigid_identity_contingent`) lives in
`Core/Intension.lean` alongside `rigid_identity_necessary`.

## References

- Kripke, S. (1980). Naming and Necessity. Harvard University Press.
-/

import Linglib.Core.Intension
import Linglib.Theories.Semantics.Reference.Basic
import Linglib.Theories.Semantics.Reference.KaplanLD

namespace Semantics.Reference.Kripke

open Core.Intension (Intension IsRigid rigid rigid_isRigid CoRefer CoExtensional
  rigid_identity_necessary varying_not_rigid rigid_neq_nonrigid)
open Semantics.Reference.Basic (properName isDirectlyReferential)
open Semantics.Reference.KaplanLD (dthatW dthatW_isRigid)

/-! ## De Re and De Dicto

Modal sentences involving referring expressions are ambiguous when the
expression takes wide scope (de re) or narrow scope (de dicto) relative
to the modal operator. We formalize both readings. -/

/-- De dicto evaluation: predicate and term both evaluated at world `w`.
This is the narrow-scope reading: the term is inside the modal operator.

"The president might have lost" (de dicto) = at some world w, whoever is
president at w lost at w. -/
@[simp] def deDicto {W E : Type*} (P : E → W → Prop) (t : Intension W E)
    (w : W) : Prop :=
  P (t w) w

/-- De re evaluation: the term is evaluated at a fixed world `w₀` (the
"actual" world), while the predicate is evaluated at `w`. This is the
wide-scope reading: the term scopes over the modal operator.

"The president might have lost" (de re) = at some world w, the actual
president (Nixon) lost at w. -/
@[simp] def deRe {W E : Type*} (P : E → W → Prop) (t : Intension W E)
    (w₀ w : W) : Prop :=
  P (t w₀) w

/-! ## The Scope-Rigidity Equivalence

Kripke's central insight formalized as a biconditional: a designator is
rigid if and only if it is scope-inert (de re = de dicto for all predicates).

The forward direction says rigid designators eliminate scope ambiguity.
The backward direction says scope-invariance FORCES rigidity — there is no
other way to be scope-inert. The proof of the backward direction constructs
the identity predicate as witness. -/

/-- **Main theorem.** A designator is rigid if and only if de re and de dicto
evaluations coincide for every predicate at every world.

Forward: names (rigid) are scope-inert. "Nixon might have lost" is
unambiguous — both scope configurations yield the same proposition.

Backward: if a designator is scope-inert for ALL predicates, it must be
rigid. We witness this by the identity predicate `λ e _ => e = t w₀`,
which discriminates any referent shift. -/
theorem rigid_iff_scope_invariant {W E : Type*}
    (t : Intension W E) (w₀ : W) :
    IsRigid t ↔ (∀ (P : E → W → Prop) (w : W), deRe P t w₀ w ↔ deDicto P t w) := by
  constructor
  · -- Forward: rigidity → scope-invariance
    intro hRigid P w
    simp only [deRe, deDicto, hRigid w₀ w]
  · -- Backward: scope-invariance → rigidity
    intro hInvariant w₁ w₂
    -- The identity predicate witnesses: if t were non-rigid, this P
    -- would distinguish de re from de dicto.
    have h₁ := (hInvariant (λ e _ => e = t w₀) w₁).mp rfl
    have h₂ := (hInvariant (λ e _ => e = t w₀) w₂).mp rfl
    exact h₁.trans h₂.symm

/-! ## Non-Rigidity Creates Scope Ambiguity -/

/-- If a term shifts reference between two worlds, there exists a predicate
for which de re and de dicto readings diverge.

The witness predicate is "being identical to the actual-world referent."
At the shifted world, the actual referent satisfies this trivially but
the shifted referent does not. This is constructive: from the mere fact
that a term is non-rigid, we build the scope ambiguity. -/
theorem nonrigid_creates_ambiguity {W E : Type*}
    (t : Intension W E) (w₀ w₁ : W) (hShift : t w₁ ≠ t w₀) :
    ∃ (P : E → W → Prop), deRe P t w₀ w₁ ∧ ¬ deDicto P t w₁ :=
  ⟨λ e _ => e = t w₀, rfl, hShift⟩

/-- Equivalent form: non-rigidity implies the scope-invariance property fails.
Contrapositive of the backward direction of `rigid_iff_scope_invariant`. -/
theorem nonrigid_scope_sensitive {W E : Type*}
    (t : Intension W E) (w₀ w₁ : W) (hShift : t w₁ ≠ t w₀) :
    ¬ (∀ (P : E → W → Prop) (w : W), deRe P t w₀ w ↔ deDicto P t w) := by
  intro h
  exact hShift ((h (λ e _ => e = t w₀) w₁).mp rfl)

/-! ## The Modal Argument

Kripke's argument against the description theory of names.
The formal core chains two lemmas from `Core.Intension`:
`varying_not_rigid` (descriptions are non-rigid) and
`rigid_neq_nonrigid` (rigid ≠ non-rigid). -/

/-- **Kripke's modal argument.** If a name rigidly designates an entity and
the associated description varies across worlds, the name is not synonymous
with the description.

This is the formal refutation of the Frege-Russell description theory of
names. The proof chains `varying_not_rigid` and `rigid_neq_nonrigid`
from `Core.Intension`. -/
theorem modal_argument {W E : Type*}
    (name desc : Intension W E)
    (hRigid : IsRigid name)
    (w₁ w₂ : W) (hVaries : desc w₁ ≠ desc w₂) :
    name ≠ desc :=
  rigid_neq_nonrigid name desc hRigid (varying_not_rigid desc w₁ w₂ hVaries)

/-- The modal argument instantiated for proper names: no proper name is
synonymous with a non-rigid description.

Bridges `properName` from `Reference/Basic.lean` to the modal argument. -/
theorem properName_neq_description {C W E : Type*}
    (e : E) (c : C) (desc : Intension W E)
    (w₁ w₂ : W) (hVaries : desc w₁ ≠ desc w₂) :
    (properName (C := C) (W := W) e).character c ≠ desc :=
  modal_argument _ desc (rigid_isRigid e) w₁ w₂ hVaries

/-! ## Essential and Accidental Properties -/

/-- An essential property of entity `e`: true at every possible world. -/
def IsEssential {W E : Type*} (e : E) (P : E → W → Prop) : Prop :=
  ∀ w, P e w

/-- An accidental property of entity `e`: true at some worlds but not others. -/
def IsAccidental {W E : Type*} (e : E) (P : E → W → Prop) : Prop :=
  (∃ w, P e w) ∧ (∃ w, ¬ P e w)

/-- Rigid designators preserve essential properties in modal contexts.

If P is essential to e, and `name` is a rigid designator of e, then
`∀ w, P(name(w), w)`. Necessity "attaches to things" (Kripke), and
rigid designators transparently transmit this necessity. -/
theorem essential_rigid_necessary {W E : Type*}
    (e : E) (P : E → W → Prop) (name : Intension W E)
    (hRigid : IsRigid name) (hEss : IsEssential e P)
    (w₀ : W) (hRef : name w₀ = e) :
    ∀ w, P (name w) w := by
  intro w
  rw [(hRigid w w₀).trans hRef]
  exact hEss w

/-- Non-rigid designators can "lose" essential properties. Even if P is
essential to e, a description that shifts to denote someone else at w₁
may fail P at w₁. This is why descriptions yield wrong modal predictions. -/
theorem nonrigid_loses_essential {W E : Type*}
    (_e : E) (P : E → W → Prop) (desc : Intension W E)
    (w₁ : W) (hNotP : ¬ P (desc w₁) w₁) :
    ¬ (∀ w, P (desc w) w) :=
  λ h => hNotP (h w₁)

/-! ## Reference-Fixing ≠ Synonymy -/

/-- Rigidifying a non-rigid description (via `dthat`) yields a rigid
designator that is NOT identical to the original description.

Linguistically: fixing the reference of "Hesperus" via "the bright star
in the evening sky" makes "Hesperus" rigidly designate Venus, but
"Hesperus" does NOT mean "the bright star in the evening sky."
The description is contingent; the name (after rigidification) is rigid.

This follows from the modal argument: `dthatW desc w₀` is rigid
(by `dthatW_isRigid`), `desc` is non-rigid (it varies), so they differ. -/
theorem rigidification_not_synonymy {W E : Type*}
    (desc : Intension W E) (w₀ w₁ : W)
    (hVaries : desc w₁ ≠ desc w₀) :
    dthatW desc w₀ ≠ desc :=
  modal_argument (dthatW desc w₀) desc (dthatW_isRigid desc w₀) w₁ w₀ hVaries

/-! ## Strong Rigidity -/

/-- Strong rigidity: the designator is rigid AND its designatum necessarily
exists. Numbers are strongly rigid (2 exists at every world); people are
not (Nixon might not have existed).

Kripke (1980, p. 48): a strongly rigid designator designates an object
that exists in every possible world. -/
def IsStronglyRigid {W E : Type*} (exists_ : E → W → Prop)
    (f : Intension W E) : Prop :=
  IsRigid f ∧ ∀ w, exists_ (f w) w

/-- Strongly rigid designators are rigid. -/
theorem stronglyRigid_isRigid {W E : Type*} {exists_ : E → W → Prop}
    {f : Intension W E} (h : IsStronglyRigid exists_ f) : IsRigid f :=
  h.1

/-- `rigid e` is strongly rigid whenever e necessarily exists. -/
theorem rigid_stronglyRigid {W E : Type*} {exists_ : E → W → Prop}
    (e : E) (hExists : ∀ w, exists_ e w) :
    IsStronglyRigid exists_ (rigid (W := W) e) :=
  ⟨rigid_isRigid e, hExists⟩

end Semantics.Reference.Kripke
