import Linglib.Semantics.Plurality.Basic
import Linglib.Core.Order.Mereology
import Mathlib.Data.Finset.Grade

/-!
# Plural Distributivity and Non-Maximality
[kriz-spector-2021] [haslinger-etal-2025]

Tolerant-distributive operators and the four-cell typology of
distributivity × maximality. The substrate primitives (`Tolerance`,
`distMaximal`, `allSatisfy`, `someSatisfy`, `noneSatisfy`) live in
`Plurality/Basic.lean`; the trivalent K&S apparatus (`pluralTruthValue`,
`homogeneity_gap_symmetric`, `pluralTruthValue_neg`) lives in
`Plurality/Trivalent.lean`.

## Main declarations

* `distTolerant` — tolerant-distributive operator (German *jeweils*-style
  semantics with exception tolerance).
* `distMaximal_iff_identity`, `distTolerant_allows_exceptions` — operator
  relations.
* `distMaximal_singleton`, `distMaximal_pair`, `distTolerant_singleton`,
  `distTolerant_identity_singleton` — atom-vacuity theorems.
* `DistMaxClass`, `DistMaxClass.{distMax,distNonMax,nonDistMax,nonDistNonMax}`
  — the four-cell typology from [haslinger-etal-2025].
* `distTolerantQuant` — hypothetical DP-internal tolerant quantifier
  (typology-predicted but unattested).
* `distMaximal_iff_forall_atom`, `distMaximal_iff_star_atoms` — grounding of
  `distMaximal` in mathlib's `IsAtom` and Link's star-closure ([link-1983]).

## Implementation notes

A tolerance relation induces a partition on pluralities: identity tolerance
→ exact QUD, coarser tolerance → coarser QUD.

-/

namespace Semantics.Plurality.Distributivity

open Semantics.Plurality

variable {Atom W : Type*} [DecidableEq Atom]

/-! ### Tolerant-distributive operator -/

/--
Tolerant distributive: ⟦each* P⟧^⪯(x) = ∃z. z ⪯ x ∧ z ≠ ∅ ∧ ∀a ∈ z. P(a)

This is the semantics of German "jeweils" (for non-max speakers).
The nonemptiness constraint prevents the empty set from vacuously
witnessing truth (∀a ∈ ∅, P a w is trivially true).
-/
def distTolerant (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (tol : Tolerance Atom) (x : Finset Atom) (w : W) : Prop :=
  ∃ z ∈ x.powerset, z.Nonempty ∧ tol.rel z x ∧ ∀ a ∈ z, P a w

instance distTolerant.instDecidable (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (tol : Tolerance Atom)
    (x : Finset Atom) (w : W) :
    Decidable (distTolerant P tol x w) := by unfold distTolerant; infer_instance

/-! ### Key theorems -/

/-- Maximal distributive ↔ tolerant distributive with identity tolerance
    (on nonempty pluralities). -/
theorem distMaximal_iff_identity (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W)
    (hne : x.Nonempty) :
    distMaximal P x w ↔ distTolerant P Tolerance.identity x w := by
  unfold distMaximal distTolerant
  refine ⟨fun h => ?_, fun ⟨z, _, _, hz_eq, hz_all⟩ => ?_⟩
  · exact ⟨x, Finset.mem_powerset.mpr (Finset.Subset.refl x), hne,
      show (x : Finset Atom) = x from rfl, h⟩
  · simp only [Tolerance.identity] at hz_eq
    exact hz_eq ▸ hz_all

omit [DecidableEq Atom] in
/-- Maximal distributive forces all atoms to satisfy P -/
theorem distMaximal_forces_all (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) :
    distMaximal P x w → ∀ a ∈ x, P a w := id

/-- Tolerant distributive with trivial tolerance allows exceptions -/
theorem distTolerant_allows_exceptions (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) (a : Atom) (ha : a ∈ x) (hPa : P a w) :
    distTolerant P Tolerance.trivial x w := by
  refine ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
          ⟨a, Finset.mem_singleton.mpr rfl⟩, ?_, ?_⟩
  · exact Finset.singleton_subset_iff.mpr ha
  · intro b hb; rw [Finset.mem_singleton.mp hb]; exact hPa

/-! ### Atom vacuity -/

omit [DecidableEq Atom] in
/--
On singletons, `distMaximal` reduces to the predicate itself.

This is WHY `each`/`jeder` forces maximality: when it distributes P to individual
atoms, the result is just P(a) — there's no plurality for tolerance to weaken.
[haslinger-etal-2025] §2.3, the argument below the four-way classification.
-/
theorem distMaximal_singleton (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (a : Atom) (w : W) :
    distMaximal P {a} w ↔ P a w := by
  simp only [distMaximal, Finset.mem_singleton, forall_eq]

/--
On pairs, `distMaximal` reduces to conjunction of individual checks.

This is the two-atom instance of Link's distributive inference
(`distr_atom_part` in `Plurality/Algebra.lean`): for a distributive P, checking
`*P` on a two-atom plurality {a, b} reduces to P(a) ∧ P(b).

When `a = b`, `{a, b} = {a}` (Finset dedup) and the result
degenerates to `P a w` (= `P a w ∧ P a w` by `and_self`).
-/
theorem distMaximal_pair (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (a b : Atom) (w : W) :
    distMaximal P {a, b} w ↔ P a w ∧ P b w := by
  simp only [distMaximal, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]

/--
**Atom Vacuity Theorem (general).**

On singletons, `distTolerant` reduces to the predicate itself for ANY
tolerance relation — not just identity tolerance.

This is because {a} has exactly one nonempty subset (itself), and
`tol.refl` guarantees `tol.rel {a} {a}` holds. The tolerance parameter
literally has nothing to vary over.
-/
theorem distTolerant_singleton (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (tol : Tolerance Atom) (a : Atom) (w : W) :
    distTolerant P tol {a} w ↔ P a w := by
  unfold distTolerant
  refine ⟨fun ⟨z, hz_mem, hz_ne, _, hz_all⟩ => ?_, fun hPa => ?_⟩
  · obtain ⟨b, hb⟩ := hz_ne
    have hba : b = a := Finset.mem_singleton.mp (Finset.mem_powerset.mp hz_mem hb)
    have hPb : P b w := hz_all b hb
    exact hba ▸ hPb
  · exact ⟨{a}, Finset.mem_powerset.mpr (Finset.Subset.refl _),
           ⟨a, Finset.mem_singleton.mpr rfl⟩, tol.refl {a},
           fun b hb => by rw [Finset.mem_singleton.mp hb]; exact hPa⟩

/--
Corollary: on singletons, all tolerance relations agree.
-/
theorem distTolerant_singleton_independent (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (tol₁ tol₂ : Tolerance Atom) (a : Atom) (w : W) :
    distTolerant P tol₁ {a} w ↔ distTolerant P tol₂ {a} w := by
  rw [distTolerant_singleton, distTolerant_singleton]

/-- Special case: identity tolerance on singletons. -/
theorem distTolerant_identity_singleton (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (a : Atom) (w : W) :
    distTolerant P Tolerance.identity {a} w ↔ P a w :=
  distTolerant_singleton P Tolerance.identity a w

/-! ### The independence result -/

/-- Classification by [±distributive] × [±maximal].

    [haslinger-etal-2025] present a four-cell typology in which
    the two properties are argued to be orthogonal: all four cells are
    attested or predicted.

    Constructors:
    * `.distMax` — +dist, +max (English *each*, German *jeder*)
    * `.distNonMax` — +dist, −max (German *jeweils*)
    * `.nonDistMax` — −dist, +max (English *all*, German *alle*)
    * `.nonDistNonMax` — −dist, −max (definite plurals) -/
inductive DistMaxClass where
  | distMax
  | distNonMax
  | nonDistMax
  | nonDistNonMax
  deriving DecidableEq, Repr

/-- Does this class force the predicate to apply to each atom separately? -/
def DistMaxClass.isDistributive : DistMaxClass → Prop
  | .distMax | .distNonMax => True
  | .nonDistMax | .nonDistNonMax => False

instance : DecidablePred DistMaxClass.isDistributive
  | .distMax | .distNonMax => isTrue trivial
  | .nonDistMax | .nonDistNonMax => isFalse not_false

/-- Does this class block exception tolerance (force all atoms to satisfy P)? -/
def DistMaxClass.isMaximal : DistMaxClass → Prop
  | .distMax | .nonDistMax => True
  | .distNonMax | .nonDistNonMax => False

instance : DecidablePred DistMaxClass.isMaximal
  | .distMax | .nonDistMax => isTrue trivial
  | .distNonMax | .nonDistNonMax => isFalse not_false

/--
Hypothetical exception-tolerant DP quantifier.
[haslinger-etal-2025] flag this as a typology cell predicted
possible by the Križ & [kriz-spector-2021] framework but not
attested in any known language. The non-attestation is a typological
puzzle — the formal tools for non-maximality (tolerance relations)
don't inherently block DP-internal quantifiers from using them.

⟦[jeder* P] Q⟧^≤ = λw.∃z[z ≤ ⊕P ∧ ∀y[y ∈ AT ∧ y ⊑ z → ⟦Q⟧^≤(w)(y)]]
-/
def distTolerantQuant (restrictor scope : Atom → W → Prop)
    [∀ a w, Decidable (restrictor a w)] [∀ a w, Decidable (scope a w)]
    (tol : Tolerance Atom) (x : Finset Atom) (w : W) : Prop :=
  ∃ z ∈ x.powerset, z.Nonempty ∧ tol.rel z x ∧
    (∀ a ∈ z, restrictor a w) ∧ (∀ a ∈ z, scope a w)

/-! ### Grounding in Link's mereology

`distMaximal` over the free `Finset Atom` model is exactly Link's
distributive inference / star-closure ([link-1983]; `Algebra.star =
Mereology.AlgClosure`). These two theorems discharge the
`distMaximal_iff_star_atoms` Todo flagged in `Plurality/Algebra.lean` §6.

The `Algebra.distr_atom_part` route does *not* instantiate at this carrier:
the bespoke `Mereology.Atom x := ∀ y ≤ x, y = x` degenerates over an
`OrderBot` lattice — only `⊥`/`∅` satisfies it (for nonempty `x`,
`∅ ≤ x ∧ ∅ ≠ x` falsifies it). The faithful bridge therefore runs through
mathlib's `IsAtom` (which excludes `⊥`); over `Finset Atom` the atoms are
the singletons (`Finset.isAtom_iff`). -/

omit [DecidableEq Atom] in
/-- `distMaximal` is Link's **distributive inference**: `P` holds maximally
    on `x` iff every atomic part of `x` satisfies `P`. Grounded in mathlib's
    `IsAtom` — over `Finset Atom` the atoms are singletons, so this is the
    `Atom`-correct restatement of `distMaximal_forces_all`. Holds for every
    `x` (the empty plurality has no atomic parts, so both sides are vacuous). -/
theorem distMaximal_iff_forall_atom (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    distMaximal P x w ↔ ∀ s : Finset Atom, IsAtom s → s ≤ x → ∀ a ∈ s, P a w := by
  unfold distMaximal
  refine ⟨fun h s _ hsx a ha => h a (hsx ha), fun h a ha => ?_⟩
  exact h {a} (Finset.isAtom_singleton a)
    (Finset.singleton_subset_iff.mpr ha) a (Finset.mem_singleton_self a)

/-- `distMaximal` is Link's **star-closure** ([link-1983]'s `*`,
    `Algebra.star = Mereology.AlgClosure`): a nonempty plurality satisfies
    `P` maximally iff it is a join of `P`-atoms (singletons). Discharges the
    `Plurality/Algebra.lean` §6 `distMaximal_iff_star_atoms` Todo; the
    `Nonempty` hypothesis carries the `⊥`-exclusion (`AlgClosure` cannot
    build `∅`). -/
theorem distMaximal_iff_star_atoms (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) (hne : x.Nonempty) :
    distMaximal P x w ↔
      Mereology.AlgClosure (fun s : Finset Atom => ∃ a, s = {a} ∧ P a w) x := by
  constructor
  · intro h
    have key : ∀ s : Finset Atom, (∀ a ∈ s, P a w) →
        s = ∅ ∨ Mereology.AlgClosure (fun t : Finset Atom => ∃ a, t = {a} ∧ P a w) s := by
      intro s
      induction s using Finset.induction with
      | empty => intro _; exact Or.inl rfl
      | @insert a t hat ih =>
        intro hall
        have hPa : P a w := hall a (Finset.mem_insert_self a t)
        have htall : ∀ b ∈ t, P b w := fun b hb => hall b (Finset.mem_insert_of_mem hb)
        refine Or.inr ?_
        rcases ih htall with ht0 | hAt
        · subst ht0
          have hsingle : (insert a (∅ : Finset Atom)) = {a} := by simp
          rw [hsingle]
          exact Mereology.AlgClosure.base ⟨a, rfl, hPa⟩
        · have hins : (insert a t : Finset Atom) = {a} ⊔ t := by
            rw [Finset.insert_eq, Finset.sup_eq_union]
          rw [hins]
          exact Mereology.AlgClosure.sum (Mereology.AlgClosure.base ⟨a, rfl, hPa⟩) hAt
    rcases key x h with hx0 | hAx
    · exact absurd hx0 (Finset.nonempty_iff_ne_empty.mp hne)
    · exact hAx
  · intro h
    clear hne
    induction h with
    | base hp =>
      obtain ⟨b, hb, hPb⟩ := hp
      subst hb
      rw [distMaximal_singleton]
      exact hPb
    | sum _ _ ih₁ ih₂ =>
      intro a ha
      rw [Finset.sup_eq_union, Finset.mem_union] at ha
      rcases ha with hau | hav
      · exact ih₁ a hau
      · exact ih₂ a hav

end Semantics.Plurality.Distributivity
