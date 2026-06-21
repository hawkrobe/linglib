import Linglib.Semantics.Definiteness.Description
import Linglib.Semantics.Definiteness.Interpret
import Linglib.Semantics.Definiteness.Maximality

/-!
# Coppock & Beaver (2015): Definiteness and Determinacy
[coppock-beaver-2015]

The central thesis of [coppock-beaver-2015] is that the Russellian iota
condition `∃!x. P x` is not a primitive, but the conjunction of two
logically independent components:

- **Existence**: `∃x. P x` (asserted, scope-bearing)
- **Uniqueness**: `∀x y. P x → P y → x = y` (presupposed, projects)

The empirical motivation is the projection contrast: under negation,
*"the King of France is bald"* still presupposes that France has at most
one king (Uniqueness), while leaving Existence in the scope of negation.
The classical Russellian analysis collapses both into the assertion and
loses this distinction.

The factorization is operationalized in `Semantics.Definiteness` as
`Existence`, `Uniqueness`, and `existsUnique`; this file tests it over a
tiny frame (`Body`: sun / moon / mars, one situation index).

## Main results

- `kingOfFrance_uniqueness_without_existence`,
  `planet_existence_without_uniqueness`: Existence and Uniqueness are
  logically independent.
- `theSun_existsUnique`, `kingOfFrance_not_existsUnique`,
  `planet_not_existsUnique`: Russellian `existsUnique` holds exactly for a
  singleton extension.
- `interpret_theSun`, `interpret_kingOfFrance`, `interpret_planet`:
  `Semantics.Definiteness.interpret` on a `.unique` description returns
  `none` precisely in the Russellian failure cases.
- `uniqueness_projects_through_negation`,
  `existence_does_not_project_through_negation`: the projection contrast —
  Uniqueness survives a scope operator, Existence does not.
-/

namespace CoppockBeaver2015

open Intensional
open Intensional.Variables
open Semantics.Definiteness

/-! ### A tiny frame for the projection diagnostics -/

/-- Three celestial bodies. `sun` is the unique satisfier of `theSun`;
    `moon` and `mars` jointly witness the multi-extension `planet`. -/
inductive Body where
  | sun
  | moon
  | mars
  deriving DecidableEq, Repr

/-- Singleton restrictor: `theSun` holds of exactly one entity. One index
    suffices — the diagnostics are about predicate extensions, not about
    world-variability. -/
def theSun : Denot Body Unit .et
  | .sun => True
  | _    => False

/-- Multi-witness restrictor: `planet` holds of two entities. -/
def planet : Denot Body Unit .et
  | .moon => True
  | .mars => True
  | _    => False

/-- Empty restrictor: `kingOfFrance` has no satisfier — the
    [coppock-beaver-2015] motivating case. -/
def kingOfFrance : Denot Body Unit .et := fun _ => False

/-! ### Existence and Uniqueness are logically independent -/

/-- The empty restrictor satisfies Uniqueness vacuously but not Existence —
    the configuration [coppock-beaver-2015] use to argue that Uniqueness is a
    separate component, projecting through assertion polarity. A concrete
    instance of the substrate's `uniqueness_does_not_imply_existence`. -/
theorem kingOfFrance_uniqueness_without_existence :
    Uniqueness kingOfFrance ∧ ¬ Existence kingOfFrance :=
  uniqueness_does_not_imply_existence

/-- The multi-witness restrictor satisfies Existence but not Uniqueness:
    moon and mars are both planets and are distinct. -/
theorem planet_existence_without_uniqueness :
    Existence planet ∧ ¬ Uniqueness planet := by
  refine ⟨⟨.moon, trivial⟩, ?_⟩
  intro h
  have : Body.moon = Body.mars := h .moon .mars trivial trivial
  cases this

/-- The singleton restrictor satisfies both components. -/
theorem theSun_existence_and_uniqueness :
    Existence theSun ∧ Uniqueness theSun := by
  refine ⟨⟨.sun, trivial⟩, ?_⟩
  intro x y hx hy
  cases x <;> cases y <;> simp only [theSun] at hx hy ⊢

/-! ### Russellian collapse: `existsUnique` is the conjunction -/

/-- For `theSun`, the Russellian condition holds: `existsUnique` is by
    construction the conjunction of Existence and Uniqueness. -/
theorem theSun_existsUnique : ∃! x, theSun x :=
  (existsUnique_iff_existence_and_uniqueness _).mpr theSun_existence_and_uniqueness

/-- For `kingOfFrance`, `existsUnique` fails — Existence is the missing
    conjunct. The factorization explains *which* component fails. -/
theorem kingOfFrance_not_existsUnique : ¬ ∃! x, kingOfFrance x := by
  rw [existsUnique_iff_existence_and_uniqueness]
  rintro ⟨hExist, _⟩
  exact kingOfFrance_uniqueness_without_existence.2 hExist

/-- For `planet`, `existsUnique` fails — Uniqueness is the missing conjunct. -/
theorem planet_not_existsUnique : ¬ ∃! x, planet x := by
  rw [existsUnique_iff_existence_and_uniqueness]
  rintro ⟨_, hUniq⟩
  exact planet_existence_without_uniqueness.2 hUniq

/-! ### Alignment with `Semantics.Definiteness.interpret` -/

/-- A trivial bi-assignment: every entity slot is `sun`, every situation
    slot is `()`. The diagnostics in this file do not bind anything. -/
def g₀ : Core.Assignment Body := fun _ => Body.sun
def gs₀ : SitAssignment Unit := fun _ => ()

/-- A `.unique` description whose restrictor lacks a unique satisfier
    interprets to `none` — the shared engine behind the Existence-failure
    and Uniqueness-failure diagnostics below. -/
private theorem interpret_unique_const_none_of_not_existsUnique
    (R : Denot Body Unit .et) (h : ¬ ∃! x, R x) :
    interpret (.unique (DenotGS.const R) 0) g₀ gs₀ = none := by
  rw [interpret_unique]
  have hns : ¬ (russellIota (fun x => (DenotGS.const R) g₀ gs₀ x)).isSome := by
    rw [russellIota_isSome_iff_exists_unique]; exact h
  rcases hr : russellIota (fun x => (DenotGS.const R) g₀ gs₀ x) with _ | e
  · rfl
  · exact absurd (hr ▸ rfl) hns

/-- `the sun` (as a `.unique` description with restrictor `theSun`)
    interprets to `some sun` — the unique-witness case. -/
theorem interpret_theSun :
    interpret (.unique (DenotGS.const theSun) 0) g₀ gs₀ = some Body.sun :=
  interpret_unique_eq_some_of_existsUnique _ 0 g₀ gs₀ Body.sun trivial
    (fun y hy => by cases y <;> simp only [theSun, DenotGS.const] at hy ⊢)

/-- `the King of France` interprets to `none` — Existence failure. The
    Russellian iota collapses the projection structure here, but §2 already
    isolated *which* component failed. -/
theorem interpret_kingOfFrance :
    interpret (.unique (DenotGS.const kingOfFrance) 0) g₀ gs₀ = none :=
  interpret_unique_const_none_of_not_existsUnique kingOfFrance kingOfFrance_not_existsUnique

/-- `the planet` interprets to `none` — Uniqueness failure. Same surface
    output as the Existence-failure case, even though the underlying
    presupposition violation is structurally different. -/
theorem interpret_planet :
    interpret (.unique (DenotGS.const planet) 0) g₀ gs₀ = none :=
  interpret_unique_const_none_of_not_existsUnique planet planet_not_existsUnique

/-! ### Negation-projection contrast -/

/-- Predicate-level negation does not affect Uniqueness. This is the
    [coppock-beaver-2015] projection diagnostic, expressed at the restrictor
    layer: whether the King of France is bald or non-bald, the Uniqueness
    presupposition on `kingOfFrance` survives. Uniqueness is a property of the
    *restrictor*, not the *scope*, so any sentential operator wrapping the
    description leaves it unchanged. -/
theorem uniqueness_projects_through_negation (scope : Denot Body Unit .et) :
    Uniqueness kingOfFrance ∧ Uniqueness (fun x => ¬ scope x ∧ kingOfFrance x) := by
  refine ⟨kingOfFrance_uniqueness_without_existence.1, ?_⟩
  intro x y hx _; exact hx.2.elim

/-- The Existence component, by contrast, can be negated independently: a
    non-existing King of France satisfies or fails any scope predicate
    vacuously. This is the contrast that motivates the factorization —
    Existence enters the scope of negation, Uniqueness does not. -/
theorem existence_does_not_project_through_negation (scope : Denot Body Unit .et) :
    ¬ Existence (fun x => scope x ∧ kingOfFrance x) := by
  rintro ⟨_, _, h⟩; exact h

end CoppockBeaver2015
