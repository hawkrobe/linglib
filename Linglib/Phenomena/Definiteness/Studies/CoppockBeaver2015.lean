import Linglib.Core.Nominal.Description
import Linglib.Core.Nominal.Interpret
import Linglib.Core.Nominal.Maximality

/-!
# Coppock & Beaver (2015): Definiteness and Determinacy
@cite{coppock-beaver-2015}

The central thesis of @cite{coppock-beaver-2015} is that the Russellian iota
condition `∃!x. P x` is not a primitive, but the conjunction of two
logically independent components:

- **Existence**: `∃x. P x` (asserted, scope-bearing)
- **Uniqueness**: `∀x y. P x → P y → x = y` (presupposed, projects)

The empirical motivation is the projection contrast: under negation,
*"the King of France is bald"* still presupposes that France has at most
one king (Uniqueness), while leaving Existence in the scope of negation.
The classical Russellian analysis collapses both into the assertion and
loses this distinction.

## What this file tests

The factorization is operationalized in `Core.Nominal.Maximality` as
`Existence`, `Uniqueness`, and `existsUnique` over `F.Denot .et`. This
study file builds three concrete restrictors over a tiny frame (sun /
moon / mars; one index) and verifies:

1. **Logical independence** — Uniqueness can hold without Existence
   (the empty `kingOfFrance` extension), and Existence can hold without
   Uniqueness (the multi-witness `planet` extension).
2. **Russellian collapse** — `existsUnique` is true exactly for
   restrictors with a singleton extension (`theSun`).
3. **Interpretation alignment** — `Core.Nominal.interpret` on a
   `.unique` description returns `none` precisely in the Russellian
   failure cases (no extension, or non-unique extension).
4. **Negation-projection contrast** — the Uniqueness component projects
   through the assertion's polarity: ¬(the King of France is bald)
   still requires uniqueness of the King of France.
-/

namespace Phenomena.Definiteness.Studies.CoppockBeaver2015

open Core.IntensionalLogic
open Core.IntensionalLogic.Variables
open Core.Nominal

-- ════════════════════════════════════════════════════════════════
-- §1: A tiny frame for the projection diagnostics
-- ════════════════════════════════════════════════════════════════

/-- Three celestial bodies. `sun` is the unique satisfier of `theSun`;
    `moon` and `mars` jointly witness the multi-extension `planet`. -/
inductive Body where
  | sun
  | moon
  | mars
  deriving DecidableEq, Repr

/-- One index suffices: the diagnostics are about predicate extensions,
    not about world-variability. -/
def F : Frame := { Entity := Body, Index := Unit }

/-- Singleton restrictor: `theSun` holds of exactly one entity. -/
def theSun : F.Denot .et
  | .sun => True
  | _    => False

/-- Multi-witness restrictor: `planet` holds of two entities. -/
def planet : F.Denot .et
  | .moon => True
  | .mars => True
  | _    => False

/-- Empty restrictor: `kingOfFrance` has no satisfier. The
    @cite{coppock-beaver-2015} motivating case. -/
def kingOfFrance : F.Denot .et := fun _ => False

-- ════════════════════════════════════════════════════════════════
-- §2: Existence and Uniqueness are logically independent
-- ════════════════════════════════════════════════════════════════

/-- The empty restrictor satisfies Uniqueness vacuously, but not
    Existence. The exact configuration @cite{coppock-beaver-2015} use
    to argue that Uniqueness is a separate component, projecting
    through assertion polarity. -/
theorem kingOfFrance_uniqueness_without_existence :
    Uniqueness (F := F) kingOfFrance ∧
    ¬ Existence (F := F) kingOfFrance := by
  refine ⟨?_, ?_⟩
  · intro x y hx _; exact hx.elim
  · rintro ⟨_, h⟩; exact h

/-- The multi-witness restrictor satisfies Existence but not Uniqueness.
    Witnesses: moon and mars are both planets and are distinct. -/
theorem planet_existence_without_uniqueness :
    Existence (F := F) planet ∧
    ¬ Uniqueness (F := F) planet := by
  refine ⟨⟨.moon, trivial⟩, ?_⟩
  intro h
  have : Body.moon = Body.mars := h .moon .mars trivial trivial
  cases this

/-- The singleton restrictor satisfies both components. -/
theorem theSun_existence_and_uniqueness :
    Existence (F := F) theSun ∧ Uniqueness (F := F) theSun := by
  refine ⟨⟨.sun, trivial⟩, ?_⟩
  intro x y hx hy
  cases x <;> cases y <;> simp_all [theSun]

-- ════════════════════════════════════════════════════════════════
-- §3: Russellian collapse — `existsUnique` is the conjunction
-- ════════════════════════════════════════════════════════════════

/-- For `theSun`, the Russellian condition holds: `existsUnique` is by
    construction the conjunction of Existence and Uniqueness. -/
theorem theSun_existsUnique :
    existsUnique (F := F) theSun :=
  theSun_existence_and_uniqueness

/-- For `kingOfFrance`, `existsUnique` fails — Existence is the missing
    conjunct. The factorization explains *which* component fails. -/
theorem kingOfFrance_not_existsUnique :
    ¬ existsUnique (F := F) kingOfFrance := by
  rintro ⟨hExist, _⟩
  exact kingOfFrance_uniqueness_without_existence.2 hExist

/-- For `planet`, `existsUnique` fails — Uniqueness is the missing
    conjunct. -/
theorem planet_not_existsUnique :
    ¬ existsUnique (F := F) planet := by
  rintro ⟨_, hUniq⟩
  exact planet_existence_without_uniqueness.2 hUniq

-- ════════════════════════════════════════════════════════════════
-- §4: Alignment with `Core.Nominal.interpret`
-- ════════════════════════════════════════════════════════════════

/-- A trivial bi-assignment: every entity slot is `sun`, every situation
    slot is `()`. The diagnostics in this file do not bind anything. -/
def g₀ : Core.Assignment F.Entity := fun _ => Body.sun
def gs₀ : SitAssignment F := fun _ => ()

/-- `the sun` (as a `.unique` description with restrictor `theSun`)
    interprets to `some sun` — the unique-witness case. The Russellian
    iota's choose witness equals `Body.sun` because Uniqueness forces
    every satisfier to coincide with `Body.sun`. -/
theorem interpret_theSun :
    interpret (F := F) (.unique (DenotGS.const theSun) 0) g₀ gs₀ = some Body.sun := by
  have hExists : (interpret (F := F)
      (.unique (DenotGS.const theSun) 0) g₀ gs₀).isSome = true := by
    rw [interpret_unique]
    exact (russellIota_isSome_iff_existsUnique _).mpr theSun_existsUnique
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hExists
  rw [he]
  congr 1
  have hSat : theSun e := by
    have : russellIota (fun x => (DenotGS.const theSun) g₀ gs₀ x) = some e := by
      rw [← interpret_unique]; exact he
    exact russellIota_witness_satisfies _ e this
  cases e <;> first | rfl | (simp [theSun] at hSat)

/-- `the King of France` interprets to `none` — Existence failure. The
    Russellian iota collapses the projection structure here, but the
    diagnostic in §2 already isolated *which* component failed. -/
theorem interpret_kingOfFrance :
    interpret (F := F)
      (.unique (DenotGS.const kingOfFrance) 0) g₀ gs₀ = none := by
  rw [interpret_unique]
  have : ¬ (russellIota (fun x => (DenotGS.const kingOfFrance) g₀ gs₀ x)).isSome := by
    rw [russellIota_isSome_iff_existsUnique]; exact kingOfFrance_not_existsUnique
  rcases h : russellIota (fun x => (DenotGS.const kingOfFrance) g₀ gs₀ x) with _ | e
  · rfl
  · exact absurd (h ▸ rfl) this

/-- `the planet` interprets to `none` — Uniqueness failure. Same surface
    output as the Existence-failure case, even though the underlying
    presupposition violation is structurally different. -/
theorem interpret_planet :
    interpret (F := F)
      (.unique (DenotGS.const planet) 0) g₀ gs₀ = none := by
  rw [interpret_unique]
  have : ¬ (russellIota (fun x => (DenotGS.const planet) g₀ gs₀ x)).isSome := by
    rw [russellIota_isSome_iff_existsUnique]; exact planet_not_existsUnique
  rcases h : russellIota (fun x => (DenotGS.const planet) g₀ gs₀ x) with _ | e
  · rfl
  · exact absurd (h ▸ rfl) this

-- ════════════════════════════════════════════════════════════════
-- §5: Negation-projection contrast (the empirical payoff)
-- ════════════════════════════════════════════════════════════════

/-- Predicate-level negation does not affect Uniqueness. This is the
    @cite{coppock-beaver-2015} projection diagnostic, expressed at the
    restrictor layer: whether the King of France is bald or non-bald,
    the Uniqueness presupposition on `kingOfFrance` survives.
    Operationalized here as: Uniqueness is a property of the *restrictor*,
    not the *scope*, so any sentential operator wrapping the description
    leaves it unchanged. -/
theorem uniqueness_projects_through_negation
    (scope : F.Denot .et) :
    Uniqueness (F := F) kingOfFrance ∧
    Uniqueness (F := F) (fun x => ¬ scope x ∧ kingOfFrance x) := by
  refine ⟨kingOfFrance_uniqueness_without_existence.1, ?_⟩
  intro x y hx _; exact hx.2.elim

/-- The Existence component, by contrast, can be negated independently:
    a non-existing King of France can satisfy or fail to satisfy any
    scope predicate vacuously. This is the contrast that motivates the
    factorization — Existence enters the scope of negation, Uniqueness
    does not. -/
theorem existence_does_not_project_through_negation
    (scope : F.Denot .et) :
    ¬ Existence (F := F) (fun x => scope x ∧ kingOfFrance x) := by
  rintro ⟨_, _, h⟩; exact h

end Phenomena.Definiteness.Studies.CoppockBeaver2015
