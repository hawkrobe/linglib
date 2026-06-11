import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.ModelTheory.Basic
import Linglib.Core.Logic.Team.Algebra
import Linglib.Core.Logic.Bilateral.Defs

/-!
# Quantified bilateral state-based modal logic (QBSML)

Core definitions for QBSML, the first-order extension of BSML ([aloni-2022],
[anttila-2021]) presented in [aloni-vanormondt-2023]: indices pair a world
with a partial assignment, states are finite sets of indices, and the formula
language adds predicates and quantifiers, the latter evaluated via state
extensions. Bilateral evaluation, split disjunction (via
`Core.Logic.Team.splitsAs`), and the `NE` atom carry over from BSML; frame
conditions are inherited through the world projection `s↓`, so `support` fits
the `Core.Logic.Team.isFlat_iff` template at the point type
`Index W Var Domain` exactly as BSML's does at `W` (see
`Core/Logic/Modal/QBSML/Properties.lean`).

## Main declarations

* `Assignment`, `Index`: partial variable assignments and world–assignment
  pairs ([aloni-vanormondt-2023] Definition 4.2).
* `State.extendIndividual`, `State.extendUniversal`, `State.extendFunctional`:
  the state extensions `s[x/d]`, `s[x]`, `s[x/h]` interpreting quantifiers
  ([aloni-vanormondt-2023] Definitions 4.5–4.7).
* `State.modalLift`, `State.worldProj`: pairing accessible worlds with an
  assignment, and the world projection `s↓`.
* `QBSMLFormula`: the formula language ([aloni-vanormondt-2023]
  Definition 4.1), with `□` derived as `QBSMLFormula.nec`.
* `QBSMLFormula.IsNEFree`: the NE-free fragment.
* `monadicLang`, `monadicStructure`: the monadic first-order signature on
  `Const` and `Pred` and its structures, as a mathlib `FirstOrder.Language`.
* `QBSMLModel`, `eval`, `support`, `antiSupport`: bilateral evaluation
  ([aloni-vanormondt-2023] Definition 4.9), with the interpretation carried
  as a world-indexed family of mathlib structures.
* `isBilateral`: `support`/`antiSupport` form a
  `Core.Logic.Bilateral.IsBilateral` under `QBSMLFormula.neg`.
* `QBSMLModel.IsStateBased`, `QBSMLModel.IsIndisputable`: frame conditions
  via `s↓` ([aloni-vanormondt-2023] Definition 4.10).

## Implementation notes

* Predicates are monadic and the paper's terms `t := c | x` appear as the
  two atom constructors `pred` (variable) and `predc` (constant), so there is
  no separate term type: [aloni-vanormondt-2023] interprets `Pⁿ(t₁ … tₙ)` for
  arbitrary arity; higher arities can be added without changing the substrate
  abstraction.
* The paper's domain `D` (part of `M = ⟨W, D, R, I⟩`) is a `Domain : Type*`
  parameter, with `[Fintype Domain]` where the universal extension must range
  over all of it. The interpretation `I` is a world-indexed family of mathlib
  first-order structures (`QBSMLModel.interp`, the
  `Semantics.Composition.Model` pattern); `QBSMLModel.pInterp` and
  `QBSMLModel.cInterp` read the world-dependent (non-rigid) predicate and
  constant denotations off `Structure.RelMap` / `Structure.funMap`.
* The paper requires all indices in a state to share an assignment domain
  (`dom gᵢ = dom gⱼ`); this is not enforced at the type level — the state
  operations preserve it.
* `□` is not primitive: the paper takes `□` primitive and derives `◇`; we
  invert this, so `eval`'s `poss` clauses match the paper's derived
  `◇`-clauses and `QBSMLFormula.nec` matches its primitive `□`.
-/

namespace Core.Logic.Modal.QBSML

variable {W Var Domain : Type*}

/-! ### Assignments and indices -/

/-- A partial assignment of domain values to variables
    ([aloni-vanormondt-2023] Definition 4.2: `gᵢ : V → D`); `Option D`
    represents the partiality. -/
abbrev Assignment (Var Domain : Type*) := Var → Option Domain

/-- An index is a (world, assignment) pair ([aloni-vanormondt-2023]
    Definition 4.2: `i = ⟨wᵢ, gᵢ⟩`). -/
abbrev Index (W Var Domain : Type*) := W × Assignment Var Domain

/-- The world component of an index. -/
abbrev Index.world (i : Index W Var Domain) : W := i.1

/-- The assignment component of an index. -/
abbrev Index.assign (i : Index W Var Domain) : Assignment Var Domain := i.2

section Update

variable [DecidableEq Var]

/-- Update an assignment at a single variable: `g[x/d](y) = d` if `y = x`,
    else `g(y)`. -/
def Assignment.update (g : Assignment Var Domain) (x : Var) (d : Domain) :
    Assignment Var Domain :=
  Function.update g x (some d)

/-- Update an index's assignment ([aloni-vanormondt-2023] Definitions 4.3–4.4:
    `i[x/d] := ⟨wᵢ, gᵢ[x/d]⟩`, with the assignment update `gᵢ[x/d]` as
    mathlib's `Function.update`). -/
def Index.update (i : Index W Var Domain) (x : Var) (d : Domain) :
    Index W Var Domain :=
  (i.world, Function.update i.assign x (some d))

@[simp] theorem Index.world_update (i : Index W Var Domain) (x : Var)
    (d : Domain) : (i.update x d).world = i.world := rfl

@[simp] theorem Index.assign_update (i : Index W Var Domain) (x : Var)
    (d : Domain) : (i.update x d).assign = Function.update i.assign x (some d) :=
  rfl

end Update

/-! ### The world projection -/

section WorldProj

variable [DecidableEq W]

/-- The world projection `s↓` of a state of indices: the set of worlds
    appearing in some index ([aloni-vanormondt-2023] Definition 4.10:
    `s↓ := {w | ∃g, (w, g) ∈ s}`). Frame conditions on accessibility are
    stated relative to `s↓`, so QBSML reuses BSML's notions via this
    projection. -/
def State.worldProj (s : Finset (Index W Var Domain)) : Finset W :=
  s.image Index.world

@[simp] theorem State.mem_worldProj {s : Finset (Index W Var Domain)} {w : W} :
    w ∈ State.worldProj s ↔ ∃ i ∈ s, i.world = w :=
  Finset.mem_image

theorem State.worldProj_mono {s t : Finset (Index W Var Domain)} (h : s ⊆ t) :
    State.worldProj s ⊆ State.worldProj t :=
  Finset.image_subset_image h

theorem State.worldProj_nonempty {s : Finset (Index W Var Domain)}
    (h : s.Nonempty) : (State.worldProj s).Nonempty :=
  h.image _

end WorldProj

/-! ### State extensions -/

section State

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain]

/-- **Individual extension** `s[x/d]`: assign `x` to `d` in every index
    ([aloni-vanormondt-2023] Definition 4.5: `s[x/d] := {i[x/d] | i ∈ s}`). -/
def State.extendIndividual (s : Finset (Index W Var Domain))
    (x : Var) (d : Domain) : Finset (Index W Var Domain) :=
  s.image (fun i => i.update x d)

/-- **Universal extension** `s[x]`: extend with every domain value at `x`
    ([aloni-vanormondt-2023] Definition 4.6: `s[x] := {i[x/d] | i ∈ s, d ∈ D}`).
    Requires `[Fintype Domain]` to range over the entire domain. -/
def State.extendUniversal [Fintype Domain] (s : Finset (Index W Var Domain))
    (x : Var) : Finset (Index W Var Domain) :=
  Finset.univ.biUnion (fun d : Domain => State.extendIndividual s x d)

/-- **Functional extension** `s[x/h]`: for each `i ∈ s`, extend with values
    drawn from `h i` ([aloni-vanormondt-2023] Definition 4.7:
    `s[x/h] := {i[x/d] | i ∈ s, d ∈ h(i)}`). Interprets existential
    quantification: `∃x φ` iff `M, s[x/h] ⊨ φ` for some functional `h`. -/
def State.extendFunctional (s : Finset (Index W Var Domain))
    (x : Var) (h : Index W Var Domain → Finset Domain) :
    Finset (Index W Var Domain) :=
  s.biUnion (fun i => (h i).image (fun d => i.update x d))

/-! ### Membership characterisations -/

@[simp] theorem State.mem_extendIndividual {s : Finset (Index W Var Domain)}
    {x : Var} {d : Domain} {j : Index W Var Domain} :
    j ∈ State.extendIndividual s x d ↔ ∃ i ∈ s, i.update x d = j :=
  Finset.mem_image

@[simp] theorem State.mem_extendUniversal [Fintype Domain]
    {s : Finset (Index W Var Domain)} {x : Var} {j : Index W Var Domain} :
    j ∈ State.extendUniversal s x ↔ ∃ d, ∃ i ∈ s, i.update x d = j := by
  simp only [State.extendUniversal, Finset.mem_biUnion, Finset.mem_univ,
    true_and, State.mem_extendIndividual]

@[simp] theorem State.mem_extendFunctional {s : Finset (Index W Var Domain)}
    {x : Var} {h : Index W Var Domain → Finset Domain} {j : Index W Var Domain} :
    j ∈ State.extendFunctional s x h ↔ ∃ i ∈ s, ∃ d ∈ h i, i.update x d = j := by
  simp only [State.extendFunctional, Finset.mem_biUnion, Finset.mem_image]

/-! ### Extension algebra -/

theorem State.extendIndividual_empty (x : Var) (d : Domain) :
    State.extendIndividual (∅ : Finset (Index W Var Domain)) x d = ∅ :=
  Finset.image_empty _

theorem State.extendIndividual_union (s t : Finset (Index W Var Domain))
    (x : Var) (d : Domain) :
    State.extendIndividual (s ∪ t) x d =
      State.extendIndividual s x d ∪ State.extendIndividual t x d :=
  Finset.image_union ..

theorem State.extendIndividual_mono {s t : Finset (Index W Var Domain)}
    (x : Var) (d : Domain) (hsub : s ⊆ t) :
    State.extendIndividual s x d ⊆ State.extendIndividual t x d :=
  Finset.image_subset_image hsub

theorem State.extendUniversal_empty [Fintype Domain] (x : Var) :
    State.extendUniversal (∅ : Finset (Index W Var Domain)) x = ∅ := by
  ext j
  simp

theorem State.extendUniversal_union [Fintype Domain]
    (s t : Finset (Index W Var Domain)) (x : Var) :
    State.extendUniversal (s ∪ t) x =
      State.extendUniversal s x ∪ State.extendUniversal t x := by
  simp only [State.extendUniversal, State.extendIndividual_union,
    Finset.biUnion_union]

theorem State.extendUniversal_mono [Fintype Domain]
    {s t : Finset (Index W Var Domain)} (x : Var) (hsub : s ⊆ t) :
    State.extendUniversal s x ⊆ State.extendUniversal t x :=
  Finset.biUnion_mono fun d _ => State.extendIndividual_mono x d hsub

theorem State.extendFunctional_empty (x : Var)
    (h : Index W Var Domain → Finset Domain) :
    State.extendFunctional (∅ : Finset (Index W Var Domain)) x h = ∅ :=
  Finset.biUnion_empty

theorem State.extendFunctional_union (s t : Finset (Index W Var Domain))
    (x : Var) (h : Index W Var Domain → Finset Domain) :
    State.extendFunctional (s ∪ t) x h =
      State.extendFunctional s x h ∪ State.extendFunctional t x h :=
  Finset.union_biUnion

theorem State.extendFunctional_mono {s t : Finset (Index W Var Domain)}
    (x : Var) (h : Index W Var Domain → Finset Domain) (hsub : s ⊆ t) :
    State.extendFunctional s x h ⊆ State.extendFunctional t x h :=
  Finset.biUnion_subset_biUnion_of_subset_left _ hsub

/-- The universal extension is the functional extension with the constant
    full-domain functional. -/
theorem State.extendUniversal_eq_extendFunctional [Fintype Domain]
    (s : Finset (Index W Var Domain)) (x : Var) :
    State.extendUniversal s x =
      State.extendFunctional s x (fun _ => Finset.univ) := by
  ext j
  simp only [State.mem_extendUniversal, State.mem_extendFunctional,
    Finset.mem_univ, true_and]
  tauto

end State

/-! ### Modal pairing -/

section ModalLift

variable [DecidableEq W] [Fintype Var] [DecidableEq Domain]

/-- **Modal pairing** `R(wᵢ)[gᵢ]`: pair each accessible world with the
    assignment of the original index. Used in modal evaluation
    ([aloni-vanormondt-2023] Definition 4.9). -/
def State.modalLift (X : Finset W) (g : Assignment Var Domain) :
    Finset (Index W Var Domain) :=
  X.image (fun v => (v, g))

@[simp] theorem State.mem_modalLift {X : Finset W} {g : Assignment Var Domain}
    {i : Index W Var Domain} :
    i ∈ State.modalLift X g ↔ i.world ∈ X ∧ i.assign = g := by
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    exact ⟨hv, rfl⟩
  · rintro ⟨h, rfl⟩
    exact Finset.mem_image.mpr ⟨i.world, h, rfl⟩

@[simp] theorem State.worldProj_modalLift (X : Finset W)
    (g : Assignment Var Domain) :
    State.worldProj (State.modalLift X g) = X := by
  ext w
  simp only [State.mem_worldProj, State.mem_modalLift]
  constructor
  · rintro ⟨i, ⟨hX, -⟩, rfl⟩
    exact hX
  · exact fun hw => ⟨(w, g), ⟨hw, rfl⟩, rfl⟩

/-- A state contained in a modal pairing is recovered by projecting its
    worlds and pairing them back with the same assignment: every index of
    `s ⊆ State.modalLift X g` carries the assignment `g`. -/
theorem State.modalLift_worldProj_of_subset {s : Finset (Index W Var Domain)}
    {X : Finset W} {g : Assignment Var Domain}
    (h : s ⊆ State.modalLift X g) :
    State.modalLift (State.worldProj s) g = s := by
  ext i
  simp only [State.mem_modalLift, State.mem_worldProj]
  constructor
  · rintro ⟨⟨j, hjs, hjw⟩, hig⟩
    have : i = j :=
      Prod.ext hjw.symm (hig.trans (State.mem_modalLift.mp (h hjs)).2.symm)
    exact this ▸ hjs
  · intro his
    exact ⟨⟨i, his, rfl⟩, (State.mem_modalLift.mp (h his)).2⟩

theorem State.worldProj_subset_of_subset_modalLift
    {s : Finset (Index W Var Domain)} {X : Finset W}
    {g : Assignment Var Domain} (h : s ⊆ State.modalLift X g) :
    State.worldProj s ⊆ X := by
  rw [← State.worldProj_modalLift X g]
  exact State.worldProj_mono h

end ModalLift

/-! ### The formula language -/

variable {Const Pred : Type*}

/-- QBSML formula language ([aloni-vanormondt-2023] Definition 4.1),
    parameterized over variable type `Var`, constant type `Const`, and
    (monadic) predicate type `Pred`. The paper's terms `t := c | x` appear
    as the two atom constructors. `□` is not primitive — see
    `QBSMLFormula.nec`. -/
inductive QBSMLFormula (Var : Type*) (Const : Type*) (Pred : Type*) where
  /-- Monadic predicate applied to a variable. -/
  | pred : Pred → Var → QBSMLFormula Var Const Pred
  /-- Monadic predicate applied to an individual constant. -/
  | predc : Pred → Const → QBSMLFormula Var Const Pred
  /-- Non-emptiness atom: state is non-empty. -/
  | ne : QBSMLFormula Var Const Pred
  /-- Bilateral negation: swap support/anti-support. -/
  | neg : QBSMLFormula Var Const Pred → QBSMLFormula Var Const Pred
  /-- Conjunction. -/
  | conj : QBSMLFormula Var Const Pred → QBSMLFormula Var Const Pred →
      QBSMLFormula Var Const Pred
  /-- Split (tensor) disjunction. -/
  | disj : QBSMLFormula Var Const Pred → QBSMLFormula Var Const Pred →
      QBSMLFormula Var Const Pred
  /-- Possibility modal. -/
  | poss : QBSMLFormula Var Const Pred → QBSMLFormula Var Const Pred
  /-- Existential quantifier. -/
  | exi : Var → QBSMLFormula Var Const Pred → QBSMLFormula Var Const Pred
  /-- Universal quantifier. -/
  | univ : Var → QBSMLFormula Var Const Pred → QBSMLFormula Var Const Pred
  deriving Repr

/-- Necessity, derived: `□φ := ¬◇¬φ`. [aloni-vanormondt-2023] takes `□`
    primitive and `◇ := ¬□¬` derived; we invert this, so `eval`'s `poss`
    clauses match the paper's derived `◇`-clauses and `nec` matches its
    primitive `□`. -/
def QBSMLFormula.nec (φ : QBSMLFormula Var Const Pred) : QBSMLFormula Var Const Pred :=
  .neg (.poss (.neg φ))

/-- The NE-free fragment: formulas not containing the `NE` atom. On this
    fragment QBSML reduces to classical first-order modal logic
    ([aloni-vanormondt-2023] analogue of [anttila-2021]
    Proposition 2.2.16); see `Core/Logic/Modal/QBSML/Properties.lean`. -/
inductive QBSMLFormula.IsNEFree : QBSMLFormula Var Const Pred → Prop
  | pred (P : Pred) (x : Var) : IsNEFree (.pred P x)
  | predc (P : Pred) (c : Const) : IsNEFree (.predc P c)
  | neg {φ : QBSMLFormula Var Const Pred} : IsNEFree φ → IsNEFree (.neg φ)
  | conj {φ ψ : QBSMLFormula Var Const Pred} :
      IsNEFree φ → IsNEFree ψ → IsNEFree (.conj φ ψ)
  | disj {φ ψ : QBSMLFormula Var Const Pred} :
      IsNEFree φ → IsNEFree ψ → IsNEFree (.disj φ ψ)
  | poss {φ : QBSMLFormula Var Const Pred} : IsNEFree φ → IsNEFree (.poss φ)
  | exi (x : Var) {φ : QBSMLFormula Var Const Pred} : IsNEFree φ → IsNEFree (.exi x φ)
  | univ (x : Var) {φ : QBSMLFormula Var Const Pred} : IsNEFree φ → IsNEFree (.univ x φ)

/-! ### The monadic signature and models -/

/-- The monadic signature on `Const` and `Pred`: one individual constant per
    `Const`, one unary relation symbol per `Pred` — [aloni-vanormondt-2023]
    Definition 4.1's signature (terms `t := c | x`, monadic relations). -/
def monadicLang.{u, v} (Const : Type u) (Pred : Type v) :
    FirstOrder.Language where
  Functions := fun n => match n with
    | 0 => Const
    | _ => PEmpty
  Relations := fun n => match n with
    | 1 => Pred
    | _ => PEmpty

/-- A constant as a symbol of the monadic signature (defeq; the parametric
    analogue of mathlib's per-symbol abbreviations, cf.
    `Fragments/English/Toy.lean`). -/
abbrev monadicConst {Const Pred : Type*} (c : Const) :
    (monadicLang Const Pred).Constants := c

/-- A predicate as a relation symbol of the monadic signature (defeq). -/
abbrev monadicRel {Const Pred : Type*} (P : Pred) :
    (monadicLang Const Pred).Relations 1 := P

/-- The `monadicLang Const Pred` structure a constant interpretation and a
    predicate valuation induce. -/
@[reducible] def monadicStructure {Const Pred Domain : Type*}
    (κ : Const → Domain) (V : Pred → Domain → Prop) :
    (monadicLang Const Pred).Structure Domain where
  funMap := fun {n} f => match n, f with
    | 0, c => fun _ => κ c
    | _ + 1, f => f.elim
  RelMap := fun {n} r => match n, r with
    | 1, P => fun v => V P (v 0)
    | 0, r => r.elim
    | _ + 2, r => r.elim

@[simp] theorem monadicStructure_relMap {Const Pred Domain : Type*}
    (κ : Const → Domain) (V : Pred → Domain → Prop) (P : Pred)
    (v : Fin 1 → Domain) :
    (monadicStructure κ V).RelMap (monadicRel P) v ↔ V P (v 0) :=
  Iff.rfl

@[simp] theorem monadicStructure_funMap {Const Pred Domain : Type*}
    (κ : Const → Domain) (V : Pred → Domain → Prop) (c : Const)
    (v : Fin 0 → Domain) :
    (monadicStructure κ V).funMap (monadicConst (Pred := Pred) c) v = κ c :=
  rfl

/-- A QBSML model ([aloni-vanormondt-2023] Definition 4.2:
    `M = ⟨W, D, R, I⟩`), with the domain as a type parameter, accessibility
    as a per-world `Finset`, and the interpretation `I` as a world-indexed
    family of mathlib first-order structures on the domain — the pattern of
    `Semantics.Composition.Model`. Structures are carried as terms, not
    instances: a world-indexed family cannot be instance-based, so interfacing
    with instance-based mathlib API (`Formula.Realize`) threads
    `letI := M.interp w`. -/
structure QBSMLModel (W : Type*) (Domain : Type*) (Const : Type*)
    (Pred : Type*) where
  /-- Accessibility relation (per-world set of accessible worlds). -/
  access : W → Finset W
  /-- World-indexed interpretation of the monadic signature. -/
  interp : W → (monadicLang Const Pred).Structure Domain

/-- The predicate denotation at a world, read off the model's structure
    family via `Structure.RelMap` — the world-relativized `I(w)(Pⁿ)` of
    [aloni-vanormondt-2023] Definition 4.2, specialised to monadic `P`
    (cf. `Semantics.Composition.Model.pred₁ext`). -/
def QBSMLModel.pInterp {W Domain Const Pred : Type*}
    (M : QBSMLModel W Domain Const Pred) (P : Pred) (w : W) (d : Domain) :
    Prop :=
  (M.interp w).RelMap (monadicRel P) (fun _ => d)

/-- The constant denotation at a world — the world-relative `I(w)(c)` of
    [aloni-vanormondt-2023] Definitions 4.2 and 4.8, read off
    `Structure.funMap` (cf. `Semantics.Composition.Model.const`). -/
def QBSMLModel.cInterp {W Domain Const Pred : Type*}
    (M : QBSMLModel W Domain Const Pred) (c : Const) (w : W) : Domain :=
  (M.interp w).funMap (monadicConst c) default

@[simp] theorem QBSMLModel.pInterp_monadicStructure
    {W Domain Const Pred : Type*} (access : W → Finset W)
    (κ : W → Const → Domain) (V : W → Pred → Domain → Prop) (P : Pred)
    (w : W) (d : Domain) :
    QBSMLModel.pInterp ⟨access, fun w => monadicStructure (κ w) (V w)⟩ P w d ↔
      V w P d :=
  Iff.rfl

@[simp] theorem QBSMLModel.cInterp_monadicStructure
    {W Domain Const Pred : Type*} (access : W → Finset W)
    (κ : W → Const → Domain) (V : W → Pred → Domain → Prop) (c : Const)
    (w : W) :
    QBSMLModel.cInterp ⟨access, fun w => monadicStructure (κ w) (V w)⟩ c w =
      κ w c :=
  rfl

/-! ### Bilateral evaluation -/

section Evaluation

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain]
variable [Fintype Domain]

/-- Bilateral evaluation of QBSML formulas ([aloni-vanormondt-2023]
    Definition 4.9): `eval M true φ s` is support (`M, s ⊨ φ`),
    `eval M false φ s` anti-support (`M, s ⫤ φ`). Negation flips the
    polarity, making double-negation elimination definitional. -/
def eval (M : QBSMLModel W Domain Const Pred) :
    Bool → QBSMLFormula Var Const Pred → Finset (Index W Var Domain) → Prop
  | true,  .pred P x, s =>
      ∀ i ∈ s, ∃ d, i.assign x = some d ∧ M.pInterp P i.world d
  | false, .pred P x, s =>
      ∀ i ∈ s, ∃ d, i.assign x = some d ∧ ¬ M.pInterp P i.world d
  | true,  .predc P c, s =>
      ∀ i ∈ s, M.pInterp P i.world (M.cInterp c i.world)
  | false, .predc P c, s =>
      ∀ i ∈ s, ¬ M.pInterp P i.world (M.cInterp c i.world)
  | true,  .ne, s => s.Nonempty
  | false, .ne, s => s = ∅
  | true,  .neg ψ, s => eval M false ψ s
  | false, .neg ψ, s => eval M true ψ s
  | true,  .conj φ ψ, s => eval M true φ s ∧ eval M true ψ s
  | false, .conj φ ψ, s => ∃ t₁ t₂ : Finset (Index W Var Domain),
      Core.Logic.Team.splitsAs s t₁ t₂ ∧ eval M false φ t₁ ∧ eval M false ψ t₂
  | true,  .disj φ ψ, s => ∃ t₁ t₂ : Finset (Index W Var Domain),
      Core.Logic.Team.splitsAs s t₁ t₂ ∧ eval M true φ t₁ ∧ eval M true ψ t₂
  | false, .disj φ ψ, s => eval M false φ s ∧ eval M false ψ s
  | true,  .poss ψ, s =>
      ∀ i ∈ s, ∃ X : Finset W, X ⊆ M.access i.world ∧ X.Nonempty ∧
        eval M true ψ (State.modalLift X i.assign)
  | false, .poss ψ, s =>
      ∀ i ∈ s, eval M false ψ (State.modalLift (M.access i.world) i.assign)
  | true,  .univ x ψ, s => eval M true ψ (State.extendUniversal s x)
  | false, .univ x ψ, s =>
      ∃ h : Index W Var Domain → Finset Domain, (∀ i ∈ s, (h i).Nonempty) ∧
        eval M false ψ (State.extendFunctional s x h)
  | true,  .exi x ψ, s =>
      ∃ h : Index W Var Domain → Finset Domain, (∀ i ∈ s, (h i).Nonempty) ∧
        eval M true ψ (State.extendFunctional s x h)
  | false, .exi x ψ, s => eval M false ψ (State.extendUniversal s x)

/-- Support: positive evaluation. -/
abbrev support (M : QBSMLModel W Domain Const Pred) (φ : QBSMLFormula Var Const Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  eval M true φ s

/-- Anti-support: negative evaluation. -/
abbrev antiSupport (M : QBSMLModel W Domain Const Pred) (φ : QBSMLFormula Var Const Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  eval M false φ s

@[simp] lemma support_neg (M : QBSMLModel W Domain Const Pred)
    (φ : QBSMLFormula Var Const Pred) (s : Finset (Index W Var Domain)) :
    support M (.neg φ) s ↔ antiSupport M φ s := Iff.rfl

@[simp] lemma antiSupport_neg (M : QBSMLModel W Domain Const Pred)
    (φ : QBSMLFormula Var Const Pred) (s : Finset (Index W Var Domain)) :
    antiSupport M (.neg φ) s ↔ support M φ s := Iff.rfl

/-- `support` and `antiSupport` form a paraconsistent bilateral logic
    (`Core.Logic.Bilateral.IsBilateral`) under `QBSMLFormula.neg`, like
    BSML's `isBilateral` at the point type `Index W Var Domain`. -/
theorem isBilateral (M : QBSMLModel W Domain Const Pred) :
    Core.Logic.Bilateral.IsBilateral (Form := QBSMLFormula Var Const Pred)
      (support M) (antiSupport M) QBSMLFormula.neg :=
  Core.Logic.Bilateral.IsBilateral.of_iff (support_neg M) (antiSupport_neg M)

end Evaluation

/-! ### Frame conditions via the world projection -/

section FrameConditions

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain]

/-- `R` is state-based on `(M, s)`: every world in `s↓` sees exactly `s↓`
    ([aloni-vanormondt-2023] Definition 4.10). Defined via
    `Core.Logic.Team.IsStateBased` applied to `State.worldProj s`, sharing
    BSML's frame-condition substrate. -/
def QBSMLModel.IsStateBased (M : QBSMLModel W Domain Const Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  Core.Logic.Team.IsStateBased M.access (State.worldProj s)

/-- `R` is indisputable on `(M, s)`: all worlds in `s↓` see the same
    accessible set ([aloni-vanormondt-2023] Definition 4.10). -/
def QBSMLModel.IsIndisputable (M : QBSMLModel W Domain Const Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  Core.Logic.Team.IsIndisputable M.access (State.worldProj s)

instance [Fintype W] (M : QBSMLModel W Domain Const Pred)
    (s : Finset (Index W Var Domain)) : Decidable (M.IsStateBased s) := by
  unfold QBSMLModel.IsStateBased; infer_instance

instance [Fintype W] (M : QBSMLModel W Domain Const Pred)
    (s : Finset (Index W Var Domain)) : Decidable (M.IsIndisputable s) := by
  unfold QBSMLModel.IsIndisputable; infer_instance

end FrameConditions

end Core.Logic.Modal.QBSML
