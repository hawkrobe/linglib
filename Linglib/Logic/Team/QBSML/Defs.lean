import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Linglib.Logic.Assignment
import Linglib.Logic.Modal.FirstOrder.Semantics
import Linglib.Logic.Modal.FirstOrder.Monadic
import Linglib.Logic.Team.Algebra
import Linglib.Logic.Bilateral.Defs

/-!
# Quantified bilateral state-based modal logic (QBSML)

QBSML ([aloni-vanormondt-2023]) is the first-order extension of BSML
([aloni-2022], [anttila-2021]). A formula is evaluated bilaterally —
supported or anti-supported — at a *state*: a finite set of *indices*
`⟨w, g⟩` pairing a world with a partial variable assignment. Quantifiers
are interpreted by extending states, disjunction by splitting them, and
the non-emptiness atom `NE` — the only source of non-classical behaviour —
by state non-emptiness.

## Main definitions

* `Index`, `State.worldProj`: indices `⟨w, g⟩` and the world projection `s↓`.
* `State.extendIndividual`, `State.extendUniversal`,
  `State.extendFunctional`: the state extensions `s[x/d]`, `s[x]`, `s[x/h]`.
* `State.modalLift`: a set of worlds, paired with one assignment.
* `Formula`: the formula language; `Formula.nec` is the derived `□`;
  `Formula.NEFree` the NE-free fragment.
* `Model`, `Model.ofMonadic`: models, as `ModalStructure`s over
  `Language.monadicWithConstants`.
* `eval`, `support`, `antiSupport`: bilateral evaluation.
* `ModalStructure.IsStateBased`, `ModalStructure.IsIndisputable`: frame
  conditions via `s↓`.

## Implementation notes

* The paper takes `□` primitive and derives `◇`; we invert this, so
  `eval`'s `poss` clauses match the paper's derived `◇`-clauses.
* The paper's requirement that all indices of a state share an assignment
  domain is not enforced at the type level; the state operations
  preserve it.
-/

namespace QBSML

open FirstOrder

variable {W Var Domain : Type*}

/-! ### Indices -/

/-- An index is a (world, assignment) pair ([aloni-vanormondt-2023]
    Definition 4.2: `i = ⟨wᵢ, gᵢ⟩`), with `gᵢ` a `PartialAssign`. -/
abbrev Index (W Var Domain : Type*) := W × PartialAssign Var Domain

/-- The world component of an index. -/
abbrev Index.world (i : Index W Var Domain) : W := i.1

/-- The assignment component of an index. -/
abbrev Index.assign (i : Index W Var Domain) : PartialAssign Var Domain := i.2

section Update

variable [DecidableEq Var]

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

/-- **Witness reconstruction**: a state `t` consisting of `x`-updates of
    indices of `s` is recovered exactly as the functional extension of `s`
    by the functional collecting, at each index, the values whose updates
    land in `t`. The shared Finset surgery behind the existential-witness
    steps of the free-choice facts
    (`Logic/Team/QBSML/FreeChoice.lean`). -/
theorem State.extendFunctional_filter_of_update_mem [Fintype Domain]
    {s t : Finset (Index W Var Domain)} {x : Var}
    (hpar : ∀ j ∈ t, ∃ i ∈ s, ∃ d, i.update x d = j) :
    State.extendFunctional s x
      (fun i => Finset.univ.filter (fun d => i.update x d ∈ t)) = t := by
  ext j
  rw [State.mem_extendFunctional]
  constructor
  · rintro ⟨i, -, d, hd, rfl⟩
    exact (Finset.mem_filter.mp hd).2
  · intro hj
    obtain ⟨i, hi, d, rfl⟩ := hpar j hj
    exact ⟨i, hi, d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hj⟩, rfl⟩

end State

/-! ### Modal pairing -/

section ModalLift

variable [DecidableEq W] [Fintype Var] [DecidableEq Domain]

/-- **Modal pairing** `R(wᵢ)[gᵢ]`: pair each accessible world with the
    assignment of the original index. Used in modal evaluation
    ([aloni-vanormondt-2023] Definition 4.9). -/
def State.modalLift (X : Finset W) (g : PartialAssign Var Domain) :
    Finset (Index W Var Domain) :=
  X.image (fun v => (v, g))

@[simp] theorem State.mem_modalLift {X : Finset W} {g : PartialAssign Var Domain}
    {i : Index W Var Domain} :
    i ∈ State.modalLift X g ↔ i.world ∈ X ∧ i.assign = g := by
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    exact ⟨hv, rfl⟩
  · rintro ⟨h, rfl⟩
    exact Finset.mem_image.mpr ⟨i.world, h, rfl⟩

@[simp] theorem State.modalLift_singleton (w : W)
    (g : PartialAssign Var Domain) :
    State.modalLift {w} g = {(w, g)} :=
  Finset.image_singleton ..

@[simp] theorem State.worldProj_modalLift (X : Finset W)
    (g : PartialAssign Var Domain) :
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
    {X : Finset W} {g : PartialAssign Var Domain}
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
    {g : PartialAssign Var Domain} (h : s ⊆ State.modalLift X g) :
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
    `Formula.nec`. -/
inductive Formula (Var : Type*) (Const : Type*) (Pred : Type*) where
  /-- Monadic predicate applied to a variable. -/
  | pred : Pred → Var → Formula Var Const Pred
  /-- Monadic predicate applied to an individual constant. -/
  | predc : Pred → Const → Formula Var Const Pred
  /-- Non-emptiness atom: state is non-empty. -/
  | ne : Formula Var Const Pred
  /-- Bilateral negation: swap support/anti-support. -/
  | neg : Formula Var Const Pred → Formula Var Const Pred
  /-- Conjunction. -/
  | conj : Formula Var Const Pred → Formula Var Const Pred →
      Formula Var Const Pred
  /-- Split (tensor) disjunction. -/
  | disj : Formula Var Const Pred → Formula Var Const Pred →
      Formula Var Const Pred
  /-- Possibility modal. -/
  | poss : Formula Var Const Pred → Formula Var Const Pred
  /-- Existential quantifier. -/
  | exi : Var → Formula Var Const Pred → Formula Var Const Pred
  /-- Universal quantifier. -/
  | univ : Var → Formula Var Const Pred → Formula Var Const Pred
  deriving Repr

/-- Necessity, derived: `□φ := ¬◇¬φ`. [aloni-vanormondt-2023] takes `□`
    primitive and `◇ := ¬□¬` derived; we invert this, so `eval`'s `poss`
    clauses match the paper's derived `◇`-clauses and `nec` matches its
    primitive `□`. -/
def Formula.nec (φ : Formula Var Const Pred) : Formula Var Const Pred :=
  .neg (.poss (.neg φ))

/-- The NE-free fragment: formulas not containing the `NE` atom. On this
    fragment QBSML reduces to classical first-order modal logic
    ([aloni-vanormondt-2023] analogue of [anttila-2021]
    Proposition 2.2.16); see `Logic/Team/QBSML/Properties.lean`. -/
inductive Formula.NEFree : Formula Var Const Pred → Prop
  | pred (P : Pred) (x : Var) : NEFree (.pred P x)
  | predc (P : Pred) (c : Const) : NEFree (.predc P c)
  | neg {φ : Formula Var Const Pred} : NEFree φ → NEFree (.neg φ)
  | conj {φ ψ : Formula Var Const Pred} :
      NEFree φ → NEFree ψ → NEFree (.conj φ ψ)
  | disj {φ ψ : Formula Var Const Pred} :
      NEFree φ → NEFree ψ → NEFree (.disj φ ψ)
  | poss {φ : Formula Var Const Pred} : NEFree φ → NEFree (.poss φ)
  | exi (x : Var) {φ : Formula Var Const Pred} : NEFree φ → NEFree (.exi x φ)
  | univ (x : Var) {φ : Formula Var Const Pred} : NEFree φ → NEFree (.univ x φ)

/-- The derived `□φ := ¬◇¬φ` preserves NE-freeness. -/
theorem Formula.NEFree.nec {φ : Formula Var Const Pred}
    (h : φ.NEFree) : φ.nec.NEFree :=
  .neg (.poss (.neg h))

/-! ### Atom substitution -/

/-- Substitute a formula for each atom, commuting with every connective and
    quantifier (and fixing `NE`). The generic congruence machinery for
    atom-rewriting operations: an atom map whose images are bilaterally
    equivalent to the atoms is *salva veritate* (`eval_mapAtoms_iff` in
    `Logic/Team/QBSML/Properties.lean`), so each such operation — e.g.
    [yan-2023]'s reinterpretation function in `Studies/Yan2023.lean` — needs
    only its two atom lemmas. -/
def Formula.mapAtoms
    (fp : Pred → Var → Formula Var Const Pred)
    (fc : Pred → Const → Formula Var Const Pred) :
    Formula Var Const Pred → Formula Var Const Pred
  | .pred P x => fp P x
  | .predc P c => fc P c
  | .ne => .ne
  | .neg φ => .neg (φ.mapAtoms fp fc)
  | .conj φ ψ => .conj (φ.mapAtoms fp fc) (ψ.mapAtoms fp fc)
  | .disj φ ψ => .disj (φ.mapAtoms fp fc) (ψ.mapAtoms fp fc)
  | .poss φ => .poss (φ.mapAtoms fp fc)
  | .exi x φ => .exi x (φ.mapAtoms fp fc)
  | .univ x φ => .univ x (φ.mapAtoms fp fc)

/-- An atom substitution with NE-free images preserves NE-freeness. -/
theorem Formula.NEFree.mapAtoms
    {fp : Pred → Var → Formula Var Const Pred}
    {fc : Pred → Const → Formula Var Const Pred}
    (hfp : ∀ P x, (fp P x).NEFree) (hfc : ∀ P c, (fc P c).NEFree)
    {φ : Formula Var Const Pred} (h : φ.NEFree) :
    (φ.mapAtoms fp fc).NEFree := by
  induction h with
  | pred P x => exact hfp P x
  | predc P c => exact hfc P c
  | neg _ ih => exact .neg ih
  | conj _ _ ih₁ ih₂ => exact .conj ih₁ ih₂
  | disj _ _ ih₁ ih₂ => exact .disj ih₁ ih₂
  | poss _ ih => exact .poss ih
  | exi x _ ih => exact .exi x ih
  | univ x _ ih => exact .univ x ih

/-! ### Models -/

/-- A QBSML model ([aloni-vanormondt-2023] Definition 4.2:
    `M = ⟨W, D, R, I⟩`) **is** a constant-domain first-order Kripke
    structure over the monadic signature with constants: accessibility `R`
    plus the world-indexed interpretation `I`, carried as a family of
    mathlib structures (`FirstOrder.Language.ModalStructure`) — true by
    construction, not by bridge. -/
abbrev Model (W : Type*) (Domain : Type*) (Const : Type*)
    (Pred : Type*) :=
  FirstOrder.Language.ModalStructure
    (Language.monadicWithConstants Const Pred) W Domain

/-- The QBSML model with accessibility `access`, constant interpretation
    `κ`, and valuation `V`. -/
def Model.ofMonadic {W Domain Const Pred : Type*} (access : W → Finset W)
    (κ : W → Const → Domain) (V : W → Pred → Domain → Prop) :
    Model W Domain Const Pred :=
  ⟨access, fun w => Language.monadicWithConstantsStructure (κ w) (V w)⟩

@[simp] theorem predInterp_ofMonadic {W Domain Const Pred : Type*}
    (access : W → Finset W) (κ : W → Const → Domain)
    (V : W → Pred → Domain → Prop) (P : Pred) (w : W) (d : Domain) :
    (Model.ofMonadic access κ V).predInterp P w d ↔ V w P d :=
  Iff.rfl

@[simp] theorem constInterp_ofMonadic {W Domain Const Pred : Type*}
    (access : W → Finset W) (κ : W → Const → Domain)
    (V : W → Pred → Domain → Prop) (c : Const) (w : W) :
    (Model.ofMonadic access κ V).constInterp c w = κ w c :=
  rfl

/-! ### Bilateral evaluation -/

section Evaluation

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain]
variable [Fintype Domain]

/-- Bilateral evaluation of QBSML formulas ([aloni-vanormondt-2023]
    Definition 4.9): `eval M true φ s` is support (`M, s ⊨ φ`),
    `eval M false φ s` anti-support (`M, s ⫤ φ`). Negation flips the
    polarity, making double-negation elimination definitional. -/
def eval (M : Model W Domain Const Pred) :
    Bool → Formula Var Const Pred → Finset (Index W Var Domain) → Prop
  | true,  .pred P x, s =>
      ∀ i ∈ s, ∃ d, i.assign x = some d ∧ M.predInterp P i.world d
  | false, .pred P x, s =>
      ∀ i ∈ s, ∃ d, i.assign x = some d ∧ ¬ M.predInterp P i.world d
  | true,  .predc P c, s =>
      ∀ i ∈ s, M.predInterp P i.world (M.constInterp c i.world)
  | false, .predc P c, s =>
      ∀ i ∈ s, ¬ M.predInterp P i.world (M.constInterp c i.world)
  | true,  .ne, s => s.Nonempty
  | false, .ne, s => s = ∅
  | true,  .neg ψ, s => eval M false ψ s
  | false, .neg ψ, s => eval M true ψ s
  | true,  .conj φ ψ, s => eval M true φ s ∧ eval M true ψ s
  | false, .conj φ ψ, s => ∃ t₁ t₂ : Finset (Index W Var Domain),
      Team.splitsAs s t₁ t₂ ∧ eval M false φ t₁ ∧ eval M false ψ t₂
  | true,  .disj φ ψ, s => ∃ t₁ t₂ : Finset (Index W Var Domain),
      Team.splitsAs s t₁ t₂ ∧ eval M true φ t₁ ∧ eval M true ψ t₂
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
abbrev support (M : Model W Domain Const Pred) (φ : Formula Var Const Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  eval M true φ s

/-- Anti-support: negative evaluation. -/
abbrev antiSupport (M : Model W Domain Const Pred) (φ : Formula Var Const Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  eval M false φ s

@[simp] lemma support_neg (M : Model W Domain Const Pred)
    (φ : Formula Var Const Pred) (s : Finset (Index W Var Domain)) :
    support M (.neg φ) s ↔ antiSupport M φ s := Iff.rfl

@[simp] lemma antiSupport_neg (M : Model W Domain Const Pred)
    (φ : Formula Var Const Pred) (s : Finset (Index W Var Domain)) :
    antiSupport M (.neg φ) s ↔ support M φ s := Iff.rfl

/-- `support` and `antiSupport` form a paraconsistent bilateral logic
    (`Bilateral.IsBilateral`) under `Formula.neg`, like
    BSML's `isBilateral` at the point type `Index W Var Domain`. -/
theorem isBilateral (M : Model W Domain Const Pred) :
    Bilateral.IsBilateral (Form := Formula Var Const Pred)
      (support M) (antiSupport M) Formula.neg :=
  Bilateral.IsBilateral.of_iff (support_neg M) (antiSupport_neg M)

end Evaluation

/-! ### Frame conditions via the world projection -/

section FrameConditions

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain]

/-- `R` is state-based on `(M, s)`: every world in `s↓` sees exactly `s↓`
    ([aloni-vanormondt-2023] Definition 4.10). Defined via
    `Team.IsStateBased` applied to `State.worldProj s`, sharing
    BSML's frame-condition substrate. -/
def _root_.FirstOrder.Language.ModalStructure.IsStateBased
    (M : Model W Domain Const Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  Team.IsStateBased M.access (State.worldProj s)

/-- `R` is indisputable on `(M, s)`: all worlds in `s↓` see the same
    accessible set ([aloni-vanormondt-2023] Definition 4.10). -/
def _root_.FirstOrder.Language.ModalStructure.IsIndisputable
    (M : Model W Domain Const Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  Team.IsIndisputable M.access (State.worldProj s)

instance [Fintype W] (M : Model W Domain Const Pred)
    (s : Finset (Index W Var Domain)) : Decidable (M.IsStateBased s) := by
  unfold FirstOrder.Language.ModalStructure.IsStateBased; infer_instance

instance [Fintype W] (M : Model W Domain Const Pred)
    (s : Finset (Index W Var Domain)) : Decidable (M.IsIndisputable s) := by
  unfold FirstOrder.Language.ModalStructure.IsIndisputable; infer_instance

end FrameConditions

end QBSML
