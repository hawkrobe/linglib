module

public import Linglib.Logic.Team.Kripke
public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Team.Bisimulation
public import Linglib.Logic.Team.Operations
public import Linglib.Logic.Team.Atoms
public import Linglib.Logic.Team.Closure
public import Linglib.Logic.Team.Definability

/-!
# Modal Dependence Logic (MDL)

[vaananen-2008] [vaananen-2007]

MDL is the modal extension of dependence logic introduced in
[vaananen-2008] ("Modal Dependence Logic", in Apt & van Rooij eds.
*New Perspectives on Games and Interaction*, pp. 237-254). It adds a
*dependence atom* `=(p₁,...,pₙ; q)` to classical modal logic, meaning
"the value of `q` is functionally determined by the values of
`p₁,...,pₙ` across the team."

The framework is grounded in Väänänen's foundational
[vaananen-2007] (the *Dependence Logic* book, Cambridge University
Press 2007), which develops the first-order team-semantic apparatus
that MDL adapts to modal logic. Where the book's quantifiers range
over assignments, MDL's modalities range over Kripke worlds — but the
team-semantic skeleton (formulas as predicates of teams, downward
closure, dependence atoms) transfers directly.

MDL is studied for its computational and model-theoretic properties
(satisfiability complexity in [lohmann-vollmer-2013] and Sevenster's
earlier expressive-power work; bisimulation invariance), with
applications in database theory, knowledge representation, and AI
rather than primarily in linguistic semantics — hence the placement in
`Logic/` rather than `Semantics/`, alongside the other
team-semantic primitives (`Logic/Team/`).

## What changes from BSML

MDL and BSML share a bilateral semantics (Player II = support, Player
I = anti-support, negation flips polarity per [vaananen-2008]
clause (T5)) and the same Kripke-model carrier. The structural
differences:

* **Atom**: BSML's `NE` becomes MDL's `dep`. `=(x⃗; y)` is supported by
  a team iff any two worlds agreeing on `x⃗` also agree on `y`.
* **Modal operator clauses**: MDL's ◇-support uses a **single witness**
  `Y` ([vaananen-2008] clause (T8)) — `∃ Y, (∀ w ∈ s, ∃ y ∈ Y,
  y ∈ R[w]) ∧ support φ Y` — rather than BSML's per-world witnesses.
  Similarly, ◇-anti-support uses the union of accessibility images
  (T9) rather than per-world checks. The two formulations are
  equivalent under union-closure but diverge for MDL since dep atoms
  break it.

## Closure profile

MDL's closure profile differs from BSML's, placing it in a different
cell of the closure-property lattice:

| Property            | BSML (NE-free) | BSML (with NE) | MDL              |
|---------------------|----------------|----------------|------------------|
| `IsLowerSet`        | ✓              | broken by NE   | ✓ (Lemma 4.2)    |
| `SupClosed`         | ✓              | ✓              | broken by `dep`  |
| `∅ ∈ support`       | ✓              | ✓              | ✓                |

The dep atom is downward-closed (subteam of a functionally-dependent
team is functionally dependent) but breaks union-closure (two
functionally-dependent teams may have conflicting `y` values at
worlds with matching `x⃗`).

## Main declarations

* `Formula` — MDL syntax (Definition 1.1).
* `eval` — bilateral semantics (Definition 4.1), parametric in polarity.
* `support` / `antiSupport` — convenience abbreviations.
* `Formula.modalDepth` — depth of nested ◇.
* `isLowerSet_support` — Lemma 4.2's downward-closure property.
* `support_empty` — every formula is supported on the empty team.
* `Formula.DepFree`, `Realize`, `support_iff_forall_realize` — without
  dependence atoms MDL is classical modal logic: support is pointwise
  Kripke truth.
* `not_supClosed_dep_of_witness` — the witness that `dep` breaks
  union-closure: in any model with two worlds sharing a `p`-value but
  differing on `q`, the singleton teams support `=(p; q)` but their
  union does not.

## Implementation notes

The MDL eval is a fold over the operations of `Team/Operations.lean`:
`Team.flat` for atoms, `Team.dep` of `Team/Atoms.lean` for the dependence atom read
through the valuation, `Team.tensor` for the split clauses, and Väänänen's
single-witness and image modalities `Team.possWitness` and `Team.necImage`,
whose closure lemmas give Lemma 4.2 and the empty-team property case by
case. The MDL eval uses Väänänen's exact clauses, not BSML's. The disjunction
clause is the under-DC simplified form `X = Y ∪ Z` (paper's (T6)'
under Lemma 4.2 part 1) rather than the literal `X ⊆ Y ∪ Z` from
(T6); under downward closure they are equivalent.

The `KripkeModel` carrier from `Logic/Team/Kripke.lean` is the
shared substrate consumed by BSML, QBSML, and the AAY-2024
extensions (BSMLOr/BSMLEmpty) alike.

## Todo

* [lohmann-vollmer-2013] — adds classical disjunction `⓿` (the
  BSML∨ analogue) and complete satisfiability complexity classification.
  Natural second consumer paper, with a Studies file anchored on it.
* Modal independence logic, with Grädel and Väänänen's independence atom beside
  `Team.dep` in `Team/Atoms.lean`.
-/

@[expose] public section

namespace ModalLogic.Dependence

variable {W : Type*} {Atom : Type*}

open ModalLogic (KripkeModel)

/-! ### Syntax (Definition 1.1) -/

/-- MDL syntax (Definition 1.1 of [vaananen-2008]): classical modal
    logic extended with the dependence atom `=(p₁,...,pₙ; q)`.

    `□` and binary `∧` are abbreviations (the paper's `□A := ¬◇¬A` and
    `A ∧ B := ¬(¬A ∨ ¬B)`). We include `conj` as a primitive constructor
    here for ergonomic parallelism with BSML, with the semantic clauses
    matching what the abbreviations would yield. -/
inductive Formula (Atom : Type*) where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Dependence atom `=(x⃗; y)`: values of `y` in the team are
      functionally determined by values of `x⃗`. -/
  | dep (xs : List Atom) (y : Atom)
  /-- Bilateral negation: swap support/anti-support. -/
  | neg (φ : Formula Atom)
  /-- Conjunction. -/
  | conj (φ ψ : Formula Atom)
  /-- Tensor disjunction (team-split form under downward closure). -/
  | disj (φ ψ : Formula Atom)
  /-- Possibility modal `◇`. -/
  | poss (φ : Formula Atom)
  deriving Repr

/-! ### Classical truth

Without dependence atoms MDL is classical modal logic ([anttila-2021]'s Proposition 2.2.16
for Väänänen's modalities, `support_iff_forall_realize` below). -/

/-- `Formula.DepFree φ` holds when `φ` contains no dependence atom. -/
def Formula.DepFree : Formula Atom → Prop
  | .atom _ => True
  | .dep _ _ => False
  | .neg φ | .poss φ => φ.DepFree
  | .conj φ ψ | .disj φ ψ => φ.DepFree ∧ ψ.DepFree

open scoped ModalLogic in
/-- Classical Kripke truth of an MDL formula at a world, with `◇` the shared
    `ModalLogic.Diamond`; a dependence atom is true at every world. -/
def Realize (M : KripkeModel W Atom) : Formula Atom → W → Prop
  | .atom p, w => M.val p w = true
  | .dep _ _, _ => True
  | .neg ψ, w => ¬ Realize M ψ w
  | .conj ψ₁ ψ₂, w => Realize M ψ₁ w ∧ Realize M ψ₂ w
  | .disj ψ₁ ψ₂, w => Realize M ψ₁ w ∨ Realize M ψ₂ w
  | .poss ψ, w => ◇[M.accessible] (Realize M ψ) w

theorem realize_poss {M : KripkeModel W Atom} {ψ : Formula Atom} {w : W} :
    Realize M (.poss ψ) w ↔ ∃ v ∈ M.access w, Realize M ψ v := Iff.rfl

variable [DecidableEq W]

/-! ### Semantics (Definition 4.1) -/

/-- Bilateral evaluation for MDL (Definition 4.1 of [vaananen-2008]).
    `eval M true φ t` is support (Player II); `eval M false φ t` is
    anti-support (Player I). Negation flips polarity (clause (T5)).

    The ◇ clauses (T8), (T9) use Väänänen's single-witness form, not
    BSML's per-world form; the two formulations diverge for non-union-
    closed logics like MDL. -/
def eval (M : KripkeModel W Atom) : Bool → Formula Atom → Finset W → Prop
  | true,  .atom p,        t => t ∈ Team.flat fun w ↦ M.val p w = true
  | false, .atom p,        t => t ∈ Team.flat fun w ↦ M.val p w = false
  | true,  .dep xs y,      t => t ∈ Team.dep (fun w ↦ xs.map (M.val · w)) (M.val y)
  | false, .dep _ _,       t => t ∈ ({∅} : Team.TeamProperty W)
  | true,  .neg ψ,         t => eval M false ψ t
  | false, .neg ψ,         t => eval M true ψ t
  | true,  .conj ψ₁ ψ₂,    t => eval M true ψ₁ t ∧ eval M true ψ₂ t
  | false, .conj ψ₁ ψ₂,    t => t ∈ Team.tensor {s | eval M false ψ₁ s} {s | eval M false ψ₂ s}
  | true,  .disj ψ₁ ψ₂,    t => t ∈ Team.tensor {s | eval M true ψ₁ s} {s | eval M true ψ₂ s}
  | false, .disj ψ₁ ψ₂,    t => eval M false ψ₁ t ∧ eval M false ψ₂ t
  | true,  .poss ψ,        t => t ∈ Team.possWitness M.access {s | eval M true ψ s}
  | false, .poss ψ,        t => t ∈ Team.necImage M.access {s | eval M false ψ s}

/-- Support: positive evaluation. -/
abbrev support (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M true φ t

/-- Anti-support: negative evaluation. -/
abbrev antiSupport (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M false φ t

@[simp] lemma support_atom (M : KripkeModel W Atom) (p : Atom) (t : Finset W) :
    support M (.atom p) t ↔ ∀ w ∈ t, M.val p w = true := Iff.rfl

@[simp] lemma antiSupport_atom (M : KripkeModel W Atom) (p : Atom) (t : Finset W) :
    antiSupport M (.atom p) t ↔ ∀ w ∈ t, M.val p w = false := Iff.rfl

@[simp] lemma support_dep (M : KripkeModel W Atom) (xs : List Atom) (y : Atom)
    (t : Finset W) :
    support M (.dep xs y) t ↔
      ∀ w₁ ∈ t, ∀ w₂ ∈ t,
        (∀ x ∈ xs, M.val x w₁ = M.val x w₂) → M.val y w₁ = M.val y w₂ := by
  simp only [support, eval, Team.mem_dep, List.map_inj_left]

@[simp] lemma antiSupport_dep (M : KripkeModel W Atom) (xs : List Atom) (y : Atom)
    (t : Finset W) :
    antiSupport M (.dep xs y) t ↔ t = ∅ := Iff.rfl

@[simp] lemma support_neg (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.neg φ) t ↔ antiSupport M φ t := Iff.rfl

@[simp] lemma antiSupport_neg (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    antiSupport M (.neg φ) t ↔ support M φ t := Iff.rfl

@[simp] lemma support_conj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.conj φ ψ) t ↔ support M φ t ∧ support M ψ t := Iff.rfl

@[simp] lemma antiSupport_conj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    antiSupport M (.conj φ ψ) t ↔
      ∃ t₁, antiSupport M φ t₁ ∧ ∃ t₂, antiSupport M ψ t₂ ∧ t₁ ∪ t₂ = t := Iff.rfl

@[simp] lemma support_disj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.disj φ ψ) t ↔
      ∃ t₁, support M φ t₁ ∧ ∃ t₂, support M ψ t₂ ∧ t₁ ∪ t₂ = t := Iff.rfl

@[simp] lemma antiSupport_disj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    antiSupport M (.disj φ ψ) t ↔ antiSupport M φ t ∧ antiSupport M ψ t := Iff.rfl

@[simp] lemma support_poss (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.poss φ) t ↔
      ∃ Y : Finset W, (∀ w ∈ t, ∃ y ∈ Y, y ∈ M.access w) ∧ support M φ Y :=
  Iff.rfl

@[simp] lemma antiSupport_poss (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    antiSupport M (.poss φ) t ↔ antiSupport M φ (t.biUnion M.access) := Iff.rfl

/-! ### Modal depth -/

/-- Modal depth of an MDL formula. Atoms and dep atoms are 0; `neg`
    preserves depth; `conj` and `disj` take max; `poss` increments. -/
def Formula.modalDepth : Formula Atom → ℕ
  | .atom _ => 0
  | .dep _ _ => 0
  | .neg ψ => ψ.modalDepth
  | .conj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .disj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .poss ψ => ψ.modalDepth + 1

/-! ### Lemma 4.2: Downward closure -/

/-- Joint downward closure for both polarities: each case is the closure lemma of its
    connective in `Team/Operations.lean`; the dependence atom is inherited by subteams. -/
private theorem support_and_antiSupport_isLowerSet (φ : Formula Atom)
    (M : KripkeModel W Atom) :
    IsLowerSet {t | support M φ t} ∧ IsLowerSet {t | antiSupport M φ t} := by
  induction φ with
  | atom p => exact ⟨Team.isLowerSet_flat _, Team.isLowerSet_flat _⟩
  | dep xs y => exact ⟨Team.isLowerSet_dep _ _, Team.isLowerSet_singleton_empty⟩
  | neg ψ ih => exact ih.symm
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁.1.inter ih₂.1, ih₁.2.tensor ih₂.2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁.1.tensor ih₂.1, ih₁.2.inter ih₂.2⟩
  | poss ψ ih => exact ⟨Team.isLowerSet_possWitness _ _, ih.2.necImage⟩

/-- **Lemma 4.2 of [vaananen-2008]**: every MDL formula's support
    is downward-closed. The defining closure property of the dependence
    family — what BSML loses when it adds NE. -/
theorem isLowerSet_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    IsLowerSet { t : Finset W | support M φ t } :=
  (support_and_antiSupport_isLowerSet φ M).1

/-! ### Empty team property -/

/-- Joint empty-team property: every MDL formula has both empty support and empty
    anti-support; no `NE` constructor breaks it. -/
private theorem support_and_antiSupport_empty
    (φ : Formula Atom) (M : KripkeModel W Atom) :
    support M φ ∅ ∧ antiSupport M φ ∅ := by
  induction φ with
  | atom p => exact ⟨Team.empty_mem_flat _, Team.empty_mem_flat _⟩
  | dep xs y => exact ⟨Team.empty_mem_dep, rfl⟩
  | neg ψ ih => exact ih.symm
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨⟨ih₁.1, ih₂.1⟩, Team.empty_mem_tensor ih₁.2 ih₂.2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨Team.empty_mem_tensor ih₁.1 ih₂.1, ⟨ih₁.2, ih₂.2⟩⟩
  | poss ψ ih => exact ⟨Team.empty_mem_possWitness ih.1, Team.empty_mem_necImage ih.2⟩

/-- Every MDL formula is supported on the empty team. -/
theorem support_empty (M : KripkeModel W Atom) (φ : Formula Atom) :
    support M φ ∅ :=
  (support_and_antiSupport_empty φ M).1

/-! ### Dep breaks union closure (the defining feature) -/

/-- **The dep atom is not union-closed**: a constructive counterexample.
    Take a model with at least two worlds `w₁, w₂` where `M.val p w₁ =
    M.val p w₂` but `M.val q w₁ ≠ M.val q w₂`. Then `{w₁}` and `{w₂}`
    each support `=(p; q)` vacuously (each is a singleton, so the
    functional-dependence condition is trivial), but `{w₁, w₂}` does not. -/
theorem not_supClosed_dep_of_witness {p q : Atom} {w₁ w₂ : W}
    {M : KripkeModel W Atom} (hp : M.val p w₁ = M.val p w₂) (hq : M.val q w₁ ≠ M.val q w₂) :
    ¬ SupClosed { t : Finset W | support M (.dep [p] q) t } := by
  simpa only [support, eval, Set.ofPred_mem_eq] using
    Team.not_supClosed_dep (f := fun w ↦ [p].map (M.val · w)) (by simp [hp]) hq

/-! ### Soundness for the closure cell (Definability bridge) -/

open Team in
/-- **MDL is sound for its closure cell**: every MDL-definable team property is
    downward-closed and has the empty-team property. The dependence family
    occupies the downward-closed, empty-team cell ([vaananen-2008];
    [anttila-2025]) — `dep` breaks union closure (see
    `not_supClosed_dep_of_witness`) but preserves downward closure.

    Composes `isLowerSet_support` (Lemma 4.2) and `support_empty` through the
    `Team/Definability.lean` bridge. The converse (every such property is
    MDL-definable) is the open half. -/
theorem definableClass_support_subset (M : KripkeModel W Atom) :
    definableClass (support M) ⊆ {P | IsLowerSet P ∧ ∅ ∈ P} :=
  definableClass_subset fun φ ↦ ⟨isLowerSet_support M φ, support_empty M φ⟩

/-! ### Bisimulation invariance (Väänänen-style ◇)

MDL's modality differs from BSML's: anti-`◇` uses the union of accessibility
images (clause (T9)), and `◇`-support a single witness team (clause (T8)),
rather than BSML's per-world sub-witnesses. The invariance proof therefore
recurses through `StateBisim.biUnionAccess` and `StateBisim.possWitness`
(carrier-level transport lemmas in `Logic/Team/Bisimulation.lean`)
at the modal step, where BSML uses `WorldBisim.accessStateBisim` /
`StateBisim.exists_image_subset`. The dependence-atom case is depth-0 and turns on
`WorldBisim.val_eq`: state bisim preserves the set of atom-valuation profiles
realised in a team, and functional dependence is a property of that set. -/

section Bisimulation

open ModalLogic

variable {W' : Type*} [DecidableEq W']

/-- **Bisimulation invariance for MDL** (the [aloni-anttila-yang-2024]
    Theorem 3.8 analogue for [vaananen-2008]'s modal dependence logic):
    if `s ⇌_k s'` and `φ` has modal depth `≤ k`, then `eval M b φ s ↔
    eval M' b φ s'` for both polarities.

    Second consumer of the carrier-level bisimulation substrate (after BSML),
    which is what licensed lifting it out of `BSML/`. -/
theorem bisim_invariant_eval {M : KripkeModel W Atom} {M' : KripkeModel W' Atom}
    (φ : Formula Atom) {k : ℕ} (hd : φ.modalDepth ≤ k)
    {s : Finset W} {s' : Finset W'} (hbisim : StateBisim k M s M' s')
    (b : Bool) : eval M b φ s ↔ eval M' b φ s' := by
  induction φ generalizing k s s' b with
  | atom p =>
    cases b <;>
    · constructor
      · intro h w' hw'
        obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
        rw [← hbw.val_eq]; exact h w hw
      · intro h w hw
        obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
        rw [hbw.val_eq]; exact h w' hw'
  | dep xs y =>
    cases b
    · -- antiSupport (dep xs y) s = (s = ∅)
      exact hbisim.eq_empty_iff
    · -- support (dep xs y): functional dependence, a property of the
      -- valuation profiles, which bisim preserves (`val_eq`).
      change support M _ s ↔ support M' _ s'
      rw [support_dep, support_dep]
      constructor
      · intro h w₁' hw₁' w₂' hw₂' hagree'
        obtain ⟨w₁, hw₁, hb₁⟩ := hbisim.2 w₁' hw₁'
        obtain ⟨w₂, hw₂, hb₂⟩ := hbisim.2 w₂' hw₂'
        have hagree : ∀ x ∈ xs, M.val x w₁ = M.val x w₂ := by
          intro x hx; rw [hb₁.val_eq x, hagree' x hx, ← hb₂.val_eq x]
        rw [← hb₁.val_eq y, ← hb₂.val_eq y]; exact h w₁ hw₁ w₂ hw₂ hagree
      · intro h w₁ hw₁ w₂ hw₂ hagree
        obtain ⟨w₁', hw₁', hb₁⟩ := hbisim.1 w₁ hw₁
        obtain ⟨w₂', hw₂', hb₂⟩ := hbisim.1 w₂ hw₂
        have hagree' : ∀ x ∈ xs, M'.val x w₁' = M'.val x w₂' := by
          intro x hx; rw [← hb₁.val_eq x, hagree x hx, hb₂.val_eq x]
        rw [hb₁.val_eq y, hb₂.val_eq y]; exact h w₁' hw₁' w₂' hw₂' hagree'
  | neg ψ ih =>
    cases b
    · exact ih hd hbisim true
    · exact ih hd hbisim false
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have hd₁ : ψ₁.modalDepth ≤ k := (le_max_left _ _).trans hd
    have hd₂ : ψ₂.modalDepth ≤ k := (le_max_right _ _).trans hd
    cases b
    · -- antiSupport (conj): split into (t, u)
      constructor
      · rintro ⟨t, h₁, u, h₂, hsplit⟩
        obtain ⟨t', u', hsplit', hbt, hbu⟩ := hbisim.splitPreserve hsplit
        exact ⟨t', (ih₁ hd₁ hbt false).mp h₁, u', (ih₂ hd₂ hbu false).mp h₂, hsplit'⟩
      · rintro ⟨t', h₁, u', h₂, hsplit'⟩
        obtain ⟨t, u, hsplit, hbt, hbu⟩ := StateBisim.splitPreserve hbisim.symm hsplit'
        exact ⟨t, (ih₁ hd₁ hbt.symm false).mpr h₁, u, (ih₂ hd₂ hbu.symm false).mpr h₂, hsplit⟩
    · -- support (conj) = support ψ₁ ∧ support ψ₂
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim true).mp h₁, (ih₂ hd₂ hbisim true).mp h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim true).mpr h₁, (ih₂ hd₂ hbisim true).mpr h₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have hd₁ : ψ₁.modalDepth ≤ k := (le_max_left _ _).trans hd
    have hd₂ : ψ₂.modalDepth ≤ k := (le_max_right _ _).trans hd
    cases b
    · -- antiSupport (disj) = antiSupport ψ₁ ∧ antiSupport ψ₂
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim false).mp h₁, (ih₂ hd₂ hbisim false).mp h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim false).mpr h₁, (ih₂ hd₂ hbisim false).mpr h₂⟩
    · -- support (disj): split into (t, u)
      constructor
      · rintro ⟨t, h₁, u, h₂, hsplit⟩
        obtain ⟨t', u', hsplit', hbt, hbu⟩ := hbisim.splitPreserve hsplit
        exact ⟨t', (ih₁ hd₁ hbt true).mp h₁, u', (ih₂ hd₂ hbu true).mp h₂, hsplit'⟩
      · rintro ⟨t', h₁, u', h₂, hsplit'⟩
        obtain ⟨t, u, hsplit, hbt, hbu⟩ := StateBisim.splitPreserve hbisim.symm hsplit'
        exact ⟨t, (ih₁ hd₁ hbt.symm true).mpr h₁, u, (ih₂ hd₂ hbu.symm true).mpr h₂, hsplit⟩
  | poss ψ ih =>
    cases k with
    | zero => exact absurd hd (Nat.not_succ_le_zero _)
    | succ k =>
      have hdψ : ψ.modalDepth ≤ k := Nat.le_of_succ_le_succ hd
      cases b
      · -- antiSupport (poss ψ) s = antiSupport ψ (s.biUnion R), evaluated on the
        -- union of images; `biUnionAccess` transports it.
        show eval M false ψ (s.biUnion M.access) ↔ eval M' false ψ (s'.biUnion M'.access)
        exact ih hdψ hbisim.biUnionAccess false
      · -- support (poss ψ): single witness team Y. Shrink to its reachable part,
        -- transport via `possWitness`, recurse.
        constructor
        · rintro ⟨Y, hwit, hYsupp⟩
          show ∃ Y' : Finset W',
            (∀ w' ∈ s', ∃ y' ∈ Y', y' ∈ M'.access w') ∧ eval M' true ψ Y'
          obtain ⟨Y', _hY'sub, hY'wit, hYbisim⟩ :=
            hbisim.possWitness (Y := Y ∩ s.biUnion M.access)
              Finset.inter_subset_right
              (fun w hw => by
                obtain ⟨y, hyY, hyw⟩ := hwit w hw
                exact ⟨y, Finset.mem_inter.mpr
                  ⟨hyY, Finset.mem_biUnion.mpr ⟨w, hw, hyw⟩⟩, hyw⟩)
          exact ⟨Y', hY'wit,
            (ih hdψ hYbisim true).mp
              (isLowerSet_support M ψ Finset.inter_subset_left hYsupp)⟩
        · rintro ⟨Y', hwit', hY'supp⟩
          show ∃ Y : Finset W,
            (∀ w ∈ s, ∃ y ∈ Y, y ∈ M.access w) ∧ eval M true ψ Y
          obtain ⟨Y, _hYsub, hYwit, hYbisim⟩ :=
            hbisim.symm.possWitness (Y := Y' ∩ s'.biUnion M'.access)
              Finset.inter_subset_right
              (fun w' hw' => by
                obtain ⟨y', hy'Y, hy'w⟩ := hwit' w' hw'
                exact ⟨y', Finset.mem_inter.mpr
                  ⟨hy'Y, Finset.mem_biUnion.mpr ⟨w', hw', hy'w⟩⟩, hy'w⟩)
          exact ⟨Y, hYwit,
            (ih hdψ hYbisim.symm true).mpr
              (isLowerSet_support M' ψ Finset.inter_subset_left hY'supp)⟩

end Bisimulation

/-! ### The classical fragment

On `dep`-free formulas support is pointwise classical truth and anti-support pointwise
classical falsity: Väänänen's single-witness and image modalities agree with the flat ones
on flat properties (`Team.possWitness_flat`, `Team.necImage_flat`). -/

section Classical

variable {M : KripkeModel W Atom} {φ : Formula Atom} {w : W} {t : Finset W}

/-- On `dep`-free formulas, support is pointwise classical truth and anti-support pointwise
    classical falsity. -/
theorem eval_iff_forall_realize (hD : φ.DepFree) (b : Bool) (t : Finset W) :
    eval M b φ t ↔ ∀ w ∈ t, (Realize M φ w ↔ b) := by
  induction φ generalizing b t with
  | atom p => cases b <;> simp [eval, Realize]
  | dep xs y => exact hD.elim
  | neg ψ ih =>
    cases b
    · simpa [eval, Realize] using ih hD true t
    · simpa [eval, Realize] using ih hD false t
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp only [eval, ih₁ hD.1, ih₂ hD.2]
      refine Team.mem_tensor_flat.trans ?_
      simp [Realize, imp_iff_not_or]
    · simp [eval, ih₁ hD.1, ih₂ hD.2, Realize, forall_and]
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp [eval, ih₁ hD.1, ih₂ hD.2, Realize, forall_and, not_or]
    · simp only [eval, ih₁ hD.1, ih₂ hD.2]
      refine Team.mem_tensor_flat.trans ?_
      simp [Realize]
  | poss ψ ih =>
    cases b
    · simp only [eval, ih hD false]
      refine Team.mem_necImage_flat.trans ?_
      simp [realize_poss]
    · simp only [eval, ih hD true]
      refine Team.mem_possWitness_flat.trans ?_
      simp [realize_poss]

theorem support_iff_forall_realize (hD : φ.DepFree) :
    support M φ t ↔ ∀ w ∈ t, Realize M φ w := by
  simpa using eval_iff_forall_realize hD true t

theorem antiSupport_iff_forall_not_realize (hD : φ.DepFree) :
    antiSupport M φ t ↔ ∀ w ∈ t, ¬ Realize M φ w := by
  simpa using eval_iff_forall_realize hD false t

theorem support_singleton_iff_realize (hD : φ.DepFree) : support M φ {w} ↔ Realize M φ w := by
  simp [support_iff_forall_realize hD]

end Classical

end ModalLogic.Dependence
