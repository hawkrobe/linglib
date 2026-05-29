import Linglib.Core.Logic.Modal.BSML.Bridge
import Linglib.Core.Logic.Modal.BSML.Bisimulation

/-!
# Characteristic (Hintikka) formulas for BSML — foundation

@cite{aloni-anttila-yang-2024} @cite{anttila-2025}

The expressive-completeness converse for BSML (`expressiveCompleteness_converse`
in `BSML/ExpressiveCompleteness.lean`) needs **characteristic formulas**: for
each world `w` and depth `k`, an NE-free formula `χ_w^k` such that a singleton
`{v}` supports it exactly when `v` is `k`-bisimilar to `w`. This file builds the
foundation — finite conjunction over an NE-free language and the **depth-0
(atomic type)** characterisation — and proves it against the classical
single-world evaluation `classicalEval` (`BSML/Bridge.lean`).

Working through `classicalEval` is the simplification that makes this tractable:
characteristic formulas are NE-free, so by `Bridge.neFree_flat_eq` their team
support reduces to pointwise `classicalEval`, and the construction becomes the
standard *classical* modal Hintikka characterisation.

## Main declarations

* `verum`, `bigConj` — `⊤` (as `p ∨ ¬p`) and finite conjunction, both NE-free.
* `atomicType M w` — the depth-0 Hintikka formula: the conjunction of atomic
  literals true at `w`.
* `classicalEval_atomicType_iff_bisim0` — `{v}` (classically) satisfies `w`'s
  atomic type iff `v` and `w` are 0-bisimilar (`WorldBisim 0`).

## Todo

* Depth-`k+1` Hintikka formula (atomic type ∧ `◇` each successor type ∧ `□`
  disjunction of successor types) and the characterisation
  `classicalEval (charFormula k w) v = true ↔ WorldBisim k M w M v` by induction
  on `k`. Then lift to team support via `Bridge.neFree_flat_eq` (currently
  `private`; expose it) for the Hennessy-Milner theorem, feeding the normal form
  that discharges `expressiveCompleteness_converse`.
-/

namespace Core.Logic.Modal.BSML

open Core.Logic.Modal

variable {W : Type*} [DecidableEq W] [Fintype W] {Atom : Type*}

/-! ### `⊤` and finite conjunction -/

/-- `⊤` as an NE-free BSML formula: `p ∨ ¬p` for the default atom. Classically
    evaluates to `true` at every world; supported by every team. Requires an
    atom (`[Inhabited Atom]`): BSML has no atom-free closed `⊤`. -/
def verum [Inhabited Atom] : BSMLFormula Atom :=
  .disj (.atom default) (.neg (.atom default))

@[simp] theorem classicalEval_verum [Inhabited Atom] (M : BSMLModel W Atom) (w : W) :
    classicalEval M verum w = true := by
  simp [verum, classicalEval, Bool.or_not_self]

@[simp] theorem isNEFree_verum [Inhabited Atom] :
    (verum : BSMLFormula Atom).isNEFree = true := by
  simp [verum, BSMLFormula.isNEFree]

/-- Finite conjunction of a list of formulas; the empty conjunction is `⊤`. -/
def bigConj [Inhabited Atom] : List (BSMLFormula Atom) → BSMLFormula Atom
  | [] => verum
  | φ :: rest => .conj φ (bigConj rest)

theorem classicalEval_bigConj [Inhabited Atom] (M : BSMLModel W Atom) (w : W)
    (l : List (BSMLFormula Atom)) :
    classicalEval M (bigConj l) w = true ↔ ∀ φ ∈ l, classicalEval M φ w = true := by
  induction l with
  | nil => simp [bigConj]
  | cons φ rest ih =>
    simp only [bigConj, classicalEval, Bool.and_eq_true, List.forall_mem_cons, ih]

theorem isNEFree_bigConj [Inhabited Atom] (l : List (BSMLFormula Atom))
    (h : ∀ φ ∈ l, φ.isNEFree = true) : (bigConj l).isNEFree = true := by
  induction l with
  | nil => simp [bigConj]
  | cons φ rest ih =>
    simp only [bigConj, BSMLFormula.isNEFree, Bool.and_eq_true]
    exact ⟨h φ (List.mem_cons.mpr (Or.inl rfl)),
           ih (fun ψ hψ => h ψ (List.mem_cons.mpr (Or.inr hψ)))⟩

/-! ### Atomic type (depth-0 Hintikka formula) -/

/-- The **atomic type** of `w`: the conjunction over all atoms `p` of the literal
    `p` (when `w ⊨ p`) or `¬p` (when `w ⊭ p`). The depth-0 characteristic
    formula. -/
noncomputable def atomicType [Fintype Atom] [Inhabited Atom]
    (M : BSMLModel W Atom) (w : W) : BSMLFormula Atom :=
  bigConj ((Finset.univ : Finset Atom).toList.map
    (fun p => if M.val p w then .atom p else .neg (.atom p)))

theorem isNEFree_atomicType [Fintype Atom] [Inhabited Atom]
    (M : BSMLModel W Atom) (w : W) : (atomicType M w).isNEFree = true := by
  apply isNEFree_bigConj
  intro φ hφ
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
  cases M.val p w <;> simp [BSMLFormula.isNEFree]

/-- The atomic type of `w` is classically satisfied at `v` exactly when `v` and
    `w` assign every atom the same value. -/
theorem classicalEval_atomicType [Fintype Atom] [Inhabited Atom]
    (M : BSMLModel W Atom) (w v : W) :
    classicalEval M (atomicType M w) v = true ↔ ∀ p : Atom, M.val p v = M.val p w := by
  rw [atomicType, classicalEval_bigConj]
  constructor
  · intro h p
    have hp := h _ (List.mem_map.mpr
      ⟨p, Finset.mem_toList.mpr (Finset.mem_univ p), rfl⟩)
    cases hb : M.val p w with
    | false => simp [hb, classicalEval] at hp; simp [hp]
    | true => simp [hb, classicalEval] at hp; simp [hp]
  · intro h φ hφ
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
    cases hb : M.val p w with
    | false => simp [hb, classicalEval, h p]
    | true => simp [hb, classicalEval, h p]

/-- **Depth-0 characterisation**: `w`'s atomic type is classically satisfied at
    `v` iff `v` and `w` are 0-bisimilar. The base case of the characteristic-
    formula characterisation. -/
theorem classicalEval_atomicType_iff_bisim0 [Fintype Atom] [Inhabited Atom]
    (M : BSMLModel W Atom) (w v : W) :
    classicalEval M (atomicType M w) v = true ↔ WorldBisim 0 M w M v := by
  rw [classicalEval_atomicType]
  constructor
  · intro h p; exact (h p).symm
  · intro h p; exact (h p).symm

end Core.Logic.Modal.BSML
