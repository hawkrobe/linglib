import Mathlib.ModelTheory.Satisfiability
import Linglib.Core.Logic.Modal.QBSML.Properties

/-!
# The standard translation for monadic quantified modal logic

[blackburn-derijke-venema-2001] [aloni-vanormondt-2023]

The standard translation of modal logic into first-order logic
([blackburn-derijke-venema-2001]), for the monadic signature: modal formulas
over `monadicLang Const Pred` translate into plain mathlib first-order
formulas over `stLang Const Pred` — accessibility as a binary relation,
predicates world-relativized to binary relations, constants world-indexed to
unary functions, and an individual-sort predicate — interpreted on the
two-sorted-as-one carrier `W ⊕ M`. `realize_st?` is satisfaction
preservation; composed with Proposition 4.1, the support relation of NE-free
QBSML bottoms out in single-structure mathlib first-order satisfaction
(`support_singleton_iff_st`).

## Main declarations

* `stLang` — the target signature; `KripkeStructure.stStructure` — the
  `W ⊕ M` encoding of a Kripke structure as one mathlib structure.
* `ModalFormula.st?` — the standard translation, with the current world as
  the free variable `Sum.inr k` and box introducing the fresh world
  variable `Sum.inr (k + 1)` (partial: embedded classical formulas
  translate when atomic, which covers all `toModal?` images).
* `realize_st?` — satisfaction preservation: Kripke satisfaction at `w` is
  first-order realization over `stStructure` at any sorted valuation
  pinning `Sum.inr k` to `w`.
* `support_singleton_iff_st` — NE-free QBSML support is first-order
  realization of the standard translation, via Proposition 4.1.
* `stClose` — sort-guarded existential closure of the current-world
  variable, turning translations into sentence candidates.
* `support_compactness` — compactness transfer: finite team
  satisfiability of an NE-free family yields one first-order structure
  satisfying all closed translations.

## Implementation notes

* The valuation in `realize_st?` is an arbitrary `val : Var ⊕ ℕ → W ⊕ M`
  constrained only at individual variables and at the current world index —
  quantifiers in the translation range over the full mixed carrier, with
  off-sort values discharged by the relational guards, so no
  `Sum.elim`-update commutation is needed in the induction.
* Freshness of world variables is by increment: each `box` shifts the
  current index from `k` to `k + 1`, and the constraint set of the theorem
  pins only index `k`, so no freshness side conditions arise.
* The compactness transfer is one-way: recovering a team model from an
  arbitrary first-order structure would need `Finset`-branching
  accessibility and a `Fintype` domain. `freeVarFinset = ∅` side
  conditions are hypotheses, dischargeable by `decide` per instance —
  no generic free-variable bookkeeping for `st?`.
-/

universe u v

namespace Core.Logic.Modal.QBSML

open FirstOrder Language

variable {W M Var Const Pred : Type*}

/-! ### The target signature and the encoded structure -/

/-- The standard-translation target signature: world-indexed constants as
    unary functions, an individual-sort predicate (unary), and
    world-relativized monadic predicates plus accessibility (binary). -/
def stLang (Const : Type u) (Pred : Type v) : FirstOrder.Language where
  Functions := fun n => match n with
    | 1 => Const
    | _ => PEmpty
  Relations := fun n => match n with
    | 1 => PUnit
    | 2 => Pred ⊕ PUnit
    | _ => PEmpty

/-- A constant as a unary function symbol of the target signature. -/
abbrev stConst {Const Pred : Type*} (c : Const) :
    (stLang Const Pred).Functions 1 := c

/-- The individual-sort predicate. -/
abbrev stIndiv {Const Pred : Type*} : (stLang Const Pred).Relations 1 :=
  PUnit.unit

/-- A predicate as a world-relativized binary relation symbol. -/
abbrev stRel {Const Pred : Type*} (P : Pred) :
    (stLang Const Pred).Relations 2 := Sum.inl P

/-- The accessibility relation symbol. -/
abbrev stAcc {Const Pred : Type*} : (stLang Const Pred).Relations 2 :=
  Sum.inr PUnit.unit

/-- The `W ⊕ M` encoding of a Kripke structure over the monadic signature
    as a single mathlib structure: worlds and individuals share the carrier,
    sorted by `stIndiv`; relational guards make all off-sort atoms false. -/
@[reducible] def _root_.FirstOrder.Language.KripkeStructure.stStructure
    (K : KripkeStructure (monadicLang Const Pred) W M) :
    (stLang Const Pred).Structure (W ⊕ M) where
  funMap := fun {n} f => match n, f with
    | 1, c => fun z => match z 0 with
      | Sum.inl w => Sum.inr (K.cInterp c w)
      | Sum.inr d => Sum.inr d
    | 0, f => f.elim
    | _ + 2, f => f.elim
  RelMap := fun {n} r => match n, r with
    | 1, _ => fun z => ∃ d : M, z 0 = Sum.inr d
    | 2, Sum.inl P => fun z =>
        ∃ w d, z 0 = Sum.inl w ∧ z 1 = Sum.inr d ∧ K.pInterp P w d
    | 2, Sum.inr _ => fun z =>
        ∃ w₁ w₂, z 0 = Sum.inl w₁ ∧ z 1 = Sum.inl w₂ ∧ w₂ ∈ K.access w₁
    | 0, r => r.elim
    | _ + 3, r => r.elim

theorem stStructure_relMap_rel (K : KripkeStructure (monadicLang Const Pred) W M)
    (P : Pred) (z : Fin 2 → W ⊕ M) :
    (K.stStructure).RelMap (stRel P) z ↔
      ∃ w d, z 0 = Sum.inl w ∧ z 1 = Sum.inr d ∧ K.pInterp P w d :=
  Iff.rfl

theorem stStructure_relMap_acc (K : KripkeStructure (monadicLang Const Pred) W M)
    (z : Fin 2 → W ⊕ M) :
    (K.stStructure).RelMap (stAcc (Const := Const)) z ↔
      ∃ w₁ w₂, z 0 = Sum.inl w₁ ∧ z 1 = Sum.inl w₂ ∧ w₂ ∈ K.access w₁ :=
  Iff.rfl

theorem stStructure_relMap_indiv (K : KripkeStructure (monadicLang Const Pred) W M)
    (z : Fin 1 → W ⊕ M) :
    (K.stStructure).RelMap (stIndiv (Const := Const)) z ↔
      ∃ d : M, z 0 = Sum.inr d :=
  Iff.rfl

theorem stStructure_funMap_inl (K : KripkeStructure (monadicLang Const Pred) W M)
    (c : Const) (w : W) (z : Fin 1 → W ⊕ M) (hz : z 0 = Sum.inl w) :
    (K.stStructure).funMap (stConst (Pred := Pred) c) z =
      Sum.inr (K.cInterp c w) := by
  show (match z 0 with
    | Sum.inl w' => Sum.inr (K.cInterp c w')
    | Sum.inr d => Sum.inr d) = _
  rw [hz]

/-! ### The translation -/

variable [DecidableEq Var]

/-- Translate a monadic term: variables stay, constants become their unary
    function applied to the current world variable. -/
def stTerm (k : ℕ) :
    (monadicLang Const Pred).Term (Var ⊕ Fin 0) →
      (stLang Const Pred).Term (Var ⊕ ℕ)
  | .var (Sum.inl x) => Term.var (Sum.inl x)
  | .var (Sum.inr i) => i.elim0
  | @Term.func _ _ l f _ => match l, f with
    | 0, c => Term.func (stConst c) ![Term.var (Sum.inr k)]
    | _ + 1, f => f.elim

/-- Translate an embedded classical formula when it is a monadic atom
    (`none` otherwise — which never arises from `QBSMLFormula.toModal?`
    images, whose embedded formulas are exactly the atoms). -/
def stAtom? (k : ℕ) :
    (monadicLang Const Pred).Formula Var →
      Option ((stLang Const Pred).Formula (Var ⊕ ℕ))
  | @BoundedFormula.rel _ _ _ l R ts => match l, R, ts with
    | 1, P, ts =>
        some ((stRel P).formula₂ (Term.var (Sum.inr k)) (stTerm k (ts 0)))
    | 0, r, _ => r.elim
    | _ + 2, r, _ => r.elim
  | _ => none

/-- The standard translation `ST_k` ([blackburn-derijke-venema-2001]): the
    current world is the free variable `Sum.inr k`; `box` relativizes a
    fresh world variable `Sum.inr (k + 1)` along accessibility; quantifiers
    relativize to the individual sort. -/
def _root_.FirstOrder.Language.ModalFormula.st? (k : ℕ) :
    ModalFormula (monadicLang Const Pred) Var →
      Option ((stLang Const Pred).Formula (Var ⊕ ℕ))
  | .ofFormula χ => stAtom? k χ
  | .not φ => (φ.st? k).map (·.not)
  | .inf φ ψ => (φ.st? k).bind fun a => (ψ.st? k).map (a ⊓ ·)
  | .sup φ ψ => (φ.st? k).bind fun a => (ψ.st? k).map (a ⊔ ·)
  | .box φ => (φ.st? (k + 1)).map fun a =>
      Formula.all₁ (Sum.inr (k + 1))
        ((stAcc.formula₂ (Term.var (Sum.inr k))
          (Term.var (Sum.inr (k + 1)))).imp a)
  | .all x φ => (φ.st? k).map fun a =>
      Formula.all₁ (Sum.inl x)
        ((stIndiv.formula₁ (Term.var (Sum.inl x))).imp a)
  | .ex x φ => (φ.st? k).map fun a =>
      Formula.ex₁ (Sum.inl x)
        (stIndiv.formula₁ (Term.var (Sum.inl x)) ⊓ a)

/-! ### Satisfaction preservation -/

omit [DecidableEq Var] in
/-- Satisfaction preservation for embedded atoms. -/
private theorem realize_stAtom? (K : KripkeStructure (monadicLang Const Pred) W M)
    {k : ℕ} {χ : (monadicLang Const Pred).Formula Var}
    {ψ : (stLang Const Pred).Formula (Var ⊕ ℕ)}
    (hψ : stAtom? k χ = some ψ) {val : Var ⊕ ℕ → W ⊕ M} {w : W}
    {v : Var → M} (hind : ∀ x, val (Sum.inl x) = Sum.inr (v x))
    (hw : val (Sum.inr k) = Sum.inl w) :
    K.RealizeAt w χ v ↔ (letI := K.stStructure; ψ.Realize val) := by
  letI := K.stStructure
  cases χ with
  | falsum => simp [stAtom?] at hψ
  | equal t₁ t₂ => simp [stAtom?] at hψ
  | imp χ₁ χ₂ => simp [stAtom?] at hψ
  | all χ' => simp [stAtom?] at hψ
  | @rel _ l R ts =>
    match l, R with
    | 0, r => exact r.elim
    | (n + 2), r => exact r.elim
    | 1, (P : Pred) =>
      rw [show stAtom? k (.rel (monadicRel P) ts) =
          some ((stRel P).formula₂ (Term.var (Sum.inr k)) (stTerm k (ts 0)))
          from rfl, Option.some.injEq] at hψ
      subst hψ
      cases hts : ts 0 with
      | var s =>
        cases s with
        | inl x =>
          have hLHS : K.RealizeAt w (.rel (monadicRel P) ts) v ↔
              K.pInterp P w (v x) := by
            letI := K.interp w
            show (K.interp w).RelMap (monadicRel P)
                (fun i => (ts i).realize (Sum.elim v (default : Fin 0 → M)))
              ↔ _
            have hfun : (fun i : Fin 1 => (ts i).realize
                (Sum.elim v (default : Fin 0 → M))) = fun _ => v x := by
              funext i
              rw [Subsingleton.elim i 0, hts]
              rfl
            rw [hfun]
            exact Iff.rfl
          rw [hLHS, Formula.realize_rel₂,
            show (stTerm k (.var (Sum.inl x)) :
                (stLang Const Pred).Term (Var ⊕ ℕ)) =
              Term.var (Sum.inl x) from rfl,
            stStructure_relMap_rel]
          simp only [Term.realize_var, hw, hind]
          constructor
          · intro h
            exact ⟨w, v x, rfl, rfl, h⟩
          · rintro ⟨w', d, hw', hd, h⟩
            obtain rfl : w = w' := Sum.inl.inj hw'
            obtain rfl : v x = d := Sum.inr.inj hd
            exact h
        | inr i => exact i.elim0
      | @func l' f args =>
        cases l' with
        | succ m => exact f.elim
        | zero =>
          have hLHS : K.RealizeAt w (.rel (monadicRel P) ts) v ↔
              K.pInterp P w (K.cInterp f w) := by
            letI := K.interp w
            show (K.interp w).RelMap (monadicRel P)
                (fun i => (ts i).realize (Sum.elim v (default : Fin 0 → M)))
              ↔ _
            have hfun : (fun i : Fin 1 => (ts i).realize
                (Sum.elim v (default : Fin 0 → M))) =
                fun _ => K.cInterp f w := by
              funext i
              rw [Subsingleton.elim i 0, hts]
              show (K.interp w).funMap f
                  (fun j => (args j).realize (Sum.elim v default)) = _
              have hargs : (fun j : Fin 0 => (args j).realize
                  (Sum.elim v (default : Fin 0 → M))) = default :=
                funext fun j => j.elim0
              rw [hargs]
              rfl
            rw [hfun]
            exact Iff.rfl
          rw [hLHS, Formula.realize_rel₂,
            show (stTerm k (.func f args) :
                (stLang Const Pred).Term (Var ⊕ ℕ)) =
              Term.func (stConst f) ![Term.var (Sum.inr k)] from rfl,
            stStructure_relMap_rel]
          have hcv : (Term.func (stConst f)
              ![Term.var (Sum.inr k)] :
              (stLang Const Pred).Term (Var ⊕ ℕ)).realize val
              = Sum.inr (K.cInterp f w) :=
            stStructure_funMap_inl K f w _ hw
          constructor
          · intro h
            exact ⟨w, K.cInterp f w, hw, hcv, h⟩
          · rintro ⟨w', d, hw', hd, h⟩
            have hww : val (Sum.inr k) = Sum.inl w' := hw'
            obtain rfl : w = w' := Sum.inl.inj (hw.symm.trans hww)
            have hdd : Sum.inr (K.cInterp f w) = Sum.inr d :=
              hcv.symm.trans hd
            obtain rfl : K.cInterp f w = d := Sum.inr.inj hdd
            exact h

/-- **Satisfaction preservation for the standard translation**: Kripke
    satisfaction at `w` is first-order realization over `stStructure`, for
    any valuation that is individual-sorted on `Var` and pins the current
    world variable `Sum.inr k` to `w`. Off-sort quantifier instances are
    discharged by the relational guards, and `box`'s fresh world variable
    `k + 1` leaves the pinned index untouched. -/
theorem realize_st? (K : KripkeStructure (monadicLang Const Pred) W M) :
    ∀ {φ : ModalFormula (monadicLang Const Pred) Var} {k : ℕ}
      {ψ : (stLang Const Pred).Formula (Var ⊕ ℕ)},
      φ.st? k = some ψ →
      ∀ {val : Var ⊕ ℕ → W ⊕ M} {w : W} {v : Var → M},
        (∀ x, val (Sum.inl x) = Sum.inr (v x)) →
        val (Sum.inr k) = Sum.inl w →
        (φ.Realize K w v ↔ (letI := K.stStructure; ψ.Realize val)) := by
  intro φ
  induction φ with
  | ofFormula χ =>
    intro k ψ hψ val w v hind hw
    exact realize_stAtom? K hψ hind hw
  | not φ ih =>
    intro k ψ hψ val w v hind hw
    rw [show (ModalFormula.not φ).st? k = (φ.st? k).map (·.not) from rfl] at hψ
    cases hφ : φ.st? k with
    | none => rw [hφ] at hψ; simp at hψ
    | some a =>
      rw [hφ, Option.map_some, Option.some.injEq] at hψ
      subst hψ
      letI := K.stStructure
      rw [ModalFormula.realize_not, Formula.realize_not]
      exact not_congr (ih hφ hind hw)
  | inf φ₁ φ₂ ih₁ ih₂ =>
    intro k ψ hψ val w v hind hw
    rw [show (ModalFormula.inf φ₁ φ₂).st? k =
        (φ₁.st? k).bind (fun a => (φ₂.st? k).map (a ⊓ ·)) from rfl] at hψ
    cases hφ₁ : φ₁.st? k with
    | none => rw [hφ₁] at hψ; simp at hψ
    | some a =>
      cases hφ₂ : φ₂.st? k with
      | none =>
        rw [hφ₁, Option.bind_some, hφ₂] at hψ
        simp at hψ
      | some b =>
        rw [hφ₁, Option.bind_some, hφ₂, Option.map_some,
          Option.some.injEq] at hψ
        subst hψ
        letI := K.stStructure
        rw [ModalFormula.realize_inf, Formula.realize_inf]
        exact and_congr (ih₁ hφ₁ hind hw) (ih₂ hφ₂ hind hw)
  | sup φ₁ φ₂ ih₁ ih₂ =>
    intro k ψ hψ val w v hind hw
    rw [show (ModalFormula.sup φ₁ φ₂).st? k =
        (φ₁.st? k).bind (fun a => (φ₂.st? k).map (a ⊔ ·)) from rfl] at hψ
    cases hφ₁ : φ₁.st? k with
    | none => rw [hφ₁] at hψ; simp at hψ
    | some a =>
      cases hφ₂ : φ₂.st? k with
      | none =>
        rw [hφ₁, Option.bind_some, hφ₂] at hψ
        simp at hψ
      | some b =>
        rw [hφ₁, Option.bind_some, hφ₂, Option.map_some,
          Option.some.injEq] at hψ
        subst hψ
        letI := K.stStructure
        rw [ModalFormula.realize_sup, Formula.realize_sup]
        exact or_congr (ih₁ hφ₁ hind hw) (ih₂ hφ₂ hind hw)
  | box φ ih =>
    intro k ψ hψ val w v hind hw
    rw [show (ModalFormula.box φ).st? k = (φ.st? (k + 1)).map (fun a =>
        Formula.all₁ (Sum.inr (k + 1))
          ((stAcc.formula₂ (Term.var (Sum.inr k))
            (Term.var (Sum.inr (k + 1)))).imp a)) from rfl] at hψ
    cases hφ : φ.st? (k + 1) with
    | none => rw [hφ] at hψ; simp at hψ
    | some a =>
      rw [hφ, Option.map_some, Option.some.injEq] at hψ
      subst hψ
      letI := K.stStructure
      rw [ModalFormula.realize_box, Formula.realize_all₁]
      constructor
      · intro h z
        rw [Formula.realize_imp, Formula.realize_rel₂]
        simp only [Term.realize_var, Function.update_of_ne
          (by simp : (Sum.inr k : Var ⊕ ℕ) ≠ Sum.inr (k + 1)),
          Function.update_self, hw]
        rintro ⟨w₁, w₂, hw₁, hw₂, hmem⟩
        obtain rfl : w = w₁ := Sum.inl.inj hw₁
        subst hw₂
        refine (ih hφ ?_ ?_).mp (h w₂ hmem)
        · intro x
          rw [Function.update_of_ne (by simp), hind]
        · rw [Function.update_self]
      · intro h w' hw'
        have hz := h (Sum.inl w')
        rw [Formula.realize_imp, Formula.realize_rel₂] at hz
        simp only [Term.realize_var, Function.update_of_ne
          (by simp : (Sum.inr k : Var ⊕ ℕ) ≠ Sum.inr (k + 1)),
          Function.update_self, hw] at hz
        refine (ih hφ ?_ ?_).mpr (hz ⟨w, w', rfl, rfl, hw'⟩)
        · intro x
          rw [Function.update_of_ne (by simp), hind]
        · rw [Function.update_self]
  | all x φ ih =>
    intro k ψ hψ val w v hind hw
    rw [show (ModalFormula.all x φ).st? k = (φ.st? k).map (fun a =>
        Formula.all₁ (Sum.inl x)
          ((stIndiv.formula₁ (Term.var (Sum.inl x))).imp a)) from rfl] at hψ
    cases hφ : φ.st? k with
    | none => rw [hφ] at hψ; simp at hψ
    | some a =>
      rw [hφ, Option.map_some, Option.some.injEq] at hψ
      subst hψ
      letI := K.stStructure
      rw [ModalFormula.realize_all, Formula.realize_all₁]
      constructor
      · intro h z
        rw [Formula.realize_imp, Formula.realize_rel₁]
        intro hsort
        obtain ⟨d, hd⟩ : ∃ d : M,
            Function.update val (Sum.inl x) z (Sum.inl x) = Sum.inr d := by
          simpa using hsort
        rw [Function.update_self] at hd
        subst hd
        refine (ih hφ ?_ ?_).mp (h d)
        · intro y
          by_cases hy : y = x
          · subst hy
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne (by simpa using hy),
              Function.update_of_ne hy, hind]
        · rw [Function.update_of_ne (by simp)]
          exact hw
      · intro h d
        have hz := h (Sum.inr d)
        rw [Formula.realize_imp, Formula.realize_rel₁] at hz
        refine (ih hφ ?_ ?_).mpr (hz ?_)
        · intro y
          by_cases hy : y = x
          · subst hy
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne (by simpa using hy),
              Function.update_of_ne hy, hind]
        · rw [Function.update_of_ne (by simp)]
          exact hw
        · show ∃ d' : M, _ = Sum.inr d'
          refine ⟨d, ?_⟩
          show Function.update val (Sum.inl x) (Sum.inr d) (Sum.inl x) = _
          rw [Function.update_self]
  | ex x φ ih =>
    intro k ψ hψ val w v hind hw
    rw [show (ModalFormula.ex x φ).st? k = (φ.st? k).map (fun a =>
        Formula.ex₁ (Sum.inl x)
          (stIndiv.formula₁ (Term.var (Sum.inl x)) ⊓ a)) from rfl] at hψ
    cases hφ : φ.st? k with
    | none => rw [hφ] at hψ; simp at hψ
    | some a =>
      rw [hφ, Option.map_some, Option.some.injEq] at hψ
      subst hψ
      letI := K.stStructure
      rw [ModalFormula.realize_ex, Formula.realize_ex₁]
      constructor
      · rintro ⟨d, hd⟩
        refine ⟨Sum.inr d, ?_⟩
        rw [Formula.realize_inf, Formula.realize_rel₁]
        refine ⟨⟨d, ?_⟩, ?_⟩
        · show Function.update val (Sum.inl x) (Sum.inr d) (Sum.inl x) = _
          rw [Function.update_self]
        · refine (ih hφ ?_ ?_).mp hd
          · intro y
            by_cases hy : y = x
            · subst hy
              rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne (by simpa using hy),
                Function.update_of_ne hy, hind]
          · rw [Function.update_of_ne (by simp)]
            exact hw
      · rintro ⟨z, hz⟩
        rw [Formula.realize_inf, Formula.realize_rel₁] at hz
        obtain ⟨hsort, hreal⟩ := hz
        obtain ⟨d, hd⟩ : ∃ d : M,
            Function.update val (Sum.inl x) z (Sum.inl x) = Sum.inr d := by
          simpa using hsort
        rw [Function.update_self] at hd
        subst hd
        refine ⟨d, (ih hφ ?_ ?_).mpr hreal⟩
        · intro y
          by_cases hy : y = x
          · subst hy
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne (by simpa using hy),
              Function.update_of_ne hy, hind]
        · rw [Function.update_of_ne (by simp)]
          exact hw

/-! ### Sort-guarded sentence closure -/

/-- Sort-guarded existential closure of the current-world variable
    `Sum.inr k`: `∃z(¬IsIndiv(z) ∧ ψ)`. The guard is load-bearing on the
    mixed carrier — a bare `ex₁` could be witnessed by a junk
    individual-as-world, which satisfies `□⊥` vacuously. -/
def stClose (k : ℕ) (ψ : (stLang Const Pred).Formula (Var ⊕ ℕ)) :
    (stLang Const Pred).Formula (Var ⊕ ℕ) :=
  Formula.ex₁ (Sum.inr k)
    ((stIndiv.formula₁ (Term.var (Sum.inr k))).not ⊓ ψ)

/-- Over `stStructure`, the guarded witness of `stClose` is exactly a
    world. -/
theorem realize_stClose (K : KripkeStructure (monadicLang Const Pred) W M)
    (k : ℕ) (ψ : (stLang Const Pred).Formula (Var ⊕ ℕ))
    (val : Var ⊕ ℕ → W ⊕ M) :
    (letI := K.stStructure; (stClose k ψ).Realize val) ↔
      ∃ w : W,
        (letI := K.stStructure
         ψ.Realize (Function.update val (Sum.inr k) (Sum.inl w))) := by
  letI := K.stStructure
  unfold stClose
  rw [Formula.realize_ex₁]
  constructor
  · rintro ⟨z, hz⟩
    rw [Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁,
      stStructure_relMap_indiv] at hz
    obtain ⟨hguard, hzψ⟩ := hz
    cases z with
    | inl w => exact ⟨w, hzψ⟩
    | inr d =>
      refine absurd ⟨d, ?_⟩ hguard
      show Function.update val (Sum.inr k) (Sum.inr d) (Sum.inr k) = _
      rw [Function.update_self]
  · rintro ⟨w, hw⟩
    refine ⟨Sum.inl w, ?_⟩
    rw [Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁,
      stStructure_relMap_indiv]
    refine ⟨?_, hw⟩
    rintro ⟨d, hd⟩
    have hd' : Function.update val (Sum.inr k) (Sum.inl w) (Sum.inr k)
        = Sum.inr d := hd
    rw [Function.update_self] at hd'
    exact Sum.inl_ne_inr hd'

/-! ### Proposition 4.1, composed: QBSML support is first-order realization -/

variable {Domain : Type*}
variable [DecidableEq W] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

/-- **NE-free QBSML support is single-structure first-order satisfaction**:
    [aloni-vanormondt-2023] Proposition 4.1 composed with the standard
    translation. Support at a singleton state is mathlib `Formula.Realize`
    of the standard translation over `stStructure` — the link along which
    classical model theory (compactness, Löwenheim–Skolem) transfers to the
    NE-free fragment. -/
theorem support_singleton_iff_st (M : QBSMLModel W Domain Const Pred)
    {φ : QBSMLFormula Var Const Pred}
    {τ : ModalFormula (monadicLang Const Pred) Var} {k : ℕ}
    {ψ : (stLang Const Pred).Formula (Var ⊕ ℕ)}
    (hτ : φ.toModal? = some τ) (hψ : τ.st? k = some ψ)
    {i : Index W Var Domain} {v : Var → Domain} (u : ℕ → W)
    (hv : ∀ y, i.assign y = some (v y)) (hu : u k = i.world) :
    support M φ {i} ↔
      (letI := M.stStructure
       ψ.Realize (Sum.elim (Sum.inr ∘ v) (Sum.inl ∘ u))) :=
  (support_singleton_iff_realize M hτ hv).trans
    (realize_st? M hψ (fun _ => rfl) (by rw [Sum.elim_inr, Function.comp_apply, hu]))

/-- Support at a singleton state forces the closed standard translation,
    as a sentence of `stStructure`. -/
theorem models_toSentence_of_support (M : QBSMLModel W Domain Const Pred)
    {φ : QBSMLFormula Var Const Pred}
    {τ : ModalFormula (monadicLang Const Pred) Var}
    {ψ : (stLang Const Pred).Formula (Var ⊕ ℕ)}
    (hτ : φ.toModal? = some τ) (hψ : τ.st? 0 = some ψ)
    (hcl : (stClose 0 ψ).freeVarFinset = ∅)
    {i : Index W Var Domain} {v : Var → Domain}
    (hv : ∀ y, i.assign y = some (v y)) (hsupp : support M φ {i}) :
    (letI := M.stStructure
     (W ⊕ Domain) ⊨ (stClose 0 ψ).toSentence hcl) := by
  letI := M.stStructure
  have h1 : ψ.Realize
      (Sum.elim (Sum.inr ∘ v) (Sum.inl ∘ (fun _ => i.world))) :=
    (support_singleton_iff_st M hτ hψ (fun _ => i.world) hv rfl).mp hsupp
  refine (Formula.realize_toSentence _ hcl
    (Sum.elim (Sum.inr ∘ v) (Sum.inl ∘ (fun _ => i.world)))).mpr ?_
  refine (realize_stClose M 0 ψ _).mpr ⟨i.world, ?_⟩
  rw [show Function.update
      (Sum.elim (Sum.inr ∘ v) (Sum.inl ∘ (fun _ => i.world)))
      (Sum.inr 0) (Sum.inl i.world)
      = Sum.elim (Sum.inr ∘ v) (Sum.inl ∘ (fun _ => i.world)) from
    Function.update_eq_self _ _]
  exact h1

/-- Conversely, the closed standard translation as a sentence of
    `stStructure` yields support at some singleton state. -/
theorem exists_support_of_models_toSentence [Nonempty Domain]
    (M : QBSMLModel W Domain Const Pred)
    {φ : QBSMLFormula Var Const Pred}
    {τ : ModalFormula (monadicLang Const Pred) Var}
    {ψ : (stLang Const Pred).Formula (Var ⊕ ℕ)}
    (hτ : φ.toModal? = some τ) (hψ : τ.st? 0 = some ψ)
    (hcl : (stClose 0 ψ).freeVarFinset = ∅)
    (h : letI := M.stStructure
         (W ⊕ Domain) ⊨ (stClose 0 ψ).toSentence hcl) :
    ∃ (i : Index W Var Domain) (v : Var → Domain),
      (∀ y, i.assign y = some (v y)) ∧ support M φ {i} := by
  letI := M.stStructure
  obtain ⟨d₀⟩ := ‹Nonempty Domain›
  have h0 : (stClose 0 ψ).Realize
      (fun _ => (Sum.inr d₀ : W ⊕ Domain)) :=
    (Formula.realize_toSentence _ hcl _).mp h
  obtain ⟨w, hw⟩ := (realize_stClose M 0 ψ _).mp h0
  have hsorted : ∀ x : Var, Function.update
      (fun _ : Var ⊕ ℕ => (Sum.inr d₀ : W ⊕ Domain)) (Sum.inr 0)
      (Sum.inl w) (Sum.inl x) = Sum.inr d₀ := fun x => by
    rw [Function.update_of_ne (by simp)]
  have hmodal : τ.Realize M w (fun _ => d₀) :=
    (realize_st? M hψ hsorted (Function.update_self _ _ _)).mpr hw
  refine ⟨⟨w, fun _ => some d₀⟩, fun _ => d₀, fun y => rfl, ?_⟩
  refine (support_singleton_iff_st M hτ hψ (fun _ => w)
    (fun y => rfl) rfl).mpr ?_
  exact (realize_st? M hψ (fun _ => rfl) rfl).mp hmodal

end Core.Logic.Modal.QBSML

/-! ### Compactness for the NE-free fragment -/

namespace Core.Logic.Modal.QBSML

open FirstOrder Language

/-- **Compactness transfer for NE-free QBSML** ([aloni-vanormondt-2023]
    Proposition 4.1, the standard translation, and mathlib's
    `Theory.isSatisfiable_iff_isFinitelySatisfiable`): if every finite
    subfamily of a family of NE-free formulas is supported at a singleton
    state of some model, the family's closed standard translations are
    jointly satisfiable in a single first-order structure.

    The converse recovery of a *team* model from that structure would need
    `Finset`-branching accessibility and a `Fintype` domain, which an
    arbitrary first-order structure does not supply, so the transfer is
    stated one-way. -/
theorem support_compactness {Var : Type*} [DecidableEq Var] [Fintype Var]
    {Const : Type u} {Pred : Type v} {ι : Type*}
    {φs : ι → QBSMLFormula Var Const Pred}
    {τs : ι → ModalFormula (monadicLang Const Pred) Var}
    {ψs : ι → (stLang Const Pred).Formula (Var ⊕ ℕ)}
    (hτ : ∀ i, (φs i).toModal? = some (τs i))
    (hψ : ∀ i, (τs i).st? 0 = some (ψs i))
    (hcl : ∀ i, (stClose 0 (ψs i)).freeVarFinset = ∅)
    (hfin : ∀ s : Finset ι, ∃ (W Domain : Type max u v)
      (_ : DecidableEq W) (_ : DecidableEq Domain) (_ : Fintype Domain)
      (M : QBSMLModel W Domain Const Pred) (i : Index W Var Domain)
      (v : Var → Domain), (∀ y, i.assign y = some (v y)) ∧
        ∀ j ∈ s, support M (φs j) {i}) :
    Theory.IsSatisfiable
      (Set.range fun i => (stClose 0 (ψs i)).toSentence (hcl i)) := by
  rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
  intro T₀ hT₀
  classical
  choose f hf using fun x : T₀ => hT₀ x.2
  obtain ⟨W, Domain, _, _, _, M, i, v, hv, hs⟩ := hfin (Finset.univ.image f)
  letI := M.stStructure
  haveI : Nonempty (W ⊕ Domain) := ⟨Sum.inl i.world⟩
  haveI : (W ⊕ Domain) ⊨ (T₀ : (stLang Const Pred).Theory) := by
    refine ⟨fun σ hσ => ?_⟩
    obtain ⟨x, rfl⟩ : ∃ x : T₀,
        (stClose 0 (ψs (f x))).toSentence (hcl (f x)) = σ :=
      ⟨⟨σ, hσ⟩, hf ⟨σ, hσ⟩⟩
    exact models_toSentence_of_support M (hτ (f x)) (hψ (f x)) (hcl (f x))
      hv (hs (f x) (Finset.mem_image_of_mem f (Finset.mem_univ x)))
  exact Theory.Model.isSatisfiable (W ⊕ Domain)

end Core.Logic.Modal.QBSML
