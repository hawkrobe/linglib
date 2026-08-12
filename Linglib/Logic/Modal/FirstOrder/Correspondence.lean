import Linglib.Core.ModelTheory.FiniteModel
import Linglib.Logic.Modal.FirstOrder.Semantics

/-!
# The correspondence language and the standard translation

The standard translation of modal logic into first-order logic, for the
monadic signature with constants: modal formulas over
`Language.monadicWithConstants Const Pred` translate into plain mathlib
first-order formulas over the correspondence language
`Language.correspondence Const Pred` — accessibility as a binary relation,
predicates world-relativized to binary relations, constants world-indexed
to unary functions, and an individual-sort predicate — interpreted on the
two-sorted-as-one carrier `W ⊕ M`. `realize_st?` is satisfaction
preservation.

## Main declarations

* `Language.correspondence` — the target signature;
  `ModalStructure.corrStructure` — the `W ⊕ M` encoding of a Kripke
  structure as one mathlib structure.
* `ModalFormula.st?` — the standard translation, with the current world as
  the free variable `Sum.inr k` and box introducing the fresh world
  variable `Sum.inr (k + 1)` (partial: embedded classical formulas
  translate when atomic, which covers all `toModal?` images).
* `realize_st?` — satisfaction preservation: Kripke satisfaction at `w` is
  first-order realization over `corrStructure` at any sorted valuation
  pinning `Sum.inr k` to `w`.
* `stClose` — sort-guarded existential closure of the current-world
  variable, turning translations into sentence candidates.

## Implementation notes

* The valuation in `realize_st?` is an arbitrary `val : Var ⊕ ℕ → W ⊕ M`
  constrained only at individual variables and at the current world index —
  quantifiers in the translation range over the full mixed carrier, with
  off-sort values discharged by the relational guards, so no
  `Sum.elim`-update commutation is needed in the induction.
* Freshness of world variables is by increment: each `box` shifts the
  current index from `k` to `k + 1`, and the constraint set of the theorem
  pins only index `k`, so no freshness side conditions arise.
* `freeVarFinset = ∅` side conditions on closures are hypotheses,
  dischargeable by `decide` per instance — no generic free-variable
  bookkeeping for `st?`.

## References

* [blackburn-derijke-venema-2001] — the standard translation
* [aloni-vanormondt-2023] — Proposition 4.1, composed with the translation
  for compactness
-/

namespace FirstOrder.Language

variable {W M Var Const Pred : Type*}

/-! ### The target signature and the encoded structure -/

/-- The standard-translation target signature: world-indexed constants as
    unary functions, an individual-sort predicate (unary), and
    world-relativized monadic predicates plus accessibility (binary). -/
def correspondence (Const : Type*) (Pred : Type*) : FirstOrder.Language where
  Functions := fun n => match n with
    | 1 => Const
    | _ => PEmpty
  Relations := fun n => match n with
    | 1 => PUnit
    | 2 => Pred ⊕ PUnit
    | _ => PEmpty

/-- A constant as a unary function symbol of the target signature. -/
abbrev corrConst (c : Const) :
    (correspondence Const Pred).Functions 1 := c

/-- The individual-sort predicate. -/
abbrev corrIndiv : (correspondence Const Pred).Relations 1 :=
  PUnit.unit

/-- A predicate as a world-relativized binary relation symbol. -/
abbrev corrRel (P : Pred) :
    (correspondence Const Pred).Relations 2 := Sum.inl P

/-- The accessibility relation symbol. -/
abbrev corrAcc : (correspondence Const Pred).Relations 2 :=
  Sum.inr PUnit.unit

/-- An individual variable as a sorted term of the correspondence
    language. -/
abbrev corrIndivVar (x : Var) :
    (correspondence Const Pred).Term (Var ⊕ ℕ) := Term.var (Sum.inl x)

/-- A world variable as a sorted term of the correspondence language. -/
abbrev corrWorldVar (k : ℕ) :
    (correspondence Const Pred).Term (Var ⊕ ℕ) := Term.var (Sum.inr k)

/-- The `W ⊕ M` encoding of a Kripke model over the monadic signature
    as a single mathlib structure: worlds and individuals share the carrier,
    sorted by `corrIndiv`; relational guards make all off-sort atoms false. -/
@[reducible] def ModalStructure.corrStructure
    (K : ModalStructure (monadicWithConstants Const Pred) W M) :
    (correspondence Const Pred).Structure (W ⊕ M) where
  funMap := fun {n} f => match n, f with
    | 1, c => fun z => match z 0 with
      | Sum.inl w => Sum.inr (K.constInterp c w)
      | Sum.inr d => Sum.inr d
    | 0, f => f.elim
    | _ + 2, f => f.elim
  RelMap := fun {n} r => match n, r with
    | 1, _ => fun z => ∃ d : M, z 0 = Sum.inr d
    | 2, Sum.inl P => fun z =>
        ∃ w d, z 0 = Sum.inl w ∧ z 1 = Sum.inr d ∧ K.relInterp₁ P w d
    | 2, Sum.inr _ => fun z =>
        ∃ w₁ w₂, z 0 = Sum.inl w₁ ∧ z 1 = Sum.inl w₂ ∧ w₂ ∈ K.access w₁
    | 0, r => r.elim
    | _ + 3, r => r.elim

@[simp] theorem corrStructure_relMap_rel
    (K : ModalStructure (monadicWithConstants Const Pred) W M)
    (P : Pred) (z : Fin 2 → W ⊕ M) :
    (K.corrStructure).RelMap (corrRel P) z ↔
      ∃ w d, z 0 = Sum.inl w ∧ z 1 = Sum.inr d ∧ K.relInterp₁ P w d :=
  Iff.rfl

@[simp] theorem corrStructure_relMap_acc (K : ModalStructure (monadicWithConstants Const Pred) W M)
    (z : Fin 2 → W ⊕ M) :
    (K.corrStructure).RelMap (corrAcc (Const := Const)) z ↔
      ∃ w₁ w₂, z 0 = Sum.inl w₁ ∧ z 1 = Sum.inl w₂ ∧ w₂ ∈ K.access w₁ :=
  Iff.rfl

@[simp] theorem corrStructure_relMap_indiv
    (K : ModalStructure (monadicWithConstants Const Pred) W M)
    (z : Fin 1 → W ⊕ M) :
    (K.corrStructure).RelMap (corrIndiv (Const := Const)) z ↔
      ∃ d : M, z 0 = Sum.inr d :=
  Iff.rfl

theorem corrStructure_funMap_inl (K : ModalStructure (monadicWithConstants Const Pred) W M)
    (c : Const) (w : W) (z : Fin 1 → W ⊕ M) (hz : z 0 = Sum.inl w) :
    (K.corrStructure).funMap (corrConst (Pred := Pred) c) z =
      Sum.inr (K.constInterp c w) := by
  show (match z 0 with
    | Sum.inl w' => Sum.inr (K.constInterp c w')
    | Sum.inr d => Sum.inr d) = _
  rw [hz]

/-! ### The translation -/

variable [DecidableEq Var]

/-- Translate a monadic term: variables stay, constants become their unary
    function applied to the current world variable. -/
def stTerm (k : ℕ) :
    (monadicWithConstants Const Pred).Term Var →
      (correspondence Const Pred).Term (Var ⊕ ℕ)
  | .var x => corrIndivVar x
  | @Term.func _ _ l f _ => match l, f with
    | 0, c => Term.func (corrConst c) ![corrWorldVar k]
    | _ + 1, f => f.elim

/-- The standard translation `ST_k` ([blackburn-derijke-venema-2001]): the
    current world is the free variable `Sum.inr k`; `box` relativizes a
    fresh world variable `Sum.inr (k + 1)` along accessibility; quantifiers
    relativize to the individual sort. Total — `ModalFormula` atoms are
    atomic. -/
def ModalFormula.st (k : ℕ) :
    ModalFormula (monadicWithConstants Const Pred) Var →
      (correspondence Const Pred).Formula (Var ⊕ ℕ)
  | .equal t₁ t₂ => Term.equal (stTerm k t₁) (stTerm k t₂)
  | @ModalFormula.rel _ _ l R ts => match l, R, ts with
    | 1, P, ts => (corrRel P).formula₂ (corrWorldVar k) (stTerm k (ts 0))
    | 0, r, _ => r.elim
    | _ + 2, r, _ => r.elim
  | .falsum => ⊥
  | .imp φ ψ => (φ.st k).imp (ψ.st k)
  | .box φ => Formula.all₁ (Sum.inr (k + 1))
      ((corrAcc.formula₂ (corrWorldVar k) (corrWorldVar (k + 1))).imp
        (φ.st (k + 1)))
  | .all x φ => Formula.all₁ (Sum.inl x)
      ((corrIndiv.formula₁ (corrIndivVar x)).imp (φ.st k))

/-! ### Satisfaction preservation -/

omit [DecidableEq Var] in
/-- Translated terms realize to the individual sort: `stTerm` commutes with
    realization, via the world pinned at index `k`. -/
private theorem realize_stTerm
    (K : ModalStructure (monadicWithConstants Const Pred) W M)
    {k : ℕ} {val : Var ⊕ ℕ → W ⊕ M} {w : W} {v : Var → M}
    (hind : ∀ x, val (Sum.inl x) = Sum.inr (v x))
    (hw : val (Sum.inr k) = Sum.inl w)
    (t : (monadicWithConstants Const Pred).Term Var) :
    (letI := K.corrStructure; (stTerm k t).realize val) =
      Sum.inr (letI := K.interp w; t.realize v) := by
  let _S := K.corrStructure
  cases t with
  | var x => exact hind x
  | @func l f args =>
    match l, f with
    | _ + 1, f => exact f.elim
    | 0, c =>
      let _I := K.interp w
      rw [show stTerm k (.func c args) =
          Term.func (corrConst c) ![corrWorldVar k] from rfl,
        show (Term.func (corrConst c) ![corrWorldVar k] :
            (correspondence Const Pred).Term (Var ⊕ ℕ)).realize val =
          (K.corrStructure).funMap (corrConst c)
            fun i => (![corrWorldVar k] i).realize val from rfl,
        corrStructure_funMap_inl K c w _ (by simpa using hw)]
      refine congrArg Sum.inr ?_
      show (K.interp w).funMap (monadicConst c) default = _
      show _ = (K.interp w).funMap (monadicConst c) fun i => (args i).realize v
      exact congrArg _ (funext fun i => i.elim0)

/-- An individual-sorted update of an individual-sorted valuation. -/
private theorem sorted_update {val : Var ⊕ ℕ → W ⊕ M} {v : Var → M}
    (hind : ∀ x, val (Sum.inl x) = Sum.inr (v x)) (x : Var) (d : M) :
    ∀ y, Function.update val (Sum.inl x) (Sum.inr d) (Sum.inl y) =
      Sum.inr (Function.update v x d y) := by
  intro y
  by_cases hy : y = x
  · subst hy; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne (by simpa using hy), Function.update_of_ne hy,
      hind]

/-- Individual updates leave the pinned world index untouched. -/
private theorem pinned_update {val : Var ⊕ ℕ → W ⊕ M} {w : W} {k : ℕ}
    (hw : val (Sum.inr k) = Sum.inl w) (x : Var) (z : W ⊕ M) :
    Function.update val (Sum.inl x) z (Sum.inr k) = Sum.inl w := by
  rw [Function.update_of_ne (by simp)]; exact hw

/-- **Satisfaction preservation for the standard translation**: Kripke
    satisfaction at `w` is first-order realization over `corrStructure`, for
    any valuation that is individual-sorted on `Var` and pins the current
    world variable `Sum.inr k` to `w`. Off-sort quantifier instances are
    discharged by the relational guards, and `box`'s fresh world variable
    `k + 1` leaves the pinned index untouched. -/
theorem realize_st (K : ModalStructure (monadicWithConstants Const Pred) W M)
    {φ : ModalFormula (monadicWithConstants Const Pred) Var} {k : ℕ}
    {val : Var ⊕ ℕ → W ⊕ M} {w : W} {v : Var → M}
    (hind : ∀ x, val (Sum.inl x) = Sum.inr (v x))
    (hw : val (Sum.inr k) = Sum.inl w) :
    φ.Realize K w v ↔ (letI := K.corrStructure; (φ.st k).Realize val) := by
  induction φ generalizing k val w v with
  | equal t₁ t₂ =>
    let _S := K.corrStructure
    rw [show (ModalFormula.equal t₁ t₂).st k =
        Term.equal (stTerm k t₁) (stTerm k t₂) from rfl]
    rw [ModalFormula.realize_equal, Formula.realize_equal,
      realize_stTerm K hind hw, realize_stTerm K hind hw]
    exact ⟨congrArg _, Sum.inr.inj⟩
  | falsum => exact Iff.rfl
  | imp φ ψ ih₁ ih₂ =>
    let _S := K.corrStructure
    rw [ModalFormula.realize_imp,
      show (ModalFormula.imp φ ψ).st k = (φ.st k).imp (ψ.st k) from rfl,
      Formula.realize_imp]
    exact imp_congr (ih₁ hind hw) (ih₂ hind hw)
  | box φ ih =>
    let _S := K.corrStructure
    rw [ModalFormula.realize_box,
      show (ModalFormula.box φ).st k = Formula.all₁ (Sum.inr (k + 1))
        ((corrAcc.formula₂ (corrWorldVar k) (corrWorldVar (k + 1))).imp
          (φ.st (k + 1))) from rfl,
      Formula.realize_all₁]
    constructor
    · intro h z
      rw [Formula.realize_imp, Formula.realize_rel₂]
      simp only [Term.realize_var, Function.update_of_ne
        (by simp : (Sum.inr k : Var ⊕ ℕ) ≠ Sum.inr (k + 1)),
        Function.update_self, hw]
      rintro ⟨w₁, w₂, hw₁, hw₂, hmem⟩
      obtain rfl : w = w₁ := Sum.inl.inj hw₁
      subst hw₂
      refine (ih ?_ ?_).mp (h w₂ hmem)
      · intro x
        rw [Function.update_of_ne (by simp), hind]
      · rw [Function.update_self]
    · intro h w' hw'
      have hz := h (Sum.inl w')
      rw [Formula.realize_imp, Formula.realize_rel₂] at hz
      simp only [Term.realize_var, Function.update_of_ne
        (by simp : (Sum.inr k : Var ⊕ ℕ) ≠ Sum.inr (k + 1)),
        Function.update_self, hw] at hz
      refine (ih ?_ ?_).mpr (hz ⟨w, w', rfl, rfl, hw'⟩)
      · intro x
        rw [Function.update_of_ne (by simp), hind]
      · rw [Function.update_self]
  | all x φ ih =>
    let _S := K.corrStructure
    rw [ModalFormula.realize_all,
      show (ModalFormula.all x φ).st k = Formula.all₁ (Sum.inl x)
        ((corrIndiv.formula₁ (corrIndivVar x)).imp (φ.st k)) from rfl,
      Formula.realize_all₁]
    constructor
    · intro h z
      rw [Formula.realize_imp, Formula.realize_rel₁]
      intro hsort
      obtain ⟨d, hd⟩ : ∃ d : M,
          Function.update val (Sum.inl x) z (Sum.inl x) = Sum.inr d := by
        simpa [corrStructure_relMap_indiv] using hsort
      rw [Function.update_self] at hd
      subst hd
      exact (ih (sorted_update hind x d) (pinned_update hw x _)).mp (h d)
    · intro h d
      have hz := h (Sum.inr d)
      rw [Formula.realize_imp, Formula.realize_rel₁] at hz
      refine (ih (sorted_update hind x d) (pinned_update hw x _)).mpr
        (hz ⟨d, ?_⟩)
      show Function.update val (Sum.inl x) (Sum.inr d) (Sum.inl x) = _
      rw [Function.update_self]
  | @rel l R ts =>
    match l, R with
    | 0, r => exact r.elim
    | (n + 2), r => exact r.elim
    | 1, (P : Pred) =>
      let _S := K.corrStructure
      rw [show (ModalFormula.rel (P : (monadicWithConstants Const
            Pred).Relations 1) ts).st k =
          (corrRel P).formula₂ (corrWorldVar k) (stTerm k (ts 0)) from rfl,
        Formula.realize_rel₂, corrStructure_relMap_rel,
        ModalFormula.realize_rel,
        show (fun i => letI := K.interp w; ((ts i).realize v)) =
          fun _ => (letI := K.interp w; (ts 0).realize v) from
          funext fun i => by rw [Subsingleton.elim i 0] ]
      constructor
      · intro h
        exact ⟨w, (letI := K.interp w; (ts 0).realize v), by simpa using hw,
          realize_stTerm K hind hw (ts 0), h⟩
      · rintro ⟨w', d, hw', hd, h⟩
        obtain rfl : w = w' := Sum.inl.inj ((by simpa using hw : (corrWorldVar
          (Const := Const) (Pred := Pred) k).realize val = Sum.inl w).symm.trans hw')
        obtain rfl : (letI := K.interp w; (ts 0).realize v) = d :=
          Sum.inr.inj ((realize_stTerm K hind hw (ts 0)).symm.trans hd)
        exact h

/-! ### Sort-guarded sentence closure -/

/-- Sort-guarded existential closure of the current-world variable
    `Sum.inr k`: `∃z(¬IsIndiv(z) ∧ ψ)`. The guard is load-bearing on the
    mixed carrier — a bare `ex₁` could be witnessed by a junk
    individual-as-world, which satisfies `□⊥` vacuously. -/
def stClose (k : ℕ) (ψ : (correspondence Const Pred).Formula (Var ⊕ ℕ)) :
    (correspondence Const Pred).Formula (Var ⊕ ℕ) :=
  Formula.ex₁ (Sum.inr k)
    ((corrIndiv.formula₁ (corrWorldVar k)).not ⊓ ψ)

/-- Over `corrStructure`, the guarded witness of `stClose` is exactly a
    world. -/
theorem realize_stClose (K : ModalStructure (monadicWithConstants Const Pred) W M)
    (k : ℕ) (ψ : (correspondence Const Pred).Formula (Var ⊕ ℕ))
    (val : Var ⊕ ℕ → W ⊕ M) :
    (letI := K.corrStructure; (stClose k ψ).Realize val) ↔
      ∃ w : W,
        (letI := K.corrStructure
         ψ.Realize (Function.update val (Sum.inr k) (Sum.inl w))) := by
  let _S := K.corrStructure
  unfold stClose
  rw [Formula.realize_ex₁]
  constructor
  · rintro ⟨z, hz⟩
    rw [Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁,
      corrStructure_relMap_indiv] at hz
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
      corrStructure_relMap_indiv]
    refine ⟨?_, hw⟩
    rintro ⟨d, hd⟩
    have hd' : Function.update val (Sum.inr k) (Sum.inl w) (Sum.inr k)
        = Sum.inr d := hd
    rw [Function.update_self] at hd'
    exact Sum.inl_ne_inr hd'

end FirstOrder.Language
