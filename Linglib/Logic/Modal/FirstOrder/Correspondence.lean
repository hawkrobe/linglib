import Linglib.Logic.Modal.FirstOrder.Semantics

/-!
# The correspondence language and the standard translation

The standard translation of quantified modal logic into first-order logic,
for an arbitrary signature: modal formulas over `L` translate into plain
mathlib first-order formulas over the correspondence language
`L.correspondence` — every symbol world-relativized to one arity higher,
plus a binary accessibility relation and an individual-sort predicate —
interpreted on the two-sorted-as-one carrier `W ⊕ M`. `realize_st` is
satisfaction preservation.

## Main declarations

* `Language.correspondence` — the correspondence language of `L`;
  `ModalStructure.correspondence` — the `W ⊕ M` encoding of a modal
  structure as one mathlib structure.
* `ModalFormula.st` — the standard translation, total: the current world is
  the free variable `Sum.inr k`, and `box` introduces the fresh world
  variable `Sum.inr (k + 1)`.
* `realize_st` — satisfaction preservation: Kripke satisfaction at `w` is
  first-order realization over `correspondence` at any sorted valuation
  pinning `Sum.inr k` to `w`.
* `stClose` — sort-guarded existential closure of the current-world
  variable, turning translations into sentence candidates.

## Implementation notes

* The canonical object here is the *two-sorted* first-order view of a
  modal structure (worlds with accessibility; individuals; world-relativized
  symbols) — the same object, in the correspondence-theory sense. The
  `W ⊕ M` carrier, the sort predicate, and the off-sort guards are the
  standard many-sorted-to-one-sorted coding, forced by mathlib's
  single-sorted `Structure`; they have no independent standing. Junk
  totalization of world-relativized functions is by `[Inhabited M]` —
  constant-domain semantics presupposes a nonempty domain.
* The valuation in `realize_st` is an arbitrary `val : Var ⊕ ℕ → W ⊕ M`
  constrained only at individual variables and at the current world index —
  quantifiers in the translation range over the full mixed carrier, with
  off-sort values discharged by the relational guards, so no
  `Sum.elim`-update commutation is needed in the induction.
* Freshness of world variables is by increment: each `box` shifts the
  current index from `k` to `k + 1`, and the constraint set of the theorem
  pins only index `k`, so no freshness side conditions arise.
* `freeVarFinset = ∅` side conditions on closures are hypotheses,
  dischargeable by `decide` per instance — no generic free-variable
  bookkeeping for `st`.

## References

* [blackburn-derijke-venema-2001] — the standard translation
-/

namespace FirstOrder.Language

variable {W M Var : Type*}

/-! ### The correspondence language and the encoded structure -/

/-- The correspondence language of `L` has an `(n + 1)`-ary symbol for
    each `n`-ary `L`-symbol — the new first argument the world — together
    with an individual-sort predicate and an accessibility relation. -/
def correspondence (L : Language) : Language where
  Functions := fun n => match n with
    | 0 => PEmpty
    | n + 1 => L.Functions n
  Relations := fun n => match n with
    | 0 => PEmpty
    | n + 1 => L.Relations n ⊕ (match n with | 0 | 1 => PUnit | _ => PEmpty)

variable {L : Language}

abbrev corrFunc {n : ℕ} (f : L.Functions n) : L.correspondence.Functions (n + 1) := f

abbrev corrRel {n : ℕ} (R : L.Relations n) : L.correspondence.Relations (n + 1) := Sum.inl R

/-- The individual-sort predicate. -/
abbrev corrIndiv : L.correspondence.Relations 1 := Sum.inr PUnit.unit

/-- The accessibility relation symbol. -/
abbrev corrAcc : L.correspondence.Relations 2 := Sum.inr PUnit.unit

abbrev corrIndivVar (x : Var) : L.correspondence.Term (Var ⊕ ℕ) := Term.var (Sum.inl x)

abbrev corrWorldVar (k : ℕ) : L.correspondence.Term (Var ⊕ ℕ) := Term.var (Sum.inr k)

/-- `K.correspondence` encodes a modal structure as a single mathlib
    structure on `W ⊕ M` — the structure half of `Language.correspondence`:
    worlds and individuals share the carrier, sorted by `corrIndiv`;
    relational guards make all off-sort atoms false, and off-sort function
    arguments default. -/
@[reducible] def ModalStructure.correspondence [Inhabited M]
    (K : ModalStructure L W M) :
    L.correspondence.Structure (W ⊕ M) where
  funMap := fun {n} f z => match n, f with
    | 0, f => f.elim
    | _ + 1, f => Sum.inr <| (z 0).elim
        (fun w => K.funInterp f w fun i => (z i.succ).getRight?.getD default) id
  RelMap := fun {n} r z => match n, r with
    | 0, r => r.elim
    | n + 1, r => r.elim
        (fun R => ∃ (w : W) (ds : Fin n → M),
          z 0 = Sum.inl w ∧ (∀ i, z i.succ = Sum.inr (ds i)) ∧
            K.relInterp R w ds)
        (fun u => match n, z, u with
          | 0, z, _ => ∃ d : M, z 0 = Sum.inr d
          | 1, z, _ =>
              ∃ w₁ w₂, z 0 = Sum.inl w₁ ∧ z 1 = Sum.inl w₂ ∧ w₂ ∈ K.access w₁
          | _ + 2, _, u => u.elim)

variable [Inhabited M]

@[simp] theorem correspondence_relMap_rel (K : ModalStructure L W M)
    {n : ℕ} (R : L.Relations n) (z : Fin (n + 1) → W ⊕ M) :
    (K.correspondence).RelMap (corrRel R) z ↔
      ∃ (w : W) (ds : Fin n → M),
        z 0 = Sum.inl w ∧ (∀ i, z i.succ = Sum.inr (ds i)) ∧
          K.relInterp R w ds :=
  Iff.rfl

@[simp] theorem correspondence_relMap_acc (K : ModalStructure L W M)
    (z : Fin 2 → W ⊕ M) :
    (K.correspondence).RelMap (corrAcc (L := L)) z ↔
      ∃ w₁ w₂, z 0 = Sum.inl w₁ ∧ z 1 = Sum.inl w₂ ∧ w₂ ∈ K.access w₁ :=
  Iff.rfl

@[simp] theorem correspondence_relMap_indiv (K : ModalStructure L W M)
    (z : Fin 1 → W ⊕ M) :
    (K.correspondence).RelMap (corrIndiv (L := L)) z ↔
      ∃ d : M, z 0 = Sum.inr d :=
  Iff.rfl

theorem correspondence_funMap_inl (K : ModalStructure L W M)
    {n : ℕ} (f : L.Functions n) (w : W) (z : Fin (n + 1) → W ⊕ M)
    (ds : Fin n → M) (hz : z 0 = Sum.inl w)
    (hds : ∀ i, z i.succ = Sum.inr (ds i)) :
    (K.correspondence).funMap (corrFunc f) z = Sum.inr (K.funInterp f w ds) := by
  show Sum.inr ((z 0).elim
      (fun w' => K.funInterp f w' fun i => (z i.succ).getRight?.getD default) id) = _
  rw [hz]
  exact congrArg Sum.inr (congrArg _ (funext fun i => by rw [hds i]; rfl))

/-! ### The translation -/

variable [DecidableEq Var]

/-- `stTerm` translates terms: a variable stays put; a function symbol
    applies its world-relativized form at the current world variable. -/
def stTerm (k : ℕ) : L.Term Var → L.correspondence.Term (Var ⊕ ℕ)
  | .var x => corrIndivVar x
  | .func f args =>
      Term.func (corrFunc f) (Fin.cons (corrWorldVar k) fun i => stTerm k (args i))

/-- The standard translation `ST_k` of [blackburn-derijke-venema-2001].
    The current world is the free variable `Sum.inr k`; atoms
    world-relativize; `box` relativizes a fresh world variable
    `Sum.inr (k + 1)` along accessibility; quantifiers relativize to the
    individual sort. -/
def ModalFormula.st (k : ℕ) :
    ModalFormula L Var → L.correspondence.Formula (Var ⊕ ℕ)
  | .equal t₁ t₂ => Term.equal (stTerm k t₁) (stTerm k t₂)
  | .rel R ts =>
      (corrRel R).formula (Fin.cons (corrWorldVar k) fun i => stTerm k (ts i))
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
private theorem realize_stTerm (K : ModalStructure L W M)
    {k : ℕ} {val : Var ⊕ ℕ → W ⊕ M} {w : W} {v : Var → M}
    (hind : ∀ x, val (Sum.inl x) = Sum.inr (v x))
    (hw : val (Sum.inr k) = Sum.inl w) :
    ∀ t : L.Term Var,
      (letI := K.correspondence; (stTerm k t).realize val) =
        Sum.inr (letI := K.interp w; t.realize v)
  | .var x => hind x
  | .func f args => by
    let _S := K.correspondence
    let _I := K.interp w
    rw [show stTerm k (.func f args) = Term.func (corrFunc f)
        (Fin.cons (corrWorldVar k) fun i => stTerm k (args i)) from rfl,
      Term.realize_func,
      correspondence_funMap_inl K f w _
        (fun i => (letI := K.interp w; (args i).realize v))
        (by simpa using hw)
        (fun i => by
          simpa [Fin.cons_succ] using realize_stTerm K hind hw (args i))]
    rfl

omit [Inhabited M] in
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

omit [Inhabited M] in
/-- Individual updates leave the pinned world index untouched. -/
private theorem pinned_update {val : Var ⊕ ℕ → W ⊕ M} {w : W} {k : ℕ}
    (hw : val (Sum.inr k) = Sum.inl w) (x : Var) (z : W ⊕ M) :
    Function.update val (Sum.inl x) z (Sum.inr k) = Sum.inl w := by
  rw [Function.update_of_ne (by simp)]; exact hw

/-- **Satisfaction preservation for the standard translation**: Kripke
    satisfaction at `w` is first-order realization over `correspondence`, for
    any valuation that is individual-sorted on `Var` and pins the current
    world variable `Sum.inr k` to `w`. Off-sort quantifier instances are
    discharged by the relational guards, and `box`'s fresh world variable
    `k + 1` leaves the pinned index untouched. -/
theorem realize_st (K : ModalStructure L W M)
    {φ : ModalFormula L Var} {k : ℕ}
    {val : Var ⊕ ℕ → W ⊕ M} {w : W} {v : Var → M}
    (hind : ∀ x, val (Sum.inl x) = Sum.inr (v x))
    (hw : val (Sum.inr k) = Sum.inl w) :
    φ.Realize K w v ↔ (letI := K.correspondence; (φ.st k).Realize val) := by
  induction φ generalizing k val w v with
  | equal t₁ t₂ =>
    let _S := K.correspondence
    rw [ModalFormula.st, ModalFormula.realize_equal, Formula.realize_equal,
      realize_stTerm K hind hw, realize_stTerm K hind hw]
    exact ⟨congrArg _, Sum.inr.inj⟩
  | falsum => exact Iff.rfl
  | imp φ ψ ih₁ ih₂ =>
    let _S := K.correspondence
    rw [ModalFormula.realize_imp, ModalFormula.st, Formula.realize_imp]
    exact imp_congr (ih₁ hind hw) (ih₂ hind hw)
  | box φ ih =>
    let _S := K.correspondence
    rw [ModalFormula.realize_box, ModalFormula.st, Formula.realize_all₁]
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
    let _S := K.correspondence
    rw [ModalFormula.realize_all, ModalFormula.st, Formula.realize_all₁]
    constructor
    · intro h z
      rw [Formula.realize_imp, Formula.realize_rel₁]
      intro hsort
      obtain ⟨d, hd⟩ : ∃ d : M,
          Function.update val (Sum.inl x) z (Sum.inl x) = Sum.inr d := by
        simpa [correspondence_relMap_indiv] using hsort
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
  | @rel n R ts =>
    let _S := K.correspondence
    rw [ModalFormula.st, Formula.realize_rel, correspondence_relMap_rel,
      ModalFormula.realize_rel]
    constructor
    · intro h
      refine ⟨w, (fun i => letI := K.interp w; (ts i).realize v),
        by simpa using hw,
        fun i => by simpa [Fin.cons_succ] using realize_stTerm K hind hw (ts i),
        h⟩
    · rintro ⟨w', ds, hw', hds, h⟩
      obtain rfl : w = w' := by
        rw [show ((Fin.cons (corrWorldVar k)
            (fun i => stTerm k (ts i)) : Fin _ → _) 0).realize val =
          val (Sum.inr k) from rfl] at hw'
        exact Sum.inl.inj (hw.symm.trans hw')
      have hds' : (fun i => letI := K.interp w; (ts i).realize v) = ds :=
        funext fun i => Sum.inr.inj
          ((realize_stTerm K hind hw (ts i)).symm.trans
            (by simpa [Fin.cons_succ] using hds i))
      exact hds' ▸ h

/-! ### Sort-guarded sentence closure -/

/-- `stClose` closes the current-world variable `Sum.inr k` under a
    sort-guarded existential, `∃z(¬IsIndiv(z) ∧ ψ)`. The guard is
    load-bearing on the mixed carrier — a bare `ex₁` could be witnessed by
    a junk individual-as-world, which satisfies `□⊥` vacuously. -/
def stClose (k : ℕ) (ψ : L.correspondence.Formula (Var ⊕ ℕ)) :
    L.correspondence.Formula (Var ⊕ ℕ) :=
  Formula.ex₁ (Sum.inr k)
    ((corrIndiv.formula₁ (corrWorldVar k)).not ⊓ ψ)

/-- Over `correspondence`, the guarded witness of `stClose` is exactly a
    world. -/
theorem realize_stClose (K : ModalStructure L W M)
    (k : ℕ) (ψ : L.correspondence.Formula (Var ⊕ ℕ))
    (val : Var ⊕ ℕ → W ⊕ M) :
    (letI := K.correspondence; (stClose k ψ).Realize val) ↔
      ∃ w : W,
        (letI := K.correspondence
         ψ.Realize (Function.update val (Sum.inr k) (Sum.inl w))) := by
  let _S := K.correspondence
  unfold stClose
  rw [Formula.realize_ex₁]
  constructor
  · rintro ⟨z, hz⟩
    rw [Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁,
      correspondence_relMap_indiv] at hz
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
      correspondence_relMap_indiv]
    refine ⟨?_, hw⟩
    rintro ⟨d, hd⟩
    have hd' : Function.update val (Sum.inr k) (Sum.inl w) (Sum.inr k)
        = Sum.inr d := hd
    rw [Function.update_self] at hd'
    exact Sum.inl_ne_inr hd'

end FirstOrder.Language
