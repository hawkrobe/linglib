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
* `realize_st` evaluates translations at sorted valuations `stVal v u` —
  the valuation invariant is carried by the constructor rather than by
  hypotheses. Binder cases reduce to the two update-commutation lemmas
  (`stVal_update_indiv`, `stVal_update_world`) and the two relativization
  lemmas, which discharge off-sort quantifier instances via the guards.
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

variable {L : Language} {n : ℕ}

abbrev corrFunc (f : L.Functions n) : L.correspondence.Functions (n + 1) := f

abbrev corrRel (R : L.Relations n) : L.correspondence.Relations (n + 1) := Sum.inl R

/-- The individual-sort predicate. -/
abbrev corrIndiv : L.correspondence.Relations 1 := Sum.inr PUnit.unit

/-- The accessibility relation symbol. -/
abbrev corrAcc : L.correspondence.Relations 2 := Sum.inr PUnit.unit

abbrev corrIndivVar (x : Var) : L.correspondence.Term (Var ⊕ ℕ) := Term.var (Sum.inl x)

abbrev corrWorldVar (k : ℕ) : L.correspondence.Term (Var ⊕ ℕ) := Term.var (Sum.inr k)

variable [Inhabited M] (K : ModalStructure L W M)

/-- `K.correspondence` encodes a modal structure as a single mathlib
    structure on `W ⊕ M` — the structure half of `Language.correspondence`:
    worlds and individuals share the carrier, sorted by `corrIndiv`;
    relational guards make all off-sort atoms false, and off-sort function
    arguments default. -/
@[reducible] def ModalStructure.correspondence : L.correspondence.Structure (W ⊕ M) where
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

@[simp] theorem correspondence_relMap_rel (R : L.Relations n) (z : Fin (n + 1) → W ⊕ M) :
    K.correspondence.RelMap (corrRel R) z ↔
      ∃ (w : W) (ds : Fin n → M),
        z 0 = Sum.inl w ∧ (∀ i, z i.succ = Sum.inr (ds i)) ∧
          K.relInterp R w ds :=
  Iff.rfl

@[simp] theorem correspondence_relMap_acc (z : Fin 2 → W ⊕ M) :
    K.correspondence.RelMap corrAcc z ↔
      ∃ w₁ w₂, z 0 = Sum.inl w₁ ∧ z 1 = Sum.inl w₂ ∧ w₂ ∈ K.access w₁ :=
  Iff.rfl

@[simp] theorem correspondence_relMap_indiv (z : Fin 1 → W ⊕ M) :
    K.correspondence.RelMap corrIndiv z ↔
      ∃ d : M, z 0 = Sum.inr d :=
  Iff.rfl

theorem correspondence_funMap_inl (f : L.Functions n) (w : W) (z : Fin (n + 1) → W ⊕ M)
    (ds : Fin n → M) (hz : z 0 = Sum.inl w)
    (hds : ∀ i, z i.succ = Sum.inr (ds i)) :
    K.correspondence.funMap (corrFunc f) z = Sum.inr (K.funInterp f w ds) := by
  obtain rfl : z = Fin.cons (Sum.inl w) (fun i => Sum.inr (ds i)) :=
    funext fun j => Fin.cases hz hds j
  rfl

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
  | .imp φ ψ => φ.st k ⟹ ψ.st k
  | .box φ => Formula.all₁ (Sum.inr (k + 1))
      (corrAcc.formula₂ (corrWorldVar k) (corrWorldVar (k + 1)) ⟹ φ.st (k + 1))
  | .all x φ => Formula.all₁ (Sum.inl x)
      (corrIndiv.formula₁ (corrIndivVar x) ⟹ φ.st k)

/-! ### Sorted valuations and relativized quantifiers -/

omit [Inhabited M] in
/-- The sorted valuation of an individual assignment `v` and a world
    assignment `u`. `realize_st` evaluates translations at these. -/
def stVal (v : Var → M) (u : ℕ → W) : Var ⊕ ℕ → W ⊕ M :=
  Sum.elim (Sum.inr ∘ v) (Sum.inl ∘ u)

omit [Inhabited M] in
/-- Updating an individual slot of a sorted valuation updates the
    individual assignment. -/
theorem stVal_update_indiv (v : Var → M) (u : ℕ → W) (x : Var) (d : M) :
    Function.update (stVal v u) (Sum.inl x) (Sum.inr d) =
      stVal (Function.update v x d) u := by
  simp only [stVal, Sum.update_elim_inl, Function.comp_update]

omit [Inhabited M] in
/-- Updating a world slot of a sorted valuation updates the world
    assignment. -/
theorem stVal_update_world (v : Var → M) (u : ℕ → W) (j : ℕ) (w : W) :
    Function.update (stVal v u) (Sum.inr j) (Sum.inl w) =
      stVal v (Function.update u j w) := by
  simp only [stVal, Sum.update_elim_inr, Function.comp_update]

/-- A sort-guarded universal quantifies exactly over individuals. -/
theorem realize_all₁_indivGuard {y : Var ⊕ ℕ}
    {ψ : L.correspondence.Formula (Var ⊕ ℕ)} {val : Var ⊕ ℕ → W ⊕ M} :
    (letI := K.correspondence;
      (Formula.all₁ y (corrIndiv.formula₁ (Term.var y) ⟹ ψ)).Realize val) ↔
      ∀ d : M,
        (letI := K.correspondence;
          ψ.Realize (Function.update val y (Sum.inr d))) := by
  simp [Formula.realize_all₁]

/-- An accessibility-guarded universal quantifies exactly over the worlds
    accessible from the world pinned at index `k`. -/
theorem realize_all₁_accGuard {j k : ℕ} (hjk : k ≠ j)
    {ψ : L.correspondence.Formula (Var ⊕ ℕ)} {val : Var ⊕ ℕ → W ⊕ M}
    {w : W} (hw : val (Sum.inr k) = Sum.inl w) :
    (letI := K.correspondence;
      (Formula.all₁ (Sum.inr j)
        (corrAcc.formula₂ (corrWorldVar k) (corrWorldVar j) ⟹ ψ)).Realize
          val) ↔
      ∀ w' ∈ K.access w,
        (letI := K.correspondence;
          ψ.Realize (Function.update val (Sum.inr j) (Sum.inl w'))) := by
  simp [Formula.realize_all₁, Function.update_of_ne (Sum.inr_injective.ne hjk), hw]

/-! ### Satisfaction preservation -/

omit [DecidableEq Var] in
/-- Translated terms realize to the individual sort: `stTerm` commutes with
    realization at a sorted valuation. -/
private theorem realize_stTerm {k : ℕ} {v : Var → M} {u : ℕ → W} :
    ∀ t : L.Term Var,
      (letI := K.correspondence; (stTerm k t).realize (stVal v u)) =
        Sum.inr (letI := K.interp (u k); t.realize v)
  | .var x => rfl
  | .func f args => by
    let _S := K.correspondence
    let _I := K.interp (u k)
    rw [show stTerm k (.func f args) = Term.func (corrFunc f)
        (Fin.cons (corrWorldVar k) fun i => stTerm k (args i)) from rfl,
      Term.realize_func,
      correspondence_funMap_inl K f (u k) _
        (fun i => (letI := K.interp (u k); (args i).realize v))
        rfl
        (fun i => by simpa [Fin.cons_succ] using realize_stTerm (args i))]
    rfl

/-- **Satisfaction preservation for the standard translation**: Kripke
    satisfaction at the world pinned at index `k` is first-order
    realization over `K.correspondence` at the sorted valuation.
    Off-sort quantifier instances are discharged by the relational guards
    (`realize_all₁_indivGuard`, `realize_all₁_accGuard`), and `box`'s fresh
    world variable `k + 1` leaves index `k` untouched. -/
theorem realize_st {φ : ModalFormula L Var} {k : ℕ}
    {v : Var → M} {u : ℕ → W} :
    φ.Realize K (u k) v ↔
      (letI := K.correspondence; (φ.st k).Realize (stVal v u)) := by
  induction φ generalizing k v u with
  | equal t₁ t₂ =>
    let _S := K.correspondence
    rw [ModalFormula.st, ModalFormula.realize_equal, Formula.realize_equal,
      realize_stTerm K, realize_stTerm K]
    exact ⟨congrArg _, Sum.inr.inj⟩
  | falsum => exact Iff.rfl
  | imp φ ψ ih₁ ih₂ =>
    let _S := K.correspondence
    rw [ModalFormula.realize_imp, ModalFormula.st, Formula.realize_imp]
    exact imp_congr ih₁ ih₂
  | box φ ih =>
    rw [ModalFormula.realize_box, ModalFormula.st,
      realize_all₁_accGuard K (Nat.succ_ne_self k).symm rfl]
    refine forall₂_congr fun w' _ => ?_
    rw [stVal_update_world]
    simpa using ih (k := k + 1) (u := Function.update u (k + 1) w')
  | all x φ ih =>
    rw [ModalFormula.realize_all, ModalFormula.st,
      realize_all₁_indivGuard K]
    refine forall_congr' fun d => ?_
    rw [stVal_update_indiv]
    exact ih
  | @rel n R ts =>
    let _S := K.correspondence
    rw [ModalFormula.st, Formula.realize_rel, correspondence_relMap_rel,
      ModalFormula.realize_rel]
    constructor
    · intro h
      exact ⟨u k, (fun i => letI := K.interp (u k); (ts i).realize v), rfl,
        fun i => by simpa [Fin.cons_succ] using realize_stTerm K (ts i), h⟩
    · rintro ⟨w', ds, hw', hds, h⟩
      obtain rfl : u k = w' := Sum.inl.inj hw'
      have hds' : (fun i => letI := K.interp (u k); (ts i).realize v) = ds :=
        funext fun i => Sum.inr.inj
          ((realize_stTerm K (ts i)).symm.trans
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
theorem realize_stClose (k : ℕ) (ψ : L.correspondence.Formula (Var ⊕ ℕ))
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
