import Linglib.Core.Algebra.RootedTree.PreLie.Defs
import Linglib.Core.Combinatorics.RootedTree.Nonplanar
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Tactic.Abel

set_option autoImplicit false

/-!
# Pre-Lie product on `RootedTree.Nonplanar α` — descent through the quotient
@cite{foissy-typed-decorated-rooted-trees-2018}
@cite{marcolli-chomsky-berwick-2025}

The Nonplanar pre-Lie product is obtained by descending the planar
`Planar.insertSum` (`PreLie/Defs.lean`) through the projection
`mk : Planar α → Nonplanar α`. The descent requires showing that the
projected grafting summands `(Planar.insertSum T₁ T₂).map Nonplanar.mk`
depend on `T₁, T₂ : Planar α` only through their `Nonplanar.mk` images,
i.e., are invariant under `Planar.PlanarEquiv` on either argument.

Once invariance is established on each side, `Quotient.lift₂` produces
`Nonplanar.insertSum`. The cardinality lemma `card_insertSum_eq_weight`
descends as well, giving a Nonplanar-level analog matching MCB §1.1.2's
unordered-children semantics.

## Reference

@cite{foissy-typed-decorated-rooted-trees-2018} Proposition 2.2 defines
the multiple pre-Lie product on D-decorated T-typed rooted trees. The
nonplanar version is obtained by quotienting by the equivalence relation
that permutes children at each node — the same passage from planar to
nonplanar trees that gives the Connes-Kreimer Hopf algebra of nonplanar
rooted trees.

@cite{marcolli-chomsky-berwick-2025} §1.1.2 (book p. 20) — the
unordered-children semantics realized as `Nonplanar α`. The pre-Lie
product descends compatibly because the grafting site (a vertex of T₁)
and the grafted tree T₂ both respect the children-list permutation
equivalence.

## File scope (R.3c)

This file (`PreLie/Nonplanar.lean`) carries the descent layer:
- §2: Right invariance — `T₂ → T₂'` (mutual induction on T₁)
- §3: List-side `Nonplanar.mk`-projection of `insertSumList` is
  `List.Perm`-invariant + componentwise-PlanarEquiv-invariant
- §4: Left invariance — `T₁ → T₁'` via PlanarStep induction
- §5: EqvGen lift to PlanarEquiv on either argument
- §6: Native `Nonplanar.insertSum` via `Quotient.lift₂`
- §7: Quotient-unfolding lemma `mk_insertSum`
- §8: Cardinality + sanity tests

Sibling files in `PreLie/`:
- `Defs.lean` (R.3a): planar substrate
- `EdgeBijection.lean` (R.3b): vertex classification + commutativity
- `Algebra.lean` (R.3d): bilinear extension + pre-Lie identity +
  `RightPreLieAlgebra ℤ` instance.

## Status

`[UPSTREAM]` candidate. Sorry-free.
-/

namespace RootedTree

namespace Nonplanar

variable {α : Type*}

open scoped RootedTree.Planar

/-! ## §1: Cons-decomposition of `insertSumList`-projection

Helper lemma used by both §2 right-invariance and §3 list permutation
proofs. The cons case of `insertSumList cs T₂` splits into a per-head
grafting (in `insertSum c T₂`) plus a per-tail grafting (in
`insertSumList tail T₂`); after projection through `mk ∘ node a`, the
two halves are clean two-summand decompositions with simpler wrappers
than the raw `Multiset.map_map` form. -/

private theorem insertSumList_cons_proj (a : α) (c : Planar α)
    (cs : List (Planar α)) (T₂ : Planar α) :
    (Planar.insertSumList (c :: cs) T₂).map
        (fun cs' => (Nonplanar.mk (Planar.node a cs') : Nonplanar α)) =
      (Planar.insertSum c T₂).map
          (fun c' => Nonplanar.mk (Planar.node a (c' :: cs))) +
        (Planar.insertSumList cs T₂).map
          (fun cs' => Nonplanar.mk (Planar.node a (c :: cs'))) := by
  rw [Planar.insertSumList_cons, Multiset.map_add, Multiset.map_map,
      Multiset.map_map]
  rfl

/-- Companion: `(insertSum (node a cs) T₂).map mk` decomposes as the head
    `mk (node a (T₂ :: cs))` plus the projected tail
    `(insertSumList cs T₂).map (fun cs' => mk (node a cs'))`. -/
private theorem insertSum_node_proj (a : α) (cs : List (Planar α)) (T₂ : Planar α) :
    (Planar.insertSum (Planar.node a cs) T₂).map Nonplanar.mk =
      Nonplanar.mk (Planar.node a (T₂ :: cs)) ::ₘ
        (Planar.insertSumList cs T₂).map
          (fun cs' => Nonplanar.mk (Planar.node a cs')) := by
  rw [Planar.insertSum_node, Multiset.map_cons, Multiset.map_map]
  rfl

/-- Wrapper-shift helper: `(M.map (fun c' => mk (node a (c' :: cs)))) =
    ((M.map mk).map (fun n => mk (node a (n.out :: cs))))`. Used when we
    want to factor the `c' :: cs` wrapper through `mk` so that the inner
    multiset becomes `M.map mk` (a form we can substitute via the IH).
    Implementation: each entry is `Quotient.out`-related to its mk-image. -/
private theorem map_node_cons_via_mk (a : α) (cs : List (Planar α))
    {M : Multiset (Planar α)} :
    M.map (fun c' => Nonplanar.mk (Planar.node a (c' :: cs))) =
      (M.map Nonplanar.mk).map
        (fun n : Nonplanar α =>
          Nonplanar.mk (Planar.node a (n.out :: cs))) := by
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro c' _
  apply Nonplanar.mk_eq_mk_iff.mpr
  apply Planar.planarEquiv_recurse_lift [] cs
  exact (Quotient.exact (Quotient.out_eq (Nonplanar.mk c'))).symm

/-- Wrapper-shift helper for sibling-cons: `(M.map (fun cs' => mk (node a
    (p :: cs')))) = ((M.map (fun cs' => mk (node a cs'))).map (fun n =>
    mk (node a (p :: n.out.children))))`. Used when we want to factor a
    sibling-cons wrapper through `mk ∘ node a` so the IH on `(M.map (mk
    ∘ node a))` substitutes cleanly. The `n.out.children` re-extraction is
    necessary because `node a` only takes a children list. -/
private theorem map_node_sibling_cons_via_mk (a : α) (p : Planar α)
    {M : Multiset (List (Planar α))} :
    M.map (fun cs' => Nonplanar.mk (Planar.node a (p :: cs'))) =
      (M.map (fun cs' => Nonplanar.mk (Planar.node a cs'))).map
        (fun n : Nonplanar α =>
          Nonplanar.mk (Planar.node a (p :: n.out.children))) := by
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro cs' _
  apply Nonplanar.mk_eq_mk_iff.mpr
  have hbase : Planar.PlanarEquiv (Planar.node a cs')
               (Nonplanar.mk (Planar.node a cs')).out :=
    (Quotient.exact (Quotient.out_eq (Nonplanar.mk (Planar.node a cs')))).symm
  have hlabel : (Nonplanar.mk (Planar.node a cs')).out.label = a := by
    have := Planar.planarEquiv_label_eq hbase
    simp only [Planar.label_node] at this
    exact this.symm
  have hform : (Nonplanar.mk (Planar.node a cs')).out =
      Planar.node a (Nonplanar.mk (Planar.node a cs')).out.children := by
    generalize (Nonplanar.mk (Planar.node a cs')).out = q at hlabel
    cases q with
    | node b qs =>
      simp only [Planar.label_node] at hlabel
      rw [hlabel]
      rfl
  have hbase' : Planar.PlanarEquiv (Planar.node a cs')
      (Planar.node a (Nonplanar.mk (Planar.node a cs')).out.children) := by
    rw [← hform]; exact hbase
  exact Planar.planarEquiv_cons_lift p hbase'

/-! ## §2: Right invariance — `T₂ → T₂'`

If `T₂ ≡ T₂'` (PlanarEquiv), then `(T₁ ◁ T₂).map mk = (T₁ ◁ T₂').map mk`
for any T₁. Mutually inducted with the children-list version
`insertSumList`. -/

mutual
/-- Right invariance for `insertSum`: replacing T₂ with a PlanarEquiv-related
    T₂' yields the same multiset of nonplanar grafting summands. Mutually
    inducted with the list version. -/
private theorem insertSum_planarEquiv_right_aux : ∀ (T₁ T₂ T₂' : Planar α)
    (_ : Planar.PlanarEquiv T₂ T₂'),
    (Planar.insertSum T₁ T₂).map Nonplanar.mk =
      (Planar.insertSum T₁ T₂').map Nonplanar.mk
  | .node a cs, T₂, T₂', h => by
    rw [insertSum_node_proj, insertSum_node_proj]
    congr 1
    · -- Head: mk (node a (T₂ :: cs)) = mk (node a (T₂' :: cs)) via recurse_lift.
      apply Nonplanar.mk_eq_mk_iff.mpr
      exact Planar.planarEquiv_recurse_lift [] cs h
    · -- Tail: invariance via the list-version IH.
      exact insertSumList_planarEquiv_right_aux a cs T₂ T₂' h
/-- Right invariance for `insertSumList`: replacing T₂ with a PlanarEquiv-
    related T₂' yields the same multiset of nonplanar tree summands when
    we wrap each result child-list under `node a`. -/
private theorem insertSumList_planarEquiv_right_aux : ∀ (a : α) (cs : List (Planar α))
    (T₂ T₂' : Planar α) (_ : Planar.PlanarEquiv T₂ T₂'),
    (Planar.insertSumList cs T₂).map
        (fun cs' => (Nonplanar.mk (Planar.node a cs') : Nonplanar α)) =
    (Planar.insertSumList cs T₂').map
        (fun cs' => Nonplanar.mk (Planar.node a cs'))
  | _, [], _, _, _ => by
    rw [Planar.insertSumList_nil, Planar.insertSumList_nil]
  | a, c :: cs, T₂, T₂', h => by
    -- Decompose both sides via insertSumList_cons_proj into (head + tail) form.
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    congr 1
    · -- Head: per-c grafting; use IH on c via map_node_cons_via_mk.
      have ih := insertSum_planarEquiv_right_aux c T₂ T₂' h
      rw [map_node_cons_via_mk a cs (M := Planar.insertSum c T₂),
          map_node_cons_via_mk a cs (M := Planar.insertSum c T₂'),
          ih]
    · -- Tail: per-cs grafting; use IH on cs (list version) via map_node_sibling_cons_via_mk.
      have ih_list := insertSumList_planarEquiv_right_aux a cs T₂ T₂' h
      rw [map_node_sibling_cons_via_mk a c (M := Planar.insertSumList cs T₂),
          map_node_sibling_cons_via_mk a c (M := Planar.insertSumList cs T₂'),
          ih_list]
end

/-- Right invariance for `insertSum`. -/
theorem insertSum_planarEquiv_right (T₁ : Planar α) {T₂ T₂' : Planar α}
    (h : Planar.PlanarEquiv T₂ T₂') :
    (Planar.insertSum T₁ T₂).map Nonplanar.mk =
      (Planar.insertSum T₁ T₂').map Nonplanar.mk :=
  insertSum_planarEquiv_right_aux T₁ T₂ T₂' h

/-! ## §3: List-side `mk`-projection of `insertSumList`

Two key properties of `(insertSumList cs T₂).map (mk ∘ .node a)` we
need for the left-invariance proof:

1. **Perm-invariance in `cs`**: `(insertSumList cs T₂)` and
   `(insertSumList cs' T₂)` for `cs.Perm cs'` produce the same
   multiset after `mk ∘ .node a` projection.

2. **Componentwise PlanarEquiv-invariance in `cs`**: replacing one
   entry of `cs` with a PlanarEquiv-related entry preserves the
   `mk`-projected multiset.

These are independent of the right-invariance machinery from §2 — for
these specific lemmas we only need PlanarStep-on-T₁, not on T₂. -/

/-- Helper: a PlanarEquiv between cs lists at the root level
    (`node a cs ≡ node a cs'`) lifts to identity on
    `(insertSumList cs T₂).map (mk ∘ node a)` whenever the planar
    insertSumList multisets project the same. -/
private theorem insertSumList_proj_perm_aux (a : α) (T₂ : Planar α) :
    ∀ {cs cs' : List (Planar α)},
      cs.Perm cs' →
      (Planar.insertSumList cs T₂).map
          (fun cs' => (Nonplanar.mk (Planar.node a cs') : Nonplanar α)) =
      (Planar.insertSumList cs' T₂).map
          (fun cs' => Nonplanar.mk (Planar.node a cs')) := by
  intro cs cs' h
  induction h with
  | nil => rfl
  | @cons x cs cs' hperm ih =>
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    -- Head: substitute cs <-> cs' inside the wrapper using planarEquiv_root_perm.
    have head_eq :
        (Planar.insertSum x T₂).map
          (fun c' => Nonplanar.mk (Planar.node a (c' :: cs))) =
        (Planar.insertSum x T₂).map
          (fun c' => Nonplanar.mk (Planar.node a (c' :: cs'))) := by
      apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_root_perm
      exact List.Perm.cons c' hperm
    -- Tail: factor the (x :: ·) wrapper out via `map_node_sibling_cons_via_mk`,
    -- then substitute via `ih`.
    rw [head_eq,
        map_node_sibling_cons_via_mk a x (M := Planar.insertSumList cs T₂),
        map_node_sibling_cons_via_mk a x (M := Planar.insertSumList cs' T₂),
        ih]
  | @swap x y cs =>
    -- Swap: x :: y :: cs vs y :: x :: cs.
    -- We avoid `simp only`'s lambda-handling subtleties by using
    -- `insertSumList_cons_proj` (already proved) twice on each side via
    -- intermediate explicit-shape lemmas. The wrappers differ — this cons
    -- helper handles them via auxiliary `cons_proj_inner` step lemmas.
    --
    -- LHS unfolds via `cons_proj` once: A + cs_remaining_lhs
    -- cs_remaining_lhs unfolds further to: B + C  (with cs eventually empty/recursing)
    --
    -- We unfold both sides in tandem and use a private cons-decomp helper.
    have lhs_eq :
        (Planar.insertSumList (x :: y :: cs) T₂).map
            (fun cs' => Nonplanar.mk (Planar.node a cs')) =
          (Planar.insertSum x T₂).map
              (fun c' => Nonplanar.mk (Planar.node a (c' :: y :: cs))) +
            (Planar.insertSumList (y :: cs) T₂).map
              (fun cs' => Nonplanar.mk (Planar.node a (x :: cs'))) := by
      exact insertSumList_cons_proj a x (y :: cs) T₂
    have rhs_eq :
        (Planar.insertSumList (y :: x :: cs) T₂).map
            (fun cs' => Nonplanar.mk (Planar.node a cs')) =
          (Planar.insertSum y T₂).map
              (fun c' => Nonplanar.mk (Planar.node a (c' :: x :: cs))) +
            (Planar.insertSumList (x :: cs) T₂).map
              (fun cs' => Nonplanar.mk (Planar.node a (y :: cs'))) := by
      exact insertSumList_cons_proj a y (x :: cs) T₂
    -- Now further unfold the inner insertSumList using insertSumList_cons.
    have lhs_inner :
        (Planar.insertSumList (y :: cs) T₂).map
            (fun cs' => Nonplanar.mk (Planar.node a (x :: cs'))) =
          (Planar.insertSum y T₂).map
              (fun c' => Nonplanar.mk (Planar.node a (x :: c' :: cs))) +
            (Planar.insertSumList cs T₂).map
              (fun cs' => Nonplanar.mk (Planar.node a (x :: y :: cs'))) := by
      rw [Planar.insertSumList_cons, Multiset.map_add, Multiset.map_map,
          Multiset.map_map]
      rfl
    have rhs_inner :
        (Planar.insertSumList (x :: cs) T₂).map
            (fun cs' => Nonplanar.mk (Planar.node a (y :: cs'))) =
          (Planar.insertSum x T₂).map
              (fun c' => Nonplanar.mk (Planar.node a (y :: c' :: cs))) +
            (Planar.insertSumList cs T₂).map
              (fun cs' => Nonplanar.mk (Planar.node a (y :: x :: cs'))) := by
      rw [Planar.insertSumList_cons, Multiset.map_add, Multiset.map_map,
          Multiset.map_map]
      rfl
    rw [lhs_eq, rhs_eq, lhs_inner, rhs_inner]
    -- LHS and RHS now: A + (B + C) vs A' + (B' + C')
    -- A := (insertSum x T₂).map (fun c' => mk (node a (c' :: y :: cs)))
    -- B := (insertSum y T₂).map (fun c' => mk (node a (x :: c' :: cs)))
    -- C := (insertSumList cs T₂).map (fun cs' => mk (node a (x :: y :: cs')))
    -- A':= (insertSum y T₂).map (fun c' => mk (node a (c' :: x :: cs)))
    -- B':= (insertSum x T₂).map (fun c' => mk (node a (y :: c' :: cs)))
    -- C':= (insertSumList cs T₂).map (fun cs' => mk (node a (y :: x :: cs')))
    -- Pointwise: A = B', B = A', C = C' (each via planarEquiv_root_perm).
    have hAB' : (Planar.insertSum x T₂).map
                  (fun c' => Nonplanar.mk (Planar.node a (c' :: y :: cs))) =
                (Planar.insertSum x T₂).map
                  (fun c' => Nonplanar.mk (Planar.node a (y :: c' :: cs))) := by
      apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_root_perm
      exact List.Perm.swap _ _ _
    have hBA' : (Planar.insertSum y T₂).map
                  (fun c' => Nonplanar.mk (Planar.node a (x :: c' :: cs))) =
                (Planar.insertSum y T₂).map
                  (fun c' => Nonplanar.mk (Planar.node a (c' :: x :: cs))) := by
      apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_root_perm
      exact List.Perm.swap _ _ _
    have hCC' : (Planar.insertSumList cs T₂).map
                  (fun cs' => Nonplanar.mk (Planar.node a (x :: y :: cs'))) =
                (Planar.insertSumList cs T₂).map
                  (fun cs' => Nonplanar.mk (Planar.node a (y :: x :: cs'))) := by
      apply Multiset.map_congr rfl
      intro cs' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_root_perm
      exact List.Perm.swap _ _ _
    rw [hAB', hBA', hCC']
    -- After rewrites, LHS = A' + (B' + C'), RHS = B' + (A' + C').
    -- Multiset is an AddCancelCommMonoid; AC reasoning closes.
    abel
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## §4: Left invariance — `T₁ → T₁'` via PlanarStep induction

The substantive content. Inducted on the step constructor. The
`swapAtRoot` case uses §3's `insertSumList_proj_perm_aux`; the
`recurse` case uses the IH plus a per-child PlanarEquiv lift through
the list-version helper `insertSumList_planarStep_at_aux`. -/

/-- List version helper: replacing one entry of cs (at position pre.length)
    with a PlanarStep-related entry preserves the mk-projection of
    insertSumList, given the corresponding PlanarStep-projected insertSum
    equality and the Nonplanar-mk equality of the entries.

    Inducted on `pre`. Used in the `recurse` case of
    `insertSum_planarStep_left`. -/
private theorem insertSumList_planarStep_at_aux : ∀ (a : α) (T₂ : Planar α)
    (pre : List (Planar α)) (post : List (Planar α)) (old new : Planar α),
    (Planar.insertSum old T₂).map Nonplanar.mk =
      (Planar.insertSum new T₂).map Nonplanar.mk →
    Nonplanar.mk old = Nonplanar.mk new →
    (Planar.insertSumList (pre ++ old :: post) T₂).map
        (fun cs' => (Nonplanar.mk (Planar.node a cs') : Nonplanar α)) =
    (Planar.insertSumList (pre ++ new :: post) T₂).map
        (fun cs' => Nonplanar.mk (Planar.node a cs'))
  | a, T₂, [], post, old, new, ih_sub, h_mk => by
    -- pre = [], so the lists are old :: post and new :: post.
    simp only [List.nil_append]
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    congr 1
    · -- Head: substitute via ih_sub through map_node_cons_via_mk.
      rw [map_node_cons_via_mk a post (M := Planar.insertSum old T₂),
          map_node_cons_via_mk a post (M := Planar.insertSum new T₂),
          ih_sub]
    · -- Tail: pointwise via h_mk + recurse_lift on the (old/new :: cs') position.
      apply Multiset.map_congr rfl
      intro cs' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_recurse_lift [] cs'
      exact Nonplanar.mk_eq_mk_iff.mp h_mk
  | a, T₂, p :: pre', post, old, new, ih_sub, h_mk => by
    show (Planar.insertSumList (p :: (pre' ++ old :: post)) T₂).map
            (fun cs' => Nonplanar.mk (Planar.node a cs')) =
         (Planar.insertSumList (p :: (pre' ++ new :: post)) T₂).map
            (fun cs' => Nonplanar.mk (Planar.node a cs'))
    rw [insertSumList_cons_proj, insertSumList_cons_proj]
    congr 1
    · -- Head: pointwise via h_mk + recurse_lift on the (c' :: pre' ++ old/new :: post) position.
      apply Multiset.map_congr rfl
      intro c' _
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_recurse_lift (c' :: pre') post
      exact Nonplanar.mk_eq_mk_iff.mp h_mk
    · -- Tail: by recursive call on `pre'` plus map_node_sibling_cons_via_mk
      -- to factor the (p :: ·) wrapper out.
      have ih_tail := insertSumList_planarStep_at_aux a T₂ pre' post old new ih_sub h_mk
      rw [map_node_sibling_cons_via_mk a p
            (M := Planar.insertSumList (pre' ++ old :: post) T₂),
          map_node_sibling_cons_via_mk a p
            (M := Planar.insertSumList (pre' ++ new :: post) T₂),
          ih_tail]

/-- Left invariance for `insertSum` under a single PlanarStep on T₁.
    Inducted on the step constructor; the recurse case uses the
    auto-generated IH. -/
theorem insertSum_planarStep_left {T₁ T₁' : Planar α}
    (h : Planar.PlanarStep T₁ T₁') (T₂ : Planar α) :
    (Planar.insertSum T₁ T₂).map Nonplanar.mk =
      (Planar.insertSum T₁' T₂).map Nonplanar.mk := by
  induction h with
  | @swapAtRoot a l r pre post =>
    -- T₁ = node a (pre ++ l :: r :: post); T₁' = node a (pre ++ r :: l :: post).
    rw [insertSum_node_proj, insertSum_node_proj]
    congr 1
    · -- Head: mk (node a (T₂ :: pre ++ l :: r :: post)) =
      --       mk (node a (T₂ :: pre ++ r :: l :: post)) via root-perm.
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_root_perm
      apply List.Perm.cons
      exact List.Perm.append_left pre (List.Perm.swap r l post)
    · -- Tail: insertSumList-perm on cs.
      have hperm : (pre ++ l :: r :: post).Perm (pre ++ r :: l :: post) :=
        List.Perm.append_left pre (List.Perm.swap r l post)
      exact insertSumList_proj_perm_aux a T₂ hperm
  | @recurse a pre old new post hsub ih =>
    -- T₁ = node a (pre ++ old :: post); T₁' = node a (pre ++ new :: post).
    -- Auto-generated IH from `induction h`:
    --   ih : (insertSum old T₂).map mk = (insertSum new T₂).map mk
    have h_mk : Nonplanar.mk old = Nonplanar.mk new :=
      Nonplanar.mk_eq_mk_iff.mpr (Planar.PlanarEquiv.of_step hsub)
    rw [insertSum_node_proj, insertSum_node_proj]
    congr 1
    · -- Head: mk (node a (T₂ :: pre ++ old :: post)) =
      --       mk (node a (T₂ :: pre ++ new :: post)) via recurse-lift on old/new
      --       at position |pre|+1.
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_recurse_lift (T₂ :: pre) post
      exact Planar.PlanarEquiv.of_step hsub
    · -- Tail: insertSumList-componentwise (via the list-version helper).
      exact insertSumList_planarStep_at_aux a T₂ pre post old new ih h_mk

/-! ## §5: EqvGen lift to `PlanarEquiv` -/

/-- Left invariance under `PlanarEquiv` on T₁. Standard `EqvGen` recipe. -/
theorem insertSum_planarEquiv_left {T₁ T₁' : Planar α}
    (h : Planar.PlanarEquiv T₁ T₁') (T₂ : Planar α) :
    (Planar.insertSum T₁ T₂).map Nonplanar.mk =
      (Planar.insertSum T₁' T₂).map Nonplanar.mk := by
  induction h with
  | rel _ _ hstep => exact insertSum_planarStep_left hstep T₂
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## §6: Native `Nonplanar.insertSum` via `Quotient.lift₂` -/

/-- The **vertex-grafting pre-Lie product on `Nonplanar α`**: lifted from
    the planar `Planar.insertSum` via `Quotient.lift₂`, using the
    invariance lemmas from §2 and §5. -/
def insertSum : Nonplanar α → Nonplanar α → Multiset (Nonplanar α) :=
  Quotient.lift₂
    (fun (t₁ t₂ : Planar α) => (Planar.insertSum t₁ t₂).map Nonplanar.mk)
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => by
      -- Need: (insertSum a₁ a₂).map mk = (insertSum b₁ b₂).map mk
      -- via two steps: a₁ ≡ b₁ (left), a₂ ≡ b₂ (right).
      have step1 : (Planar.insertSum a₁ a₂).map Nonplanar.mk =
                   (Planar.insertSum b₁ a₂).map Nonplanar.mk :=
        insertSum_planarEquiv_left h₁ a₂
      have step2 : (Planar.insertSum b₁ a₂).map Nonplanar.mk =
                   (Planar.insertSum b₁ b₂).map Nonplanar.mk :=
        insertSum_planarEquiv_right b₁ h₂
      exact step1.trans step2)

/-- Notation `T₁ ◁ T₂` for `Nonplanar.insertSum T₁ T₂`. Scoped to the
    `Nonplanar` namespace to coexist with the planar `◁` from
    `Defs.lean`. -/
scoped infixl:65 " ◁ " => Nonplanar.insertSum

/-! ## §7: Quotient-unfolding lemma -/

/-- Quotient unfolding: `Nonplanar.insertSum (mk t₁) (mk t₂)` is the
    multiset of nonplanar grafting summands obtained by projecting the
    planar grafting summands. -/
@[simp] theorem mk_insertSum (t₁ t₂ : Planar α) :
    Nonplanar.insertSum (Nonplanar.mk t₁) (Nonplanar.mk t₂) =
      (Planar.insertSum t₁ t₂).map Nonplanar.mk := rfl

/-! ## §8: Cardinality + sanity tests -/

/-- The number of summands of `T₁ ◁ T₂` equals `T₁.weight`, i.e., the
    nonplanar tree-vertex count of T₁. Direct corollary of the planar
    `card_insertSum_eq_weight` plus the lifted `Nonplanar.weight`. -/
theorem card_insertSum_eq_weight (T₁ T₂ : Nonplanar α) :
    Multiset.card (Nonplanar.insertSum T₁ T₂) = T₁.weight := by
  refine Quotient.inductionOn₂ T₁ T₂ ?_
  intro t₁ t₂
  show Multiset.card ((Planar.insertSum t₁ t₂).map Nonplanar.mk) = (Nonplanar.mk t₁).weight
  rw [Multiset.card_map, Planar.card_insertSum_eq_weight]
  rfl

section Tests

/-- A leaf grafted onto a leaf gives the canonical 1-vertex grafting summand. -/
example : Nonplanar.insertSum (Nonplanar.leaf 1 : Nonplanar Nat) (Nonplanar.leaf 2)
    = ({Nonplanar.mk (Planar.node 1 [Planar.leaf 2])} : Multiset (Nonplanar Nat)) := by
  show (Planar.insertSum (Planar.leaf 1) (Planar.leaf 2)).map Nonplanar.mk = _
  rw [Planar.insertSum_leaf, Multiset.map_singleton]

/-- A nonplanar binary tree has 3 vertices, hence 3 grafting summands. -/
example : Multiset.card
    (Nonplanar.insertSum
      (Nonplanar.mk (Planar.binary 1 (Planar.leaf 2) (Planar.leaf 3)))
      (Nonplanar.leaf 4 : Nonplanar Nat)) = 3 := by
  rw [card_insertSum_eq_weight]
  show (Nonplanar.mk (Planar.binary 1 (Planar.leaf 2) (Planar.leaf 3))).weight = 3
  show (Planar.binary 1 (Planar.leaf 2) (Planar.leaf 3) : Planar Nat).weight = 3
  unfold Planar.binary Planar.leaf Planar.weight Planar.weightList; rfl

end Tests

end Nonplanar

end RootedTree
