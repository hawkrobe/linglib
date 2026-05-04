import Linglib.Core.Algebra.ConnesKreimer.LhsIndex
import Linglib.Core.Algebra.ConnesKreimer.DoubleCut

/-!
# Bridge: `lhsRealCuts T = LhsIndex.tripleTensor` sum
@cite{marcolli-chomsky-berwick-2025} @cite{marcolli-skigin-2025}

The substantive bridge between the existing `Sections`-based LHS double-cut
enumeration (`lhsRealCuts T` in `DoubleCut.lean`) and the new structurally
indexed enumeration (`LhsIndex T` in `LhsIndex.lean`).

**Theorem**: `lhsRealCuts T = (Finset.univ : Finset (LhsIndex T)).val.map
(LhsIndex.tripleTensor R)`.

**Proof strategy**: factor through `perLayerContrib_top` (already proven in
`DoubleCut.lean`). The bridge reduces to a purely combinatorial identity at the
`(botForest, midForest, remainder)` triple level, which is proven via:

1. A per-`cl_outer` factoring (`perCutShape_pair_bridge`): for each
   `cl_outer : CutShape T`, the LHS section structure equals the
   `lhsAllWithMS cl_outer` enumeration's `(botForest, midForest)` projection.
   Proven by induction on `cl_outer`.

2. The partition `(univ : LhsIndex T) = ⋃ cl_outer, allWith T cl_outer`
   (`lhsIndex_univ_eq_bind`, disjoint union).

3. The Multiset-form correspondence `lhsAllWithMS = (allWith T cl).val`
   (`lhsAllWithMS_eq_allWith_val`).

## Status

Complete. All four `.node` sub-cases of `perCutShape_pair_bridge` (§2) close
via the same pattern: expand `Sections` via `sections_cons`/`sections_add`,
apply `Multiset.bind_map` + `Multiset.map_bind` + `Multiset.map_map` to reorder,
apply IH for recursive cases, match per-element via `pairsMS = univ.val.map
(cf_aug, rem)`.

## Layer status

`[UPSTREAM]` candidate, paired with `LhsIndex.lean`. Future home:
`Mathlib.Combinatorics.HopfAlgebra.ConnesKreimer.LhsBridge`.
-/

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ## §1: Multiset reformulation of `LhsIndex.allWith`

To work cleanly with multiset bind/map (avoiding `Finset.image_val` dedup
considerations), reformulate `allWith T cl_outer` as a `Multiset (LhsIndex T)`
via direct bind/map operations. The bridge then equates these multiset forms. -/

/-- Multiset version of `LhsIndex.allWith T cl_outer`'s underlying multiset.
    Defined directly to avoid `Finset.image_val` dedup considerations. -/
def lhsAllWithMS : ∀ {T : TraceTree α Unit} (_ : CutShape T), Multiset (LhsIndex T)
  | .leaf _, .atLeaf => ({.atLeaf} : Multiset _)
  | .trace _, .atTrace => ({.atTrace} : Multiset _)
  | .node l _, .bothCut hl hr =>
      (Finset.univ : Finset (AugCutShape l)).val.bind fun ac_l =>
        (Finset.univ : Finset (AugCutShape _)).val.map fun ac_r =>
          LhsIndex.bothCut hl hr ac_l ac_r
  | .node l _, .onlyLeftCut hl cr =>
      (Finset.univ : Finset (AugCutShape l)).val.bind fun ac_l =>
        (lhsAllWithMS cr).map fun rhs => LhsIndex.onlyLeftCut hl ac_l rhs
  | .node _ r, .onlyRightCut hr cl =>
      (lhsAllWithMS cl).bind fun lhs =>
        (Finset.univ : Finset (AugCutShape r)).val.map fun ac_r =>
          LhsIndex.onlyRightCut hr lhs ac_r
  | .node _ _, .bothRecurse cl cr =>
      (lhsAllWithMS cl).bind fun lhs =>
        (lhsAllWithMS cr).map fun rhs => LhsIndex.bothRecurse lhs rhs

/-- Mapping a binary function across a multiset product equals binding then
    mapping per-component. Mathlib gap (parallel to `_root_.Multiset.Sections_map_map`
    in `DoubleCut.lean` — both `[UPSTREAM]` candidates). -/
theorem _root_.Multiset.map_product_eq_bind {α β γ : Type*} (s : Multiset α) (t : Multiset β)
    (f : α → β → γ) :
    (s ×ˢ t).map (fun p => f p.1 p.2) = s.bind fun a => t.map fun b => f a b := by
  show (s.bind fun a => t.map (Prod.mk a)).map (fun p => f p.1 p.2) = _
  rw [Multiset.map_bind]
  refine Multiset.bind_congr (fun a _ => ?_)
  rw [Multiset.map_map]
  rfl

/-- The multiset reformulation `lhsAllWithMS` matches the underlying multiset of
    `LhsIndex.allWith T cl_outer`. The Finset image is injective. -/
theorem lhsAllWithMS_eq_allWith_val {T : TraceTree α Unit} (cl_outer : CutShape T) :
    lhsAllWithMS cl_outer = (LhsIndex.allWith T cl_outer).val := by
  induction cl_outer with
  | atLeaf => rfl
  | atTrace => rfl
  | @bothCut l r hl hr =>
    show ((Finset.univ : Finset (AugCutShape l)).val.bind fun ac_l =>
          (Finset.univ : Finset (AugCutShape r)).val.map fun ac_r =>
            LhsIndex.bothCut hl hr ac_l ac_r) = _
    rw [show (LhsIndex.allWith (.node l r) (CutShape.bothCut hl hr) :
              Finset (LhsIndex (.node l r))).val
          = (((Finset.univ : Finset (AugCutShape l)) ×ˢ
              (Finset.univ : Finset (AugCutShape r))).val.map fun p =>
              LhsIndex.bothCut hl hr p.1 p.2) from
        Finset.image_val_of_injOn (fun p _ q _ h => by
          obtain ⟨a, b⟩ := p
          obtain ⟨c, d⟩ := q
          cases h
          rfl)]
    rw [Finset.product_val]
    exact (Multiset.map_product_eq_bind _ _ _).symm
  | @onlyLeftCut l r hl cr ih =>
    show ((Finset.univ : Finset (AugCutShape l)).val.bind fun ac_l =>
          (lhsAllWithMS cr).map fun rhs =>
            LhsIndex.onlyLeftCut hl ac_l rhs) = _
    rw [ih]
    rw [show (LhsIndex.allWith (.node l r) (CutShape.onlyLeftCut hl cr) :
              Finset (LhsIndex (.node l r))).val
          = (((Finset.univ : Finset (AugCutShape l)) ×ˢ
              (LhsIndex.allWith r cr)).val.map fun p =>
              LhsIndex.onlyLeftCut hl p.1 p.2) from
        Finset.image_val_of_injOn (fun p _ q _ h => by
          obtain ⟨a, b⟩ := p
          obtain ⟨c, d⟩ := q
          cases h
          rfl)]
    rw [Finset.product_val]
    exact (Multiset.map_product_eq_bind _ _ _).symm
  | @onlyRightCut l r hr cl ih =>
    show ((lhsAllWithMS cl).bind fun lhs =>
          (Finset.univ : Finset (AugCutShape r)).val.map fun ac_r =>
            LhsIndex.onlyRightCut hr lhs ac_r) = _
    rw [ih]
    rw [show (LhsIndex.allWith (.node l r) (CutShape.onlyRightCut hr cl) :
              Finset (LhsIndex (.node l r))).val
          = (((LhsIndex.allWith l cl) ×ˢ
              (Finset.univ : Finset (AugCutShape r))).val.map fun p =>
              LhsIndex.onlyRightCut hr p.1 p.2) from
        Finset.image_val_of_injOn (fun p _ q _ h => by
          obtain ⟨a, b⟩ := p
          obtain ⟨c, d⟩ := q
          cases h
          rfl)]
    rw [Finset.product_val]
    exact (Multiset.map_product_eq_bind _ _ _).symm
  | @bothRecurse l r cl cr ih_l ih_r =>
    show ((lhsAllWithMS cl).bind fun lhs =>
          (lhsAllWithMS cr).map fun rhs =>
            LhsIndex.bothRecurse lhs rhs) = _
    rw [ih_l, ih_r]
    rw [show (LhsIndex.allWith (.node l r) (CutShape.bothRecurse cl cr) :
              Finset (LhsIndex (.node l r))).val
          = (((LhsIndex.allWith l cl) ×ˢ
              (LhsIndex.allWith r cr)).val.map fun p =>
              LhsIndex.bothRecurse p.1 p.2) from
        Finset.image_val_of_injOn (fun p _ q _ h => by
          obtain ⟨a, b⟩ := p
          obtain ⟨c, d⟩ := q
          cases h
          rfl)]
    rw [Finset.product_val]
    exact (Multiset.map_product_eq_bind _ _ _).symm

/-! ## §2: Per-`cl_outer` bridge lemma at the `(botForest, midForest)` pair level

For each `cl_outer : CutShape T`, the multi-tree `Sections` over `pairsMS` gives
a multiset of `(TraceForest × TraceForest)` pairs (after summing each section's
first and second components) that exactly matches the `(botForest, midForest)` projection
of `lhsAllWithMS cl_outer`.

The base cases (`atLeaf`, `atTrace`) are proven by direct reduction. The four
`.node` sub-cases (one per CutShape constructor) each follow the pattern:

1. **bothCut** — no recursion. `cutForest = {l, r}`. Sections of a 2-tree
   forest give all `(a, b)` pairs from `pairsMS l × pairsMS r`. Match via:
   * `pairsMS T = (univ : AugCutShape T).val.map (cf_aug, rem)`
   * `botForest (bothCut hl hr ac_l ac_r) = cf_aug ac_l + cf_aug ac_r`
   * `midForest = rem ac_l + rem ac_r`.

2. **onlyLeftCut** — recursion on `r`. `cutForest = {l} + cutForest cr`.
   Use `Multiset.sections_add` to split, IH on `cr` at the `(s.fsts.sum, s.snds.sum)`
   level (factored via `Multiset.map_map`), then match per-`(ac_l, rhs)`.

3. **onlyRightCut** — symmetric to `onlyLeftCut`, recursion on `l`.

4. **bothRecurse** — recursion on both. `cutForest = cutForest cl + cutForest cr`.
   Use `sections_add` + IH on both sides + match. -/

/-- The per-`cl_outer` Forest-pair bridge: Sections over `(cutForest cl_outer).map pairsMS`
    matches `lhsAllWithMS cl_outer` at the `(botForest, midForest)` level. -/
theorem perCutShape_pair_bridge {T : TraceTree α Unit} (cl_outer : CutShape T) :
    (Multiset.Sections ((CutShape.cutForest cl_outer).map (pairsMS (α := α)))).map
      (fun s => ((s.map Prod.fst).sum, (s.map Prod.snd).sum))
    = (lhsAllWithMS cl_outer).map
      (fun rhs => (LhsIndex.botForest rhs, LhsIndex.midForest rhs)) := by
  induction cl_outer with
  | atLeaf =>
    show (Multiset.Sections (((0 : Multiset _).map (pairsMS (α := α))))).map _ = _
    rw [Multiset.map_zero, Multiset.sections_zero, Multiset.map_singleton]
    rfl
  | atTrace =>
    show (Multiset.Sections (((0 : Multiset _).map (pairsMS (α := α))))).map _ = _
    rw [Multiset.map_zero, Multiset.sections_zero, Multiset.map_singleton]
    rfl
  | @bothCut l r hl hr =>
    -- Strategy: convert both sides to a bind-of-bind-of-singleton form, then match.
    -- LHS: Sections (({l, r}).map pairsMS) .map (s => (s.fsts.sum, s.snds.sum))
    --   After expand Sections: ((pairsMS l).bind a => ((pairsMS r).bind b => {b ::ₘ 0}).map (cons a)).map (s => ...)
    --   After Multiset.map_bind, Multiset.map_singleton, Multiset.bind_singleton, etc:
    --   = (pairsMS l).bind a => (pairsMS r).bind b => {(a.1 + b.1, a.2 + b.2)}
    -- RHS: lhsAllWithMS (bothCut hl hr).map (botForest, midForest)
    --   = (univ_l.val.bind ac_l => univ_r.val.map ac_r => bothCut hl hr ac_l ac_r) .map (botForest, midForest)
    --   = univ_l.val.bind ac_l => univ_r.val.bind ac_r => {(cf_aug ac_l + cf_aug ac_r, rem ac_l + rem ac_r)}
    --     [via Multiset.map_bind + Multiset.bind_singleton]
    -- Match via pairsMS = univ.val.map (cf_aug, rem) and Multiset.bind_map.
    show (Multiset.Sections (({l, r} : TraceForest α Unit).map (pairsMS (α := α)))).map _ = _
    rw [show ({l, r} : Multiset (TraceTree α Unit))
            = l ::ₘ ({r} : Multiset (TraceTree α Unit)) from rfl,
        Multiset.map_cons, Multiset.sections_cons,
        show ({r} : Multiset (TraceTree α Unit)).map (pairsMS (α := α))
            = (pairsMS r) ::ₘ (0 : Multiset _) from rfl,
        Multiset.sections_cons, Multiset.sections_zero]
    -- LHS now: ((pairsMS l).bind a => ((pairsMS r).bind b => Multiset.map (cons b) {0}).map (cons a)).map ...
    simp only [Multiset.map_singleton]
    -- Now: ((pairsMS l).bind a => ((pairsMS r).bind b => {b ::ₘ 0}).map (cons a)).map ...
    -- bind_singleton: (pairsMS r).bind b => {b ::ₘ 0} = (pairsMS r).map (b => b ::ₘ 0)
    simp only [Multiset.bind_singleton]
    -- Now: ((pairsMS l).bind a => Multiset.map (fun x => a ::ₘ x) (Multiset.map (fun x => x ::ₘ 0) (pairsMS r))).map (s => ...)
    -- Use simp_rw to rewrite under the bind binder.
    simp_rw [show (∀ a : TraceForest α Unit × TraceForest α Unit,
              (Multiset.map (fun x => a ::ₘ x)
                (Multiset.map (fun x => (x ::ₘ (0 : Multiset _))) (pairsMS r)))
              = Multiset.map (fun x => (a ::ₘ x ::ₘ (0 : Multiset _))) (pairsMS r))
            from fun a => by
        rw [Multiset.map_map]
        rfl]
    -- Now: ((pairsMS l).bind a => (pairsMS r).map (b => a ::ₘ b ::ₘ 0)).map (s => ...)
    rw [Multiset.map_bind]
    -- Now: (pairsMS l).bind a => ((pairsMS r).map (b => a ::ₘ b ::ₘ 0)).map (s => ...)
    -- Use simp_rw to rewrite under the bind binder.
    simp_rw [show (∀ a : TraceForest α Unit × TraceForest α Unit,
              Multiset.map (fun s => ((s.map Prod.fst).sum, (s.map Prod.snd).sum))
                (Multiset.map (fun x => (a ::ₘ x ::ₘ (0 : Multiset _))) (pairsMS r))
              = Multiset.map (fun b => (a.1 + b.1, a.2 + b.2)) (pairsMS r))
            from fun a => by
        rw [Multiset.map_map]
        refine Multiset.map_congr rfl (fun b _ => ?_)
        show ((((a ::ₘ b ::ₘ (0 : Multiset _)).map Prod.fst).sum,
              ((a ::ₘ b ::ₘ (0 : Multiset _)).map Prod.snd).sum) : _ × _) = _
        rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_zero,
            Multiset.sum_cons, Multiset.sum_cons, Multiset.sum_zero, add_zero,
            Multiset.map_cons, Multiset.map_cons, Multiset.map_zero,
            Multiset.sum_cons, Multiset.sum_cons, Multiset.sum_zero, add_zero]]
    -- LHS: (pairsMS l).bind a => (pairsMS r).map (b => (a.1 + b.1, a.2 + b.2))
    -- RHS:
    show _ = (lhsAllWithMS (CutShape.bothCut hl hr) : Multiset _).map _
    rw [show (lhsAllWithMS (CutShape.bothCut hl hr) : Multiset (LhsIndex (.node l r)))
          = ((Finset.univ : Finset (AugCutShape l)).val.bind fun ac_l =>
              (Finset.univ : Finset (AugCutShape r)).val.map fun ac_r =>
                LhsIndex.bothCut hl hr ac_l ac_r) from rfl]
    rw [Multiset.map_bind]
    -- RHS: univ_l.val.bind ac_l => (univ_r.val.map ac_r => bothCut hl hr ac_l ac_r).map (botForest, midForest)
    --    = univ_l.val.bind ac_l => univ_r.val.map ac_r => (botForest (bothCut hl hr ac_l ac_r), midForest (...))
    --    = univ_l.val.bind ac_l => univ_r.val.map ac_r => (cf_aug ac_l + cf_aug ac_r, rem ac_l + rem ac_r)
    -- LHS: pairsMS l = univ_l.val.map (cf_aug, rem). So:
    show ((((Finset.univ : Finset (AugCutShape l)).val.map fun ac =>
            (AugCutShape.cutForest_aug ac, AugCutShape.remainderForest ac))).bind fun a =>
            (pairsMS r).map fun b => (a.1 + b.1, a.2 + b.2)) = _
    rw [Multiset.bind_map]
    refine Multiset.bind_congr (fun ac_l _ => ?_)
    -- Per ac_l: ((Finset.univ : Finset (AugCutShape r)).val.map (cf_aug, rem)).map (b => (cf_aug ac_l + b.1, rem ac_l + b.2))
    --        = univ_r.val.map (ac_r => bothCut hl hr ac_l ac_r) .map (botForest, midForest)
    show ((Finset.univ : Finset (AugCutShape r)).val.map (fun ac =>
            (AugCutShape.cutForest_aug ac, AugCutShape.remainderForest ac))).map (fun b =>
            (AugCutShape.cutForest_aug ac_l + b.1, AugCutShape.remainderForest ac_l + b.2)) = _
    rw [Multiset.map_map, Multiset.map_map]
    rfl
  | @onlyLeftCut l r hl cr ih =>
    -- cutForest (onlyLeftCut hl cr) = ({l} : Multiset _) + cutForest cr
    show (Multiset.Sections ((((({l} : Multiset _) + CutShape.cutForest cr)).map
            (pairsMS (α := α))))).map _ = _
    rw [Multiset.map_add, Multiset.sections_add,
        show (({l} : Multiset (TraceTree α Unit)).map (pairsMS (α := α)))
            = (pairsMS l) ::ₘ (0 : Multiset _) from rfl,
        Multiset.sections_cons, Multiset.sections_zero]
    -- Goal: ((pairsMS l).bind a => Multiset.map (cons a) {0}).bind fun m => Multiset.map (m + ·) (Sections ...) .map (s => ...)
    simp only [Multiset.map_singleton, Multiset.bind_singleton]
    -- After: ((pairsMS l).map (a => a ::ₘ 0)).bind (fun m => Multiset.map (m + ·) (Sections ...)) .map (s => ...)
    rw [Multiset.bind_map]
    -- After: ((pairsMS l).bind (a => Multiset.map ((a ::ₘ 0) + ·) (Sections ...))) .map (s => ...)
    rw [Multiset.map_bind]
    -- After: (pairsMS l).bind (a => (Multiset.map ((a ::ₘ 0) + ·) (Sections ...)) .map (s => ...))
    -- Apply Multiset.map_map twice + simplify (a ::ₘ 0 + s_cr) = a ::ₘ s_cr to factor for IH:
    --   .map (s => (s.fsts.sum, s.snds.sum)) ∘ .map (x => (a ::ₘ 0) + x)
    -- = .map (fun x => (((a ::ₘ 0) + x).fsts.sum, ((a ::ₘ 0) + x).snds.sum))
    -- = .map (fun x => (a.1 + x.fsts.sum, a.2 + x.snds.sum))
    -- = .map (s => (s.fsts.sum, s.snds.sum)) .map (p => (a.1 + p.1, a.2 + p.2))
    simp_rw [show (∀ a : TraceForest α Unit × TraceForest α Unit,
              Multiset.map (fun s => ((s.map Prod.fst).sum, (s.map Prod.snd).sum))
                (Multiset.map (fun x => (a ::ₘ (0 : Multiset _)) + x)
                  (Multiset.Sections ((CutShape.cutForest cr).map (pairsMS (α := α)))))
              = Multiset.map (fun p => (a.1 + p.1, a.2 + p.2))
                  (Multiset.map (fun s => ((s.map Prod.fst).sum, (s.map Prod.snd).sum))
                    (Multiset.Sections ((CutShape.cutForest cr).map (pairsMS (α := α))))))
            from fun a => by
        rw [Multiset.map_map, Multiset.map_map]
        refine Multiset.map_congr rfl (fun s_cr _ => ?_)
        show ((((a ::ₘ (0 : Multiset _)) + s_cr).map Prod.fst).sum,
              (((a ::ₘ (0 : Multiset _)) + s_cr).map Prod.snd).sum) =
              ((fun p : TraceForest α Unit × TraceForest α Unit =>
                  (a.1 + p.1, a.2 + p.2)) ∘
                (fun s : Multiset (TraceForest α Unit × TraceForest α Unit) =>
                  ((s.map Prod.fst).sum, (s.map Prod.snd).sum))) s_cr
        show ((((a ::ₘ (0 : Multiset _)) + s_cr).map Prod.fst).sum,
              (((a ::ₘ (0 : Multiset _)) + s_cr).map Prod.snd).sum) =
              (a.1 + (s_cr.map Prod.fst).sum, a.2 + (s_cr.map Prod.snd).sum)
        rw [Multiset.cons_add, Multiset.zero_add, Multiset.map_cons, Multiset.map_cons,
            Multiset.sum_cons, Multiset.sum_cons]]
    -- Apply IH
    rw [ih]
    -- After: (pairsMS l).bind (a => (lhsAllWithMS cr).map (botForest, midForest) .map (p => (a.1 + p.1, a.2 + p.2)))
    -- RHS:
    show _ = (lhsAllWithMS (CutShape.onlyLeftCut hl cr) : Multiset _).map _
    rw [show (lhsAllWithMS (CutShape.onlyLeftCut hl cr) : Multiset (LhsIndex (.node l r)))
          = ((Finset.univ : Finset (AugCutShape l)).val.bind fun ac_l =>
              (lhsAllWithMS cr).map fun rhs =>
                LhsIndex.onlyLeftCut hl ac_l rhs) from rfl]
    rw [Multiset.map_bind]
    -- After RHS: univ_l.val.bind (ac_l => (lhsAllWithMS cr).map (rhs => onlyLeftCut hl ac_l rhs).map (botForest, midForest))
    -- Match: pairsMS l = univ_l.val.map (cf_aug, rem)
    show ((((Finset.univ : Finset (AugCutShape l)).val.map fun ac =>
            (AugCutShape.cutForest_aug ac, AugCutShape.remainderForest ac))).bind fun a =>
            (Multiset.map (fun p => (a.1 + p.1, a.2 + p.2))
              ((lhsAllWithMS cr).map fun rhs =>
                (LhsIndex.botForest rhs, LhsIndex.midForest rhs)))) = _
    rw [Multiset.bind_map]
    refine Multiset.bind_congr (fun ac_l _ => ?_)
    -- Per ac_l: Multiset.map (p => (cf_aug ac_l + p.1, rem ac_l + p.2)) ((lhsAllWithMS cr).map (botForest, midForest))
    --        = ((lhsAllWithMS cr).map (rhs => onlyLeftCut hl ac_l rhs)).map (botForest, midForest)
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun rhs _ => ?_)
    rfl
  | @onlyRightCut l r hr cl ih =>
    -- cutForest (onlyRightCut hr cl) = cutForest cl + ({r} : Multiset _)
    show (Multiset.Sections (((CutShape.cutForest cl + ({r} : Multiset _)).map
            (pairsMS (α := α))))).map _ = _
    rw [Multiset.map_add, Multiset.sections_add,
        show (({r} : Multiset (TraceTree α Unit)).map (pairsMS (α := α)))
            = (pairsMS r) ::ₘ (0 : Multiset _) from rfl,
        Multiset.sections_cons, Multiset.sections_zero]
    simp only [Multiset.map_singleton, Multiset.bind_singleton]
    -- After: ((Sections (cutForest cl).map pairsMS).bind fun s_cl => Multiset.map (s_cl + ·) ((pairsMS r).map (a => a ::ₘ 0))) .map (s => ...)
    rw [Multiset.map_bind]
    -- After: (Sections cl).bind (s_cl => (Multiset.map (s_cl + ·) ((pairsMS r).map (a => a ::ₘ 0))).map (s => ...))
    -- Apply Multiset.map_map twice + simplify (s_cl + a ::ₘ 0).fsts.sum etc
    simp_rw [show (∀ s_cl : Multiset (TraceForest α Unit × TraceForest α Unit),
              Multiset.map (fun s => ((s.map Prod.fst).sum, (s.map Prod.snd).sum))
                (Multiset.map (fun x => s_cl + x)
                  (Multiset.map (fun x => (x ::ₘ (0 : Multiset _))) (pairsMS r)))
              = Multiset.map (fun a => ((s_cl.map Prod.fst).sum + a.1,
                                          (s_cl.map Prod.snd).sum + a.2))
                  (pairsMS r))
            from fun s_cl => by
        rw [Multiset.map_map, Multiset.map_map]
        refine Multiset.map_congr rfl (fun a _ => ?_)
        show (((s_cl + (a ::ₘ (0 : Multiset _))).map Prod.fst).sum,
              ((s_cl + (a ::ₘ (0 : Multiset _))).map Prod.snd).sum) =
              ((s_cl.map Prod.fst).sum + a.1, (s_cl.map Prod.snd).sum + a.2)
        simp only [Multiset.map_add, Multiset.map_cons, Multiset.map_zero,
                   Multiset.sum_add, Multiset.sum_cons, Multiset.sum_zero, add_zero]]
    -- After: (Sections cl).bind (s_cl => (pairsMS r).map (a => (s_cl.fsts.sum + a.1, s_cl.snds.sum + a.2)))
    -- Restructure for IH on cl: factor through ((Sections cl).map (fsts, snds)).bind ...
    rw [show ((Multiset.Sections ((CutShape.cutForest cl).map (pairsMS (α := α)))).bind fun s_cl =>
              Multiset.map (fun a => ((s_cl.map Prod.fst).sum + a.1,
                                       (s_cl.map Prod.snd).sum + a.2)) (pairsMS r))
          = ((Multiset.Sections ((CutShape.cutForest cl).map (pairsMS (α := α)))).map fun s_cl =>
              ((s_cl.map Prod.fst).sum, (s_cl.map Prod.snd).sum)).bind fun p_l =>
              Multiset.map (fun a => (p_l.1 + a.1, p_l.2 + a.2)) (pairsMS r) from by
        rw [Multiset.bind_map]]
    rw [ih]
    rw [Multiset.bind_map]
    -- After: (lhsAllWithMS cl).bind (lhs => Multiset.map (a => (botForest lhs + a.1, midForest lhs + a.2)) (pairsMS r))
    -- RHS:
    show _ = (lhsAllWithMS (CutShape.onlyRightCut hr cl) : Multiset _).map _
    rw [show (lhsAllWithMS (CutShape.onlyRightCut hr cl) : Multiset (LhsIndex (.node l r)))
          = ((lhsAllWithMS cl).bind fun lhs =>
              (Finset.univ : Finset (AugCutShape r)).val.map fun ac_r =>
                LhsIndex.onlyRightCut hr lhs ac_r) from rfl]
    rw [Multiset.map_bind]
    refine Multiset.bind_congr (fun lhs _ => ?_)
    -- Per lhs: Multiset.map (a => (botForest lhs + a.1, midForest lhs + a.2)) (pairsMS r)
    --        = (univ_r.val.map (ac_r => onlyRightCut hr lhs ac_r)).map (botForest, midForest)
    show Multiset.map (fun a => (LhsIndex.botForest lhs + a.1, LhsIndex.midForest lhs + a.2))
          ((Finset.univ : Finset (AugCutShape r)).val.map fun ac =>
            (AugCutShape.cutForest_aug ac, AugCutShape.remainderForest ac)) = _
    rw [Multiset.map_map, Multiset.map_map]
    rfl
  | @bothRecurse l r cl cr ih_l ih_r =>
    -- cutForest = cutForest cl + cutForest cr
    show (Multiset.Sections (((CutShape.cutForest cl + CutShape.cutForest cr).map
            (pairsMS (α := α))))).map _ = _
    rw [Multiset.map_add, Multiset.sections_add]
    rw [Multiset.map_bind]
    -- After: (Sections cl).bind (s_l => (Sections cr).map (s_l + ·) .map (s => ...))
    -- Apply Multiset.map_map twice + Multiset.map_add + sum_add
    simp_rw [show (∀ s_l : Multiset (TraceForest α Unit × TraceForest α Unit),
              Multiset.map (fun s => ((s.map Prod.fst).sum, (s.map Prod.snd).sum))
                (Multiset.map (fun x => s_l + x)
                  (Multiset.Sections ((CutShape.cutForest cr).map (pairsMS (α := α)))))
              = Multiset.map (fun s_r => ((s_l.map Prod.fst).sum + (s_r.map Prod.fst).sum,
                                          (s_l.map Prod.snd).sum + (s_r.map Prod.snd).sum))
                  (Multiset.Sections ((CutShape.cutForest cr).map (pairsMS (α := α)))))
            from fun s_l => by
        rw [Multiset.map_map]
        refine Multiset.map_congr rfl (fun s_r _ => ?_)
        show (((s_l + s_r).map Prod.fst).sum, ((s_l + s_r).map Prod.snd).sum) = _
        rw [Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add]]
    -- Restructure for IH: factor through (Sections cl).map (fsts, snds)
    rw [show ((Multiset.Sections ((CutShape.cutForest cl).map (pairsMS (α := α)))).bind fun s_l =>
              Multiset.map (fun s_r => ((s_l.map Prod.fst).sum + (s_r.map Prod.fst).sum,
                                         (s_l.map Prod.snd).sum + (s_r.map Prod.snd).sum))
                (Multiset.Sections ((CutShape.cutForest cr).map (pairsMS (α := α)))))
          = ((Multiset.Sections ((CutShape.cutForest cl).map (pairsMS (α := α)))).map fun s_l =>
              ((s_l.map Prod.fst).sum, (s_l.map Prod.snd).sum)).bind fun p_l =>
              Multiset.map (fun s_r => (p_l.1 + (s_r.map Prod.fst).sum,
                                         p_l.2 + (s_r.map Prod.snd).sum))
                (Multiset.Sections ((CutShape.cutForest cr).map (pairsMS (α := α))))
          from by rw [Multiset.bind_map]]
    rw [ih_l]
    -- Now: (lhsAllWithMS cl).map (botForest, midForest) .bind (p_l => Multiset.map (s_r => (p_l.1 + s_r.fsts.sum, p_l.2 + s_r.snds.sum)) (Sections cr))
    rw [Multiset.bind_map]
    -- Now: (lhsAllWithMS cl).bind (lhs => Multiset.map (s_r => (botForest lhs + s_r.fsts.sum, midForest lhs + s_r.snds.sum)) (Sections cr))
    -- Apply IH on cr (factor map_map)
    simp_rw [show (∀ lhs : LhsIndex l,
              Multiset.map (fun s_r => (LhsIndex.botForest lhs + (s_r.map Prod.fst).sum,
                                         LhsIndex.midForest lhs + (s_r.map Prod.snd).sum))
                (Multiset.Sections ((CutShape.cutForest cr).map (pairsMS (α := α))))
              = Multiset.map (fun p_r => (LhsIndex.botForest lhs + p_r.1, LhsIndex.midForest lhs + p_r.2))
                  (Multiset.map (fun s => ((s.map Prod.fst).sum, (s.map Prod.snd).sum))
                    (Multiset.Sections ((CutShape.cutForest cr).map (pairsMS (α := α))))))
            from fun lhs => by
        rw [Multiset.map_map]
        rfl]
    rw [ih_r]
    -- Now: (lhsAllWithMS cl).bind (lhs => Multiset.map (p_r => (botForest lhs + p_r.1, midForest lhs + p_r.2)) ((lhsAllWithMS cr).map (botForest, midForest)))
    -- RHS:
    show _ = (lhsAllWithMS (CutShape.bothRecurse cl cr) : Multiset _).map _
    rw [show (lhsAllWithMS (CutShape.bothRecurse cl cr) : Multiset (LhsIndex (.node l r)))
          = ((lhsAllWithMS cl).bind fun lhs =>
              (lhsAllWithMS cr).map fun rhs =>
                LhsIndex.bothRecurse lhs rhs) from rfl]
    rw [Multiset.map_bind]
    refine Multiset.bind_congr (fun lhs _ => ?_)
    -- Per lhs: Multiset.map (p_r => (botForest lhs + p_r.1, midForest lhs + p_r.2)) ((lhsAllWithMS cr).map (botForest, midForest))
    --        = ((lhsAllWithMS cr).map (rhs => bothRecurse lhs rhs)).map (botForest, midForest)
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun rhs _ => ?_)
    rfl

/-! ## §3: Main bridge theorem -/

/-- Partition of `(univ : Finset (LhsIndex T)).val` by `outerCut`. -/
theorem lhsIndex_univ_eq_bind (T : TraceTree α Unit) :
    ((Finset.univ : Finset (LhsIndex T)).val : Multiset (LhsIndex T))
      = ((Finset.univ : Finset (CutShape T)).val.bind fun cl =>
          (LhsIndex.allWith T cl).val) := by
  have hdisj : ((Finset.univ : Finset (CutShape T)) : Set (CutShape T)).PairwiseDisjoint
                 (fun cl => LhsIndex.allWith T cl) := by
    intro cl₁ _ cl₂ _ hne
    exact LhsIndex.allWith_disjoint hne
  have hext : (Finset.univ : Finset (LhsIndex T))
      = (Finset.univ : Finset (CutShape T)).disjiUnion
          (fun cl => LhsIndex.allWith T cl) hdisj := by
    apply Finset.ext
    intro rhs
    constructor
    · intro _
      exact Finset.mem_disjiUnion.mpr
        ⟨LhsIndex.outerCut rhs, Finset.mem_univ _, LhsIndex.mem_allWith T rhs⟩
    · intro _
      exact Finset.mem_univ _
  rw [hext, Finset.disjiUnion_val]

/-- The substantive bridge between LHS double-cut Sections-form and LhsIndex
    structurally indexed enumeration. -/
theorem lhsRealCuts_eq_lhsIndexSum (T : TraceTree α Unit) :
    (lhsRealCuts T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = (Finset.univ : Finset (LhsIndex T)).val.map (LhsIndex.tripleTensor R) := by
  rw [lhsRealCuts_eq_perLayerContrib_top]
  unfold perLayerContrib
  rw [Multiset.map_bind]
  rw [lhsIndex_univ_eq_bind, Multiset.map_bind]
  refine Multiset.bind_congr (fun cl_outer _ => ?_)
  -- Note: (univ : AugCutShape T').val.map (cf_aug, rem) IS pairsMS T' (definitionally).
  rw [show ((CutShape.cutForest cl_outer).map fun T' =>
              (Finset.univ : Finset (AugCutShape T')).val.map fun ac' =>
                (AugCutShape.cutForest_aug ac', AugCutShape.remainderForest ac'))
          = ((CutShape.cutForest cl_outer).map (pairsMS (α := α))) from rfl]
  rw [Multiset.map_map]
  -- Reformulate via composition through (s.fsts.sum, s.snds.sum):
  rw [show ((Multiset.Sections ((CutShape.cutForest cl_outer).map (pairsMS (α := α)))).map
            ((ChildSlots.toTriple R) ∘ fun s : Multiset (TraceForest α Unit × TraceForest α Unit) =>
              (⟨(s.map Prod.fst).sum, (s.map Prod.snd).sum,
                CutShape.remainder cl_outer⟩ : ChildSlots α)))
          = ((Multiset.Sections ((CutShape.cutForest cl_outer).map (pairsMS (α := α)))).map
              fun s => ((s.map Prod.fst).sum, (s.map Prod.snd).sum)).map
              fun p =>
                (forestToHc (R := R) p.1)
                  ⊗ₜ[R] ((forestToHc (R := R) p.2)
                    ⊗ₜ[R] forestToHc (R := R)
                      ({CutShape.remainder cl_outer} : TraceForest α Unit)) from by
        rw [Multiset.map_map]
        rfl]
  rw [perCutShape_pair_bridge cl_outer, lhsAllWithMS_eq_allWith_val]
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun rhs hrhs => ?_)
  have houter : LhsIndex.outerCut rhs = cl_outer :=
    LhsIndex.outerCut_of_mem_allWith T cl_outer rhs hrhs
  show (forestToHc (R := R) (LhsIndex.botForest rhs))
       ⊗ₜ[R] ((forestToHc (R := R) (LhsIndex.midForest rhs))
              ⊗ₜ[R] forestToHc (R := R)
                ({CutShape.remainder cl_outer} : TraceForest α Unit))
       = LhsIndex.tripleTensor R rhs
  unfold LhsIndex.tripleTensor
  rw [houter]

end ConnesKreimer
