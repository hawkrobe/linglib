import Linglib.Core.Algebra.RootedTree.GrossmanLarsonAssoc
import Linglib.Core.Algebra.RootedTree.GrossmanLarsonPairing

set_option autoImplicit false

/-!
# The split coproduct side of GL/CK duality
[foissy-2002] [oudom-guin-2008]

Two combinatorial laws connecting the Grossman-Larson product to the
sub-multiset ("split") decomposition of forests, the substrate for the
GL/CK duality theorem `pairing_gl_eq_pairing_coproduct_Rho`
(`Coproduct/PruningDuality.lean`):

* `Nonplanar.insertionMultiset_antidiagonal` — splits of a multi-graft
  output factor through splits of host and guests (each guest follows
  its host component). The multi-graft counterpart of
  `insertionMultiset_add_host`, from which it is proved by induction
  on the host.
* `pairing_product_of'_mul_of'` — the GL-product/CK-product duality at
  the pairing level: `⟨A ⋆ B, C₁ · C₂⟩` decomposes over independent
  splits of `A` and `B`. Combines the insertion split law with the
  pairing product rule `pairing_of'_mul` (`GrossmanLarsonPairing.lean`).

Both statements are computationally validated against the planar
simulation harness (`scratch/validate_duality.lean`, V3/V3b batteries,
exhaustive over forests of weight ≤ 3 plus duplicate-tree traps).
-/

namespace RootedTree

namespace GrossmanLarson

open ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### Helper lemmas

A few small multiset/insertion building blocks used by both targets below.
-/

/-- `Multiset.antidiagonal` of a singleton: `antidiag {a} = {(0, {a}), ({a}, 0)}`.
    Follows from `antidiagonal_cons` + `antidiagonal_zero`. -/
private theorem antidiagonal_singleton {β : Type*} (a : β) :
    Multiset.antidiagonal ({a} : Multiset β) =
      ({(0, {a}), ({a}, 0)} : Multiset (Multiset β × Multiset β)) := by
  show Multiset.antidiagonal (a ::ₘ (0 : Multiset β)) = _
  rw [Multiset.antidiagonal_cons, Multiset.antidiagonal_zero]
  simp [Multiset.map_singleton, Prod.map]

omit [DecidableEq α] in
/-- A `NIM {T} G` output is always a singleton forest (card 1). This is the
    `Nonplanar.insertionMultiset_card_eq` specialization to a singleton host. -/
private theorem insertionMultiset_singleton_host_singleton
    (T : Nonplanar α) (G : Multiset (Nonplanar α))
    {X : Multiset (Nonplanar α)} (hX : X ∈ Nonplanar.insertionMultiset {T} G) :
    ∃ T' : Nonplanar α, X = {T'} := by
  have hcard : X.card = ({T} : Multiset (Nonplanar α)).card :=
    Nonplanar.insertionMultiset_card_eq {T} G hX
  rw [Multiset.card_singleton] at hcard
  exact Multiset.card_eq_one.mp hcard

/-- **Triple-partition reindexing** (`[UPSTREAM]` candidate): two equivalent
    enumerations of ordered triple-partitions of a multiset `G`. The
    "powerset-then-antidiagonal" enumeration (pick `G₁ ⊆ G`, then split
    `G - G₁`) equals the "antidiagonal-then-powerset" enumeration (split
    `G`, then pick `G₂ ⊆` second part of the split), under the bijection
    `(G₁, pg'.1, pg'.2) ↔ (pg.1, G₂, pg.2 - G₂)` where `G₂ = G₁`,
    `pg.1 = pg'.1`, `pg.2 = G₁ + pg'.2`.

    Reduces to `Multiset.powerset_powerset_pair_swap` (Shuffle.lean) after
    converting both `antidiagonal` factors to `powerset.map` form via
    `antidiagonal_eq_map_powerset` and identifying the inner bind as `f`
    applied to the implicit third-part `G - G₁ - S`.

    Used by `insertionMultiset_antidiagonal` to align the LHS structure
    (one host tree peeled, free guest split, A' substructure split) with
    the RHS structure (A split, G split, free guest sub-split). -/
private theorem triple_partition_reindex {β γ : Type*} [DecidableEq β]
    (G : Multiset β)
    (f : Multiset β → Multiset β → Multiset β → Multiset γ) :
    (G.powerset.bind fun G₁ =>
        (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
          f G₁ pg'.1 pg'.2) =
      (Multiset.antidiagonal G).bind fun pg =>
        pg.2.powerset.bind fun G₂ =>
          f G₂ pg.1 (pg.2 - G₂) := by
  -- Step 1: Reformulate LHS as a `(pair-enum).bind h` where `h (a, b) := f a (G - a - b) b`.
  -- Use `antidiagonal_eq_map_powerset` to turn `antidiag (G - G₁)` into
  -- `(G - G₁).powerset.map (S ↦ ((G - G₁) - S, S))`.
  set h : Multiset β × Multiset β → Multiset γ :=
    fun p => f p.1 (G - p.1 - p.2) p.2 with h_def
  have h_lhs : (G.powerset.bind fun G₁ =>
            (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
              f G₁ pg'.1 pg'.2) =
        (G.powerset.bind fun G₁ =>
          (G - G₁).powerset.map (fun B => (G₁, B))).bind h := by
    rw [Multiset.bind_assoc]
    refine Multiset.bind_congr fun G₁ _ => ?_
    rw [Multiset.antidiagonal_eq_map_powerset, Multiset.bind_map, Multiset.bind_map]
  -- Step 2: Reformulate RHS similarly.
  have h_rhs : (Multiset.antidiagonal G).bind (fun pg =>
            pg.2.powerset.bind (fun G₂ =>
              f G₂ pg.1 (pg.2 - G₂))) =
        (G.powerset.bind fun F₁ =>
          F₁.powerset.map (fun A => (A, F₁ - A))).bind h := by
    -- RHS uses antidiag G, the second coord pg.2 indexes the bind. By antidiag_eq_map_powerset
    -- with t ↦ (G - t, t), pg = (G - pg.2, pg.2). Set T = pg.2. Then pg.1 = G - T.
    rw [Multiset.antidiagonal_eq_map_powerset, Multiset.bind_map]
    rw [Multiset.bind_assoc]
    refine Multiset.bind_congr fun T hT => ?_
    rw [Multiset.bind_map]
    refine Multiset.bind_congr fun G₂ hG₂ => ?_
    -- Goal: f G₂ (G - T) (T - G₂) = h (G₂, T - G₂) = f G₂ (G - G₂ - (T - G₂)) (T - G₂).
    -- Need: G - G₂ - (T - G₂) = G - T. Since G₂ ⊆ T ⊆ G, use tsub_tsub + add identities.
    have hG₂_le : G₂ ≤ T := Multiset.mem_powerset.mp hG₂
    have hT_le : T ≤ G := Multiset.mem_powerset.mp hT
    show f G₂ (G - T) (T - G₂) = f G₂ (G - G₂ - (T - G₂)) (T - G₂)
    congr 1
    -- G - G₂ - (T - G₂) = G - (G₂ + (T - G₂)) = G - T (using G₂ + (T - G₂) = T from add_tsub_cancel_of_le).
    rw [tsub_tsub, add_tsub_cancel_of_le hG₂_le]
  rw [h_lhs, h_rhs, Multiset.powerset_powerset_pair_swap]

/-- **Triple-partition reindexing (flipped)**: variant of
    `triple_partition_reindex` where the second-level powerset goes through
    the *first* coordinate of the antidiagonal instead of the second.

    Bijection: `(G₁, pg'.1, pg'.2) ↔ (G₂, pg.1 - G₂, pg.2)` where `G₂ = G₁`,
    `pg.1 = G₁ + pg'.1`, `pg.2 = pg'.2`.

    Derived from `triple_partition_reindex` via `Multiset.antidiagonal_swap`. -/
private theorem triple_partition_reindex_flip {β γ : Type*} [DecidableEq β]
    (G : Multiset β)
    (f : Multiset β → Multiset β → Multiset β → Multiset γ) :
    (G.powerset.bind fun G₁ =>
        (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
          f G₁ pg'.1 pg'.2) =
      (Multiset.antidiagonal G).bind fun pg =>
        pg.1.powerset.bind fun G₂ =>
          f G₂ (pg.1 - G₂) pg.2 := by
  -- Reindex the inner `antidiag (G - G₁)` via `antidiagonal_swap` to switch pg'.1 ↔ pg'.2,
  -- then apply `triple_partition_reindex` with f's arguments shifted.
  -- LHS = G.powerset.bind (G₁ ↦ ((antidiag (G - G₁)).map swap).bind (pg' ↦ f G₁ pg'.2 pg'.1))
  --     [using antidiag_swap to expose pg.swap]
  -- = G.powerset.bind (G₁ ↦ antidiag (G - G₁).bind (pg' ↦ f G₁ pg'.2 pg'.1))
  --     [the swap.bind absorbed into pg'.swap]
  -- Now apply triple_partition_reindex with f' G₁ x y := f G₁ y x.
  -- Define helper function with swapped 2nd/3rd args.
  set g : Multiset β → Multiset β → Multiset β → Multiset γ :=
    fun a b c => f a c b with g_def
  -- LHS: original form (using f).
  -- Goal: ... = antidiag G.bind (pg ↦ pg.1.powerset.bind (G₂ ↦ f G₂ (pg.1 - G₂) pg.2))
  -- Rewrite LHS as g G₁ pg'.2 pg'.1 (= f G₁ pg'.1 pg'.2 by def of g).
  have h_lhs : (G.powerset.bind fun G₁ =>
            (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
              f G₁ pg'.1 pg'.2) =
        G.powerset.bind fun G₁ =>
          ((Multiset.antidiagonal (G - G₁)).map Prod.swap).bind fun pg' =>
            g G₁ pg'.1 pg'.2 := by
    refine Multiset.bind_congr fun G₁ _ => ?_
    rw [Multiset.bind_map]
    refine Multiset.bind_congr fun pg' _ => ?_
    rfl
  rw [h_lhs]
  -- Use antidiag_swap to absorb the .map Prod.swap.
  simp_rw [Multiset.antidiagonal_swap]
  -- Now LHS is `G.powerset.bind (G₁ ↦ antidiag (G - G₁).bind (pg' ↦ g G₁ pg'.1 pg'.2))`.
  rw [triple_partition_reindex G g]
  -- Goal: antidiag G.bind (pg ↦ pg.2.powerset.bind (G₂ ↦ g G₂ pg.1 (pg.2 - G₂)))
  --     = antidiag G.bind (pg ↦ pg.1.powerset.bind (G₂ ↦ f G₂ (pg.1 - G₂) pg.2))
  -- g G₂ pg.1 (pg.2 - G₂) = f G₂ (pg.2 - G₂) pg.1. Use antidiag_swap to flip pg.
  conv_lhs => rw [show Multiset.antidiagonal G =
      (Multiset.antidiagonal G).map Prod.swap from (Multiset.antidiagonal_swap G).symm]
  rw [Multiset.bind_map]
  refine Multiset.bind_congr fun pg _ => ?_
  -- After swap: (Prod.swap pg).2 = pg.1, (Prod.swap pg).1 = pg.2. So:
  --   g G₂ (Prod.swap pg).1 ((Prod.swap pg).2 - G₂) = g G₂ pg.2 (pg.1 - G₂)
  --                                                 = f G₂ (pg.1 - G₂) pg.2.
  rfl

/-- Antidiagonal of `(X_T + X_A')` where `X_T` is a singleton multiset
    `{T'}`: by `antidiagonal_add` + `antidiagonal_singleton`, the result
    splits into two summands "T' joins right" + "T' joins left". -/
private theorem antidiagonal_singleton_add {β : Type*} [DecidableEq β] (T' : β) (Y : Multiset β) :
    Multiset.antidiagonal (({T'} : Multiset β) + Y) =
      (Multiset.antidiagonal Y).map (fun pA' => (pA'.1, ({T'} : Multiset β) + pA'.2)) +
      (Multiset.antidiagonal Y).map (fun pA' => (({T'} : Multiset β) + pA'.1, pA'.2)) := by
  rw [Multiset.antidiagonal_add, antidiagonal_singleton]
  show ({(0, {T'}), ({T'}, 0)} :
            Multiset (Multiset β × Multiset β)).bind (fun pT =>
        (Multiset.antidiagonal Y).map (fun pA' => (pT.1 + pA'.1, pT.2 + pA'.2))) = _
  -- {(0,{T'}), ({T'},0)}.bind f = f (0,{T'}) + f ({T'},0)
  rw [show ({(0, {T'}), ({T'}, 0)} : Multiset (Multiset β × Multiset β)) =
        (0, ({T'} : Multiset β)) ::ₘ (({T'} : Multiset β), 0) ::ₘ 0 from rfl,
      Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  -- Now compute each .map by 0 + x = x.
  congr 1
  · apply Multiset.map_congr rfl
    intro pA' _
    show ((0 : Multiset β) + pA'.1, ({T'} : Multiset β) + pA'.2) =
         (pA'.1, ({T'} : Multiset β) + pA'.2)
    rw [zero_add]
  · apply Multiset.map_congr rfl
    intro pA' _
    show (({T'} : Multiset β) + pA'.1, (0 : Multiset β) + pA'.2) =
         (({T'} : Multiset β) + pA'.1, pA'.2)
    rw [zero_add]

/-! ### Split law for multi-graft outputs -/

/-- **Splits of an insertion output factor through splits of host and
    guests.** Each component of a multi-graft output `X ∈ NIM(A, G)` is
    one host component of `A` carrying the guests grafted into it, so a
    sub-multiset split of `X` induces a split of `A` and a split of `G`
    (guests follow their host), and the correspondence is
    multiplicity-faithful:

    `Σ_{X ∈ NIM(A,G)} Σ_{X = X₁ + X₂} (X₁, X₂)
       = Σ_{A = A₁+A₂} Σ_{G = G₁+G₂} NIM(A₁,G₁) ×ˢ NIM(A₂,G₂)`.

    Proved by induction on `A` from `insertionMultiset_add_host`
    (peeling one host tree; `NIM({T}, G)` outputs are singleton
    forests, whose antidiagonal is the trivial two-way split). -/
theorem _root_.RootedTree.Nonplanar.insertionMultiset_antidiagonal
    (A G : Forest (Nonplanar α)) :
    (Nonplanar.insertionMultiset A G).bind Multiset.antidiagonal =
      (Multiset.antidiagonal A).bind (fun pa =>
        (Multiset.antidiagonal G).bind (fun pg =>
          (Nonplanar.insertionMultiset pa.1 pg.1) ×ˢ
            (Nonplanar.insertionMultiset pa.2 pg.2))) := by
  induction A using Multiset.induction_on generalizing G with
  | empty =>
    -- A = 0. Case on G.
    rw [Multiset.antidiagonal_zero, Multiset.singleton_bind]
    by_cases hG : G = 0
    · -- G = 0: NIM 0 0 = {0}, antidiag 0 = {(0,0)}. RHS = NIM 0 0 ×ˢ NIM 0 0 = {(0,0)}.
      subst hG
      rw [Nonplanar.insertionMultiset_zero_right, Multiset.singleton_bind,
          Multiset.antidiagonal_zero, Multiset.singleton_bind,
          Nonplanar.insertionMultiset_zero_right]
      rfl
    · -- G ≠ 0: LHS = (NIM 0 G).bind antidiag = 0.bind = 0. RHS: each pg has at least one nonzero side.
      rw [Nonplanar.insertionMultiset_zero_left_of_ne_zero G hG, Multiset.zero_bind]
      -- RHS: prove the bind is 0 by showing each summand is 0.
      symm
      have h_rhs_eq :
          (Multiset.antidiagonal G).bind (fun pg =>
              (Nonplanar.insertionMultiset 0 pg.1) ×ˢ
              (Nonplanar.insertionMultiset 0 pg.2)) =
          (Multiset.antidiagonal G).bind (fun _ => (0 : Multiset (Multiset (Nonplanar α) ×
            Multiset (Nonplanar α)))) := by
        refine Multiset.bind_congr fun pg hpg => ?_
        have hpg_sum : pg.1 + pg.2 = G := Multiset.mem_antidiagonal.mp hpg
        by_cases h1 : pg.1 = 0
        · -- pg.1 = 0 ⇒ pg.2 = G ≠ 0.
          have h2 : pg.2 ≠ 0 := by
            intro h2eq
            apply hG
            rw [← hpg_sum, h1, h2eq]; rfl
          rw [Nonplanar.insertionMultiset_zero_left_of_ne_zero pg.2 h2,
              Multiset.product_zero]
        · rw [Nonplanar.insertionMultiset_zero_left_of_ne_zero pg.1 h1,
              Multiset.zero_product]
      rw [h_rhs_eq, Multiset.bind_zero]
  | cons T A' ih =>
    -- A = T ::ₘ A' = {T} + A'.
    have h_cons_eq : (T ::ₘ A' : Multiset (Nonplanar α)) = ({T} : Multiset _) + A' := by
      rw [Multiset.singleton_add]
    -- Step 1: Rewrite LHS via insertionMultiset_add_host.
    rw [h_cons_eq, Nonplanar.insertionMultiset_add_host {T} A' G]
    -- LHS = (G.powerset.bind (G₁ ↦ (NIM {T} G₁ ×ˢ NIM A' (G-G₁)).map (·.1+·.2))).bind antidiag
    rw [Multiset.bind_assoc]
    -- LHS = G.powerset.bind (G₁ ↦ ((NIM {T} G₁ ×ˢ NIM A' (G-G₁)).map (·.1+·.2)).bind antidiag)
    -- Step 2: Push antidiag through the .map ↦ bind, expand antidiag (X_T + X_A')
    -- via antidiagonal_singleton_add (since X_T is a singleton).
    have h_lhs_inner : ∀ G₁ : Multiset (Nonplanar α),
        (((Nonplanar.insertionMultiset {T} G₁) ×ˢ
            (Nonplanar.insertionMultiset A' (G - G₁))).map
            (fun p => p.1 + p.2)).bind Multiset.antidiagonal =
        ((Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
            (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (pA'.1, X_T + pA'.2)) +
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (X_T + pA'.1, pA'.2))) := by
      intro G₁
      -- LHS_inner: bind . map = map then bind = ... apply antidiagonal_singleton_add per X_T.
      rw [Multiset.bind_map]
      -- Goal: (NIM {T} G₁ ×ˢ NIM A' (G-G₁)).bind (p ↦ antidiag (p.1 + p.2)) = (NIM {T} G₁).bind ...
      -- Unfold ×ˢ as bind.
      show ((Nonplanar.insertionMultiset {T} G₁).bind (fun X_T =>
              (Nonplanar.insertionMultiset A' (G - G₁)).map (Prod.mk X_T))).bind
                (fun p => Multiset.antidiagonal (p.1 + p.2)) = _
      rw [Multiset.bind_assoc]
      refine Multiset.bind_congr fun X_T hX_T => ?_
      rw [Multiset.bind_map]
      refine Multiset.bind_congr fun X_A' hX_A' => ?_
      -- Each X_T is a singleton {T'}. Apply antidiagonal_singleton_add.
      obtain ⟨T', hT'⟩ := insertionMultiset_singleton_host_singleton T G₁ hX_T
      subst hT'
      exact antidiagonal_singleton_add T' X_A'
    rw [show (G.powerset.bind fun G₁ =>
            (((Nonplanar.insertionMultiset {T} G₁) ×ˢ
                (Nonplanar.insertionMultiset A' (G - G₁))).map
                (fun p => p.1 + p.2)).bind Multiset.antidiagonal) =
          G.powerset.bind fun G₁ =>
            ((Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
                (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                  (Multiset.antidiagonal X_A').map
                      (fun pA' => (pA'.1, X_T + pA'.2)) +
                  (Multiset.antidiagonal X_A').map
                      (fun pA' => (X_T + pA'.1, pA'.2)))
        from Multiset.bind_congr (fun G₁ _ => h_lhs_inner G₁)]
    -- Step 3: Split LHS into two summands (T-right + T-left) using bind_add via map_add and sum_add.
    -- Strategy: each inner sum splits via bind_congr.
    have h_split_inner : ∀ G₁ : Multiset (Nonplanar α),
        ((Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
            (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (pA'.1, X_T + pA'.2)) +
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (X_T + pA'.1, pA'.2))) =
        ((Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
            (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (pA'.1, X_T + pA'.2))) +
        ((Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
            (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
              (Multiset.antidiagonal X_A').map
                  (fun pA' => (X_T + pA'.1, pA'.2))) := by
      intro G₁
      -- Split each X_A' bind summand and each X_T bind summand.
      rw [← Multiset.bind_add]
      refine Multiset.bind_congr fun X_T _ => ?_
      rw [← Multiset.bind_add]
    rw [show (G.powerset.bind fun G₁ =>
            (Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
              (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                (Multiset.antidiagonal X_A').map
                    (fun pA' => (pA'.1, X_T + pA'.2)) +
                (Multiset.antidiagonal X_A').map
                    (fun pA' => (X_T + pA'.1, pA'.2))) =
          (G.powerset.bind fun G₁ =>
            (Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
              (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                (Multiset.antidiagonal X_A').map
                    (fun pA' => (pA'.1, X_T + pA'.2))) +
          (G.powerset.bind fun G₁ =>
            (Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
              (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                (Multiset.antidiagonal X_A').map
                    (fun pA' => (X_T + pA'.1, pA'.2)))
        from by
      rw [← Multiset.bind_add]
      exact Multiset.bind_congr (fun G₁ _ => h_split_inner G₁)]
    -- Step 4: Now rewrite RHS via antidiagonal_cons split into T-right + T-left summands.
    rw [show (Multiset.antidiagonal ({T} + A' : Multiset (Nonplanar α))) =
            Multiset.antidiagonal (T ::ₘ A') from by rw [← h_cons_eq],
        Multiset.antidiagonal_cons]
    -- RHS: antidiag (T ::ₘ A') = antidiag A'.map (Prod.map id (cons T)) + antidiag A'.map (Prod.map (cons T) id)
    rw [Multiset.add_bind]
    -- RHS = RHS_T_right_old + RHS_T_left_old
    -- The two map-binds become bind-(after rebrand).
    rw [Multiset.bind_map, Multiset.bind_map]
    -- Goal: (LHS_T_right + LHS_T_left) = (RHS_T_right + RHS_T_left)
    -- We'll match LHS_T_right ↔ RHS_T_right (T on right side of pair) and similarly for left.
    congr 1
    · -- Match T-right: pair has X_T on .2.
      -- Strategy: massage both LHS_T_right and RHS_T_right into a common form
      --   "antidiag A'.bind (pa' ↦ (NIM A').bind X_A' ↦ antidiag X_A' .bind (...) ...)"
      -- via IH on the LHS and `insertionMultiset_add_host` on the RHS, then apply
      -- `triple_partition_reindex` to align the G-indexing.
      -- 1) Reorder LHS_T_right using bind_map_comm to expose `antidiag (NIM A' (G-G₁)).bind`.
      rw [show (G.powerset.bind fun G₁ =>
              (Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
                (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                  (Multiset.antidiagonal X_A').map (fun pA' => (pA'.1, X_T + pA'.2))) =
            (G.powerset.bind fun G₁ =>
              ((Nonplanar.insertionMultiset A' (G - G₁)).bind Multiset.antidiagonal).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (pA'.1, X_T + pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [Multiset.bind_assoc]
        rw [Multiset.bind_bind]
        refine Multiset.bind_congr fun X_A' _ => ?_
        rw [Multiset.bind_map_comm]]
      -- 2) Apply IH on (NIM A' (G - G₁)).bind antidiag.
      rw [show (G.powerset.bind fun G₁ =>
              ((Nonplanar.insertionMultiset A' (G - G₁)).bind Multiset.antidiagonal).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (pA'.1, X_T + pA'.2)) =
            (G.powerset.bind fun G₁ =>
              ((Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  (Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                    (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (pA'.1, X_T + pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [ih (G - G₁)]]
      -- 3) Pull the binds inside via bind_assoc.
      rw [show (G.powerset.bind fun G₁ =>
              ((Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  (Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                    (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (pA'.1, X_T + pA'.2)) =
            (G.powerset.bind fun G₁ =>
              (Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                      fun X_T => (pA'.1, X_T + pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [Multiset.bind_assoc]
        refine Multiset.bind_congr fun pa' _ => ?_
        rw [Multiset.bind_assoc]]
      -- 4) Reorder G₁ and pa' binds (swap G.powerset and antidiag A').
      rw [show (G.powerset.bind fun G₁ =>
              (Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                      fun X_T => (pA'.1, X_T + pA'.2)) =
            (Multiset.antidiagonal A').bind fun pa' =>
              G.powerset.bind fun G₁ =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                      fun X_T => (pA'.1, X_T + pA'.2)
        from Multiset.bind_bind _ _]
      -- 5) Apply triple_partition_reindex on the G.powerset / antidiag (G - G₁) layer.
      refine Multiset.bind_congr fun pa' _ => ?_
      rw [triple_partition_reindex G
        (fun G₁ x y =>
          ((Nonplanar.insertionMultiset pa'.1 x) ×ˢ
              (Nonplanar.insertionMultiset pa'.2 y)).bind
            (fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
              fun X_T => (pA'.1, X_T + pA'.2)))]
      -- 6) Now LHS form matches RHS form (with bind_bind for G₂/X_T to T ::ₘ pa'.2 NIM).
      -- The RHS form (after bind_map): antidiag G.bind (pg ↦
      --   NIM pa'.1 pg.1 ×ˢ NIM (T ::ₘ pa'.2) pg.2).
      -- Compare with our current LHS form: antidiag G.bind (pg ↦ pg.2.powerset.bind (G₂ ↦ ...))
      refine Multiset.bind_congr fun pg _ => ?_
      -- RHS at this position: NIM pa'.1 pg.1 ×ˢ NIM (T ::ₘ pa'.2) pg.2 (after Prod.map id (cons T)).
      -- The Prod.map id (cons T) pa' has fst = pa'.1 and snd = T ::ₘ pa'.2 = {T} + pa'.2.
      -- Apply insertionMultiset_add_host on the RHS to peel {T} from the second argument.
      have h_prod_map_id : (Prod.map (id : Multiset (Nonplanar α) → _) (Multiset.cons T) pa') =
          (pa'.1, T ::ₘ pa'.2) := rfl
      rw [h_prod_map_id]
      show (pg.2.powerset.bind fun G₂ =>
              ((Nonplanar.insertionMultiset pa'.1 pg.1) ×ˢ
                  (Nonplanar.insertionMultiset pa'.2 (pg.2 - G₂))).bind
                (fun pA' => (Nonplanar.insertionMultiset {T} G₂).map
                  fun X_T => (pA'.1, X_T + pA'.2))) =
            (Nonplanar.insertionMultiset pa'.1 pg.1) ×ˢ
              (Nonplanar.insertionMultiset (T ::ₘ pa'.2) pg.2)
      -- Apply insertionMultiset_add_host to NIM (T ::ₘ pa'.2) pg.2.
      rw [show (T ::ₘ pa'.2 : Multiset (Nonplanar α)) = ({T} : Multiset _) + pa'.2 from
            (Multiset.singleton_add T pa'.2).symm,
          Nonplanar.insertionMultiset_add_host {T} pa'.2 pg.2]
      -- RHS: NIM pa'.1 pg.1 ×ˢ (pg.2.powerset.bind (G₂ ↦ (NIM {T} G₂ ×ˢ NIM pa'.2 (pg.2-G₂)).map (·.1+·.2)))
      -- Need: pg.2.powerset.bind LHS_inner = NIM pa'.1 pg.1 ×ˢ (pg.2.powerset.bind RHS_inner_form).
      -- Use s ×ˢ (t.bind f) = t.bind (b ↦ s ×ˢ f b).
      rw [show ∀ s : Multiset (Multiset (Nonplanar α)),
              ∀ tt : Multiset (Nonplanar α) → Multiset (Multiset (Nonplanar α)),
                s ×ˢ (pg.2.powerset.bind tt) =
                  pg.2.powerset.bind (fun G₂ => s ×ˢ tt G₂) from ?_]
      · refine Multiset.bind_congr fun G₂ _ => ?_
        -- Goal: ((NIM pa'.1 pg.1) ×ˢ NIM pa'.2 (pg.2-G₂)).bind (pA' ↦ NIM {T} G₂.map (X_T ↦ (pA'.1, X_T + pA'.2)))
        --     = NIM pa'.1 pg.1 ×ˢ ((NIM {T} G₂ ×ˢ NIM pa'.2 (pg.2-G₂)).map (·.1+·.2))
        -- Both sides describe pairs (Y₁, X_T + Y₂) for (Y₁, Y₂, X_T) ∈
        -- NIM pa'.1 pg.1 × NIM pa'.2 (pg.2-G₂) × NIM {T} G₂.
        -- Unfold ×ˢ as bind on both sides.
        show ((Nonplanar.insertionMultiset pa'.1 pg.1).bind (fun Y₁ =>
              (Nonplanar.insertionMultiset pa'.2 (pg.2 - G₂)).map (Prod.mk Y₁))).bind
                (fun pA' => (Nonplanar.insertionMultiset {T} G₂).map
                  fun X_T => (pA'.1, X_T + pA'.2)) =
              (Nonplanar.insertionMultiset pa'.1 pg.1).bind (fun Y₁ =>
                (((Nonplanar.insertionMultiset {T} G₂).bind fun X_T =>
                  (Nonplanar.insertionMultiset pa'.2 (pg.2 - G₂)).map (Prod.mk X_T)).map
                    (fun p => p.1 + p.2)).map (Prod.mk Y₁))
        rw [Multiset.bind_assoc]
        refine Multiset.bind_congr fun Y₁ _ => ?_
        rw [Multiset.bind_map]
        -- Compose the outer (Prod.mk Y₁) and (·.1+·.2) maps + push through bind.
        rw [Multiset.map_map, Multiset.map_bind]
        -- Inside each X_T, compose Prod.mk X_T with (Y₁, ·.1+·.2): Y₂ ↦ (Y₁, X_T + Y₂).
        rw [show ((Nonplanar.insertionMultiset {T} G₂).bind fun X_T =>
                Multiset.map ((Prod.mk Y₁) ∘
                    fun p : Multiset (Nonplanar α) × Multiset (Nonplanar α) => p.1 + p.2)
                  (Multiset.map (Prod.mk X_T)
                    (Nonplanar.insertionMultiset pa'.2 (pg.2 - G₂)))) =
              ((Nonplanar.insertionMultiset {T} G₂).bind fun X_T =>
                (Nonplanar.insertionMultiset pa'.2 (pg.2 - G₂)).map
                  (fun Y₂ => (Y₁, X_T + Y₂))) from by
          refine Multiset.bind_congr fun X_T _ => ?_
          rw [Multiset.map_map]
          rfl]
        -- Both sides now: bind/bind ⇒ bind_map_comm.
        exact Multiset.bind_map_comm _ _
      · -- Prove the helper: s ×ˢ (t.bind f) = t.bind (b ↦ s ×ˢ f b).
        intros s tt
        show s.bind (fun a => (pg.2.powerset.bind tt).map (Prod.mk a)) =
            pg.2.powerset.bind (fun G₂ => s.bind (fun a => (tt G₂).map (Prod.mk a)))
        rw [Multiset.bind_bind]
        refine Multiset.bind_congr fun G₂ _ => ?_
        rw [Multiset.map_bind]
    · -- Match T-left: pair has X_T on .1. Symmetric to T-right by mirror argument.
      -- Same proof scheme as T-right but with X_T joining the first coord of the pair.
      rw [show (G.powerset.bind fun G₁ =>
              (Nonplanar.insertionMultiset {T} G₁).bind fun X_T =>
                (Nonplanar.insertionMultiset A' (G - G₁)).bind fun X_A' =>
                  (Multiset.antidiagonal X_A').map (fun pA' => (X_T + pA'.1, pA'.2))) =
            (G.powerset.bind fun G₁ =>
              ((Nonplanar.insertionMultiset A' (G - G₁)).bind Multiset.antidiagonal).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (X_T + pA'.1, pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [Multiset.bind_assoc]
        rw [Multiset.bind_bind]
        refine Multiset.bind_congr fun X_A' _ => ?_
        rw [Multiset.bind_map_comm]]
      rw [show (G.powerset.bind fun G₁ =>
              ((Nonplanar.insertionMultiset A' (G - G₁)).bind Multiset.antidiagonal).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (X_T + pA'.1, pA'.2)) =
            (G.powerset.bind fun G₁ =>
              ((Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  (Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                    (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (X_T + pA'.1, pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [ih (G - G₁)]]
      rw [show (G.powerset.bind fun G₁ =>
              ((Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  (Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                    (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                  fun X_T => (X_T + pA'.1, pA'.2)) =
            (G.powerset.bind fun G₁ =>
              (Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                      fun X_T => (X_T + pA'.1, pA'.2)) from by
        refine Multiset.bind_congr fun G₁ _ => ?_
        rw [Multiset.bind_assoc]
        refine Multiset.bind_congr fun pa' _ => ?_
        rw [Multiset.bind_assoc]]
      rw [show (G.powerset.bind fun G₁ =>
              (Multiset.antidiagonal A').bind fun pa' =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                      fun X_T => (X_T + pA'.1, pA'.2)) =
            (Multiset.antidiagonal A').bind fun pa' =>
              G.powerset.bind fun G₁ =>
                (Multiset.antidiagonal (G - G₁)).bind fun pg' =>
                  ((Nonplanar.insertionMultiset pa'.1 pg'.1) ×ˢ
                      (Nonplanar.insertionMultiset pa'.2 pg'.2)).bind
                    fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
                      fun X_T => (X_T + pA'.1, pA'.2)
        from Multiset.bind_bind _ _]
      -- For T-left RHS: antidiag G.bind (pg ↦ NIM (T ::ₘ pa'.1) pg.1 ×ˢ NIM pa'.2 pg.2).
      -- Symmetry: T attaches to the *first* host part. Apply triple_partition_reindex_flip.
      refine Multiset.bind_congr fun pa' _ => ?_
      rw [triple_partition_reindex_flip G
        (fun G₁ x y =>
          ((Nonplanar.insertionMultiset pa'.1 x) ×ˢ
              (Nonplanar.insertionMultiset pa'.2 y)).bind
            (fun pA' => (Nonplanar.insertionMultiset {T} G₁).map
              fun X_T => (X_T + pA'.1, pA'.2)))]
      refine Multiset.bind_congr fun pg _ => ?_
      have h_prod_map_id : (Prod.map (Multiset.cons T) (id : Multiset (Nonplanar α) → _) pa') =
          (T ::ₘ pa'.1, pa'.2) := rfl
      rw [h_prod_map_id]
      show (pg.1.powerset.bind fun G₂ =>
              ((Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)) ×ˢ
                  (Nonplanar.insertionMultiset pa'.2 pg.2)).bind
                (fun pA' => (Nonplanar.insertionMultiset {T} G₂).map
                  fun X_T => (X_T + pA'.1, pA'.2))) =
            (Nonplanar.insertionMultiset (T ::ₘ pa'.1) pg.1) ×ˢ
              (Nonplanar.insertionMultiset pa'.2 pg.2)
      -- Apply insertionMultiset_add_host on NIM (T ::ₘ pa'.1) pg.1.
      rw [show (T ::ₘ pa'.1 : Multiset (Nonplanar α)) = ({T} : Multiset _) + pa'.1 from
            (Multiset.singleton_add T pa'.1).symm,
          Nonplanar.insertionMultiset_add_host {T} pa'.1 pg.1]
      -- RHS: (pg.1.powerset.bind (G₂ ↦ (NIM {T} G₂ ×ˢ NIM pa'.1 (pg.1-G₂)).map (·.1+·.2))) ×ˢ NIM pa'.2 pg.2
      -- Use (s.bind f) ×ˢ t = s.bind (a ↦ f a ×ˢ t).
      rw [show ∀ s : Multiset (Multiset (Nonplanar α)),
              ∀ tt : Multiset (Nonplanar α) → Multiset (Multiset (Nonplanar α)),
                (pg.1.powerset.bind tt) ×ˢ s =
                  pg.1.powerset.bind (fun G₂ => tt G₂ ×ˢ s) from ?_]
      · refine Multiset.bind_congr fun G₂ _ => ?_
        -- Goal: ((NIM pa'.1 (pg.1-G₂)) ×ˢ NIM pa'.2 pg.2).bind (pA' ↦ NIM {T} G₂.map (X_T ↦ (X_T + pA'.1, pA'.2)))
        --     = ((NIM {T} G₂ ×ˢ NIM pa'.1 (pg.1-G₂)).map (·.1+·.2)) ×ˢ NIM pa'.2 pg.2
        -- Unfold ×ˢ everywhere.
        show ((Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).bind (fun Y₁ =>
              (Nonplanar.insertionMultiset pa'.2 pg.2).map (Prod.mk Y₁))).bind
                (fun pA' => (Nonplanar.insertionMultiset {T} G₂).map
                  fun X_T => (X_T + pA'.1, pA'.2)) =
            (Multiset.map (fun p : Multiset (Nonplanar α) × Multiset (Nonplanar α) => p.1 + p.2)
                ((Nonplanar.insertionMultiset {T} G₂).bind (fun X_T =>
                  (Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).map (Prod.mk X_T)))).bind
              (fun first => (Nonplanar.insertionMultiset pa'.2 pg.2).map (Prod.mk first))
        -- Reformulate LHS: bind, bind_map, bind.
        rw [Multiset.bind_assoc]
        -- Goal: NIM pa'.1 (pg.1-G₂).bind (Y₁ ↦ ((NIM pa'.2 pg.2).map (Prod.mk Y₁)).bind (pA' ↦ NIM {T} G₂.map (...)))
        rw [show ((Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).bind (fun Y₁ =>
                ((Nonplanar.insertionMultiset pa'.2 pg.2).map (Prod.mk Y₁)).bind
                  (fun pA' => (Nonplanar.insertionMultiset {T} G₂).map
                    fun X_T => (X_T + pA'.1, pA'.2)))) =
              (Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).bind (fun Y₁ =>
                (Nonplanar.insertionMultiset pa'.2 pg.2).bind (fun Y₂ =>
                  (Nonplanar.insertionMultiset {T} G₂).map
                    fun X_T => (X_T + Y₁, Y₂))) from by
          refine Multiset.bind_congr fun Y₁ _ => ?_
          rw [Multiset.bind_map]]
        -- RHS: Push map p.1+p.2 through inner bind, then bind outer.
        rw [show (Multiset.map (fun p : Multiset (Nonplanar α) × Multiset (Nonplanar α) =>
                  p.1 + p.2)
                ((Nonplanar.insertionMultiset {T} G₂).bind (fun X_T =>
                  (Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).map (Prod.mk X_T)))).bind
              (fun first => (Nonplanar.insertionMultiset pa'.2 pg.2).map (Prod.mk first)) =
              ((Nonplanar.insertionMultiset {T} G₂).bind fun X_T =>
                (Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).bind fun Y₁ =>
                  (Nonplanar.insertionMultiset pa'.2 pg.2).map (fun Y₂ => (X_T + Y₁, Y₂)))
            from by
          rw [Multiset.map_bind, Multiset.bind_assoc]
          refine Multiset.bind_congr fun X_T _ => ?_
          rw [Multiset.map_map, Multiset.bind_map]
          refine Multiset.bind_congr fun Y₁ _ => ?_
          rfl]
        -- Now LHS: NIM pa'.1.bind (Y₁ ↦ NIM pa'.2.bind (Y₂ ↦ NIM {T} G₂.map (X_T ↦ (X_T + Y₁, Y₂))))
        -- RHS: NIM {T} G₂.bind (X_T ↦ NIM pa'.1.bind (Y₁ ↦ NIM pa'.2.map (Y₂ ↦ (X_T + Y₁, Y₂))))
        -- Step a: Apply bind_map_comm to swap Y₂ and X_T inside Y₁.
        rw [show ((Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).bind fun Y₁ =>
              (Nonplanar.insertionMultiset pa'.2 pg.2).bind (fun Y₂ =>
                (Nonplanar.insertionMultiset {T} G₂).map fun X_T => (X_T + Y₁, Y₂))) =
            ((Nonplanar.insertionMultiset pa'.1 (pg.1 - G₂)).bind fun Y₁ =>
              (Nonplanar.insertionMultiset {T} G₂).bind (fun X_T =>
                (Nonplanar.insertionMultiset pa'.2 pg.2).map fun Y₂ => (X_T + Y₁, Y₂)))
            from by
          refine Multiset.bind_congr fun Y₁ _ => ?_
          rw [Multiset.bind_map_comm]]
        -- Step b: Swap Y₁ and X_T via bind_bind.
        rw [Multiset.bind_bind]
      · -- Prove the helper: (s.bind f) ×ˢ t = s.bind (a ↦ f a ×ˢ t).
        intros s tt
        show (pg.1.powerset.bind tt).bind (fun a => s.map (Prod.mk a)) =
            pg.1.powerset.bind (fun G₂ => (tt G₂).bind (fun a => s.map (Prod.mk a)))
        rw [Multiset.bind_assoc]

/-! ### Generic sum/product plumbing -/

/-- Sum of a product-indexed multiset of products factors. -/
theorem sum_map_product_mul {β γ : Type*} (s : Multiset β) (t : Multiset γ)
    (f : β → R) (g : γ → R) :
    ((s ×ˢ t).map (fun p => f p.1 * g p.2)).sum = (s.map f).sum * (t.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.zero_product, Multiset.map_zero, Multiset.sum_zero,
      zero_mul]
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.sum_add, ih,
        Multiset.map_map, Multiset.map_cons, Multiset.sum_cons, add_mul]
    congr 1
    rw [show ((fun p : β × γ => f p.1 * g p.2) ∘ Prod.mk a) = fun b => f a * g b from rfl,
        Multiset.sum_map_mul_left]

/-- `(s ×ˢ t).bind F = s.bind (a ↦ t.bind (b ↦ F (a, b)))`. -/
private theorem product_bind {β γ δ : Type*} (s : Multiset β) (t : Multiset γ)
    (F : β × γ → Multiset δ) :
    (s ×ˢ t).bind F = s.bind (fun a => t.bind (fun b => F (a, b))) := by
  show (s.bind (fun a => t.map (Prod.mk a))).bind F = _
  rw [Multiset.bind_assoc]
  exact Multiset.bind_congr fun a _ => Multiset.bind_map t F (Prod.mk a)

/-- `(s.bind f) ×ˢ t = s.bind (a ↦ f a ×ˢ t)`. -/
private theorem bind_product_left {β γ δ : Type*} (s : Multiset β)
    (f : β → Multiset γ) (t : Multiset δ) :
    (s.bind f) ×ˢ t = s.bind (fun a => f a ×ˢ t) := by
  show (s.bind f).bind (fun a => t.map (Prod.mk a)) = _
  rw [Multiset.bind_assoc]
  rfl

/-- `s ×ˢ (t.bind g) = t.bind (b ↦ s ×ˢ g b)`. -/
private theorem product_bind_right {β γ δ : Type*} (s : Multiset β)
    (t : Multiset γ) (g : γ → Multiset δ) :
    s ×ˢ (t.bind g) = t.bind (fun b => s ×ˢ g b) := by
  show s.bind (fun a => (t.bind g).map (Prod.mk a)) = _
  rw [show (fun a => (t.bind g).map (Prod.mk a)) =
      fun a => t.bind (fun b => (g b).map (Prod.mk a)) from
    funext fun a => Multiset.map_bind t g (Prod.mk a)]
  rw [Multiset.bind_bind]
  rfl

/-- `(s.map f) ×ˢ (t.map g) = (s ×ˢ t).map (Prod.map f g)`. -/
private theorem map_product_map {β γ β' γ' : Type*} (s : Multiset β) (t : Multiset γ)
    (f : β → β') (g : γ → γ') :
    (s.map f) ×ˢ (t.map g) = (s ×ˢ t).map (Prod.map f g) := by
  show (s.map f).bind (fun a => (t.map g).map (Prod.mk a)) = _
  rw [Multiset.bind_map]
  show (s.bind fun a => (t.map g).map (Prod.mk (f a))) = _
  rw [show (fun a => (t.map g).map (Prod.mk (f a))) =
      fun a => t.map (fun b => (f a, g b)) from
    funext fun a => by rw [Multiset.map_map]; rfl]
  show _ = ((s.bind fun a => t.map (Prod.mk a)).map (Prod.map f g))
  rw [Multiset.map_bind]
  refine Multiset.bind_congr fun a _ => ?_
  rw [Multiset.map_map]
  rfl

/-- Boundary conversion: a powerset-with-complement bind equals an
    antidiagonal bind (second slot = chosen sub-multiset). -/
private theorem powerset_bind_eq_antidiagonal_bind {β γ : Type*} [DecidableEq β]
    (B : Multiset β) (m : Multiset β → Multiset β → Multiset γ) :
    B.powerset.bind (fun B₁ => m B₁ (B - B₁)) =
      (Multiset.antidiagonal B).bind (fun pb => m pb.2 pb.1) := by
  rw [Multiset.antidiagonal_eq_map_powerset, Multiset.bind_map]

/-! ### quadBind (from dev_quad.lean) -/

private def quadBind {β γ : Type*} (B : Multiset β)
    (g : Multiset β → Multiset β → Multiset β → Multiset β → Multiset γ) :
    Multiset γ :=
  (Multiset.antidiagonal B).bind (fun p =>
    (Multiset.antidiagonal p.1).bind (fun u =>
      (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2)))

private theorem quadBind_zero {β γ : Type*}
    (g : Multiset β → Multiset β → Multiset β → Multiset β → Multiset γ) :
    quadBind 0 g = g 0 0 0 0 := by
  simp only [quadBind, Multiset.antidiagonal_zero, Multiset.singleton_bind]

private theorem quadBind_cons {β γ : Type*} (x : β) (B : Multiset β)
    (g : Multiset β → Multiset β → Multiset β → Multiset β → Multiset γ) :
    quadBind (x ::ₘ B) g =
      quadBind B (fun a b c d => g (x ::ₘ a) b c d) +
      quadBind B (fun a b c d => g a (x ::ₘ b) c d) +
      quadBind B (fun a b c d => g a b (x ::ₘ c) d) +
      quadBind B (fun a b c d => g a b c (x ::ₘ d)) := by
  have h2 : (((Multiset.antidiagonal B).map (Prod.map id (x ::ₘ ·))).bind
        (fun p => (Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2)))) =
      quadBind B (fun a b c d => g a b c (x ::ₘ d)) +
      quadBind B (fun a b c d => g a b (x ::ₘ c) d) := by
    rw [Multiset.bind_map]
    have step : ∀ p ∈ Multiset.antidiagonal B,
        ((Multiset.antidiagonal (Prod.map id (x ::ₘ ·) p).1).bind (fun u =>
          (Multiset.antidiagonal (Prod.map id (x ::ₘ ·) p).2).bind (fun v =>
            g u.1 u.2 v.1 v.2))) =
        ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 (x ::ₘ v.2)))) +
        ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 (x ::ₘ v.1) v.2))) := by
      intro p _
      have inner : ∀ u : Multiset β × Multiset β,
          ((Multiset.antidiagonal (x ::ₘ p.2)).bind (fun v => g u.1 u.2 v.1 v.2)) =
          ((Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 (x ::ₘ v.2))) +
          ((Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 (x ::ₘ v.1) v.2)) := by
        intro u
        rw [Multiset.antidiagonal_cons, Multiset.add_bind, Multiset.bind_map,
            Multiset.bind_map]
        rfl
      show ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal (x ::ₘ p.2)).bind (fun v => g u.1 u.2 v.1 v.2))) = _
      rw [Multiset.bind_congr (fun u _ => inner u), Multiset.bind_add]
    rw [Multiset.bind_congr step, Multiset.bind_add]
    rfl
  have h1 : (((Multiset.antidiagonal B).map (Prod.map (x ::ₘ ·) id)).bind
        (fun p => (Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2)))) =
      quadBind B (fun a b c d => g a (x ::ₘ b) c d) +
      quadBind B (fun a b c d => g (x ::ₘ a) b c d) := by
    rw [Multiset.bind_map]
    have step : ∀ p ∈ Multiset.antidiagonal B,
        ((Multiset.antidiagonal (Prod.map (x ::ₘ ·) id p).1).bind (fun u =>
          (Multiset.antidiagonal (Prod.map (x ::ₘ ·) id p).2).bind (fun v =>
            g u.1 u.2 v.1 v.2))) =
        ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 (x ::ₘ u.2) v.1 v.2))) +
        ((Multiset.antidiagonal p.1).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g (x ::ₘ u.1) u.2 v.1 v.2))) := by
      intro p _
      show ((Multiset.antidiagonal (x ::ₘ p.1)).bind (fun u =>
          (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2))) = _
      rw [Multiset.antidiagonal_cons, Multiset.add_bind, Multiset.bind_map,
          Multiset.bind_map]
      rfl
    rw [Multiset.bind_congr step, Multiset.bind_add]
    rfl
  show ((Multiset.antidiagonal (x ::ₘ B)).bind (fun p =>
      (Multiset.antidiagonal p.1).bind (fun u =>
        (Multiset.antidiagonal p.2).bind (fun v => g u.1 u.2 v.1 v.2)))) = _
  rw [Multiset.antidiagonal_cons, Multiset.add_bind, h2, h1]
  abel

private theorem quadBind_middle_swap {β γ : Type*} (B : Multiset β)
    (g : Multiset β → Multiset β → Multiset β → Multiset β → Multiset γ) :
    quadBind B g = quadBind B (fun a b c d => g a c b d) := by
  induction B using Multiset.induction_on generalizing g with
  | empty => rw [quadBind_zero, quadBind_zero]
  | cons x B ih =>
    rw [quadBind_cons, quadBind_cons]
    rw [← ih (fun a b c d => g (x ::ₘ a) b c d),
        ← ih (fun a b c d => g a b (x ::ₘ c) d),
        ← ih (fun a b c d => g a (x ::ₘ b) c d),
        ← ih (fun a b c d => g a b c (x ::ₘ d))]
    abel

/-! ### The product index multiset -/

/-- Index multiset of GL-product outputs: forests `X + (B' − H)` over
    `H ⊆ B'` and `X ∈ NIM(A', H)`. `product (of' A') (of' B')` is the
    formal sum of `of'` over this multiset (`of'_mul_of'_nim_form`). -/
private noncomputable def productIdx (A' B' : Forest (Nonplanar α)) :
    Multiset (Forest (Nonplanar α)) :=
  B'.powerset.bind (fun H =>
    (Nonplanar.insertionMultiset A' H).map (fun X => X + (B' - H)))

/-- Antidiagonal form of `productIdx`. -/
private theorem productIdx_eq_antidiagonal (A' B' : Forest (Nonplanar α)) :
    productIdx A' B' =
      (Multiset.antidiagonal B').bind (fun u =>
        (Nonplanar.insertionMultiset A' u.2).map (fun X => X + u.1)) := by
  unfold productIdx
  exact powerset_bind_eq_antidiagonal_bind B'
    (fun H Bf => (Nonplanar.insertionMultiset A' H).map (fun X => X + Bf))

/-- `pairing (product (of' A') (of' B')) z` as a `productIdx`-indexed sum. -/
private theorem pairing_product_of'_expand (A' B' : Forest (Nonplanar α))
    (z : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) (product (ConnesKreimer.of' A') (ConnesKreimer.of' B')) z =
      ((productIdx A' B').map (fun W =>
        pairing (R := R) (ConnesKreimer.of' W) z)).sum := by
  have hexp : product (ConnesKreimer.of' (R := R) A') (ConnesKreimer.of' B') =
      (((productIdx A' B').map (fun W => ConnesKreimer.of' (R := R) W)).sum :
        ConnesKreimer R (Nonplanar α)) := by
    show ((of' (R := R) A' : GrossmanLarson R α) * of' B' : GrossmanLarson R α) = _
    rw [of'_mul_of'_nim_form]
    show (((B'.powerset.bind fun H =>
        (Nonplanar.insertionMultiset A' H).map fun X =>
          ConnesKreimer.of' (R := R) (X + (B' - H))).sum :
        ConnesKreimer R (Nonplanar α))) = _
    unfold productIdx
    rw [Multiset.map_bind]
    congr 1
    refine Multiset.bind_congr fun H _ => ?_
    rw [Multiset.map_map]
    rfl
  rw [show pairing (R := R) (product (ConnesKreimer.of' A') (ConnesKreimer.of' B')) z =
      (pairing (R := R)).flip z (product (ConnesKreimer.of' A') (ConnesKreimer.of' B'))
    from rfl]
  rw [hexp, map_multiset_sum, Multiset.map_map]
  rfl

/-! ### The index identity -/

/-- **Index identity**: the cut-split index multiset of `A ⋆ B` against a
    two-factor product equals the doubly-split product index. The multiset
    backbone of `pairing_product_of'_mul_of'`. -/
private theorem productIdx_mul_split (A B : Forest (Nonplanar α)) :
    (B.powerset.bind (fun B₁ =>
       (Nonplanar.insertionMultiset A B₁).bind (fun X =>
         Multiset.antidiagonal (X + (B - B₁))))) =
      (Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).bind (fun pq =>
        productIdx pq.1.1 pq.2.1 ×ˢ productIdx pq.1.2 pq.2.2) := by
  -- Step A+B+C+D: inner antidiagonal split + Lemma G, per B₁.
  have stepACD : ∀ B₁ ∈ B.powerset,
      ((Nonplanar.insertionMultiset A B₁).bind (fun X =>
        Multiset.antidiagonal (X + (B - B₁)))) =
      (Multiset.antidiagonal A).bind (fun pa =>
        (Multiset.antidiagonal B₁).bind (fun pH =>
          (Multiset.antidiagonal (B - B₁)).bind (fun q =>
            (Nonplanar.insertionMultiset pa.1 pH.1 ×ˢ
              Nonplanar.insertionMultiset pa.2 pH.2).map
              (fun pX => (pX.1 + q.1, pX.2 + q.2))))) := by
    intro B₁ _
    have h1 : ((Nonplanar.insertionMultiset A B₁).bind (fun X =>
          Multiset.antidiagonal (X + (B - B₁)))) =
        ((Nonplanar.insertionMultiset A B₁).bind Multiset.antidiagonal).bind
          (fun p => (Multiset.antidiagonal (B - B₁)).map
            (fun q => (p.1 + q.1, p.2 + q.2))) := by
      rw [Multiset.bind_assoc]
      refine Multiset.bind_congr fun X _ => ?_
      exact Multiset.antidiagonal_add X (B - B₁)
    rw [h1, Nonplanar.insertionMultiset_antidiagonal, Multiset.bind_assoc]
    refine Multiset.bind_congr fun pa _ => ?_
    rw [Multiset.bind_assoc]
    refine Multiset.bind_congr fun pH _ => ?_
    -- (NIMprod).bind (pX ↦ (antidiag Bf).map h) = (antidiag Bf).bind (q ↦ NIMprod.map ...)
    exact Multiset.bind_map_comm _ _
  rw [Multiset.bind_congr stepACD]
  -- Step E: pull the antidiagonal-A bind out front.
  rw [Multiset.bind_bind]
  -- Step F+G+H: per pa, reorganize the B-part into quadBind form and swap.
  have stepB : ∀ pa : Forest (Nonplanar α) × Forest (Nonplanar α),
      (B.powerset.bind (fun B₁ =>
        (Multiset.antidiagonal B₁).bind (fun pH =>
          (Multiset.antidiagonal (B - B₁)).bind (fun q =>
            (Nonplanar.insertionMultiset pa.1 pH.1 ×ˢ
              Nonplanar.insertionMultiset pa.2 pH.2).map
              (fun pX => (pX.1 + q.1, pX.2 + q.2)))))) =
      (Multiset.antidiagonal B).bind (fun pb =>
        productIdx pa.1 pb.1 ×ˢ productIdx pa.2 pb.2) := by
    intro pa
    -- Boundary: powerset + complement → antidiagonal.
    rw [powerset_bind_eq_antidiagonal_bind B (fun B₁ Bf =>
      (Multiset.antidiagonal B₁).bind (fun pH =>
        (Multiset.antidiagonal Bf).bind (fun q =>
          (Nonplanar.insertionMultiset pa.1 pH.1 ×ˢ
            Nonplanar.insertionMultiset pa.2 pH.2).map
            (fun pX => (pX.1 + q.1, pX.2 + q.2)))))]
    -- Commute the two inner antidiagonal binds to reach quadBind shape.
    have hcomm : ∀ pb : Forest (Nonplanar α) × Forest (Nonplanar α),
        ((Multiset.antidiagonal pb.2).bind (fun pH =>
          (Multiset.antidiagonal pb.1).bind (fun q =>
            (Nonplanar.insertionMultiset pa.1 pH.1 ×ˢ
              Nonplanar.insertionMultiset pa.2 pH.2).map
              (fun pX => (pX.1 + q.1, pX.2 + q.2))))) =
        ((Multiset.antidiagonal pb.1).bind (fun q =>
          (Multiset.antidiagonal pb.2).bind (fun pH =>
            (Nonplanar.insertionMultiset pa.1 pH.1 ×ˢ
              Nonplanar.insertionMultiset pa.2 pH.2).map
              (fun pX => (pX.1 + q.1, pX.2 + q.2))))) := by
      intro pb
      exact Multiset.bind_bind _ _
    rw [Multiset.bind_congr (fun pb _ => hcomm pb)]
    -- Now: quadBind B (fun q₁ q₂ H₁ H₂ => k H₁ H₂ q₁ q₂); middle-swap it.
    rw [show ((Multiset.antidiagonal B).bind (fun pb =>
        (Multiset.antidiagonal pb.1).bind (fun q =>
          (Multiset.antidiagonal pb.2).bind (fun pH =>
            (Nonplanar.insertionMultiset pa.1 pH.1 ×ˢ
              Nonplanar.insertionMultiset pa.2 pH.2).map
              (fun pX => (pX.1 + q.1, pX.2 + q.2)))))) =
      quadBind B (fun a b c d =>
        (Nonplanar.insertionMultiset pa.1 c ×ˢ
          Nonplanar.insertionMultiset pa.2 d).map
          (fun pX => (pX.1 + a, pX.2 + b))) from rfl]
    rw [quadBind_middle_swap]
    -- Unfold back and match against productIdx ×ˢ productIdx.
    show ((Multiset.antidiagonal B).bind (fun pb =>
        (Multiset.antidiagonal pb.1).bind (fun u =>
          (Multiset.antidiagonal pb.2).bind (fun v =>
            (Nonplanar.insertionMultiset pa.1 u.2 ×ˢ
              Nonplanar.insertionMultiset pa.2 v.2).map
              (fun pX => (pX.1 + u.1, pX.2 + v.1)))))) = _
    refine Multiset.bind_congr fun pb _ => ?_
    rw [productIdx_eq_antidiagonal, productIdx_eq_antidiagonal,
        bind_product_left]
    refine Multiset.bind_congr fun u _ => ?_
    rw [product_bind_right]
    refine Multiset.bind_congr fun v _ => ?_
    rw [map_product_map]
    rfl
  rw [Multiset.bind_congr (fun pa _ => stepB pa)]
  -- Outer product-bind unfolding on the RHS.
  rw [product_bind]

/-! ### The fused product rule for the GL product -/

/-- **GL-product/CK-product pairing duality** (basis form): pairing a GL
    product against a CK product decomposes over independent splits of
    the two GL factors:

    `⟨A ⋆ B, C₁ · C₂⟩ =
       Σ_{A = A₁+A₂} Σ_{B = B₁+B₂} ⟨A₁ ⋆ B₁, C₁⟩ · ⟨A₂ ⋆ B₂, C₂⟩`.

    This is the multiplicative-structure compatibility making the GL
    basis dual to the CK polynomial algebra: combines
    `pairing_of'_mul` (pairing product rule, one application per output
    forest of `A ⋆ B`) with `insertionMultiset_antidiagonal` (routing
    splits of grafted outputs) and the powerset/antidiagonal
    bookkeeping for the non-grafted guest components.

    Proof: reduce both sides to sums of the diagonal pairing over the
    index multiset `productIdx`; the multiset backbone is
    `productIdx_mul_split`, whose combinatorial heart is the middle-four
    interchange `quadBind_middle_swap`. -/
theorem pairing_product_of'_mul_of' (A B C₁ C₂ : Forest (Nonplanar α)) :
    pairing (R := R)
        (product (ConnesKreimer.of' A) (ConnesKreimer.of' B))
        (ConnesKreimer.of' C₁ * ConnesKreimer.of' C₂) =
      ((Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).map (fun pq =>
        pairing (R := R)
            (product (ConnesKreimer.of' pq.1.1) (ConnesKreimer.of' pq.2.1))
            (ConnesKreimer.of' C₁) *
        pairing (R := R)
            (product (ConnesKreimer.of' pq.1.2) (ConnesKreimer.of' pq.2.2))
            (ConnesKreimer.of' C₂))).sum := by
  -- φ evaluates a split pair against (C₁, C₂).
  set φ : Forest (Nonplanar α) × Forest (Nonplanar α) → R :=
    fun p => pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
      pairing (R := R) (ConnesKreimer.of' p.2) (ConnesKreimer.of' C₂) with hφ
  -- LHS = sum of φ over the cut-split index multiset.
  have hLHS : pairing (R := R)
        (product (ConnesKreimer.of' A) (ConnesKreimer.of' B))
        (ConnesKreimer.of' C₁ * ConnesKreimer.of' C₂) =
      (((B.powerset.bind (fun B₁ =>
        (Nonplanar.insertionMultiset A B₁).bind (fun X =>
          Multiset.antidiagonal (X + (B - B₁)))))).map φ).sum := by
    rw [pairing_product_of'_expand]
    unfold productIdx
    rw [Multiset.map_bind, Multiset.map_bind, Multiset.sum_bind, Multiset.sum_bind]
    congr 1
    refine Multiset.map_congr rfl fun B₁ _ => ?_
    rw [Multiset.map_map, Multiset.map_bind, Multiset.sum_bind]
    congr 1
    refine Multiset.map_congr rfl fun X _ => ?_
    show pairing (R := R) (ConnesKreimer.of' (X + (B - B₁)))
        (ConnesKreimer.of' C₁ * ConnesKreimer.of' C₂) = _
    rw [pairing_of'_mul]
  rw [hLHS, productIdx_mul_split, Multiset.map_bind, Multiset.sum_bind]
  congr 1
  refine Multiset.map_congr rfl fun pq _ => ?_
  show ((productIdx pq.1.1 pq.2.1 ×ˢ productIdx pq.1.2 pq.2.2).map φ).sum = _
  rw [hφ]
  rw [sum_map_product_mul (productIdx pq.1.1 pq.2.1) (productIdx pq.1.2 pq.2.2)
      (fun W => pairing (R := R) (ConnesKreimer.of' W) (ConnesKreimer.of' C₁))
      (fun W => pairing (R := R) (ConnesKreimer.of' W) (ConnesKreimer.of' C₂))]
  rw [← pairing_product_of'_expand, ← pairing_product_of'_expand]

end GrossmanLarson

end RootedTree
