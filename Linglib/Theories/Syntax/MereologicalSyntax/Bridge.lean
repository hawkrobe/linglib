import Linglib.Theories.Syntax.MereologicalSyntax.Basic
import Linglib.Theories.Syntax.SynGraph

set_option autoImplicit false

/-!
# Bridge: SynObj → SynGraph
@cite{adger-2025}

Embeds tree-based syntactic objects (`SynObj`) into graph-based structures
(`SynGraph MLabel`), making `SynGraph` the canonical operational type for
Angular Locality while preserving `SynObj` as an ergonomic builder.

`SynObj` is an inductive type that gives structural recursion and `rfl`
proofs — useful for tree-shaped work (classifier hierarchies, basic clause
structure). `SynGraph` supports multiparthood (unbounded in-degree),
required for movement in mereological syntax. The embedding connects them:
build with `SynObj`, convert to `SynGraph` when you need AL, movement,
or island constraints.

## Pre-order Indexing

The embedding assigns node indices via pre-order traversal:
- Root = 0
- 1-part subtree: indices `[1, 1 + onePart.size)`
- 2-part subtree: indices `[1 + onePart.size, size)`

## Key Results

- `toSynGraph`: embeds any `SynObj` as a `SynGraph MLabel`
- `isTree` verified on all test structures
- `compLine` agrees with `onePartChain`
- `angularLocalityOK` (tree, label-based) agrees with `satisfiesAL`
  (graph, index-based) — verified on the critical cross-dimensional
  structure from @cite{adger-2025} p. 95
-/

namespace MereologicalSyntax

-- ════════════════════════════════════════════════════
-- § 1. Size
-- ════════════════════════════════════════════════════

/-- Number of nodes in a `SynObj` tree. -/
def SynObj.size : SynObj → Nat
  | .leaf _ => 1
  | .sub₁ _ one => 1 + one.size
  | .sub₁₂ _ one two => 1 + one.size + two.size

theorem SynObj.size_pos (t : SynObj) : 0 < t.size := by
  cases t <;> simp [size] <;> omega

-- ════════════════════════════════════════════════════
-- § 2. Embedding
-- ════════════════════════════════════════════════════

/-- Embed a `SynObj` tree into a `SynGraph MLabel`, with a proof that
    `numNodes > 0`. Used by `toSynGraph` which extracts the graph. -/
def SynObj.toSynGraphAux :
    SynObj → { g : SynGraph MLabel // 0 < g.numNodes }
  | .leaf l =>
    ⟨{ numNodes := 1
       label := fun _ => l
       onePart := fun _ => none
       twoPart := fun _ => none }, Nat.one_pos⟩
  | .sub₁ l one =>
    let ⟨g, hg⟩ := one.toSynGraphAux
    ⟨{ numNodes := 1 + g.numNodes
       label := fun ⟨i, hi⟩ =>
         if i = 0 then l else g.label ⟨i - 1, by omega⟩
       onePart := fun ⟨i, hi⟩ =>
         if i = 0 then some ⟨1, by omega⟩
         else (g.onePart ⟨i - 1, by omega⟩).map
           (fun ⟨j, hj⟩ => ⟨j + 1, by omega⟩)
       twoPart := fun ⟨i, hi⟩ =>
         if i = 0 then none
         else (g.twoPart ⟨i - 1, by omega⟩).map
           (fun ⟨j, hj⟩ => ⟨j + 1, by omega⟩)
       }, by show 0 < 1 + g.numNodes; omega⟩
  | .sub₁₂ l one two =>
    let ⟨g₁, hg₁⟩ := one.toSynGraphAux
    let ⟨g₂, hg₂⟩ := two.toSynGraphAux
    ⟨{ numNodes := 1 + g₁.numNodes + g₂.numNodes
       label := fun ⟨i, hi⟩ =>
         if i = 0 then l
         else if h : i - 1 < g₁.numNodes then g₁.label ⟨i - 1, h⟩
         else g₂.label ⟨i - 1 - g₁.numNodes, by omega⟩
       onePart := fun ⟨i, hi⟩ =>
         if i = 0 then some ⟨1, by omega⟩
         else if h : i - 1 < g₁.numNodes then
           (g₁.onePart ⟨i - 1, h⟩).map
             (fun ⟨j, hj⟩ => ⟨j + 1, by omega⟩)
         else
           (g₂.onePart ⟨i - 1 - g₁.numNodes, by omega⟩).map
             (fun ⟨j, hj⟩ => ⟨j + 1 + g₁.numNodes, by omega⟩)
       twoPart := fun ⟨i, hi⟩ =>
         if i = 0 then some ⟨1 + g₁.numNodes, by omega⟩
         else if h : i - 1 < g₁.numNodes then
           (g₁.twoPart ⟨i - 1, h⟩).map
             (fun ⟨j, hj⟩ => ⟨j + 1, by omega⟩)
         else
           (g₂.twoPart ⟨i - 1 - g₁.numNodes, by omega⟩).map
             (fun ⟨j, hj⟩ => ⟨j + 1 + g₁.numNodes, by omega⟩)
       }, by show 0 < 1 + g₁.numNodes + g₂.numNodes; omega⟩

/-- Embed a `SynObj` tree into a `SynGraph MLabel`.

    Node indexing follows pre-order: root = 0, then 1-part subtree,
    then 2-part subtree. The result satisfies `isTree` (acyclic,
    in-degree ≤ 1).

    The definition is compositional: each case builds the graph from
    subgraphs, making structural induction possible. -/
def SynObj.toSynGraph (t : SynObj) : SynGraph MLabel := t.toSynGraphAux.val

theorem SynObj.toSynGraph_pos (t : SynObj) : 0 < t.toSynGraph.numNodes :=
  t.toSynGraphAux.property

-- ════════════════════════════════════════════════════
-- § 4. Graph-Based AL Check (via labels)
-- ════════════════════════════════════════════════════

/-- Angular Locality check via the graph representation: does any node
    with label `l` satisfy `satisfiesAL` for the root (node 0)?

    This is the existential analogue of `satisfiesAL` that operates
    on labels rather than node indices, making it directly comparable
    to the tree-based `angularLocalityOK`. -/
def SynObj.alOK_via_graph (l : MLabel) (t : SynObj) : Bool :=
  let g := t.toSynGraph
  have hroot : 0 < g.numNodes := t.toSynGraph_pos
  (List.range g.numNodes).any λ i =>
    if h : i < g.numNodes then
      g.label ⟨i, h⟩ == l && g.satisfiesAL ⟨i, h⟩ ⟨0, hroot⟩
    else false

-- ════════════════════════════════════════════════════
-- § 5. Verification
-- ════════════════════════════════════════════════════

section BridgeTests

-- ────────────────────────────────────────────────────
-- (a) Antilocal: C ──1──▶ N
-- ────────────────────────────────────────────────────

private def t_antilocal := SynObj.sub₁ .C (.leaf .N)

theorem antilocal_al_agrees :
    angularLocalityOK .N t_antilocal = t_antilocal.alOK_via_graph .N := by native_decide

theorem antilocal_isTree :
    t_antilocal.toSynGraph.isTree = true := by native_decide

-- ────────────────────────────────────────────────────
-- (b) Rollup: C ──1──▶ T ──1──▶ v ──1──▶ V, v ──2──▶ D
-- ────────────────────────────────────────────────────

private def t_rollup := SynObj.sub₁ .C (.sub₁ .T (.sub₁₂ .v (.leaf .V) (.leaf .D)))

theorem rollup_2part_agrees :
    angularLocalityOK .D t_rollup = t_rollup.alOK_via_graph .D := by native_decide

theorem rollup_1part_agrees :
    angularLocalityOK .V t_rollup = t_rollup.alOK_via_graph .V := by native_decide

theorem rollup_isTree :
    t_rollup.toSynGraph.isTree = true := by native_decide

theorem rollup_compLine :
    t_rollup.compLine =
    t_rollup.toSynGraph.onePartChain ⟨0, by decide⟩ := by native_decide

-- ────────────────────────────────────────────────────
-- (c) Cross-dimensional (@cite{adger-2025} p. 95)
--     C ──1──▶ T ──1──▶ V,  T ──2──▶ v ──1──▶ N,  v ──2──▶ D
--
--     D (within dim-2) CAN subjoin to C.
--     N (cross-dim: N <₁ v <₂ T) CANNOT subjoin to C.
--     This is the critical test that the corrected AL gets right.
-- ────────────────────────────────────────────────────

private def t_crossdim := SynObj.sub₁ .C
  (.sub₁₂ .T (.leaf .V) (.sub₁₂ .v (.leaf .N) (.leaf .D)))

theorem crossdim_allows_agrees :
    angularLocalityOK .D t_crossdim = t_crossdim.alOK_via_graph .D := by native_decide

theorem crossdim_blocks_agrees :
    angularLocalityOK .N t_crossdim = t_crossdim.alOK_via_graph .N := by native_decide

theorem crossdim_isTree :
    t_crossdim.toSynGraph.isTree = true := by native_decide

theorem crossdim_compLine :
    t_crossdim.compLine =
    t_crossdim.toSynGraph.onePartChain ⟨0, by decide⟩ := by native_decide

-- ────────────────────────────────────────────────────
-- (d) Classifier structure: D ──1──▶ Cl ──1──▶ N
-- ────────────────────────────────────────────────────

private def t_classifier := SynObj.sub₁ .D (.sub₁ .Cl (.leaf .N))

theorem classifier_compLine :
    t_classifier.compLine =
    t_classifier.toSynGraph.onePartChain ⟨0, by decide⟩ := by native_decide

theorem classifier_isTree :
    t_classifier.toSynGraph.isTree = true := by native_decide

end BridgeTests

-- ════════════════════════════════════════════════════
-- § 6. General Agreement
-- ════════════════════════════════════════════════════

-- ── Abbreviations ──

private abbrev G (t : SynObj) := t.toSynGraphAux.val
private theorem G_pos (t : SynObj) : 0 < (G t).numNodes := t.toSynGraphAux.property
private theorem G_nn1 (l : MLabel) (one : SynObj) :
    (G (.sub₁ l one)).numNodes = 1 + (G one).numNodes := rfl
private theorem G_nn12 (l : MLabel) (one two : SynObj) :
    (G (.sub₁₂ l one two)).numNodes = 1 + (G one).numNodes + (G two).numNodes := rfl
set_option hygiene false in
local macro "nn_omega" : tactic =>
  `(tactic| first
    | omega
    | (simp only [G_nn1, G_nn12]; omega)
    | (have := G_pos one; simp only [G_nn1, G_nn12]; omega)
    | (have := G_pos two; simp only [G_nn1, G_nn12]; omega)
    | (have := G_pos one; have := G_pos two; simp only [G_nn1, G_nn12]; omega))

-- ── List/Bool helpers ──

private theorem any_or_distrib {α : Type} (xs : List α) (f g : α → Bool) :
    xs.any (fun x => f x || g x) = (xs.any f || xs.any g) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.any_cons, ih]
    cases f x <;> cases g x <;> cases xs.any f <;> cases xs.any g <;> rfl

private theorem any_const_false {α : Type} (xs : List α) :
    xs.any (fun _ => false) = false := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [List.any_cons, ih]

private theorem scan_chain_swap {n : Nat} (chain : List (Fin n)) (f : Fin n → Bool) :
    (List.range n).any (fun i => if h : i < n then
      f ⟨i, h⟩ && chain.any (· == ⟨i, h⟩) else false) =
    chain.any (fun k => f k) := by
  induction chain with
  | nil =>
    apply Bool.eq_false_iff.mpr; intro h
    rw [List.any_eq_true] at h
    obtain ⟨i, _, hval⟩ := h; simp at hval
  | cons x xs ih =>
    simp only [List.any_cons]
    suffices hsuff :
      (List.range n).any (fun i => if h : i < n then
        f ⟨i, h⟩ && (x == ⟨i, h⟩ || xs.any (· == ⟨i, h⟩)) else false) =
      (f x || xs.any (fun k => f k)) by exact hsuff
    have h_distrib : ∀ i, (if h : i < n then
        f ⟨i, h⟩ && (x == ⟨i, h⟩ || xs.any (· == ⟨i, h⟩)) else false) =
      ((if h : i < n then f ⟨i, h⟩ && (x == ⟨i, h⟩) else false) ||
       (if h : i < n then f ⟨i, h⟩ && xs.any (· == ⟨i, h⟩) else false)) := by
      intro i; split <;> simp [Bool.and_or_distrib_left]
    simp_rw [h_distrib]
    rw [any_or_distrib, ih]
    congr 1
    suffices h_sing : (List.range n).any
      (fun i => if h : i < n then f ⟨i, h⟩ && (x == ⟨i, h⟩) else false) = f x by exact h_sing
    cases hfx : f x with
    | true =>
      rw [List.any_eq_true]
      exact ⟨x.val, List.mem_range.mpr x.isLt, by
        simp only [dif_pos x.isLt, hfx, Bool.true_and]; simp [BEq.beq]⟩
    | false =>
      apply Bool.eq_false_iff.mpr; intro h
      rw [List.any_eq_true] at h
      obtain ⟨i, hi_mem, hval⟩ := h
      simp only [List.mem_range] at hi_mem
      simp only [dif_pos hi_mem] at hval
      have ⟨hf_true, hbeq⟩ := Bool.and_eq_true_iff.mp hval
      simp [BEq.beq] at hbeq
      rw [← hbeq] at hf_true
      exact absurd hf_true (by rw [hfx]; decide)

-- ── Option.map helper ──

private theorem option_map_some_elim {α β : Type} {f : α → β} {o : Option α} {b : β}
    (h : o.map f = some b) : ∃ a, o = some a ∧ f a = b := by
  cases o with
  | none => simp at h
  | some a => simp only [Option.map_some] at h; exact ⟨a, rfl, Option.some.inj h⟩

-- ── Edges increasing ──

private theorem edges_incr_op (t : SynObj) :
    ∀ (i j : Fin (G t).numNodes),
    (G t).onePart i = some j → i.val < j.val := by
  induction t with
  | leaf _ => intro i j h; simp [G, SynObj.toSynGraphAux] at h
  | sub₁ l one ih =>
    intro ⟨i, hi⟩ ⟨j, hj⟩ h; show i < j
    change (G (.sub₁ l one)).onePart ⟨i, hi⟩ = some ⟨j, hj⟩ at h
    simp only [G, SynObj.toSynGraphAux] at h
    by_cases h0 : i = 0
    · subst h0; simp only [ite_true] at h
      have := congr_arg Fin.val (Option.some.inj h); simp only [Fin.val_mk] at this; omega
    · have hnn : (G (.sub₁ l one)).numNodes = 1 + (G one).numNodes := rfl
      simp only [if_neg h0] at h
      have hi' : i - 1 < (G one).numNodes := by nn_omega
      obtain ⟨⟨k, hkb⟩, hk_eq, hk_fin⟩ := option_map_some_elim h
      have := ih ⟨i - 1, hi'⟩ ⟨k, hkb⟩ hk_eq
      simp only [Fin.val_mk] at this
      have := congr_arg Fin.val hk_fin; simp only [Fin.val_mk] at this; omega
  | sub₁₂ l one two ih₁ ih₂ =>
    intro ⟨i, hi⟩ ⟨j, hj⟩ h; show i < j
    have hnn : (G (.sub₁₂ l one two)).numNodes = 1 + (G one).numNodes + (G two).numNodes := rfl
    change (G (.sub₁₂ l one two)).onePart ⟨i, hi⟩ = some ⟨j, hj⟩ at h
    simp only [G, SynObj.toSynGraphAux] at h
    by_cases h0 : i = 0
    · subst h0; simp only [ite_true] at h
      have := congr_arg Fin.val (Option.some.inj h); simp only [Fin.val_mk] at this; omega
    · simp only [if_neg h0] at h
      by_cases h1 : i - 1 < (G one).numNodes
      · simp only [dif_pos h1] at h
        obtain ⟨⟨k, hkb⟩, hk_eq, hk_fin⟩ := option_map_some_elim h
        have := ih₁ ⟨i - 1, h1⟩ ⟨k, hkb⟩ hk_eq
        simp only [Fin.val_mk] at this
        have := congr_arg Fin.val hk_fin; simp only [Fin.val_mk] at this; omega
      · simp only [dif_neg h1] at h
        have hi' : i - 1 - (G one).numNodes < (G two).numNodes := by nn_omega
        obtain ⟨⟨k, hkb⟩, hk_eq, hk_fin⟩ := option_map_some_elim h
        have := ih₂ ⟨i - 1 - (G one).numNodes, hi'⟩ ⟨k, hkb⟩ hk_eq
        simp only [Fin.val_mk] at this
        have := congr_arg Fin.val hk_fin; simp only [Fin.val_mk] at this
        have : (G one).numNodes = (↑one.toSynGraphAux : SynGraph MLabel).numNodes := rfl
        omega

private theorem edges_incr_tp (t : SynObj) :
    ∀ (i j : Fin (G t).numNodes),
    (G t).twoPart i = some j → i.val < j.val := by
  induction t with
  | leaf _ => intro i j h; simp [G, SynObj.toSynGraphAux] at h
  | sub₁ l one ih =>
    intro ⟨i, hi⟩ ⟨j, hj⟩ h; show i < j
    have hnn : (G (.sub₁ l one)).numNodes = 1 + (G one).numNodes := rfl
    change (G (.sub₁ l one)).twoPart ⟨i, hi⟩ = some ⟨j, hj⟩ at h
    simp only [G, SynObj.toSynGraphAux] at h
    by_cases h0 : i = 0
    · subst h0; simp only [ite_true] at h; simp at h
    · simp only [if_neg h0] at h
      have hi' : i - 1 < (G one).numNodes := by nn_omega
      obtain ⟨⟨k, hkb⟩, hk_eq, hk_fin⟩ := option_map_some_elim h
      have := ih ⟨i - 1, hi'⟩ ⟨k, hkb⟩ hk_eq
      simp only [Fin.val_mk] at this
      have := congr_arg Fin.val hk_fin; simp only [Fin.val_mk] at this; omega
  | sub₁₂ l one two ih₁ ih₂ =>
    intro ⟨i, hi⟩ ⟨j, hj⟩ h; show i < j
    have hnn : (G (.sub₁₂ l one two)).numNodes = 1 + (G one).numNodes + (G two).numNodes := rfl
    change (G (.sub₁₂ l one two)).twoPart ⟨i, hi⟩ = some ⟨j, hj⟩ at h
    simp only [G, SynObj.toSynGraphAux] at h
    by_cases h0 : i = 0
    · subst h0; simp only [ite_true] at h
      have := congr_arg Fin.val (Option.some.inj h); simp only [Fin.val_mk] at this; omega
    · simp only [if_neg h0] at h
      by_cases h1 : i - 1 < (G one).numNodes
      · simp only [dif_pos h1] at h
        obtain ⟨⟨k, hkb⟩, hk_eq, hk_fin⟩ := option_map_some_elim h
        have := ih₁ ⟨i - 1, h1⟩ ⟨k, hkb⟩ hk_eq
        simp only [Fin.val_mk] at this
        have := congr_arg Fin.val hk_fin; simp only [Fin.val_mk] at this; omega
      · simp only [dif_neg h1] at h
        have hi' : i - 1 - (G one).numNodes < (G two).numNodes := by nn_omega
        obtain ⟨⟨k, hkb⟩, hk_eq, hk_fin⟩ := option_map_some_elim h
        have := ih₂ ⟨i - 1 - (G one).numNodes, hi'⟩ ⟨k, hkb⟩ hk_eq
        simp only [Fin.val_mk] at this
        have := congr_arg Fin.val hk_fin; simp only [Fin.val_mk] at this
        have : (G one).numNodes = (↑one.toSynGraphAux : SynGraph MLabel).numNodes := rfl
        omega

-- ── Chain stabilization ──

private theorem chain_succ {L : Type} (g : SynGraph L)
    (f : Fin g.numNodes → Option (Fin g.numNodes))
    (h_incr : ∀ i j, f i = some j → i.val < j.val)
    (start : Fin g.numNodes) (fuel : Nat) (hfuel : fuel ≥ g.numNodes - start.val) :
    g.chain f start (fuel + 1) = g.chain f start fuel := by
  induction fuel generalizing start with
  | zero => have := start.isLt; omega
  | succ n ih =>
    conv_lhs => unfold SynGraph.chain
    conv_rhs => unfold SynGraph.chain
    cases hf : f start with
    | none => rfl
    | some next => simp only []; congr 1; apply ih; have := h_incr start next hf; omega

private theorem chain_elem_gt {L : Type} (g : SynGraph L)
    (f : Fin g.numNodes → Option (Fin g.numNodes))
    (h_incr : ∀ i j, f i = some j → i.val < j.val)
    (start : Fin g.numNodes) (fuel : Nat)
    (x : Fin g.numNodes) (hx : x ∈ g.chain f start fuel) :
    start.val < x.val := by
  induction fuel generalizing start with
  | zero => simp [SynGraph.chain] at hx
  | succ n ih =>
    unfold SynGraph.chain at hx
    cases hf : f start with
    | none => simp [hf] at hx
    | some nxt =>
      simp only [hf, List.mem_cons] at hx
      cases hx with
      | inl heq => subst heq; exact h_incr _ _ hf
      | inr hmem => have h1 := ih _ hmem; have h2 := h_incr _ _ hf; omega

-- ── Shift lemmas ──

private theorem root_label (t : SynObj) : (G t).label ⟨0, G_pos t⟩ = t.label := by
  cases t with
  | leaf l => rfl
  | sub₁ l one => rfl
  | sub₁₂ l one two => rfl

private theorem label_shift_sub1 (l : MLabel) (one : SynObj)
    (j : Fin (G one).numNodes) :
    (G (.sub₁ l one)).label ⟨j.val + 1, by nn_omega⟩ = (G one).label j := by
  simp only [G, SynObj.toSynGraphAux]; simp [Nat.add_one_ne_zero]

private theorem onePart_shift_sub1 (l : MLabel) (one : SynObj)
    (i : Fin (G one).numNodes) :
    (G (.sub₁ l one)).onePart ⟨i.val + 1, by nn_omega⟩ =
    ((G one).onePart i).map (fun ⟨j, hj⟩ => ⟨j + 1, by nn_omega⟩) := by
  simp only [G, SynObj.toSynGraphAux]; simp [Nat.add_one_ne_zero]

private theorem twoPart_shift_sub1 (l : MLabel) (one : SynObj)
    (i : Fin (G one).numNodes) :
    (G (.sub₁ l one)).twoPart ⟨i.val + 1, by nn_omega⟩ =
    ((G one).twoPart i).map (fun ⟨j, hj⟩ => ⟨j + 1, by nn_omega⟩) := by
  simp only [G, SynObj.toSynGraphAux]; simp [Nat.add_one_ne_zero]

private theorem chain_shift_sub1_op (l : MLabel) (one : SynObj) (fuel : Nat)
    (i : Fin (G one).numNodes) :
    (G (.sub₁ l one)).chain (G (.sub₁ l one)).onePart
      ⟨i.val + 1, by nn_omega⟩ fuel =
    ((G one).chain (G one).onePart i fuel).map
      (fun ⟨j, hj⟩ => ⟨j + 1, by nn_omega⟩) := by
  induction fuel generalizing i with
  | zero => simp [SynGraph.chain]
  | succ n ih =>
    simp only [SynGraph.chain]; rw [onePart_shift_sub1]
    cases h : (G one).onePart i with
    | none => simp [Option.map]
    | some next => simp only [Option.map, List.map_cons]; congr 1; exact ih next

private theorem chain_shift_sub1_tp (l : MLabel) (one : SynObj) (fuel : Nat)
    (i : Fin (G one).numNodes) :
    (G (.sub₁ l one)).chain (G (.sub₁ l one)).twoPart
      ⟨i.val + 1, by nn_omega⟩ fuel =
    ((G one).chain (G one).twoPart i fuel).map
      (fun ⟨j, hj⟩ => ⟨j + 1, by nn_omega⟩) := by
  induction fuel generalizing i with
  | zero => simp [SynGraph.chain]
  | succ n ih =>
    simp only [SynGraph.chain]; rw [twoPart_shift_sub1]
    cases h : (G one).twoPart i with
    | none => simp [Option.map]
    | some next => simp only [Option.map, List.map_cons]; congr 1; exact ih next

private theorem any_map_shift_label_sub1 {l₀ : MLabel} {one : SynObj}
    (xs : List (Fin (G one).numNodes)) (lbl : MLabel) :
    (xs.map (fun ⟨j, hj⟩ => (⟨j + 1, by nn_omega⟩ : Fin (G (.sub₁ l₀ one)).numNodes))).any
      (fun k => (G (.sub₁ l₀ one)).label k == lbl) =
    xs.any (fun k => (G one).label k == lbl) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.any_cons, ih, label_shift_sub1]

-- Sub₁₂ one-region shifts

private theorem label_shift_sub12_one (l : MLabel) (one two : SynObj)
    (j : Fin (G one).numNodes) :
    (G (.sub₁₂ l one two)).label ⟨j.val + 1, by nn_omega⟩ = (G one).label j := by
  simp only [G, SynObj.toSynGraphAux]
  simp [Nat.add_one_ne_zero, dif_pos (show j.val < (G one).numNodes from j.isLt)]

private theorem onePart_shift_sub12_one (l : MLabel) (one two : SynObj)
    (i : Fin (G one).numNodes) :
    (G (.sub₁₂ l one two)).onePart ⟨i.val + 1, by nn_omega⟩ =
    ((G one).onePart i).map (fun ⟨j, hj⟩ => ⟨j + 1, by nn_omega⟩) := by
  simp only [G, SynObj.toSynGraphAux]
  simp [Nat.add_one_ne_zero, dif_pos (show i.val < (G one).numNodes from i.isLt)]

private theorem chain_shift_sub12_one_op (l : MLabel) (one two : SynObj) (fuel : Nat)
    (i : Fin (G one).numNodes) :
    (G (.sub₁₂ l one two)).chain (G (.sub₁₂ l one two)).onePart
      ⟨i.val + 1, by nn_omega⟩ fuel =
    ((G one).chain (G one).onePart i fuel).map
      (fun ⟨j, hj⟩ => ⟨j + 1, by nn_omega⟩) := by
  induction fuel generalizing i with
  | zero => simp [SynGraph.chain]
  | succ n ih =>
    simp only [SynGraph.chain]; rw [onePart_shift_sub12_one]
    cases h : (G one).onePart i with
    | none => simp [Option.map]
    | some next => simp only [Option.map, List.map_cons]; congr 1; exact ih next

private theorem any_map_shift_label_sub12_one {l₀ : MLabel} {one two : SynObj}
    (xs : List (Fin (G one).numNodes)) (lbl : MLabel) :
    (xs.map (fun ⟨j, hj⟩ => (⟨j + 1, by nn_omega⟩ : Fin (G (.sub₁₂ l₀ one two)).numNodes))).any
      (fun k => (G (.sub₁₂ l₀ one two)).label k == lbl) =
    xs.any (fun k => (G one).label k == lbl) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.any_cons, ih]; congr 1
    exact congrArg (· == lbl) (label_shift_sub12_one l₀ one two x)

-- Sub₁₂ two-region shifts

private theorem label_shift_sub12_two (l : MLabel) (one two : SynObj)
    (j : Fin (G two).numNodes) :
    (G (.sub₁₂ l one two)).label ⟨j.val + 1 + (G one).numNodes, by nn_omega⟩ =
    (G two).label j := by
  simp only [G, SynObj.toSynGraphAux]
  have h1 : ¬ (j.val + 1 + (G one).numNodes = 0) := by nn_omega
  have h2 : ¬ (j.val + 1 + (G one).numNodes - 1 < (G one).numNodes) := by nn_omega
  simp [h1, dif_neg h2]

private theorem twoPart_shift_sub12_two (l : MLabel) (one two : SynObj)
    (i : Fin (G two).numNodes) :
    (G (.sub₁₂ l one two)).twoPart ⟨i.val + 1 + (G one).numNodes, by nn_omega⟩ =
    ((G two).twoPart i).map
      (fun ⟨j, hj⟩ => ⟨j + 1 + (G one).numNodes, by nn_omega⟩) := by
  simp only [G, SynObj.toSynGraphAux]
  have h1 : ¬ (i.val + 1 + (G one).numNodes = 0) := by nn_omega
  have h2 : ¬ (i.val + 1 + (G one).numNodes - 1 < (G one).numNodes) := by nn_omega
  simp [h1, dif_neg h2]

private theorem chain_shift_sub12_two_tp (l : MLabel) (one two : SynObj) (fuel : Nat)
    (i : Fin (G two).numNodes) :
    (G (.sub₁₂ l one two)).chain (G (.sub₁₂ l one two)).twoPart
      ⟨i.val + 1 + (G one).numNodes, by nn_omega⟩ fuel =
    ((G two).chain (G two).twoPart i fuel).map
      (fun ⟨j, hj⟩ => ⟨j + 1 + (G one).numNodes, by nn_omega⟩) := by
  induction fuel generalizing i with
  | zero => simp [SynGraph.chain]
  | succ n ih =>
    simp only [SynGraph.chain]; rw [twoPart_shift_sub12_two]
    cases h : (G two).twoPart i with
    | none => simp [Option.map]
    | some next => simp only [Option.map, List.map_cons]; congr 1; exact ih next

private theorem any_map_shift_label_sub12_two {l₀ : MLabel} {one two : SynObj}
    (xs : List (Fin (G two).numNodes)) (lbl : MLabel) :
    (xs.map (fun ⟨j, hj⟩ =>
      (⟨j + 1 + (G one).numNodes, by nn_omega⟩ : Fin (G (.sub₁₂ l₀ one two)).numNodes))).any
      (fun k => (G (.sub₁₂ l₀ one two)).label k == lbl) =
    xs.any (fun k => (G two).label k == lbl) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.any_cons, ih]; congr 1
    exact congrArg (· == lbl) (label_shift_sub12_two l₀ one two x)

-- ── Chain-from-root decomposition ──

private theorem chain_from_root_sub1 (l : MLabel) (one : SynObj) :
    (G (.sub₁ l one)).chain (G (.sub₁ l one)).onePart
      ⟨0, G_pos (.sub₁ l one)⟩ (G (.sub₁ l one)).numNodes =
    ⟨1, by nn_omega⟩ ::
    ((G one).chain (G one).onePart ⟨0, G_pos one⟩ (G one).numNodes).map
      (fun ⟨j, hj⟩ => ⟨j + 1, by nn_omega⟩) := by
  have hfuel : (G (.sub₁ l one)).chain (G (.sub₁ l one)).onePart
      ⟨0, G_pos (.sub₁ l one)⟩ (G (.sub₁ l one)).numNodes =
    (G (.sub₁ l one)).chain (G (.sub₁ l one)).onePart
      ⟨0, G_pos (.sub₁ l one)⟩ ((G one).numNodes + 1) := by congr 1; nn_omega
  rw [hfuel]; conv_lhs => unfold SynGraph.chain
  have h0 : (G (.sub₁ l one)).onePart ⟨0, G_pos (.sub₁ l one)⟩ =
    some ⟨1, by nn_omega⟩ := by simp [G, SynObj.toSynGraphAux]
  simp only [h0, List.cons.injEq, true_and]
  exact chain_shift_sub1_op l one (G one).numNodes ⟨0, G_pos one⟩

private theorem chain_from_root_sub12_op (l : MLabel) (one two : SynObj) :
    (G (.sub₁₂ l one two)).chain (G (.sub₁₂ l one two)).onePart
      ⟨0, G_pos (.sub₁₂ l one two)⟩ (G (.sub₁₂ l one two)).numNodes =
    ⟨1, by nn_omega⟩ ::
    ((G one).chain (G one).onePart ⟨0, G_pos one⟩ (G one).numNodes).map
      (fun ⟨j, hj⟩ => ⟨j + 1, by nn_omega⟩) := by
  have hfuel_top : (G (.sub₁₂ l one two)).chain (G (.sub₁₂ l one two)).onePart
      ⟨0, G_pos (.sub₁₂ l one two)⟩ (G (.sub₁₂ l one two)).numNodes =
    (G (.sub₁₂ l one two)).chain (G (.sub₁₂ l one two)).onePart
      ⟨0, G_pos (.sub₁₂ l one two)⟩ ((G one).numNodes + (G two).numNodes + 1) := by
    congr 1; nn_omega
  rw [hfuel_top]; conv_lhs => unfold SynGraph.chain
  have h0 : (G (.sub₁₂ l one two)).onePart ⟨0, G_pos (.sub₁₂ l one two)⟩ =
    some ⟨1, by nn_omega⟩ := by simp [G, SynObj.toSynGraphAux]
  simp only [h0, List.cons.injEq, true_and]
  rw [chain_shift_sub12_one_op l one two ((G one).numNodes + (G two).numNodes) ⟨0, G_pos one⟩]
  suffices hred : (G one).chain (G one).onePart ⟨0, G_pos one⟩
      ((G one).numNodes + (G two).numNodes) =
    (G one).chain (G one).onePart ⟨0, G_pos one⟩ (G one).numNodes by rw [hred]
  have : ∀ k, (G one).chain (G one).onePart ⟨0, G_pos one⟩ ((G one).numNodes + k) =
    (G one).chain (G one).onePart ⟨0, G_pos one⟩ (G one).numNodes := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [show (G one).numNodes + (k + 1) = ((G one).numNodes + k) + 1 from by omega]
      rw [chain_succ _ _ (edges_incr_op one) _ _ (by omega)]; exact ih
  exact this (G two).numNodes

private theorem chain_from_root_sub12_tp (l : MLabel) (one two : SynObj) :
    (G (.sub₁₂ l one two)).chain (G (.sub₁₂ l one two)).twoPart
      ⟨0, G_pos (.sub₁₂ l one two)⟩ (G (.sub₁₂ l one two)).numNodes =
    ⟨1 + (G one).numNodes, by nn_omega⟩ ::
    ((G two).chain (G two).twoPart ⟨0, G_pos two⟩ (G two).numNodes).map
      (fun ⟨j, hj⟩ => ⟨j + 1 + (G one).numNodes, by nn_omega⟩) := by
  have hfuel_top : (G (.sub₁₂ l one two)).chain (G (.sub₁₂ l one two)).twoPart
      ⟨0, G_pos (.sub₁₂ l one two)⟩ (G (.sub₁₂ l one two)).numNodes =
    (G (.sub₁₂ l one two)).chain (G (.sub₁₂ l one two)).twoPart
      ⟨0, G_pos (.sub₁₂ l one two)⟩ ((G one).numNodes + (G two).numNodes + 1) := by
    congr 1; nn_omega
  rw [hfuel_top]; conv_lhs => unfold SynGraph.chain
  have h0 : (G (.sub₁₂ l one two)).twoPart ⟨0, G_pos (.sub₁₂ l one two)⟩ =
    some ⟨1 + (G one).numNodes, by nn_omega⟩ := by simp [G, SynObj.toSynGraphAux]
  simp only [h0, List.cons.injEq, true_and]
  rw [chain_shift_sub12_two_tp l one two ((G one).numNodes + (G two).numNodes) ⟨0, G_pos two⟩]
  suffices hred : (G two).chain (G two).twoPart ⟨0, G_pos two⟩
      ((G one).numNodes + (G two).numNodes) =
    (G two).chain (G two).twoPart ⟨0, G_pos two⟩ (G two).numNodes by rw [hred]
  have : ∀ k, (G two).chain (G two).twoPart ⟨0, G_pos two⟩ ((G two).numNodes + k) =
    (G two).chain (G two).twoPart ⟨0, G_pos two⟩ (G two).numNodes := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [show (G two).numNodes + (k + 1) = ((G two).numNodes + k) + 1 from by omega]
      rw [chain_succ _ _ (edges_incr_tp two) _ _ (by omega)]; exact ih
  rw [show (G one).numNodes + (G two).numNodes = (G two).numNodes + (G one).numNodes from by omega]
  exact this (G one).numNodes

-- ── onePartChain / twoPartChain bridge ──

private theorem onePartChain_bridge (t : SynObj) (l : MLabel) :
    ((G t).chain (G t).onePart ⟨0, G_pos t⟩ (G t).numNodes).any
      (fun k => (G t).label k == l) =
    labelInOnePartChain l t := by
  induction t with
  | leaf l' =>
    simp [G, SynObj.toSynGraphAux, SynGraph.chain, labelInOnePartChain]
  | sub₁ l' one ih =>
    rw [chain_from_root_sub1 l' one]
    simp only [List.any_cons]
    have hlbl : ((G (.sub₁ l' one)).label ⟨1, by nn_omega⟩ == l) =
      (one.label == l) := by
      congr 1; rw [label_shift_sub1 l' one ⟨0, G_pos one⟩, root_label]
    rw [hlbl, any_map_shift_label_sub1, ih]; rfl
  | sub₁₂ l' one two ih₁ ih₂ =>
    rw [chain_from_root_sub12_op l' one two]
    simp only [List.any_cons]
    have hlbl : ((G (.sub₁₂ l' one two)).label ⟨1, by nn_omega⟩ == l) =
      (one.label == l) := by
      congr 1; rw [label_shift_sub12_one l' one two ⟨0, G_pos one⟩, root_label]
    rw [hlbl, any_map_shift_label_sub12_one, ih₁]; rfl

private theorem twoPartChain_bridge (t : SynObj) (l : MLabel) :
    ((G t).chain (G t).twoPart ⟨0, G_pos t⟩ (G t).numNodes).any
      (fun k => (G t).label k == l) =
    labelInTwoPartChain l t := by
  induction t with
  | leaf l' =>
    simp [G, SynObj.toSynGraphAux, SynGraph.chain, labelInTwoPartChain]
  | sub₁ l' one ih =>
    have h0 : (G (.sub₁ l' one)).twoPart ⟨0, G_pos (.sub₁ l' one)⟩ = none := by
      simp [G, SynObj.toSynGraphAux]
    have hfuel : (G (.sub₁ l' one)).chain (G (.sub₁ l' one)).twoPart
        ⟨0, G_pos (.sub₁ l' one)⟩ (G (.sub₁ l' one)).numNodes =
      (G (.sub₁ l' one)).chain (G (.sub₁ l' one)).twoPart
        ⟨0, G_pos (.sub₁ l' one)⟩ ((G one).numNodes + 1) := by congr 1; nn_omega
    rw [hfuel]; conv_lhs => unfold SynGraph.chain; rw [h0]
    simp [labelInTwoPartChain]
  | sub₁₂ l' one two ih₁ ih₂ =>
    rw [chain_from_root_sub12_tp l' one two]
    simp only [List.any_cons]
    have hlbl : ((G (.sub₁₂ l' one two)).label ⟨1 + (G one).numNodes, by nn_omega⟩ == l) =
      (two.label == l) := by
      congr 1
      exact (label_shift_sub12_two l' one two ⟨0, G_pos two⟩).trans (root_label two)
    rw [hlbl, any_map_shift_label_sub12_two, ih₂]; rfl

-- ── isTrans/isWithinDim shift ──

private theorem list_any_map_succ_beq {n m : Nat}
    (xs : List (Fin n)) (target : Fin n) (hm : n < m) :
    (xs.map (fun ⟨j, hj⟩ => (⟨j + 1, by nn_omega⟩ : Fin m))).any
      (· == ⟨target.val + 1, by nn_omega⟩) =
    xs.any (· == target) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.any_cons, ih]
    congr 1; simp [BEq.beq]; exact ⟨Fin.ext, congr_arg _⟩

private theorem isTrans1PartOf_shift_sub1 (l : MLabel) (one : SynObj)
    (x y : Fin (G one).numNodes) :
    (G (.sub₁ l one)).isTrans1PartOf
      ⟨x.val + 1, by nn_omega⟩ ⟨y.val + 1, by nn_omega⟩ =
    (G one).isTrans1PartOf x y := by
  unfold SynGraph.isTrans1PartOf
  rw [chain_shift_sub1_op]
  have hfuel : (G one).chain (G one).onePart y ((G (.sub₁ l one)).numNodes) =
    (G one).chain (G one).onePart y ((G one).numNodes) := by
    rw [show (G (.sub₁ l one)).numNodes = (G one).numNodes + 1 from by nn_omega]
    exact chain_succ _ _ (edges_incr_op one) y _ (by nn_omega)
  rw [hfuel]
  exact list_any_map_succ_beq _ x (by nn_omega)

private theorem isTrans2PartOf_shift_sub1 (l : MLabel) (one : SynObj)
    (x y : Fin (G one).numNodes) :
    (G (.sub₁ l one)).isTrans2PartOf
      ⟨x.val + 1, by nn_omega⟩ ⟨y.val + 1, by nn_omega⟩ =
    (G one).isTrans2PartOf x y := by
  unfold SynGraph.isTrans2PartOf
  rw [chain_shift_sub1_tp]
  have hfuel : (G one).chain (G one).twoPart y ((G (.sub₁ l one)).numNodes) =
    (G one).chain (G one).twoPart y ((G one).numNodes) := by
    rw [show (G (.sub₁ l one)).numNodes = (G one).numNodes + 1 from by nn_omega]
    exact chain_succ _ _ (edges_incr_tp one) y _ (by nn_omega)
  rw [hfuel]
  exact list_any_map_succ_beq _ x (by nn_omega)

private theorem isWithinDimPartOf_shift_sub1 (l : MLabel) (one : SynObj)
    (x y : Fin (G one).numNodes) :
    (G (.sub₁ l one)).isWithinDimPartOf
      ⟨x.val + 1, by nn_omega⟩ ⟨y.val + 1, by nn_omega⟩ =
    (G one).isWithinDimPartOf x y := by
  simp only [SynGraph.isWithinDimPartOf]
  rw [isTrans1PartOf_shift_sub1, isTrans2PartOf_shift_sub1]

-- ── satisfiesAL analysis ──

private theorem satisfiesAL_zero_false (t : SynObj) :
    (G t).satisfiesAL ⟨0, G_pos t⟩ ⟨0, G_pos t⟩ = false := by
  simp only [SynGraph.satisfiesAL, SynGraph.isWithinDimPartOf,
             SynGraph.isTrans1PartOf, SynGraph.isTrans2PartOf]
  apply Bool.eq_false_iff.mpr; intro h
  rw [List.any_eq_true] at h
  obtain ⟨α, hα_mem, hα_val⟩ := h
  have hα_gt := chain_elem_gt _ _ (edges_incr_op t) ⟨0, G_pos t⟩ _ α hα_mem
  rw [Bool.or_eq_true] at hα_val
  cases hα_val with
  | inl h1 =>
    rw [List.any_eq_true] at h1
    obtain ⟨β, hβ_mem, hβ_eq⟩ := h1
    have hβ_gt := chain_elem_gt _ _ (edges_incr_op t) α _ β hβ_mem
    simp [BEq.beq] at hβ_eq
    have := congr_arg Fin.val hβ_eq; omega
  | inr h2 =>
    rw [List.any_eq_true] at h2
    obtain ⟨β, hβ_mem, hβ_eq⟩ := h2
    have hβ_gt := chain_elem_gt _ _ (edges_incr_tp t) α _ β hβ_mem
    simp [BEq.beq] at hβ_eq
    have := congr_arg Fin.val hβ_eq; omega

private theorem satisfiesAL_shift_sub1 (l : MLabel) (one : SynObj)
    (j : Fin (G one).numNodes) :
    (G (.sub₁ l one)).satisfiesAL
      ⟨j.val + 1, by nn_omega⟩ ⟨0, G_pos (.sub₁ l one)⟩ =
    ((G one).isWithinDimPartOf j ⟨0, G_pos one⟩ ||
     (G one).satisfiesAL j ⟨0, G_pos one⟩) := by
  simp only [SynGraph.satisfiesAL]
  rw [chain_from_root_sub1]
  simp only [List.any_cons]
  congr 1
  · exact isWithinDimPartOf_shift_sub1 l one j ⟨0, G_pos one⟩
  · induction (G one).chain (G one).onePart ⟨0, G_pos one⟩ (G one).numNodes with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.any_cons]; congr 1
      · exact isWithinDimPartOf_shift_sub1 l one j x

-- ── isTrans/isWithinDim shift for sub₁₂ ──

private theorem isTrans1PartOf_shift_sub12_one (l : MLabel) (one two : SynObj)
    (x y : Fin (G one).numNodes) :
    (G (.sub₁₂ l one two)).isTrans1PartOf
      ⟨x.val + 1, by nn_omega⟩ ⟨y.val + 1, by nn_omega⟩ =
    (G one).isTrans1PartOf x y := by
  unfold SynGraph.isTrans1PartOf
  rw [chain_shift_sub12_one_op]
  have hfuel : (G one).chain (G one).onePart y ((G (.sub₁₂ l one two)).numNodes) =
    (G one).chain (G one).onePart y ((G one).numNodes) := by
    have : ∀ k, (G one).chain (G one).onePart y ((G one).numNodes + k) =
      (G one).chain (G one).onePart y ((G one).numNodes) := by
      intro k; induction k with
      | zero => simp
      | succ k ih =>
        rw [show (G one).numNodes + (k + 1) = ((G one).numNodes + k) + 1 from by nn_omega]
        rw [chain_succ _ _ (edges_incr_op one) y _ (by nn_omega)]; exact ih
    rw [show (G (.sub₁₂ l one two)).numNodes = (G one).numNodes + (1 + (G two).numNodes) from by nn_omega]
    exact this _
  rw [hfuel]
  exact list_any_map_succ_beq _ x (by nn_omega)

private theorem twoPart_shift_sub12_one (l : MLabel) (one two : SynObj)
    (i : Fin (G one).numNodes) :
    (G (.sub₁₂ l one two)).twoPart ⟨i.val + 1, by nn_omega⟩ =
    ((G one).twoPart i).map (fun ⟨j, hj⟩ => ⟨j + 1, by nn_omega⟩) := by
  simp only [G, SynObj.toSynGraphAux]
  simp [Nat.add_one_ne_zero, dif_pos (show i.val < (G one).numNodes from i.isLt)]

private theorem chain_shift_sub12_one_tp (l : MLabel) (one two : SynObj) (fuel : Nat)
    (i : Fin (G one).numNodes) :
    (G (.sub₁₂ l one two)).chain (G (.sub₁₂ l one two)).twoPart
      ⟨i.val + 1, by nn_omega⟩ fuel =
    ((G one).chain (G one).twoPart i fuel).map
      (fun ⟨j, hj⟩ => ⟨j + 1, by nn_omega⟩) := by
  induction fuel generalizing i with
  | zero => simp [SynGraph.chain]
  | succ n ih =>
    simp only [SynGraph.chain]; rw [twoPart_shift_sub12_one]
    cases h : (G one).twoPart i with
    | none => simp [Option.map]
    | some next => simp only [Option.map, List.map_cons]; congr 1; exact ih next

private theorem isTrans2PartOf_shift_sub12_one (l : MLabel) (one two : SynObj)
    (x y : Fin (G one).numNodes) :
    (G (.sub₁₂ l one two)).isTrans2PartOf
      ⟨x.val + 1, by nn_omega⟩ ⟨y.val + 1, by nn_omega⟩ =
    (G one).isTrans2PartOf x y := by
  unfold SynGraph.isTrans2PartOf
  rw [chain_shift_sub12_one_tp]
  have hfuel : (G one).chain (G one).twoPart y ((G (.sub₁₂ l one two)).numNodes) =
    (G one).chain (G one).twoPart y ((G one).numNodes) := by
    have : ∀ k, (G one).chain (G one).twoPart y ((G one).numNodes + k) =
      (G one).chain (G one).twoPart y ((G one).numNodes) := by
      intro k; induction k with
      | zero => simp
      | succ k ih =>
        rw [show (G one).numNodes + (k + 1) = ((G one).numNodes + k) + 1 from by nn_omega]
        rw [chain_succ _ _ (edges_incr_tp one) y _ (by nn_omega)]; exact ih
    rw [show (G (.sub₁₂ l one two)).numNodes = (G one).numNodes + (1 + (G two).numNodes) from by nn_omega]
    exact this _
  rw [hfuel]
  exact list_any_map_succ_beq _ x (by nn_omega)

private theorem isWithinDimPartOf_shift_sub12_one (l : MLabel) (one two : SynObj)
    (x y : Fin (G one).numNodes) :
    (G (.sub₁₂ l one two)).isWithinDimPartOf
      ⟨x.val + 1, by nn_omega⟩ ⟨y.val + 1, by nn_omega⟩ =
    (G one).isWithinDimPartOf x y := by
  simp only [SynGraph.isWithinDimPartOf]
  rw [isTrans1PartOf_shift_sub12_one, isTrans2PartOf_shift_sub12_one]

private theorem satisfiesAL_shift_sub12 (l : MLabel) (one two : SynObj)
    (j : Fin (G one).numNodes) :
    (G (.sub₁₂ l one two)).satisfiesAL
      ⟨j.val + 1, by nn_omega⟩ ⟨0, G_pos (.sub₁₂ l one two)⟩ =
    ((G one).isWithinDimPartOf j ⟨0, G_pos one⟩ ||
     (G one).satisfiesAL j ⟨0, G_pos one⟩) := by
  unfold SynGraph.satisfiesAL
  have hfuel_root : (G (.sub₁₂ l one two)).chain (G (.sub₁₂ l one two)).onePart
      ⟨0, G_pos (.sub₁₂ l one two)⟩ (G (.sub₁₂ l one two)).numNodes =
    ⟨1, by nn_omega⟩ ::
    ((G one).chain (G one).onePart ⟨0, G_pos one⟩ (G one).numNodes).map
      (fun ⟨j, hj⟩ => ⟨j + 1, by nn_omega⟩) :=
    chain_from_root_sub12_op l one two
  rw [hfuel_root]
  simp only [List.any_cons]
  congr 1
  · exact isWithinDimPartOf_shift_sub12_one l one two j ⟨0, G_pos one⟩
  · induction (G one).chain (G one).onePart ⟨0, G_pos one⟩ (G one).numNodes with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.any_cons]; congr 1
      · exact isWithinDimPartOf_shift_sub12_one l one two j x

-- Two-region nodes have satisfiesAL = false because the onePart chain
-- from root stays in the one-region.
private theorem two_region_satisfiesAL_false (l : MLabel) (one two : SynObj)
    (j : Fin (G two).numNodes) :
    (G (.sub₁₂ l one two)).satisfiesAL
      ⟨j.val + 1 + (G one).numNodes, by nn_omega⟩
      ⟨0, G_pos (.sub₁₂ l one two)⟩ = false := by
  simp only [SynGraph.satisfiesAL]
  rw [chain_from_root_sub12_op l one two]
  apply Bool.eq_false_iff.mpr; intro h
  simp only [List.any_cons, Bool.or_eq_true] at h
  cases h with
  | inl h1 =>
    simp only [SynGraph.isWithinDimPartOf, SynGraph.isTrans1PartOf,
               SynGraph.isTrans2PartOf, Bool.or_eq_true] at h1
    cases h1 with
    | inl hop =>
      rw [List.any_eq_true] at hop
      obtain ⟨β, hβ_mem, hβ_eq⟩ := hop
      rw [chain_shift_sub12_one_op l one two _ ⟨0, G_pos one⟩] at hβ_mem
      simp only [List.mem_map] at hβ_mem
      obtain ⟨⟨k, hk⟩, _, hk_eq⟩ := hβ_mem
      simp [BEq.beq] at hβ_eq
      have := congr_arg Fin.val hβ_eq
      have := congr_arg Fin.val hk_eq; simp only [] at *; omega
    | inr htp =>
      rw [List.any_eq_true] at htp
      obtain ⟨β, hβ_mem, hβ_eq⟩ := htp
      rw [chain_shift_sub12_one_tp l one two _ ⟨0, G_pos one⟩] at hβ_mem
      simp only [List.mem_map] at hβ_mem
      obtain ⟨⟨k, hk⟩, _, hk_eq⟩ := hβ_mem
      simp [BEq.beq] at hβ_eq
      have := congr_arg Fin.val hβ_eq
      have := congr_arg Fin.val hk_eq; simp only [] at *; omega
  | inr h2 =>
    rw [List.any_eq_true] at h2
    obtain ⟨α, hα_mem, hα_val⟩ := h2
    simp only [List.mem_map] at hα_mem
    obtain ⟨⟨k, hk⟩, _, hk_eq⟩ := hα_mem
    subst hk_eq
    simp only [SynGraph.isWithinDimPartOf, SynGraph.isTrans1PartOf,
               SynGraph.isTrans2PartOf, Bool.or_eq_true] at hα_val
    cases hα_val with
    | inl hop =>
      rw [List.any_eq_true] at hop
      obtain ⟨β, hβ_mem, hβ_eq⟩ := hop
      rw [chain_shift_sub12_one_op l one two _ ⟨k, hk⟩] at hβ_mem
      simp only [List.mem_map] at hβ_mem
      obtain ⟨⟨m, hm⟩, _, hm_eq⟩ := hβ_mem
      simp [BEq.beq] at hβ_eq
      have := congr_arg Fin.val hβ_eq
      have := congr_arg Fin.val hm_eq; simp only [] at *; omega
    | inr htp =>
      rw [List.any_eq_true] at htp
      obtain ⟨β, hβ_mem, hβ_eq⟩ := htp
      rw [chain_shift_sub12_one_tp l one two _ ⟨k, hk⟩] at hβ_mem
      simp only [List.mem_map] at hβ_mem
      obtain ⟨⟨m, hm⟩, _, hm_eq⟩ := hβ_mem
      simp [BEq.beq] at hβ_eq
      have := congr_arg Fin.val hβ_eq
      have := congr_arg Fin.val hm_eq; simp only [] at *; omega

-- ── alOK decomposition ──

private theorem range_any_split_zero {n : Nat} (hn : 0 < n) (f : Nat → Bool) :
    (List.range n).any f = (f 0 || (List.range (n - 1)).any (fun i => f (i + 1))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_one]
  clear hn
  induction m with
  | zero =>
    simp [List.range_succ, List.any_cons, List.any_nil, Bool.or_false]
  | succ k ih =>
    rw [show List.range (k + 2) = List.range (k + 1) ++ [k + 1] from List.range_succ]
    simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
    rw [ih]
    rw [show List.range (k + 1) = List.range k ++ [k] from List.range_succ]
    simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
    cases f 0 <;> cases (List.range k).any (fun i => f (i + 1)) <;> cases f (k + 1) <;> rfl

private theorem range_any_split_sum (a b : Nat) (f : Nat → Bool) :
    (List.range (a + b)).any f =
    ((List.range a).any f || (List.range b).any (fun i => f (i + a))) := by
  induction b with
  | zero => simp [List.any_nil]
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 from by omega]
    rw [show List.range ((a + b) + 1) = List.range (a + b) ++ [a + b] from List.range_succ]
    simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false, ih]
    rw [show List.range (b + 1) = List.range b ++ [b] from List.range_succ]
    simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
    rw [show b + a = a + b from by omega]
    cases (List.range a).any f <;> cases (List.range b).any (fun i => f (i + a)) <;>
      cases f (a + b) <;> rfl

private theorem alOK_decomp_sub1 (l' : MLabel) (one : SynObj) (l : MLabel) :
    SynObj.alOK_via_graph l (.sub₁ l' one) =
    (labelWithinDimPartOf l one || SynObj.alOK_via_graph l one) := by
  simp only [SynObj.alOK_via_graph, SynObj.toSynGraph]
  rw [range_any_split_zero (G_pos (.sub₁ l' one))]
  simp only [dif_pos (G_pos (.sub₁ l' one)), satisfiesAL_zero_false, Bool.and_false, Bool.false_or]
  rw [show (G (.sub₁ l' one)).numNodes - 1 = (G one).numNodes from by nn_omega]
  have h_fn_eq : ∀ (i : Nat),
    (if h : i + 1 < (G (.sub₁ l' one)).numNodes then
      (G (.sub₁ l' one)).label ⟨i + 1, h⟩ == l &&
      (G (.sub₁ l' one)).satisfiesAL ⟨i + 1, h⟩ ⟨0, G_pos (.sub₁ l' one)⟩
    else false) =
    (if hj : i < (G one).numNodes then
      (G one).label ⟨i, hj⟩ == l &&
      ((G one).isWithinDimPartOf ⟨i, hj⟩ ⟨0, G_pos one⟩ ||
       (G one).satisfiesAL ⟨i, hj⟩ ⟨0, G_pos one⟩)
    else false) := by
    intro i
    by_cases hi : i < (G one).numNodes
    · rw [dif_pos (show i + 1 < (G (.sub₁ l' one)).numNodes by nn_omega), dif_pos hi,
           label_shift_sub1 l' one ⟨i, hi⟩, satisfiesAL_shift_sub1 l' one ⟨i, hi⟩]
    · rw [dif_neg (show ¬ i + 1 < (G (.sub₁ l' one)).numNodes by nn_omega), dif_neg hi]
  simp_rw [h_fn_eq]
  have h_distrib : ∀ j, (if hj : j < (G one).numNodes then
      (G one).label ⟨j, hj⟩ == l &&
      ((G one).isWithinDimPartOf ⟨j, hj⟩ ⟨0, G_pos one⟩ ||
       (G one).satisfiesAL ⟨j, hj⟩ ⟨0, G_pos one⟩)
    else false) =
    ((if hj : j < (G one).numNodes then
        (G one).label ⟨j, hj⟩ == l && (G one).isWithinDimPartOf ⟨j, hj⟩ ⟨0, G_pos one⟩
      else false) ||
     (if hj : j < (G one).numNodes then
        (G one).label ⟨j, hj⟩ == l && (G one).satisfiesAL ⟨j, hj⟩ ⟨0, G_pos one⟩
      else false)) := by
    intro j; split <;> simp [Bool.and_or_distrib_left]
  simp_rw [h_distrib]; rw [any_or_distrib]
  have hwd_goal : (List.range (G one).numNodes).any (fun j =>
      if hj : j < (G one).numNodes then
        (G one).label ⟨j, hj⟩ == l && (G one).isWithinDimPartOf ⟨j, hj⟩ ⟨0, G_pos one⟩
      else false) = labelWithinDimPartOf l one := by
    have hwd : ∀ j, (if hj : j < (G one).numNodes then
        (G one).label ⟨j, hj⟩ == l && (G one).isWithinDimPartOf ⟨j, hj⟩ ⟨0, G_pos one⟩
      else false) =
      ((if hj : j < (G one).numNodes then
          (G one).label ⟨j, hj⟩ == l && (G one).isTrans1PartOf ⟨j, hj⟩ ⟨0, G_pos one⟩
        else false) ||
       (if hj : j < (G one).numNodes then
          (G one).label ⟨j, hj⟩ == l && (G one).isTrans2PartOf ⟨j, hj⟩ ⟨0, G_pos one⟩
        else false)) := by
      intro j; simp only [SynGraph.isWithinDimPartOf]; split <;> simp [Bool.and_or_distrib_left]
    simp_rw [hwd]; rw [any_or_distrib]
    simp only [SynGraph.isTrans1PartOf, SynGraph.isTrans2PartOf]
    rw [scan_chain_swap _ (fun k => (G one).label k == l)]
    rw [scan_chain_swap _ (fun k => (G one).label k == l)]
    rw [onePartChain_bridge one l, twoPartChain_bridge one l]; rfl
  rw [hwd_goal]

set_option maxHeartbeats 400000 in
private theorem alOK_decomp_sub12 (l' : MLabel) (one two : SynObj) (l : MLabel) :
    SynObj.alOK_via_graph l (.sub₁₂ l' one two) =
    (labelWithinDimPartOf l one || SynObj.alOK_via_graph l one) := by
  simp only [SynObj.alOK_via_graph, SynObj.toSynGraph]
  rw [range_any_split_zero (G_pos (.sub₁₂ l' one two))]
  simp only [dif_pos (G_pos (.sub₁₂ l' one two)), satisfiesAL_zero_false, Bool.and_false, Bool.false_or]
  rw [show (G (.sub₁₂ l' one two)).numNodes - 1 = (G one).numNodes + (G two).numNodes from by nn_omega]
  rw [range_any_split_sum]
  have h_idx : ∀ i : Nat, i + (G one).numNodes + 1 = i + 1 + (G one).numNodes := by intro i; omega
  simp_rw [h_idx]
  have h_two_fn : ∀ (i : Nat),
    (if h : i + 1 + (G one).numNodes < (G (.sub₁₂ l' one two)).numNodes then
      (G (.sub₁₂ l' one two)).label ⟨i + 1 + (G one).numNodes, h⟩ == l &&
      (G (.sub₁₂ l' one two)).satisfiesAL ⟨i + 1 + (G one).numNodes, h⟩
        ⟨0, G_pos (.sub₁₂ l' one two)⟩
    else false) = false := by
    intro i
    by_cases hi : i < (G two).numNodes
    · simp only [dif_pos (show i + 1 + (G one).numNodes < (G (.sub₁₂ l' one two)).numNodes by nn_omega)]
      simp only [two_region_satisfiesAL_false l' one two ⟨i, hi⟩, Bool.and_false]
    · simp only [dif_neg (show ¬ (i + 1 + (G one).numNodes < (G (.sub₁₂ l' one two)).numNodes) by nn_omega)]
  simp_rw [h_two_fn]
  simp only [any_const_false, Bool.or_false]
  have h_fn_eq : ∀ (i : Nat),
    (if h : i + 1 < (G (.sub₁₂ l' one two)).numNodes then
      (G (.sub₁₂ l' one two)).label ⟨i + 1, h⟩ == l &&
      (G (.sub₁₂ l' one two)).satisfiesAL ⟨i + 1, h⟩ ⟨0, G_pos (.sub₁₂ l' one two)⟩
    else false) =
    (if hj : i < (G one).numNodes then
      (G one).label ⟨i, hj⟩ == l &&
      ((G one).isWithinDimPartOf ⟨i, hj⟩ ⟨0, G_pos one⟩ ||
       (G one).satisfiesAL ⟨i, hj⟩ ⟨0, G_pos one⟩)
    else false) := by
    intro i
    by_cases hi : i < (G one).numNodes
    · simp only [dif_pos (show i + 1 < (G (.sub₁₂ l' one two)).numNodes by nn_omega), dif_pos hi]
      congr 1
      · exact congrArg (· == l) (label_shift_sub12_one l' one two ⟨i, hi⟩)
      · exact satisfiesAL_shift_sub12 l' one two ⟨i, hi⟩
    · rw [dif_neg hi]
      by_cases hi2 : i + 1 < (G (.sub₁₂ l' one two)).numNodes
      · rw [dif_pos hi2]
        have hnn12 := G_nn12 l' one two
        have hj : i - (G one).numNodes < (G two).numNodes := by omega
        have h := two_region_satisfiesAL_false l' one two ⟨i - (G one).numNodes, hj⟩
        have hnat : (i - (G one).numNodes) + 1 + (G one).numNodes = i + 1 := by omega
        simp only [hnat] at h
        simp only [h, Bool.and_false]
      · rw [dif_neg hi2]
  simp_rw [h_fn_eq]
  have h_distrib : ∀ j, (if hj : j < (G one).numNodes then
      (G one).label ⟨j, hj⟩ == l &&
      ((G one).isWithinDimPartOf ⟨j, hj⟩ ⟨0, G_pos one⟩ ||
       (G one).satisfiesAL ⟨j, hj⟩ ⟨0, G_pos one⟩)
    else false) =
    ((if hj : j < (G one).numNodes then
        (G one).label ⟨j, hj⟩ == l && (G one).isWithinDimPartOf ⟨j, hj⟩ ⟨0, G_pos one⟩
      else false) ||
     (if hj : j < (G one).numNodes then
        (G one).label ⟨j, hj⟩ == l && (G one).satisfiesAL ⟨j, hj⟩ ⟨0, G_pos one⟩
      else false)) := by
    intro j; split <;> simp [Bool.and_or_distrib_left]
  simp_rw [h_distrib]; rw [any_or_distrib]
  have hwd_goal : (List.range (G one).numNodes).any (fun j =>
      if hj : j < (G one).numNodes then
        (G one).label ⟨j, hj⟩ == l && (G one).isWithinDimPartOf ⟨j, hj⟩ ⟨0, G_pos one⟩
      else false) = labelWithinDimPartOf l one := by
    have hwd : ∀ j, (if hj : j < (G one).numNodes then
        (G one).label ⟨j, hj⟩ == l && (G one).isWithinDimPartOf ⟨j, hj⟩ ⟨0, G_pos one⟩
      else false) =
      ((if hj : j < (G one).numNodes then
          (G one).label ⟨j, hj⟩ == l && (G one).isTrans1PartOf ⟨j, hj⟩ ⟨0, G_pos one⟩
        else false) ||
       (if hj : j < (G one).numNodes then
          (G one).label ⟨j, hj⟩ == l && (G one).isTrans2PartOf ⟨j, hj⟩ ⟨0, G_pos one⟩
        else false)) := by
      intro j; simp only [SynGraph.isWithinDimPartOf]; split <;> simp [Bool.and_or_distrib_left]
    simp_rw [hwd]; rw [any_or_distrib]
    simp only [SynGraph.isTrans1PartOf, SynGraph.isTrans2PartOf]
    rw [scan_chain_swap _ (fun k => (G one).label k == l)]
    rw [scan_chain_swap _ (fun k => (G one).label k == l)]
    rw [onePartChain_bridge one l, twoPartChain_bridge one l]; rfl
  rw [hwd_goal]

-- ── Main theorem ──

/-- The tree-based Angular Locality check agrees with the graph-based
    version on all `SynObj` trees: `angularLocalityOK l t` returns
    the same answer as the existential check "does any node with label
    `l` satisfy `satisfiesAL` in the embedded graph?"

    Proved by induction on `SynObj`, showing that the pre-order
    embedding preserves within-dimension chains. -/
theorem al_bridge (t : SynObj) (l : MLabel) :
    angularLocalityOK l t = t.alOK_via_graph l := by
  induction t with
  | leaf l' =>
    simp only [angularLocalityOK, SynObj.onePartChainObjs, List.any_nil]
    simp only [SynObj.alOK_via_graph, SynObj.toSynGraph, SynObj.toSynGraphAux,
               SynGraph.satisfiesAL, SynGraph.chain]
    simp
  | sub₁ l' one ih =>
    show (labelWithinDimPartOf l one || angularLocalityOK l one) =
         SynObj.alOK_via_graph l (.sub₁ l' one)
    rw [ih, alOK_decomp_sub1]
  | sub₁₂ l' one two ih₁ ih₂ =>
    show (labelWithinDimPartOf l one || angularLocalityOK l one) =
         SynObj.alOK_via_graph l (.sub₁₂ l' one two)
    rw [ih₁, alOK_decomp_sub12]

end MereologicalSyntax
