import Linglib.Core.Computability.CFGTree

/-!
# CFL Pumping Lemma

The CFL pumping property (`HasCFLPumpingProperty`) is defined over mathlib's
`Language α` (= `Set (List α)`).

## Key Results

- `cfl_pumping_lemma : L.IsContextFree → HasCFLPumpingProperty L` — fully proved
- `not_isContextFree_of_not_pumpable` — contrapositive

## Proof Structure

The proof follows the standard textbook argument via derivation trees:

1. **`exists_valid_tree`** ✓ (in `CFGTree.lean`)
2. **`yield_length_le_of_height`** ✓ (in `CFGTree.lean`)
3. **`pumping_from_tall_tree`** ✓: pigeonhole + subtree replacement +
   `validFor_derives`
-/
/-- The CFL pumping property for a language.

    Every context-free language satisfies this property — the pumping lemma
    for CFLs. Showing a language lacks it proves it is not context-free. -/
def HasCFLPumpingProperty {α : Type} (L : Language α) : Prop :=
    ∃ p : Nat, p > 0 ∧
    ∀ w : List α, w ∈ L → w.length ≥ p →
      ∃ u v x y z : List α,
        w = u ++ v ++ x ++ y ++ z ∧
        (v ++ x ++ y).length ≤ p ∧
        (v.length + y.length) ≥ 1 ∧
        ∀ i : Nat, (u ++ List.flatten (List.replicate i v) ++ x ++
                    List.flatten (List.replicate i y) ++ z) ∈ L

private theorem flatten_replicate_succ_right {T : Type} (l : List T) (n : Nat) :
    (List.replicate (n + 1) l).flatten = (List.replicate n l).flatten ++ l := by
  induction n with
  | zero => simp
  | succ k ih =>
    conv_lhs => rw [List.replicate_succ, List.flatten_cons, ih]
    conv_rhs => rw [List.replicate_succ, List.flatten_cons]
    rw [List.append_assoc]

set_option maxHeartbeats 800000 in
theorem pumping_from_tall_tree {T : Type} (g : ContextFreeGrammar T)
    (t : CFGTree T g.NT) (ht : t.ValidFor g)
    (hroot : t.rootSymbol = .nonterminal g.initial)
    (hyield_long : t.yield.length ≥ g.pumpingConstant) :
    ∃ u v x y z : List T,
      t.yield = u ++ v ++ x ++ y ++ z ∧
      (v ++ x ++ y).length ≤ g.pumpingConstant ∧
      (v.length + y.length) ≥ 1 ∧
      ∀ i : Nat, (u ++ List.flatten (List.replicate i v) ++ x ++
                  List.flatten (List.replicate i y) ++ z) ∈ g.language := by
  classical
  -- Step 1: Pick min-size valid tree with same yield and root
  obtain ⟨t_min, ht_min_v, ht_min_y, ht_min_r, ht_min_minimal⟩ :=
    CFGTree.exists_min_size_tree t ht
  -- Step 2: Establish t_min.height > g.rules.card
  have htmin_tall : t_min.height > g.rules.card := by
    by_contra hle
    simp only [not_lt] at hle
    have hbound := yield_length_le_of_height g t_min ht_min_v
    have h1 : g.maxBranch ^ t_min.height ≤ g.maxBranch ^ g.rules.card :=
      Nat.pow_le_pow_right (by have := g.maxBranch_ge_two; omega) hle
    have h2 : g.maxBranch ^ g.rules.card < g.maxBranch ^ (g.rules.card + 1) :=
      Nat.pow_lt_pow_right (by have := g.maxBranch_ge_two; omega) (by omega)
    have hyl : t_min.yield.length ≥ g.pumpingConstant := by
      rw [ht_min_y]; exact hyield_long
    unfold ContextFreeGrammar.pumpingConstant at hyl
    omega
  -- Step 3: Max-descent path of length t_min.height - 1
  obtain ⟨p, hp_len, hpath⟩ :=
    CFGTree.exists_pos_max_descent t_min (t_min.height - 1) (by omega)
  -- Step 4: Restricted pigeonhole. Use Finset.range (#rules + 1) with shift.
  -- offset = p.length - #rules. Indices in [offset, offset + #rules].
  have hoffset_le : p.length - g.rules.card + g.rules.card = p.length := by omega
  -- Define f on shifted range
  let offset := p.length - g.rules.card
  -- Helper: get the rule at depth k for k ≤ p.length, with proof of NT match
  have hroot_at : ∀ k, k ≤ p.length →
      ∃ nt children, t_min.subtreeAt? (p.take k) = some (.node nt children) := by
    intro k hk_le
    obtain ⟨sub, hsub_at, hsub_h⟩ := hpath k (by omega)
    have hsub_h_ge : sub.height ≥ 1 := by rw [hsub_h]; omega
    match sub, hsub_h_ge with
    | .node nt children, _ => exact ⟨nt, children, hsub_at⟩
  let f : Nat → ContextFreeRule T g.NT := fun k =>
    (CFGTree.ruleAt? t_min (p.take (k + offset))).getD ⟨g.initial, []⟩
  have hf_in : ∀ k ∈ Finset.range (g.rules.card + 1), f k ∈ g.rules := by
    intro k hk
    simp at hk
    have hk_off_le : k + offset ≤ p.length := by simp [offset]; omega
    obtain ⟨nt, children, hsub_k⟩ := hroot_at (k + offset) hk_off_le
    obtain ⟨hrule_eq, hrule_in⟩ := CFGTree.ruleAt?_mem_rules t_min ht_min_v
      (p.take (k + offset)) nt children hsub_k
    show f k ∈ g.rules
    simp only [f, hrule_eq, Option.getD_some]
    exact hrule_in
  have hcard : g.rules.card < (Finset.range (g.rules.card + 1)).card := by
    simp [Finset.card_range]
  obtain ⟨a₀, ha₀, b₀, hb₀, hne₀, hfeq₀⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hf_in
  simp at ha₀ hb₀
  -- Reduce to a < b
  obtain ⟨a, b, ha, hb, hab, hfeq⟩ : ∃ a b,
      a < g.rules.card + 1 ∧ b < g.rules.card + 1 ∧ a < b ∧ f a = f b := by
    rcases Nat.lt_or_ge a₀ b₀ with h | h
    · exact ⟨a₀, b₀, ha₀, hb₀, h, hfeq₀⟩
    · exact ⟨b₀, a₀, hb₀, ha₀, lt_of_le_of_ne h hne₀.symm, hfeq₀.symm⟩
  -- Step 5: Set up t_outer, t_inner via the pigeonhole pair
  let i := a + offset
  let j := b + offset
  have hi_le : i ≤ p.length := by simp [i, offset]; omega
  have hj_le : j ≤ p.length := by simp [j, offset]; omega
  have hij : i < j := by simp [i, j]; omega
  have hi_ge_off : i ≥ offset := by simp [i]
  -- Get the subtrees and rules at i, j
  obtain ⟨nt_o, ch_o, hsub_o⟩ := hroot_at i hi_le
  obtain ⟨nt_i, ch_i, hsub_i⟩ := hroot_at j hj_le
  obtain ⟨hrule_o, hrule_o_in⟩ := CFGTree.ruleAt?_mem_rules t_min ht_min_v
    (p.take i) nt_o ch_o hsub_o
  obtain ⟨hrule_i, hrule_i_in⟩ := CFGTree.ruleAt?_mem_rules t_min ht_min_v
    (p.take j) nt_i ch_i hsub_i
  have hfa : f a = ⟨nt_o, ch_o.map CFGTree.rootSymbol⟩ := by
    change (CFGTree.ruleAt? t_min (p.take i)).getD _ = _
    rw [hrule_o]; rfl
  have hfb : f b = ⟨nt_i, ch_i.map CFGTree.rootSymbol⟩ := by
    change (CFGTree.ruleAt? t_min (p.take j)).getD _ = _
    rw [hrule_i]; rfl
  have hroot_eq : nt_o = nt_i := by
    have hh : (⟨nt_o, ch_o.map CFGTree.rootSymbol⟩ : ContextFreeRule T g.NT) =
        ⟨nt_i, ch_i.map CFGTree.rootSymbol⟩ := by rw [← hfa, ← hfb, hfeq]
    exact ContextFreeRule.mk.injEq _ _ _ _ |>.mp hh |>.1
  -- t_outer = .node nt_o ch_o, t_inner = .node nt_i ch_i
  -- t_outer has same root nonterminal as t_inner
  set t_outer : CFGTree T g.NT := .node nt_o ch_o with ht_outer_def
  set t_inner : CFGTree T g.NT := .node nt_i ch_i with ht_inner_def
  have hroot_o_eq_i : t_outer.rootSymbol = t_inner.rootSymbol := by
    show CFGTree.rootSymbol (.node nt_o ch_o) = CFGTree.rootSymbol (.node nt_i ch_i)
    show Symbol.nonterminal nt_o = Symbol.nonterminal nt_i
    rw [hroot_eq]
  -- Bound on t_outer.height
  have ht_outer_h : t_outer.height = t_min.height - i := by
    obtain ⟨sub_o, hsub_o', hsub_o_h⟩ := hpath i (by omega)
    rw [hsub_o] at hsub_o'
    have : t_outer = sub_o := by injection hsub_o'
    rw [this, hsub_o_h]
  have ht_outer_h_le : t_outer.height ≤ g.rules.card + 1 := by
    rw [ht_outer_h]; simp [i, offset]; omega
  -- t_inner is a subtree of t_outer at relative path
  have hsubtree_path_eq : p.take j = p.take i ++ (p.take j).drop i := by
    conv_lhs => rw [← List.take_append_drop i (p.take j)]
    congr 1; rw [List.take_take, min_eq_left (by omega)]
  let p_outer := p.take i
  let p_inner_rel := (p.take j).drop i
  have hp_inner_compose : t_min.subtreeAt? (p_outer ++ p_inner_rel) = some t_inner := by
    show t_min.subtreeAt? (p.take i ++ (p.take j).drop i) = _
    rw [← hsubtree_path_eq]; exact hsub_i
  have hsub_inner_in_outer : t_outer.subtreeAt? p_inner_rel = some t_inner := by
    rw [CFGTree.subtreeAt?_append] at hp_inner_compose
    rw [show t_min.subtreeAt? p_outer = some t_outer from hsub_o] at hp_inner_compose
    simpa using hp_inner_compose
  -- Step 6: Yield decomposition
  obtain ⟨u, z, hyield_t, hreplace_t⟩ :=
    CFGTree.yield_replaceAt_decomp t_min p_outer t_outer hsub_o
  obtain ⟨v, y, hyield_outer, hreplace_outer⟩ :=
    CFGTree.yield_replaceAt_decomp t_outer p_inner_rel t_inner hsub_inner_in_outer
  -- x := t_inner.yield
  let x := t_inner.yield
  -- t.yield = u ++ v ++ x ++ y ++ z (via t_min)
  have hyield_decomp : t.yield = u ++ v ++ x ++ y ++ z := by
    rw [← ht_min_y, hyield_t, hyield_outer]
    show u ++ (v ++ t_inner.yield ++ y) ++ z = u ++ v ++ x ++ y ++ z
    show u ++ (v ++ x ++ y) ++ z = u ++ v ++ x ++ y ++ z
    simp [List.append_assoc]
  -- Step 7: |vxy| ≤ pumpingConstant
  have hvxy_bound : (v ++ x ++ y).length ≤ g.pumpingConstant := by
    have ht_outer_yield_eq : t_outer.yield = v ++ x ++ y := by
      rw [hyield_outer]
    rw [← ht_outer_yield_eq]
    have hbound := yield_length_le_of_height g t_outer
      (CFGTree.subtreeAt?_validFor t_min ht_min_v p_outer t_outer hsub_o)
    have hpow_le : g.maxBranch ^ t_outer.height ≤ g.maxBranch ^ (g.rules.card + 1) :=
      Nat.pow_le_pow_right (by have := g.maxBranch_ge_two; omega) ht_outer_h_le
    unfold ContextFreeGrammar.pumpingConstant
    omega
  -- Step 8: |vy| ≥ 1 via minimality
  have hvy_pos : v.length + y.length ≥ 1 := by
    by_contra hcontra
    push Not at hcontra
    have hv_empty : v = [] :=
      List.eq_nil_of_length_eq_zero (by omega)
    have hy_empty : y = [] :=
      List.eq_nil_of_length_eq_zero (by omega)
    -- If v = y = ε, then yield(t_outer) = yield(t_inner)
    have ht_outer_yield_eq_inner : t_outer.yield = t_inner.yield := by
      rw [hyield_outer, hv_empty, hy_empty]; simp
    -- Replace t_outer with t_inner in t_min: same yield, but smaller size
    let t_replaced := t_min.replaceAt p_outer t_inner
    have hyield_replaced : t_replaced.yield = t_min.yield := by
      show (t_min.replaceAt p_outer t_inner).yield = t_min.yield
      rw [hreplace_t t_inner, hyield_t, ht_outer_yield_eq_inner]
    have hvalid_replaced : t_replaced.ValidFor g := by
      apply CFGTree.validFor_replaceAt t_min p_outer t_outer t_inner hsub_o
        hroot_o_eq_i.symm ht_min_v
      exact CFGTree.subtreeAt?_validFor t_min ht_min_v _ _ hp_inner_compose
    have hroot_replaced : t_replaced.rootSymbol = t_min.rootSymbol := by
      show (t_min.replaceAt p_outer t_inner).rootSymbol = t_min.rootSymbol
      cases hp_outer_eq : p_outer with
      | nil =>
        have hto_eq_tmin : t_outer = t_min := by
          have h0 : t_min.subtreeAt? [] = some t_outer := by rw [← hp_outer_eq]; exact hsub_o
          simp [CFGTree.subtreeAt?] at h0; exact h0.symm
        simp [CFGTree.replaceAt]
        rw [← hroot_o_eq_i, ← hto_eq_tmin]
      | cons hh tt =>
        exact CFGTree.rootSymbol_replaceAt_cons t_min hh tt t_inner
    -- size strict decrease
    have hsize_lt : t_replaced.size < t_min.size := by
      have hi_size_lt : t_inner.size < t_outer.size := by
        have hp_inner_rel_nonempty : p_inner_rel ≠ [] := by
          intro hempty
          have : (p.take j).drop i = [] := hempty
          have hlen_eq : (p.take j).length ≤ i := by
            have := congr_arg List.length this; simp at this; omega
          have : j ≤ i := by
            have h1 : (p.take j).length = min j p.length := by simp
            rw [h1] at hlen_eq; omega
          omega
        obtain ⟨idx, rest, hp_eq⟩ : ∃ idx rest, p_inner_rel = idx :: rest := by
          rcases p_inner_rel with _ | ⟨a, b⟩
          · exact absurd rfl hp_inner_rel_nonempty
          · exact ⟨a, b, rfl⟩
        have hsub' : t_outer.subtreeAt? (idx :: rest) = some t_inner := by
          rw [← hp_eq]; exact hsub_inner_in_outer
        exact CFGTree.size_subtreeAt?_lt_of_cons t_outer idx rest t_inner hsub'
      exact CFGTree.size_replaceAt_lt t_min p_outer t_outer t_inner hsub_o hi_size_lt
    -- Apply minimality
    have := ht_min_minimal t_replaced hvalid_replaced
      (by rw [hyield_replaced]; exact ht_min_y)
      (by rw [hroot_replaced]; exact ht_min_r)
    omega
  -- Step 9: Pumping iteration
  refine ⟨u, v, x, y, z, hyield_decomp, hvxy_bound, hvy_pos, ?_⟩
  -- For ∀ i, prove the pumped string is in g.language
  -- Define pumpInner : Nat → CFGTree, with yield = v^i ++ x ++ y^i
  intro k
  -- pumpInner k: replace t_inner with itself k times (giving v^k ++ x ++ y^k yield in t_outer's slot)
  -- Then graft into t_min at p_outer.
  -- For brevity, define recursively and prove by induction.
  let pumpInner : Nat → CFGTree T g.NT := fun n => Nat.rec t_inner
    (fun _ prev => t_outer.replaceAt p_inner_rel prev) n
  have hpump_yield : ∀ n, (pumpInner n).yield =
      List.flatten (List.replicate n v) ++ x ++ List.flatten (List.replicate n y) := by
    intro n
    induction n with
    | zero => simp [pumpInner, x]
    | succ m ih =>
      show (t_outer.replaceAt p_inner_rel (pumpInner m)).yield = _
      rw [hreplace_outer (pumpInner m), ih]
      conv_rhs =>
        rw [show List.replicate (m + 1) v = v :: List.replicate m v from rfl,
            List.flatten_cons, flatten_replicate_succ_right]
      simp only [List.append_assoc]
  have hpump_root : ∀ n, (pumpInner n).rootSymbol = t_inner.rootSymbol := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      show (t_outer.replaceAt p_inner_rel (pumpInner m)).rootSymbol = _
      cases hp_rel_eq : p_inner_rel with
      | nil =>
        simp [CFGTree.replaceAt]
        exact ih
      | cons hh tt =>
        exact (CFGTree.rootSymbol_replaceAt_cons t_outer hh tt (pumpInner m)).trans hroot_o_eq_i
  have hpump_valid : ∀ n, (pumpInner n).ValidFor g := by
    intro n
    induction n with
    | zero =>
      show t_inner.ValidFor g
      exact CFGTree.subtreeAt?_validFor t_min ht_min_v _ _ hp_inner_compose
    | succ m ih =>
      show (t_outer.replaceAt p_inner_rel (pumpInner m)).ValidFor g
      apply CFGTree.validFor_replaceAt t_outer p_inner_rel t_inner (pumpInner m)
        hsub_inner_in_outer
      · -- (pumpInner m).rootSymbol = t_inner.rootSymbol
        exact hpump_root m
      · exact CFGTree.subtreeAt?_validFor t_min ht_min_v _ _ hsub_o
      · exact ih
  -- Final pumped tree
  let final := t_min.replaceAt p_outer (pumpInner k)
  have hfinal_yield : final.yield =
      u ++ List.flatten (List.replicate k v) ++ x ++ List.flatten (List.replicate k y) ++ z := by
    show (t_min.replaceAt p_outer (pumpInner k)).yield = _
    rw [hreplace_t (pumpInner k), hpump_yield k]
    simp [List.append_assoc]
  have hfinal_valid : final.ValidFor g := by
    apply CFGTree.validFor_replaceAt t_min p_outer t_outer (pumpInner k) hsub_o
    · exact (hpump_root k).trans hroot_o_eq_i.symm
    · exact ht_min_v
    · exact hpump_valid k
  have hfinal_root : final.rootSymbol = .nonterminal g.initial := by
    show (t_min.replaceAt p_outer (pumpInner k)).rootSymbol = .nonterminal g.initial
    cases hp_outer_eq : p_outer with
    | nil =>
      have hto_eq_tmin : t_outer = t_min := by
        have h0 : t_min.subtreeAt? [] = some t_outer := by rw [← hp_outer_eq]; exact hsub_o
        simp [CFGTree.subtreeAt?] at h0; exact h0.symm
      simp [CFGTree.replaceAt]
      rw [hpump_root k, ← hroot_o_eq_i, hto_eq_tmin, ht_min_r, hroot]
    | cons hh tt =>
      exact (CFGTree.rootSymbol_replaceAt_cons t_min hh tt (pumpInner k)).trans
        (by rw [ht_min_r, hroot])
  -- Conclude: final.yield ∈ g.language
  show (u ++ List.flatten (List.replicate k v) ++ x ++
        List.flatten (List.replicate k y) ++ z) ∈ g.language
  rw [← hfinal_yield]
  have h := CFGTree.validFor_derives final hfinal_valid
  rw [hfinal_root] at h
  exact h

/-- **The CFL pumping lemma.** Every context-free language satisfies
    `HasCFLPumpingProperty`.

    Proof: given a CFG g generating L, set p = g.pumpingConstant.
    For any w ∈ L with |w| ≥ p:
    1. `exists_valid_tree`: w has a valid derivation tree t.
    2. `yield_length_le_of_height` (contrapositive): |w| ≥ p = b^(k+1)
       forces t.height > k = g.rules.card.
    3. `pumping_from_tall_tree`: the tall tree yields the decomposition. -/
theorem cfl_pumping_lemma {T : Type} (L : Language T)
    (hcf : L.IsContextFree) : HasCFLPumpingProperty L := by
  obtain ⟨g, rfl⟩ := hcf
  refine ⟨g.pumpingConstant, g.pumpingConstant_pos, ?_⟩
  intro w hw hlen
  obtain ⟨t, hvalid, hyield, hroot⟩ := exists_valid_tree g w hw
  have hyield_long : t.yield.length ≥ g.pumpingConstant := hyield ▸ hlen
  obtain ⟨u, v, x, y, z, hdecomp, hvxy, hvy, hpump⟩ :=
    pumping_from_tall_tree g t hvalid hroot hyield_long
  exact ⟨u, v, x, y, z, hyield ▸ hdecomp, hvxy, hvy, hpump⟩

/-- Contrapositive of the CFL pumping lemma: if a language lacks the pumping
    property, it is not context-free. -/
theorem not_isContextFree_of_not_pumpable {T : Type} (L : Language T)
    (h : ¬ HasCFLPumpingProperty L) : ¬ L.IsContextFree :=
  fun hcf => h (cfl_pumping_lemma L hcf)

