import Mathlib.Computability.ContextFreeGrammar

/-!
# Derivation Trees for Context-Free Grammars

`CFGTree T N` is a derivation tree whose leaves hold terminal symbols of type `T`
and whose internal nodes hold a nonterminal of type `N` together with a list of
children. The file provides:

- `ValidFor g` — validity: every internal node matches a production rule in `g`
- `yield` / `yieldList` — terminal frontier (left-to-right)
- `subtreeAt?` / `replaceAt` — position-based subtree access and replacement
- `validFor_derives` — soundness: a valid tree derives its yield from its root
- Tree existence (`exists_valid_tree`) and height–yield bounds
- Size measure, minimality, pigeonhole on derivation paths
-/
/-- A derivation tree for a context-free grammar.
    Leaves hold terminal symbols; internal nodes hold a nonterminal
    and a list of children (matching a production rule's RHS). -/
inductive CFGTree (T N : Type) where
  | leaf (t : T) : CFGTree T N
  | node (nt : N) (children : List (CFGTree T N)) : CFGTree T N

namespace CFGTree

variable {T N : Type}

/-- The root symbol of a subtree. -/
def rootSymbol : CFGTree T N → Symbol T N
  | .leaf t => .terminal t
  | .node nt _ => .nonterminal nt

mutual
/-- The terminal frontier (yield) of a derivation tree, read left to right. -/
def yield : CFGTree T N → List T
  | .leaf t => [t]
  | .node _ children => yieldList children

/-- Concatenate yields of a list of subtrees. -/
def yieldList : List (CFGTree T N) → List T
  | [] => []
  | t :: ts => t.yield ++ yieldList ts
end

mutual
/-- The height: 0 for leaves, 1 + max child height for nodes. -/
def height : CFGTree T N → Nat
  | .leaf _ => 0
  | .node _ children => 1 + heightMax children

/-- Maximum height among a list of subtrees. -/
def heightMax : List (CFGTree T N) → Nat
  | [] => 0
  | t :: ts => max t.height (heightMax ts)
end

/-- A derivation tree is valid for a CFG if every internal node (A, children)
    corresponds to a rule A → [rootSymbol c₁, ..., rootSymbol cₖ], and all
    children are themselves valid. -/
inductive ValidFor (g : ContextFreeGrammar T) : CFGTree T g.NT → Prop where
  | leaf (t : T) : ValidFor g (.leaf t)
  | node (nt : g.NT) (children : List (CFGTree T g.NT))
    (hrule : ⟨nt, children.map rootSymbol⟩ ∈ g.rules)
    (hchildren : ∀ c ∈ children, ValidFor g c) :
    ValidFor g (.node nt children)

end CFGTree

-- ============================================================================
-- CFL Pumping Lemma — Helper Lemmas
-- ============================================================================

private theorem CFGTree.height_le_heightMax {T N : Type}
    {t : CFGTree T N} {ts : List (CFGTree T N)}
    (ht : t ∈ ts) : t.height ≤ CFGTree.heightMax ts := by
  induction ts with
  | nil => simp at ht
  | cons s ss ih =>
    simp only [CFGTree.heightMax]
    rcases List.mem_cons.mp ht with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

private theorem le_foldl_max_init (l : List Nat) (init : Nat) :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact le_refl _
  | cons a as ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_max_left init a) (ih _)

private theorem le_foldl_max_of_mem (l : List Nat) (x : Nat) (init : Nat) (hx : x ∈ l) :
    x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp at hx
  | cons a as ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_trans (le_max_right init x) (le_foldl_max_init as _)
    · exact ih _ h

-- ============================================================================
-- CFL Pumping Lemma — Grammar Properties
-- ============================================================================

/-- Maximum rule RHS length in a grammar (at least 2).

    We take the max over all rules' output lengths, floored at 2 to ensure
    the branching factor is nontrivial (a tree of branching ≥ 2 and height h
    has at most b^h leaves). -/
noncomputable def ContextFreeGrammar.maxBranch {T : Type}
    (g : ContextFreeGrammar T) : Nat :=
  max 2 (g.rules.val.toList.map (·.output.length) |>.foldl max 0)

/-- The pumping constant for a CFG: b^(k+1) where b = maxBranch ≥ 2
    and k = number of rules (upper bound on distinct nonterminals). -/
noncomputable def ContextFreeGrammar.pumpingConstant {T : Type}
    (g : ContextFreeGrammar T) : Nat :=
  g.maxBranch ^ (g.rules.card + 1)

/-- maxBranch is at least 2. -/
theorem ContextFreeGrammar.maxBranch_ge_two {T : Type}
    (g : ContextFreeGrammar T) : g.maxBranch ≥ 2 := le_max_left _ _

/-- The pumping constant is positive (b ≥ 2 so b^(k+1) ≥ 2). -/
theorem ContextFreeGrammar.pumpingConstant_pos {T : Type}
    (g : ContextFreeGrammar T) : g.pumpingConstant > 0 :=
  Nat.pos_of_ne_zero (by
    unfold pumpingConstant
    exact ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one
      (Nat.one_le_pow _ _ (by have := g.maxBranch_ge_two; omega))))

/-- Any rule's RHS length is at most `maxBranch`. -/
private theorem ContextFreeGrammar.maxBranch_ge_output {T : Type} (g : ContextFreeGrammar T)
    (r : ContextFreeRule T g.NT) (hr : r ∈ g.rules) :
    r.output.length ≤ g.maxBranch := by
  unfold maxBranch
  apply le_trans _ (le_max_right _ _)
  apply le_foldl_max_of_mem
  exact List.mem_map.mpr
    ⟨r, Multiset.mem_toList.mpr (Finset.mem_val.mpr hr), rfl⟩

/-- Sum of children's yields is at most `|children| * b ^ heightMax`. -/
private theorem CFGTree.yieldList_le {T N : Type} (b : Nat) (_hb : b ≥ 2)
    (ts : List (CFGTree T N))
    (hbound : ∀ c ∈ ts, c.yield.length ≤ b ^ c.height) :
    (CFGTree.yieldList ts).length ≤ ts.length * b ^ CFGTree.heightMax ts := by
  induction ts with
  | nil => simp [CFGTree.yieldList, CFGTree.heightMax]
  | cons t rest ih =>
    simp only [CFGTree.yieldList, List.length_append, List.length_cons, CFGTree.heightMax]
    have ht := hbound t (List.mem_cons_self ..)
    have hrest := ih (fun c hc => hbound c (List.mem_cons_of_mem t hc))
    have hle_t : b ^ t.height ≤ b ^ (max t.height (CFGTree.heightMax rest)) :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have hle_rest : b ^ (CFGTree.heightMax rest) ≤
        b ^ (max t.height (CFGTree.heightMax rest)) :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    set p := b ^ (max t.height (CFGTree.heightMax rest))
    have h1 : t.yield.length ≤ p := le_trans ht hle_t
    have h2 : (CFGTree.yieldList rest).length ≤ rest.length * p :=
      le_trans hrest (Nat.mul_le_mul_left _ hle_rest)
    have h3 : (rest.length + 1) * p = p + rest.length * p := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    omega

-- ============================================================================
-- Tree Existence — Helper Lemmas
-- ============================================================================

namespace ContextFreeGrammar

variable {T : Type} {g : ContextFreeGrammar T}

/-- A rewriting step at any position: applying a rule's RHS in place. -/
private theorem Rewrites.at_position {r : ContextFreeRule T g.NT}
    (p q : List (Symbol T g.NT)) :
    r.Rewrites (p ++ [Symbol.nonterminal r.input] ++ q) (p ++ r.output ++ q) := by
  induction p with
  | nil =>
    simp only [List.nil_append]
    exact .head q
  | cons x xs ih =>
    have h1 : (x :: xs) ++ [Symbol.nonterminal r.input] ++ q =
              x :: (xs ++ [Symbol.nonterminal r.input] ++ q) := by simp
    have h2 : (x :: xs) ++ r.output ++ q = x :: (xs ++ r.output ++ q) := by simp
    rw [h1, h2]
    exact .cons x ih

set_option maxHeartbeats 400000 in
/-- A `Rewrites` step on a concatenated list happens in one of the two halves. -/
private theorem Rewrites.append_split {r : ContextFreeRule T g.NT}
    {u₁ u₂ v : List (Symbol T g.NT)} (h : r.Rewrites (u₁ ++ u₂) v) :
    (∃ v₁, v = v₁ ++ u₂ ∧ r.Rewrites u₁ v₁) ∨
    (∃ v₂, v = u₁ ++ v₂ ∧ r.Rewrites u₂ v₂) := by
  obtain ⟨p, q, hpq, hv⟩ := h.exists_parts
  rw [List.append_assoc] at hpq
  rcases List.append_eq_append_iff.mp hpq with ⟨e, hp_eq, hu₂⟩ | ⟨e, hu₁, hrest⟩
  · -- nonterminal in u₂
    right
    have hu₂' : u₂ = e ++ [Symbol.nonterminal r.input] ++ q := by
      rw [hu₂]; simp [List.append_assoc]
    refine ⟨e ++ r.output ++ q, ?_, ?_⟩
    · subst hp_eq; rw [hv]; simp [List.append_assoc]
    · rw [hu₂']; exact Rewrites.at_position e q
  · rcases e with _ | ⟨e_head, e_tail⟩
    · -- u₁ = p, nonterminal at start of u₂
      simp at hu₁
      simp only [List.nil_append] at hrest
      right
      refine ⟨r.output ++ q, ?_, ?_⟩
      · subst hu₁; rw [hv]; simp [List.append_assoc]
      · rw [← hrest]
        simp only [List.singleton_append]
        exact .head q
    · -- nonterminal in u₁
      simp only [List.nil_append, List.cons_append] at hrest
      rw [List.cons_eq_cons] at hrest
      obtain ⟨he_head, h_tail⟩ := hrest
      left
      refine ⟨p ++ r.output ++ e_tail, ?_, ?_⟩
      · rw [hv, h_tail]; simp [List.append_assoc]
      · rw [hu₁]
        rw [show p ++ e_head :: e_tail = p ++ [e_head] ++ e_tail by simp]
        rw [he_head.symm]
        exact Rewrites.at_position p e_tail

/-- A `Produces` step on a concatenated list happens in one of the two halves. -/
private theorem Produces.append_split {u₁ u₂ v : List (Symbol T g.NT)}
    (h : g.Produces (u₁ ++ u₂) v) :
    (∃ v₁, v = v₁ ++ u₂ ∧ g.Produces u₁ v₁) ∨
    (∃ v₂, v = u₁ ++ v₂ ∧ g.Produces u₂ v₂) := by
  obtain ⟨r, hr, hrew⟩ := h
  rcases Rewrites.append_split hrew with ⟨v₁, hv, hpr⟩ | ⟨v₂, hv, hpr⟩
  · exact .inl ⟨v₁, hv, r, hr, hpr⟩
  · exact .inr ⟨v₂, hv, r, hr, hpr⟩

/-- A `Derives` chain on a concatenated list decomposes into chains for each half. -/
private theorem Derives.append_split {u₁ u₂ v : List (Symbol T g.NT)}
    (h : g.Derives (u₁ ++ u₂) v) :
    ∃ v₁ v₂, v = v₁ ++ v₂ ∧ g.Derives u₁ v₁ ∧ g.Derives u₂ v₂ := by
  induction h with
  | refl => exact ⟨u₁, u₂, rfl, .refl _, .refl _⟩
  | tail _ h_step ih =>
    obtain ⟨m₁, m₂, hmid, hd₁, hd₂⟩ := ih
    rw [hmid] at h_step
    rcases Produces.append_split h_step with ⟨v₁, hv, hp⟩ | ⟨v₂, hv, hp⟩
    · exact ⟨v₁, m₂, hv, hd₁.trans_produces hp, hd₂⟩
    · exact ⟨m₁, v₂, hv, hd₁, hd₂.trans_produces hp⟩

/-- A terminal symbol can never be rewritten (productions only replace nonterminals). -/
private theorem Derives.of_terminal {t : T} {v : List (Symbol T g.NT)}
    (h : g.Derives [Symbol.terminal t] v) : v = [Symbol.terminal t] := by
  induction h with
  | refl => rfl
  | tail _ h_step ih =>
    rw [ih] at h_step
    obtain ⟨r, _, hrew⟩ := h_step
    obtain ⟨p, q, hpq, _⟩ := hrew.exists_parts
    have hmem : (Symbol.nonterminal r.input : Symbol T g.NT) ∈
        ([Symbol.terminal t] : List _) := by
      rw [hpq]; simp
    simp at hmem

/-- The yield of a list of leaves is the original list of terminals. -/
private theorem yieldList_leaves (w : List T) :
    CFGTree.yieldList (w.map (CFGTree.leaf : T → CFGTree T g.NT)) = w := by
  induction w with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, CFGTree.yieldList, CFGTree.yield, List.singleton_append, ih]

/-- `yieldList` distributes over list concatenation. -/
private theorem yieldList_append {N : Type} (xs ys : List (CFGTree T N)) :
    CFGTree.yieldList (xs ++ ys) = CFGTree.yieldList xs ++ CFGTree.yieldList ys := by
  induction xs with
  | nil => simp [CFGTree.yieldList]
  | cons x xs ih =>
    simp only [List.cons_append, CFGTree.yieldList, ih, List.append_assoc]

set_option maxHeartbeats 800000 in
/-- **Forest existence.** For any sentential form `sf` deriving a terminal string `w`,
    there exists a list of trees whose roots match `sf`, are all valid, and whose
    concatenated yields equal `w`. -/
private theorem forest_exists {sf : List (Symbol T g.NT)} {w : List T}
    (h : g.Derives sf (w.map Symbol.terminal)) :
    ∃ trees : List (CFGTree T g.NT),
      trees.map CFGTree.rootSymbol = sf ∧
      (∀ t ∈ trees, t.ValidFor g) ∧
      CFGTree.yieldList trees = w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨w.map (CFGTree.leaf : T → CFGTree T g.NT), ?_, ?_, ?_⟩
    · simp [List.map_map, Function.comp_def, CFGTree.rootSymbol]
    · intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨_, _, rfl⟩ := ht
      exact .leaf _
    · exact yieldList_leaves w
  | head h_step _ ih =>
    obtain ⟨forest_c, hroot, hvalid, hyield⟩ := ih
    obtain ⟨r, hr, hrew⟩ := h_step
    obtain ⟨p, q, hsf, hc⟩ := hrew.exists_parts
    let pLen := p.length
    let outLen := r.output.length
    let prefix' := forest_c.take pLen
    let middle := (forest_c.drop pLen).take outLen
    let suffix := forest_c.drop (pLen + outLen)
    let new_node : CFGTree T g.NT := .node r.input middle
    let new_forest := prefix' ++ [new_node] ++ suffix
    have hprefix_root : prefix'.map CFGTree.rootSymbol = p := by
      have h1 : (forest_c.take pLen).map CFGTree.rootSymbol =
          (forest_c.map CFGTree.rootSymbol).take pLen := by rw [List.map_take]
      rw [show prefix' = forest_c.take pLen from rfl, h1, hroot, hc]
      simp [pLen]
    have hmiddle_root : middle.map CFGTree.rootSymbol = r.output := by
      have h1 : ((forest_c.drop pLen).take outLen).map CFGTree.rootSymbol =
          ((forest_c.map CFGTree.rootSymbol).drop pLen).take outLen := by
        rw [List.map_take, List.map_drop]
      rw [show middle = (forest_c.drop pLen).take outLen from rfl, h1, hroot, hc]
      simp [pLen, outLen, List.append_assoc]
    have hsuffix_root : suffix.map CFGTree.rootSymbol = q := by
      have h1 : (forest_c.drop (pLen + outLen)).map CFGTree.rootSymbol =
          (forest_c.map CFGTree.rootSymbol).drop (pLen + outLen) := by
        rw [List.map_drop]
      rw [show suffix = forest_c.drop (pLen + outLen) from rfl, h1, hroot, hc]
      simp [pLen, outLen, List.append_assoc]
    refine ⟨new_forest, ?_, ?_, ?_⟩
    · rw [hsf]
      show (prefix' ++ [new_node] ++ suffix).map CFGTree.rootSymbol =
           p ++ [Symbol.nonterminal r.input] ++ q
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [hprefix_root, hsuffix_root]
      show p ++ [new_node.rootSymbol] ++ q = p ++ [Symbol.nonterminal r.input] ++ q
      rfl
    · intro t ht
      simp only [new_forest, List.mem_append, List.mem_singleton] at ht
      rcases ht with (ht | ht) | ht
      · exact hvalid t (List.mem_of_mem_take ht)
      · subst ht
        refine .node r.input middle ?_ ?_
        · rw [hmiddle_root]; exact hr
        · intro c hc
          have : c ∈ forest_c := by
            have := List.mem_of_mem_take hc
            exact List.mem_of_mem_drop this
          exact hvalid c this
      · exact hvalid t (List.mem_of_mem_drop ht)
    · show CFGTree.yieldList new_forest = w
      have h_decomp : forest_c = prefix' ++ middle ++ suffix := by
        show forest_c = forest_c.take pLen ++ (forest_c.drop pLen).take outLen ++
                        forest_c.drop (pLen + outLen)
        conv_lhs => rw [← List.take_append_drop pLen forest_c,
                        ← List.take_append_drop outLen (forest_c.drop pLen),
                        List.drop_drop]
        rw [List.append_assoc]
      have hy_orig : CFGTree.yieldList (prefix' ++ middle ++ suffix) = w := by
        rw [← h_decomp]; exact hyield
      rw [yieldList_append, yieldList_append] at hy_orig
      show CFGTree.yieldList (prefix' ++ [new_node] ++ suffix) = w
      rw [yieldList_append, yieldList_append]
      have h_node_yield : CFGTree.yieldList [new_node] = CFGTree.yieldList middle := by
        show CFGTree.yieldList [new_node] = CFGTree.yieldList middle
        simp [CFGTree.yieldList, CFGTree.yield, new_node]
      rw [h_node_yield]
      exact hy_orig

end ContextFreeGrammar

/-- **Tree existence.** Every word in a CFG's language has a valid derivation
    tree rooted at the start symbol.

    Proof: applies `forest_exists` to the start nonterminal `[g.initial]`,
    which yields a singleton forest containing the desired tree. The
    `forest_exists` lemma generalizes to all sentential forms by induction
    on the derivation, with each `Produces` step "folding" the children of
    the rewritten nonterminal back into a single node tree. -/
theorem exists_valid_tree {T : Type} (g : ContextFreeGrammar T)
    (w : List T) (hw : w ∈ g.language) :
    ∃ t : CFGTree T g.NT,
      t.ValidFor g ∧ t.yield = w ∧ t.rootSymbol = .nonterminal g.initial := by
  have hd : g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) := hw
  obtain ⟨trees, hroot, hvalid, hyield⟩ := ContextFreeGrammar.forest_exists hd
  have hlen : trees.length = 1 := by
    have := congr_arg List.length hroot
    simp at this; exact this
  match trees, hlen with
  | [t], _ =>
    refine ⟨t, ?_, ?_, ?_⟩
    · exact hvalid t (List.mem_singleton.mpr rfl)
    · have hy : CFGTree.yieldList [t] = w := hyield
      simp only [CFGTree.yieldList, List.append_nil] at hy
      exact hy
    · have hr : [t].map CFGTree.rootSymbol = [Symbol.nonterminal g.initial] := hroot
      simp at hr; exact hr

set_option maxHeartbeats 400000 in
/-- **Height–yield bound.** A valid derivation tree of height h has at most
    b^h terminal leaves, where b is the max branching factor.

    Proof: well-founded recursion on tree size. A leaf has height 0 and
    1 = b⁰ leaves. A node with children c₁...cₖ (k ≤ b) has
    |yield| = Σᵢ |yield(cᵢ)| ≤ k · b^(max heights) ≤ b · b^(h-1) = b^h. -/
theorem yield_length_le_of_height {T : Type} (g : ContextFreeGrammar T)
    (t : CFGTree T g.NT) (ht : t.ValidFor g) :
    t.yield.length ≤ g.maxBranch ^ t.height := by
  match t, ht with
  | .leaf _, _ => simp [CFGTree.yield, CFGTree.height]
  | .node nt children, .node _ _ hrule hvalid =>
    simp only [CFGTree.yield, CFGTree.height]
    have hchildren_bound : ∀ c ∈ children, c.yield.length ≤ g.maxBranch ^ c.height :=
      fun c hc => yield_length_le_of_height g c (hvalid c hc)
    have hlist := CFGTree.yieldList_le g.maxBranch g.maxBranch_ge_two children hchildren_bound
    have hlen : children.length ≤ g.maxBranch := by
      have heq : children.length = (children.map CFGTree.rootSymbol).length := by simp
      rw [heq]
      show (children.map CFGTree.rootSymbol).length ≤ g.maxBranch
      have : (children.map CFGTree.rootSymbol).length =
          (ContextFreeRule.mk nt (children.map CFGTree.rootSymbol)).output.length := rfl
      rw [this]
      exact g.maxBranch_ge_output ⟨nt, children.map CFGTree.rootSymbol⟩ hrule
    set b := g.maxBranch
    set hm := CFGTree.heightMax children
    have h1 : children.length * b ^ hm ≤ b * b ^ hm := Nat.mul_le_mul_right _ hlen
    have h2 : b * b ^ hm = b ^ (1 + hm) := by
      rw [show 1 + hm = hm + 1 from by omega, Nat.pow_succ']
    omega
termination_by sizeOf t
-- ============================================================================
-- Pumping Infrastructure: Position-based Subtree Access
-- ============================================================================

namespace CFGTree

variable {T N : Type}

/-- A position in a tree: list of child indices to follow from the root. -/
abbrev Pos := List Nat

/-- Subtree at a given position. Returns `none` if the path is invalid. -/
def subtreeAt? : CFGTree T N → Pos → Option (CFGTree T N)
  | t, [] => some t
  | .leaf _, _ :: _ => none
  | .node _ children, i :: rest =>
    children[i]?.bind (·.subtreeAt? rest)

/-- Replace the subtree at a given position. If the path is invalid, returns the
    original tree unchanged. -/
def replaceAt : CFGTree T N → Pos → CFGTree T N → CFGTree T N
  | _, [], new => new
  | .leaf t, _ :: _, _ => .leaf t
  | .node nt children, i :: rest, new =>
    if h : i < children.length then
      .node nt (children.set i (children[i].replaceAt rest new))
    else
      .node nt children

/-- Replacing a subtree at a non-root position preserves the root symbol. -/
theorem rootSymbol_replaceAt_cons (t : CFGTree T N) (i : Nat) (rest : Pos)
    (new : CFGTree T N) :
    (t.replaceAt (i :: rest) new).rootSymbol = t.rootSymbol := by
  match t with
  | .leaf _ => rfl
  | .node _ children =>
    by_cases hi : i < children.length
    · simp [replaceAt, hi, rootSymbol]
    · simp [replaceAt, hi, rootSymbol]

/-- Yield decomposition: replacing a subtree at position `p` produces yield
    `pre ++ new.yield ++ post`, where `pre`/`post` are the surrounding context. -/
theorem yield_replaceAt_decomp (t : CFGTree T N) (p : Pos) (sub : CFGTree T N)
    (h : t.subtreeAt? p = some sub) :
    ∃ pre post : List T,
      t.yield = pre ++ sub.yield ++ post ∧
      ∀ new : CFGTree T N, (t.replaceAt p new).yield = pre ++ new.yield ++ post := by
  induction p generalizing t with
  | nil =>
    simp [subtreeAt?] at h
    subst h
    refine ⟨[], [], ?_, ?_⟩
    · simp
    · intro new; simp [replaceAt]
  | cons i rest ih =>
    match t with
    | .leaf _ => simp [subtreeAt?] at h
    | .node nt children =>
      simp only [subtreeAt?] at h
      rcases hi : children[i]? with _ | child
      · simp [hi] at h
      · simp [hi] at h
        obtain ⟨pre_inner, post_inner, hyield_inner, hreplace_inner⟩ := ih child h
        have hi_lt : i < children.length := by
          rw [List.getElem?_eq_some_iff] at hi; exact hi.1
        have hget : children[i] = child := by
          rw [List.getElem?_eq_some_iff] at hi; exact hi.2
        have hsplit_orig : children = children.take i ++ child :: children.drop (i+1) := by
          calc children
              = children.take i ++ children.drop i := (List.take_append_drop _ _).symm
            _ = children.take i ++ children[i] :: children.drop (i+1) := by
                congr 1; exact List.drop_eq_getElem_cons hi_lt
            _ = children.take i ++ child :: children.drop (i+1) := by rw [hget]
        have hsplit_set : ∀ new : CFGTree T N,
            children.set i new = children.take i ++ new :: children.drop (i+1) := by
          intro new
          clear hsplit_orig hget hi h hyield_inner hreplace_inner ih
          induction children generalizing i with
          | nil => simp at hi_lt
          | cons c cs ih_cs =>
            cases i with
            | zero => simp [List.set]
            | succ k =>
              simp only [List.length_cons] at hi_lt
              have hk_lt : k < cs.length := by omega
              simp [List.set, ih_cs k hk_lt]
        refine ⟨yieldList (children.take i) ++ pre_inner,
                post_inner ++ yieldList (children.drop (i+1)), ?_, ?_⟩
        · show yieldList children = _
          conv_lhs => rw [hsplit_orig]
          rw [ContextFreeGrammar.yieldList_append]
          show _ = (yieldList (children.take i) ++ pre_inner) ++ sub.yield ++
              (post_inner ++ yieldList (children.drop (i+1)))
          have hcons_eq : yieldList (child :: children.drop (i+1)) =
              child.yield ++ yieldList (children.drop (i+1)) := by
            simp [yieldList]
          rw [hcons_eq, hyield_inner]
          simp [List.append_assoc]
        · intro new
          have hreplace_unfolds :
              replaceAt (.node nt children) (i :: rest) new =
              .node nt (children.set i (child.replaceAt rest new)) := by
            simp only [replaceAt, hi_lt, ↓reduceDIte, hget]
          rw [hreplace_unfolds]
          show yieldList (children.set i (child.replaceAt rest new)) = _
          rw [hsplit_set, ContextFreeGrammar.yieldList_append]
          show _ = (yieldList (children.take i) ++ pre_inner) ++ new.yield ++
              (post_inner ++ yieldList (children.drop (i+1)))
          have hcons_eq2 : yieldList (child.replaceAt rest new :: children.drop (i+1)) =
              (child.replaceAt rest new).yield ++ yieldList (children.drop (i+1)) := by
            simp [yieldList]
          rw [hcons_eq2, hreplace_inner new]
          simp [List.append_assoc]

/-- Replacing a subtree of the same root symbol preserves validity. -/
theorem validFor_replaceAt {g : ContextFreeGrammar T}
    (t : CFGTree T g.NT) (p : Pos) (sub new : CFGTree T g.NT)
    (h : t.subtreeAt? p = some sub)
    (hroot : new.rootSymbol = sub.rootSymbol)
    (ht_valid : t.ValidFor g) (hnew_valid : new.ValidFor g) :
    (t.replaceAt p new).ValidFor g := by
  induction p generalizing t with
  | nil =>
    simp [subtreeAt?] at h
    subst h
    simp [replaceAt]
    exact hnew_valid
  | cons i rest ih =>
    match t with
    | .leaf _ => simp [subtreeAt?] at h
    | .node nt children =>
      simp only [subtreeAt?] at h
      rcases hi : children[i]? with _ | child
      · simp [hi] at h
      · simp [hi] at h
        have hi_lt : i < children.length := by
          rw [List.getElem?_eq_some_iff] at hi; exact hi.1
        have hget : children[i] = child := by
          rw [List.getElem?_eq_some_iff] at hi; exact hi.2
        have hreplace_unfolds :
            replaceAt (.node nt children) (i :: rest) new =
            .node nt (children.set i (child.replaceAt rest new)) := by
          simp only [replaceAt, hi_lt, ↓reduceDIte, hget]
        rw [hreplace_unfolds]
        match ht_valid with
        | .node _ _ hrule hchildren =>
          have hchild_valid : child.ValidFor g := hchildren child (by
            rw [show child = children[i] from hget.symm]
            exact List.getElem_mem _)
          have hchild_replace_valid : (child.replaceAt rest new).ValidFor g :=
            ih child h hchild_valid
          have hchild_replace_root :
              (child.replaceAt rest new).rootSymbol = child.rootSymbol := by
            cases rest with
            | nil =>
              simp [replaceAt]
              simp [subtreeAt?] at h
              subst h
              exact hroot
            | cons _ _ => exact rootSymbol_replaceAt_cons _ _ _ _
          refine .node nt _ ?_ ?_
          · have hmap_eq : (children.set i (child.replaceAt rest new)).map rootSymbol =
                children.map rootSymbol := by
              rw [List.map_set, hchild_replace_root, ← hget]
              have h_map_lt : i < (children.map rootSymbol).length := by
                rw [List.length_map]; exact hi_lt
              rw [show children[i].rootSymbol = (children.map rootSymbol)[i]'h_map_lt from
                (List.getElem_map _).symm]
              exact List.set_getElem_self _
            rw [hmap_eq]; exact hrule
          · intro c hc_mem
            rcases List.mem_or_eq_of_mem_set hc_mem with hc_orig | hc_eq
            · exact hchildren c hc_orig
            · subst hc_eq; exact hchild_replace_valid

/-- Among a nonempty list of trees, there is one with maximum height. -/
private theorem exists_max_height (c : CFGTree T N) (cs : List (CFGTree T N)) :
    ∃ c_max ∈ (c :: cs : List (CFGTree T N)),
      ∀ c' ∈ (c :: cs : List (CFGTree T N)), c'.height ≤ c_max.height := by
  induction cs generalizing c with
  | nil =>
    refine ⟨c, List.mem_singleton.mpr rfl, ?_⟩
    intro c' hc'
    rw [List.mem_singleton.mp hc']
  | cons d ds ih =>
    obtain ⟨m, hm_mem, hm_max⟩ := ih c
    by_cases hgt : d.height > m.height
    · refine ⟨d, by simp, ?_⟩
      intro c' hc'
      simp only [List.mem_cons] at hc'
      rcases hc' with hcc | hcd | hcds
      · subst hcc
        have := hm_max c' (List.mem_cons_self ..)
        omega
      · subst hcd; exact le_refl _
      · have := hm_max c' (by simp [hcds]); omega
    · refine ⟨m, ?_, ?_⟩
      · simp only [List.mem_cons] at hm_mem ⊢
        rcases hm_mem with hmc | hmds
        · left; exact hmc
        · right; right; exact hmds
      · intro c' hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with hcc | hcd | hcds
        · subst hcc; exact hm_max c' (List.mem_cons_self ..)
        · subst hcd; push Not at hgt; exact hgt
        · exact hm_max c' (by simp [hcds])

-- ============================================================================
-- Spine extraction & pigeonhole
-- ============================================================================

/-- For a max-height list, find the max-height element. -/
private theorem exists_max_height_child (c : CFGTree T N) (cs : List (CFGTree T N)) :
    ∃ c_max ∈ (c :: cs : List (CFGTree T N)),
      c_max.height = heightMax (c :: cs) := by
  induction cs generalizing c with
  | nil => exact ⟨c, by simp, by simp [heightMax]⟩
  | cons d ds ih =>
    obtain ⟨m, hm_mem, hm_eq⟩ := ih c
    have hc_le_m : c.height ≤ m.height := by
      have : heightMax (c :: ds) = max c.height (heightMax ds) := by simp [heightMax]
      rw [this] at hm_eq; omega
    have hds_le_m : heightMax ds ≤ m.height := by
      have : heightMax (c :: ds) = max c.height (heightMax ds) := by simp [heightMax]
      rw [this] at hm_eq; omega
    by_cases hgt : d.height > m.height
    · refine ⟨d, by simp, ?_⟩
      have h1 : heightMax (c :: d :: ds) = max c.height (max d.height (heightMax ds)) := by
        simp [heightMax]
      rw [h1, max_eq_left (le_of_lt (by omega : heightMax ds < d.height)),
          max_eq_right (by omega : c.height ≤ d.height)]
    · push Not at hgt
      refine ⟨m, ?_, ?_⟩
      · simp at hm_mem ⊢
        rcases hm_mem with hmc | hmds
        · left; exact hmc
        · right; right; exact hmds
      · have h1 : heightMax (c :: d :: ds) = max c.height (max d.height (heightMax ds)) := by
          simp [heightMax]
        rw [h1]
        apply le_antisymm
        · have hm_eq' : m.height = max c.height (heightMax ds) := by
            have : heightMax (c :: ds) = max c.height (heightMax ds) := by simp [heightMax]
            rw [this] at hm_eq; exact hm_eq
          rw [hm_eq']
          exact max_le_max (le_refl _) (le_max_right _ _)
        · exact max_le hc_le_m (max_le hgt hds_le_m)

/-- For a tree of height ≥ k+1, there exists a position list of length k
    such that the subtree at that position has height ≥ 1 (i.e., is a `.node`). -/
theorem exists_pos_of_height (t : CFGTree T N) (k : Nat) (h : t.height ≥ k + 1) :
    ∃ p : Pos, p.length = k ∧ ∃ sub, t.subtreeAt? p = some sub ∧ sub.height ≥ 1 := by
  induction k generalizing t with
  | zero => exact ⟨[], rfl, t, rfl, h⟩
  | succ n ih =>
    match t with
    | .leaf _ => simp [height] at h
    | .node nt children =>
      have hmax : heightMax children ≥ n + 1 := by simp [height] at h; omega
      match hcs : children with
      | [] => simp [heightMax] at hmax
      | c :: cs =>
        obtain ⟨c_max, hmem, heq⟩ := exists_max_height_child c cs
        have hc_height : c_max.height ≥ n + 1 := by rw [heq]; exact hmax
        rcases List.mem_iff_get.mp hmem with ⟨⟨k_idx, hk_lt⟩, hk_get⟩
        obtain ⟨p_inner, hp_len, sub, hsub, hsub_h⟩ := ih c_max hc_height
        refine ⟨k_idx :: p_inner, ?_, sub, ?_, hsub_h⟩
        · simp [hp_len]
        · simp only [subtreeAt?]
          rw [show (c :: cs)[k_idx]? = some c_max from
            List.getElem?_eq_some_iff.mpr ⟨hk_lt, hk_get⟩]
          simp [hsub]

/-- Stronger: extract a max-descent path of length k, with subtree at depth i
    having height = t.height - i. -/
theorem exists_pos_max_descent (t : CFGTree T N) (k : Nat) (h : t.height ≥ k + 1) :
    ∃ p : Pos, p.length = k ∧
      ∀ i, i ≤ k → ∃ sub, t.subtreeAt? (p.take i) = some sub ∧ sub.height = t.height - i := by
  induction k generalizing t with
  | zero =>
    refine ⟨[], rfl, ?_⟩
    intro i hi
    have : i = 0 := by omega
    subst this
    refine ⟨t, rfl, ?_⟩
    simp
  | succ n ih =>
    match t with
    | .leaf _ => simp [height] at h
    | .node nt children =>
      have hmax : heightMax children ≥ n + 1 := by simp [height] at h; omega
      match hcs : children with
      | [] => simp [heightMax] at hmax
      | c :: cs =>
        obtain ⟨c_max, hmem, heq⟩ := exists_max_height_child c cs
        have hc_height_ge : c_max.height ≥ n + 1 := by rw [heq]; exact hmax
        rcases List.mem_iff_get.mp hmem with ⟨⟨k_idx, hk_lt⟩, hk_get⟩
        obtain ⟨p_inner, hp_len, hsub_at⟩ := ih c_max hc_height_ge
        refine ⟨k_idx :: p_inner, by simp [hp_len], ?_⟩
        intro i hi
        subst hcs
        cases i with
        | zero =>
          simp only [List.take_zero, subtreeAt?]
          refine ⟨.node nt (c :: cs), rfl, ?_⟩
          simp
        | succ k' =>
          simp only [List.take_succ_cons]
          have hk'_le_n : k' ≤ n := by omega
          obtain ⟨sub, hsub_at_inner, hsub_h⟩ := hsub_at k' hk'_le_n
          refine ⟨sub, ?_, ?_⟩
          · simp only [subtreeAt?]
            rw [show (c :: cs)[k_idx]? = some c_max from
              List.getElem?_eq_some_iff.mpr ⟨hk_lt, hk_get⟩]
            simpa using hsub_at_inner
          · rw [hsub_h, heq]
            simp [height]
            omega

/-- subtreeAt? splits along path concatenation. -/
theorem subtreeAt?_append (t : CFGTree T N) (p1 p2 : Pos) :
    t.subtreeAt? (p1 ++ p2) = (t.subtreeAt? p1).bind (·.subtreeAt? p2) := by
  induction p1 generalizing t with
  | nil => simp [subtreeAt?]
  | cons i rest ih =>
    match t with
    | .leaf _ => simp [subtreeAt?]
    | .node _ children =>
      simp only [List.cons_append, subtreeAt?]
      rcases hi : children[i]? with _ | child
      · simp
      · simp [ih]

/-- For a valid tree and a path that descends, each prefix subtree is a `.node`. -/
theorem spine_node_at_prefix (t : CFGTree T N) (p : Pos) (sub : CFGTree T N)
    (hsub : t.subtreeAt? p = some sub) (hsub_h : sub.height ≥ 1)
    (k : Nat) (hk : k < p.length + 1) :
    ∃ nt children, t.subtreeAt? (p.take k) = some (.node nt children) := by
  induction p generalizing t k with
  | nil =>
    simp at hk; subst hk
    simp [subtreeAt?] at hsub
    subst hsub
    match t, hsub_h with
    | .node nt children, _ => exact ⟨nt, children, rfl⟩
  | cons i rest ih =>
    cases k with
    | zero =>
      simp [subtreeAt?]
      match t with
      | .leaf _ => simp [subtreeAt?] at hsub
      | .node nt children => exact ⟨nt, children, rfl⟩
    | succ k' =>
      simp only [List.take_succ_cons]
      simp only [List.length_cons] at hk
      have hk' : k' < rest.length + 1 := by omega
      match t with
      | .leaf _ => simp [subtreeAt?] at hsub
      | .node nt children =>
        simp only [subtreeAt?] at hsub ⊢
        rcases hi : children[i]? with _ | child
        · simp [hi] at hsub
        · simp [hi] at hsub
          exact ih child hsub k' hk'

/-- Validity propagates through subtreeAt?. -/
theorem subtreeAt?_validFor {g : ContextFreeGrammar T} (t : CFGTree T g.NT)
    (ht : t.ValidFor g) (p : Pos) (sub : CFGTree T g.NT)
    (hsub : t.subtreeAt? p = some sub) : sub.ValidFor g := by
  induction p generalizing t with
  | nil => simp [subtreeAt?] at hsub; subst hsub; exact ht
  | cons i rest ih =>
    match t with
    | .leaf _ => simp [subtreeAt?] at hsub
    | .node nt children =>
      simp only [subtreeAt?] at hsub
      rcases hi : children[i]? with _ | child
      · simp [hi] at hsub
      · simp [hi] at hsub
        match ht with
        | .node _ _ _ hchildren =>
          have hi_lt : i < children.length := by
            rw [List.getElem?_eq_some_iff] at hi; exact hi.1
          have hchild_in : child ∈ children := by
            rw [show child = children[i] from by
              rw [List.getElem?_eq_some_iff] at hi; exact hi.2.symm]
            exact List.getElem_mem _
          exact ih child (hchildren child hchild_in) hsub

/-- Extract the rule used at a position (option-valued). -/
def ruleAt? {g : ContextFreeGrammar T} (t : CFGTree T g.NT) (p : Pos) :
    Option (ContextFreeRule T g.NT) :=
  match t.subtreeAt? p with
  | some (.node nt children) => some ⟨nt, children.map rootSymbol⟩
  | _ => none

/-- For a valid tree at a `.node` subtree, ruleAt? returns the matching rule in g.rules. -/
theorem ruleAt?_mem_rules {g : ContextFreeGrammar T} (t : CFGTree T g.NT)
    (ht : t.ValidFor g) (p : Pos) (nt : g.NT) (children : List (CFGTree T g.NT))
    (hsub : t.subtreeAt? p = some (.node nt children)) :
    ruleAt? t p = some ⟨nt, children.map rootSymbol⟩ ∧
    ⟨nt, children.map rootSymbol⟩ ∈ g.rules := by
  refine ⟨?_, ?_⟩
  · simp [ruleAt?, hsub]
  · have hsub_valid : (CFGTree.node nt children).ValidFor g :=
      subtreeAt?_validFor t ht p (.node nt children) hsub
    match hsub_valid with
    | .node _ _ hrule _ => exact hrule

-- ============================================================================
-- Tree size measure (for minimality argument)
-- ============================================================================

mutual
def size : CFGTree T N → Nat
  | .leaf _ => 1
  | .node _ children => 1 + sizeList children

def sizeList : List (CFGTree T N) → Nat
  | [] => 0
  | t :: ts => t.size + sizeList ts
end

theorem size_pos (t : CFGTree T N) : t.size ≥ 1 := by
  match t with
  | .leaf _ => simp [size]
  | .node _ _ => simp [size]

theorem sizeList_le_of_mem {t : CFGTree T N} {ts : List (CFGTree T N)} (h : t ∈ ts) :
    t.size ≤ sizeList ts := by
  induction ts with
  | nil => simp at h
  | cons s ss ih =>
    simp only [sizeList]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem size_subtreeAt?_le (t : CFGTree T N) (p : Pos) (sub : CFGTree T N)
    (h : t.subtreeAt? p = some sub) : sub.size ≤ t.size := by
  induction p generalizing t with
  | nil =>
    have hsub : sub = t := (by simpa [subtreeAt?] using h : t = sub).symm
    rw [hsub]
  | cons i rest ih =>
    match t with
    | .leaf _ => simp [subtreeAt?] at h
    | .node _ children =>
      simp only [subtreeAt?] at h
      rcases hi : children[i]? with _ | child
      · simp [hi] at h
      · simp [hi] at h
        have hi_lt := (List.getElem?_eq_some_iff.mp hi).1
        have hget := (List.getElem?_eq_some_iff.mp hi).2
        have := ih child h
        have := sizeList_le_of_mem (hget ▸ List.getElem_mem hi_lt)
        simp [size]; omega

theorem size_subtreeAt?_lt_of_cons (t : CFGTree T N) (i : Nat) (rest : Pos)
    (sub : CFGTree T N) (h : t.subtreeAt? (i :: rest) = some sub) :
    sub.size < t.size := by
  match t with
  | .leaf _ => simp [subtreeAt?] at h
  | .node _ children =>
    simp only [subtreeAt?] at h
    rcases hi : children[i]? with _ | child
    · simp [hi] at h
    · simp [hi] at h
      have hi_lt := (List.getElem?_eq_some_iff.mp hi).1
      have hget := (List.getElem?_eq_some_iff.mp hi).2
      have := size_subtreeAt?_le child rest sub h
      have := sizeList_le_of_mem (hget ▸ List.getElem_mem hi_lt)
      simp [size]; omega

theorem sizeList_set (l : List (CFGTree T N)) (i : Nat) (x : CFGTree T N) (hi : i < l.length) :
    sizeList (l.set i x) + l[i].size = sizeList l + x.size := by
  induction l generalizing i with
  | nil => simp at hi
  | cons h t ih =>
    cases i with
    | zero => simp [List.set, sizeList]; omega
    | succ k =>
      simp only [List.length_cons] at hi
      have hk_lt : k < t.length := by omega
      simp only [List.set, sizeList, List.getElem_cons_succ]
      have := ih k hk_lt
      omega

/-- Replacing a subtree with a strictly smaller one gives a strictly smaller tree. -/
theorem size_replaceAt_lt (t : CFGTree T N) (p : Pos) (sub new : CFGTree T N)
    (h : t.subtreeAt? p = some sub) (hlt : new.size < sub.size) :
    (t.replaceAt p new).size < t.size := by
  induction p generalizing t with
  | nil =>
    simp [subtreeAt?] at h; subst h; simp [replaceAt]; exact hlt
  | cons i rest ih =>
    match t with
    | .leaf _ => simp [subtreeAt?] at h
    | .node nt children =>
      simp only [subtreeAt?] at h
      rcases hi : children[i]? with _ | child
      · simp [hi] at h
      · simp [hi] at h
        have hi_lt : i < children.length := by
          rw [List.getElem?_eq_some_iff] at hi; exact hi.1
        have hget : children[i] = child := by
          rw [List.getElem?_eq_some_iff] at hi; exact hi.2
        have hreplace_unfolds :
            replaceAt (.node nt children) (i :: rest) new =
            .node nt (children.set i (child.replaceAt rest new)) := by
          simp only [replaceAt, hi_lt, ↓reduceDIte, hget]
        rw [hreplace_unfolds]
        simp only [size]
        have hchild_lt : (child.replaceAt rest new).size < child.size := ih child h
        have hset := sizeList_set children i (child.replaceAt rest new) hi_lt
        rw [hget] at hset
        omega

/-- Existence of minimum-size valid tree with given yield and root. -/
theorem exists_min_size_tree {g : ContextFreeGrammar T} (t : CFGTree T g.NT) (ht : t.ValidFor g) :
    ∃ t_min : CFGTree T g.NT,
      t_min.ValidFor g ∧
      t_min.yield = t.yield ∧
      t_min.rootSymbol = t.rootSymbol ∧
      ∀ t' : CFGTree T g.NT,
        t'.ValidFor g → t'.yield = t.yield →
        t'.rootSymbol = t.rootSymbol →
        t_min.size ≤ t'.size := by
  classical
  let P : Nat → Prop := fun n => ∃ t' : CFGTree T g.NT,
    t'.ValidFor g ∧ t'.yield = t.yield ∧ t'.rootSymbol = t.rootSymbol ∧ t'.size = n
  have hP_ne : ∃ n, P n := ⟨t.size, t, ht, rfl, rfl, rfl⟩
  obtain ⟨t_min, ht_min_v, ht_min_y, ht_min_r, ht_min_s⟩ := Nat.find_spec hP_ne
  refine ⟨t_min, ht_min_v, ht_min_y, ht_min_r, ?_⟩
  intro t' ht'_v ht'_y ht'_r
  have hP_t' : P t'.size := ⟨t', ht'_v, ht'_y, ht'_r, rfl⟩
  have hle : Nat.find hP_ne ≤ t'.size := Nat.find_le hP_t'
  omega

/-- Pigeonhole: along a long-enough valid path, two prefixes have same root nonterminal. -/
theorem exists_repeat_root {g : ContextFreeGrammar T}
    (t : CFGTree T g.NT) (ht : t.ValidFor g)
    (p : Pos) (sub : CFGTree T g.NT)
    (hsub : t.subtreeAt? p = some sub) (hsub_h : sub.height ≥ 1)
    (hlen : p.length ≥ g.rules.card) :
    ∃ i j : Nat, i < j ∧ j ≤ p.length ∧
      ∃ ntᵢ children_i ntⱼ children_j,
        t.subtreeAt? (p.take i) = some (.node ntᵢ children_i) ∧
        t.subtreeAt? (p.take j) = some (.node ntⱼ children_j) ∧
        ntᵢ = ntⱼ := by
  classical
  let f : Nat → ContextFreeRule T g.NT := fun k =>
    (ruleAt? t (p.take k)).getD ⟨g.initial, []⟩
  have hf_in : ∀ k ∈ Finset.range (p.length + 1), f k ∈ g.rules := by
    intro k hk
    simp at hk
    obtain ⟨nt, children, hsub_k⟩ := spine_node_at_prefix t p sub hsub hsub_h k hk
    obtain ⟨hrule_eq, hrule_in⟩ := ruleAt?_mem_rules t ht (p.take k) nt children hsub_k
    show f k ∈ g.rules
    simp only [f, hrule_eq, Option.getD_some]
    exact hrule_in
  have hcard : g.rules.card < (Finset.range (p.length + 1)).card := by
    simp [Finset.card_range]; omega
  obtain ⟨a, ha, b, hb, hne, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hf_in
  simp at ha hb
  rcases Nat.lt_or_ge a b with hab | hab
  · obtain ⟨nt_a, children_a, hsub_a⟩ := spine_node_at_prefix t p sub hsub hsub_h a ha
    obtain ⟨nt_b, children_b, hsub_b⟩ := spine_node_at_prefix t p sub hsub hsub_h b hb
    obtain ⟨hrule_a, _⟩ := ruleAt?_mem_rules t ht (p.take a) nt_a children_a hsub_a
    obtain ⟨hrule_b, _⟩ := ruleAt?_mem_rules t ht (p.take b) nt_b children_b hsub_b
    have h_fa : f a = ⟨nt_a, children_a.map rootSymbol⟩ := by
      simp only [f, hrule_a, Option.getD_some]
    have h_fb : f b = ⟨nt_b, children_b.map rootSymbol⟩ := by
      simp only [f, hrule_b, Option.getD_some]
    have : nt_a = nt_b := by
      have : (⟨nt_a, children_a.map rootSymbol⟩ : ContextFreeRule T g.NT) =
          ⟨nt_b, children_b.map rootSymbol⟩ := by rw [← h_fa, ← h_fb, hfeq]
      exact ContextFreeRule.mk.injEq _ _ _ _ |>.mp this |>.1
    exact ⟨a, b, hab, by omega, nt_a, children_a, nt_b, children_b, hsub_a, hsub_b, this⟩
  · have hba : b < a := lt_of_le_of_ne hab (Ne.symm hne)
    obtain ⟨nt_a, children_a, hsub_a⟩ := spine_node_at_prefix t p sub hsub hsub_h a ha
    obtain ⟨nt_b, children_b, hsub_b⟩ := spine_node_at_prefix t p sub hsub hsub_h b hb
    obtain ⟨hrule_a, _⟩ := ruleAt?_mem_rules t ht (p.take a) nt_a children_a hsub_a
    obtain ⟨hrule_b, _⟩ := ruleAt?_mem_rules t ht (p.take b) nt_b children_b hsub_b
    have h_fa : f a = ⟨nt_a, children_a.map rootSymbol⟩ := by
      simp only [f, hrule_a, Option.getD_some]
    have h_fb : f b = ⟨nt_b, children_b.map rootSymbol⟩ := by
      simp only [f, hrule_b, Option.getD_some]
    have : nt_b = nt_a := by
      have : (⟨nt_b, children_b.map rootSymbol⟩ : ContextFreeRule T g.NT) =
          ⟨nt_a, children_a.map rootSymbol⟩ := by rw [← h_fa, ← h_fb, hfeq]
      exact ContextFreeRule.mk.injEq _ _ _ _ |>.mp this |>.1
    exact ⟨b, a, hba, by omega, nt_b, children_b, nt_a, children_a, hsub_b, hsub_a, this⟩

-- ============================================================================
-- Soundness: valid tree ⇒ grammar derives its yield
-- ============================================================================

private theorem derives_yieldList {T : Type} {g : ContextFreeGrammar T}
    (ts : List (CFGTree T g.NT))
    (hvalid : ∀ t ∈ ts, g.Derives [t.rootSymbol] (t.yield.map Symbol.terminal)) :
    g.Derives (ts.map CFGTree.rootSymbol) ((CFGTree.yieldList ts).map Symbol.terminal) := by
  induction ts with
  | nil => exact Relation.ReflTransGen.refl
  | cons c cs ih =>
    simp only [List.map_cons, CFGTree.yieldList, List.map_append]
    show g.Derives ([c.rootSymbol] ++ cs.map CFGTree.rootSymbol)
      (c.yield.map Symbol.terminal ++ (CFGTree.yieldList cs).map Symbol.terminal)
    exact ((hvalid c (List.mem_cons_self ..)).append_right _).trans
      ((ih (fun t ht => hvalid t (List.mem_cons_of_mem _ ht))).append_left _)

theorem validFor_derives {T : Type} {g : ContextFreeGrammar T}
    (t : CFGTree T g.NT) (ht : t.ValidFor g) :
    g.Derives [t.rootSymbol] (t.yield.map Symbol.terminal) := by
  match t, ht with
  | .leaf _, _ => exact Relation.ReflTransGen.refl
  | .node nt children, .node _ _ hrule hchildren =>
    exact (ContextFreeGrammar.Produces.single
      ⟨⟨nt, children.map CFGTree.rootSymbol⟩, hrule,
       ContextFreeRule.Rewrites.input_output⟩).trans
      (derives_yieldList children (fun c hc => validFor_derives c (hchildren c hc)))
termination_by t

end CFGTree
