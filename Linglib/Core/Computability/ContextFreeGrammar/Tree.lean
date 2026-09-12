/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.ContextFreeGrammar
import Linglib.Core.Data.RoseTree.Get
import Linglib.Core.Data.RoseTree.Countable
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-!
# Derivation trees of a context-free grammar

A derivation tree of a context-free grammar is a rose tree over its symbols,
`RoseTree (Symbol T N)`. It is valid for a grammar when every terminal node is a leaf and every
nonterminal node, read with the symbols of its children, is a rule. The yield of a tree is the
list of terminals at its leaves, left to right.

## Main definitions

* `RoseTree.yield`: the terminal frontier.
* `RoseTree.ValidFor g`: validity for the grammar `g`.
* `RoseTree.ruleCount`, `RoseTree.corpusRuleCount`: the number of applications of a rule in a
  tree and in a corpus of trees.
* `RoseTree.ruleAt?`: the rule applied at a Gorn address.
* `ContextFreeGrammar.maxBranch`, `ContextFreeGrammar.pumpingConstant`: the branching bound and
  the pumping constant of a grammar.

## Main results

* `RoseTree.ValidFor.derives`: a valid tree derives its yield from its root symbol.
* `ContextFreeGrammar.exists_valid_tree`: every word of the language has a valid derivation tree
  from the start symbol.
* `RoseTree.ValidFor.length_yield_le`: a valid tree of height `h` has at most `maxBranch ^ h`
  terminals.
* `RoseTree.ValidFor.replaceAt`, `RoseTree.ValidFor.exists_repeat`: replacing a subtree by one
  with the same root symbol preserves validity, and a long enough path in a valid tree passes two
  nodes with the same nonterminal; together with `RoseTree.numNodes_replaceAt_lt` these are the
  ingredients of the pumping lemma.
-/

/-- The terminal at a symbol, if it is one. -/
def Symbol.terminal? {T N : Type*} : Symbol T N → Option T
  | .terminal a => some a
  | .nonterminal _ => none

@[simp] theorem Symbol.terminal?_terminal {T N : Type*} (a : T) :
    (Symbol.terminal a : Symbol T N).terminal? = some a := rfl

@[simp] theorem Symbol.terminal?_nonterminal {T N : Type*} (A : N) :
    (Symbol.nonterminal A : Symbol T N).terminal? = none := rfl

/-- Relabel the nonterminals of a symbol. -/
def Symbol.mapNonterminal {T N N' : Type*} (f : N → N') : Symbol T N → Symbol T N'
  | .terminal a => .terminal a
  | .nonterminal A => .nonterminal (f A)

@[simp] theorem Symbol.mapNonterminal_terminal {T N N' : Type*} (f : N → N') (a : T) :
    Symbol.mapNonterminal f (Symbol.terminal a : Symbol T N) = .terminal a := rfl

@[simp] theorem Symbol.mapNonterminal_nonterminal {T N N' : Type*} (f : N → N') (A : N) :
    Symbol.mapNonterminal f (Symbol.nonterminal A : Symbol T N) = .nonterminal (f A) := rfl

@[simp] theorem Symbol.terminal?_mapNonterminal {T N N' : Type*} (f : N → N') (s : Symbol T N) :
    (s.mapNonterminal f).terminal? = s.terminal? := by cases s <;> rfl

instance Symbol.instCountable {T N : Type*} [Countable T] [Countable N] : Countable (Symbol T N) :=
  Function.Injective.countable (f := fun s : Symbol T N => match s with
    | .terminal t => Sum.inl t
    | .nonterminal n => Sum.inr n) fun s s' h => by
    cases s <;> cases s' <;> simp_all

namespace RoseTree

variable {T N : Type*}

/-! ### The yield -/

/-- The terminal frontier of a tree: the terminals among its leaves, left to right. -/
def yield (t : RoseTree (Symbol T N)) : List T := t.leafList.filterMap Symbol.terminal?

@[simp] theorem yield_node_nil (s : Symbol T N) : yield (node s []) = s.terminal?.toList := by
  cases s <;> simp [yield]

@[simp] theorem yield_leaf (s : Symbol T N) : yield (leaf s) = s.terminal?.toList :=
  yield_node_nil s

theorem yield_node_of_ne_nil (s : Symbol T N) {cs : List (RoseTree (Symbol T N))} (h : cs ≠ []) :
    yield (node s cs) = (cs.map yield).flatten := by
  rw [yield, leafList_node_of_ne_nil _ h, List.filterMap_flatten, List.map_map]
  rfl

@[simp] theorem yield_node_cons (s : Symbol T N) (c : RoseTree (Symbol T N))
    (cs : List (RoseTree (Symbol T N))) :
    yield (node s (c :: cs)) = ((c :: cs).map yield).flatten :=
  yield_node_of_ne_nil s (List.cons_ne_nil c cs)

@[simp] theorem yield_node_nonterminal (A : N) (cs : List (RoseTree (Symbol T N))) :
    yield (node (.nonterminal A) cs) = (cs.map yield).flatten := by
  cases cs with
  | nil => simp
  | cons c cs => exact yield_node_cons _ c cs

@[simp] theorem yield_map {N' : Type*} (f : N → N') (t : RoseTree (Symbol T N)) :
    (t.map (Symbol.mapNonterminal f)).yield = t.yield := by
  simp only [yield, leafList_map, List.filterMap_map, Function.comp_def,
    Symbol.terminal?_mapNonterminal]

/-- Replacing inside the tree splits the yield into the terminals left of the address, the yield
of the subtree there, and the terminals to its right. -/
theorem yield_replaceAt {t s : RoseTree (Symbol T N)} {p : List ℕ} (h : t.subtreeAt p = some s) :
    ∃ pre post : List T, t.yield = pre ++ s.yield ++ post ∧
      ∀ new : RoseTree (Symbol T N), (t.replaceAt p new).yield = pre ++ new.yield ++ post := by
  obtain ⟨pre, post, hy, hy'⟩ := leafList_replaceAt h
  exact ⟨pre.filterMap Symbol.terminal?, post.filterMap Symbol.terminal?,
    by simp [yield, hy, List.filterMap_append],
    fun new => by simp [yield, hy', List.filterMap_append]⟩

/-! ### Validity -/

/-- A derivation tree is valid for a grammar when every terminal node is a leaf and every
nonterminal node, with the symbols of its children, is a rule of the grammar. -/
inductive ValidFor (g : ContextFreeGrammar T) : RoseTree (Symbol T g.NT) → Prop
  | terminal (a : T) : ValidFor g (leaf (.terminal a))
  | nonterminal (A : g.NT) (cs : List (RoseTree (Symbol T g.NT)))
      (hrule : ⟨A, cs.map value⟩ ∈ g.rules) (hcs : ∀ c ∈ cs, ValidFor g c) :
      ValidFor g (node (.nonterminal A) cs)

namespace ValidFor

variable {g : ContextFreeGrammar T}

theorem of_mem {s : Symbol T g.NT} {cs : List (RoseTree (Symbol T g.NT))}
    (h : ValidFor g (node s cs)) {c : RoseTree (Symbol T g.NT)} (hc : c ∈ cs) : ValidFor g c := by
  cases h with
  | terminal => simp at hc
  | nonterminal _ _ _ hcs => exact hcs c hc

theorem rule_mem {A : g.NT} {cs : List (RoseTree (Symbol T g.NT))}
    (h : ValidFor g (node (.nonterminal A) cs)) : ⟨A, cs.map value⟩ ∈ g.rules := by
  cases h with
  | nonterminal _ _ hrule => exact hrule

theorem eq_nil_of_terminal {a : T} {cs : List (RoseTree (Symbol T g.NT))}
    (h : ValidFor g (node (.terminal a) cs)) : cs = [] := by
  cases h; rfl

/-- A node with children is a nonterminal node. -/
theorem exists_nonterminal_of_ne_nil {s : Symbol T g.NT} {cs : List (RoseTree (Symbol T g.NT))}
    (h : ValidFor g (node s cs)) (hcs : cs ≠ []) : ∃ A, s = .nonterminal A := by
  cases h with
  | terminal => exact absurd rfl hcs
  | nonterminal A => exact ⟨A, rfl⟩

theorem subtreeAt {t : RoseTree (Symbol T g.NT)} (ht : ValidFor g t) {p : List ℕ}
    {s : RoseTree (Symbol T g.NT)} (hs : t.subtreeAt p = some s) : ValidFor g s := by
  induction p generalizing t with
  | nil => exact Option.some.inj hs ▸ ht
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp hs
    cases t with
    | node s cs => exact ih (ht.of_mem (List.mem_of_getElem? hc)) hcs

/-- Replacing a subtree by a valid tree with the same root symbol preserves validity. -/
theorem replaceAt {t : RoseTree (Symbol T g.NT)} (ht : ValidFor g t) {p : List ℕ}
    {s : RoseTree (Symbol T g.NT)} (hs : t.subtreeAt p = some s)
    {new : RoseTree (Symbol T g.NT)} (hnew : ValidFor g new) (hv : new.value = s.value) :
    ValidFor g (t.replaceAt p new) := by
  induction p generalizing t with
  | nil => rw [replaceAt_nil]; exact hnew
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp hs
    cases t with
    | node s₀ cs =>
      rw [children_node] at hc
      rw [replaceAt_cons_of_getElem? (by simpa using hc), value_node, children_node]
      have hval : (c.replaceAt p new).value = c.value := by
        cases p with
        | nil => rw [replaceAt_nil, hv, Option.some.inj hcs]
        | cons j p => exact value_replaceAt_cons c j p new
      obtain ⟨A, rfl⟩ := ht.exists_nonterminal_of_ne_nil
        (List.ne_nil_of_mem (List.mem_of_getElem? hc))
      refine nonterminal A _ ?_ fun d hd => ?_
      · obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hc
        have h := List.set_getElem_self (as := cs.map value) (i := i) (by simpa using hi)
        rw [List.getElem_map] at h
        rw [List.map_set, hval, h]
        exact ht.rule_mem
      · rcases List.mem_or_eq_of_mem_set hd with hd | rfl
        · exact ht.of_mem hd
        · exact ih (ht.of_mem (List.mem_of_getElem? hc)) hcs

end ValidFor

/-! ### Rule counts -/

section RuleCount

variable [DecidableEq T] [DecidableEq N]

/-- The number of applications of the rule `r` in a tree: the nonterminal nodes whose symbol and
children's symbols spell out `r`. -/
def ruleCount (r : ContextFreeRule T N) (t : RoseTree (Symbol T N)) : ℕ :=
  t.offspring.count (.nonterminal r.input, r.output)

theorem ruleCount_node_nonterminal (r : ContextFreeRule T N) (A : N)
    (cs : List (RoseTree (Symbol T N))) :
    ruleCount r (node (.nonterminal A) cs) =
      (if r = ⟨A, cs.map value⟩ then 1 else 0) + (cs.map (ruleCount r)).sum := by
  simp only [ruleCount, offspring_node, List.count_cons, List.count_flatten, List.map_map,
    Function.comp_def, beq_iff_eq, Prod.mk.injEq, Symbol.nonterminal.injEq]
  rw [add_comm]
  congr 1
  cases r
  simp [ContextFreeRule.mk.injEq, eq_comm]

theorem ruleCount_node_terminal (r : ContextFreeRule T N) (a : T)
    (cs : List (RoseTree (Symbol T N))) :
    ruleCount r (node (.terminal a) cs) = (cs.map (ruleCount r)).sum := by
  simp only [ruleCount, offspring_node, List.count_cons, List.count_flatten, List.map_map,
    Function.comp_def, beq_iff_eq, Prod.mk.injEq, reduceCtorEq, false_and, if_false, add_zero]
  rfl

/-- The number of applications of the rule `r` in a corpus of trees. -/
def corpusRuleCount (r : ContextFreeRule T N) (D : Multiset (RoseTree (Symbol T N))) : ℕ :=
  (D.map (ruleCount r)).sum

@[simp] theorem corpusRuleCount_zero (r : ContextFreeRule T N) :
    corpusRuleCount r (0 : Multiset (RoseTree (Symbol T N))) = 0 := by
  simp [corpusRuleCount]

@[simp] theorem corpusRuleCount_singleton (r : ContextFreeRule T N) (t : RoseTree (Symbol T N)) :
    corpusRuleCount r {t} = ruleCount r t := by
  simp [corpusRuleCount]

theorem corpusRuleCount_add (r : ContextFreeRule T N) (D₁ D₂ : Multiset (RoseTree (Symbol T N))) :
    corpusRuleCount r (D₁ + D₂) = corpusRuleCount r D₁ + corpusRuleCount r D₂ := by
  simp [corpusRuleCount]

end RuleCount

/-! ### The rule at an address -/

/-- The rule applied at a Gorn address: the nonterminal there with the symbols of its children,
`none` off the tree or at a terminal. -/
def ruleAt? {g : ContextFreeGrammar T} (t : RoseTree (Symbol T g.NT)) (p : List ℕ) :
    Option (ContextFreeRule T g.NT) :=
  (t.subtreeAt p).bind fun s => match s.value with
    | .nonterminal A => some ⟨A, s.children.map value⟩
    | .terminal _ => none

theorem ruleAt?_eq_some {g : ContextFreeGrammar T} {t : RoseTree (Symbol T g.NT)} {p : List ℕ}
    {A : g.NT} {cs : List (RoseTree (Symbol T g.NT))}
    (h : t.subtreeAt p = some (node (.nonterminal A) cs)) :
    ruleAt? t p = some ⟨A, cs.map value⟩ := by
  simp [ruleAt?, h]

/-- Along an address into a valid tree, every proper prefix ends at a nonterminal node, and so
does the address itself when the subtree there has children. -/
theorem ValidFor.exists_subtreeAt_take {g : ContextFreeGrammar T} {t : RoseTree (Symbol T g.NT)}
    (ht : ValidFor g t) {p : List ℕ} {s : RoseTree (Symbol T g.NT)} (hs : t.subtreeAt p = some s)
    (hh : 0 < s.height) {k : ℕ} (hk : k ≤ p.length) :
    ∃ A cs, t.subtreeAt (p.take k) = some (node (.nonterminal A) cs) := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (subtreeAt_take_isSome hs k)
  obtain ⟨s₀, cs, rfl⟩ : ∃ s₀ cs, u = node s₀ cs := by cases u; exact ⟨_, _, rfl⟩
  have hne : cs ≠ [] := by
    rcases Nat.lt_or_ge k p.length with hlt | hge
    · rw [← List.take_append_drop k p, subtreeAt_append, hu, Option.bind_some,
        List.drop_eq_getElem_cons hlt] at hs
      obtain ⟨c, hc, -⟩ := subtreeAt_cons_eq_some_iff.mp hs
      exact List.ne_nil_of_mem (List.mem_of_getElem? hc)
    · rw [List.take_of_length_le (le_antisymm hk hge ▸ le_rfl), hs] at hu
      obtain rfl := Option.some.inj hu
      obtain ⟨c, hc, -⟩ := exists_mem_children_height_add_one hh
      exact List.ne_nil_of_mem hc
  obtain ⟨A, rfl⟩ := (ht.subtreeAt hu).exists_nonterminal_of_ne_nil hne
  exact ⟨A, cs, hu⟩

/-- Pigeonhole along an address: a path of at least `g.rules.card` steps through a valid tree,
ending at a node with children, passes two nodes with the same nonterminal. -/
theorem ValidFor.exists_repeat {g : ContextFreeGrammar T} {t : RoseTree (Symbol T g.NT)}
    (ht : ValidFor g t) {p : List ℕ} {s : RoseTree (Symbol T g.NT)} (hs : t.subtreeAt p = some s)
    (hh : 0 < s.height) (hlen : g.rules.card ≤ p.length) :
    ∃ i j, i < j ∧ j ≤ p.length ∧ ∃ A csᵢ csⱼ,
      t.subtreeAt (p.take i) = some (node (.nonterminal A) csᵢ) ∧
      t.subtreeAt (p.take j) = some (node (.nonterminal A) csⱼ) := by
  classical
  let f : ℕ → ContextFreeRule T g.NT := fun k => (ruleAt? t (p.take k)).getD ⟨g.initial, []⟩
  have hf : ∀ k ∈ Finset.range (p.length + 1), f k ∈ g.rules := fun k hk => by
    obtain ⟨A, cs, hA⟩ :=
      ht.exists_subtreeAt_take hs hh (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    simp only [f, ruleAt?_eq_some hA, Option.getD_some]
    exact (ht.subtreeAt hA).rule_mem
  obtain ⟨a, ha, b, hb, hne, hfeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by simp only [Finset.card_range]; omega) hf
  wlog hab : a < b generalizing a b
  · exact this b hb a ha hne.symm hfeq.symm (lt_of_le_of_ne (not_lt.mp hab) hne.symm)
  rw [Finset.mem_range] at ha hb
  obtain ⟨A, csₐ, hA⟩ := ht.exists_subtreeAt_take hs hh (Nat.lt_succ_iff.mp ha)
  obtain ⟨B, cs_b, hB⟩ := ht.exists_subtreeAt_take hs hh (Nat.lt_succ_iff.mp hb)
  have : A = B := by
    have h := hfeq
    simp only [f, ruleAt?_eq_some hA, ruleAt?_eq_some hB, Option.getD_some,
      ContextFreeRule.mk.injEq] at h
    exact h.1
  subst this
  exact ⟨a, b, hab, Nat.lt_succ_iff.mp hb, A, csₐ, cs_b, hA, hB⟩

/-- Among the valid trees with a given yield and root symbol there is one of least size. -/
theorem ValidFor.exists_min_numNodes {g : ContextFreeGrammar T} {t : RoseTree (Symbol T g.NT)}
    (ht : ValidFor g t) :
    ∃ t' : RoseTree (Symbol T g.NT), ValidFor g t' ∧ t'.yield = t.yield ∧ t'.value = t.value ∧
      ∀ t'' : RoseTree (Symbol T g.NT), ValidFor g t'' → t''.yield = t.yield →
        t''.value = t.value → t'.numNodes ≤ t''.numNodes := by
  classical
  let P : ℕ → Prop := fun n => ∃ t' : RoseTree (Symbol T g.NT),
    ValidFor g t' ∧ t'.yield = t.yield ∧ t'.value = t.value ∧ t'.numNodes = n
  have hP : ∃ n, P n := ⟨t.numNodes, t, ht, rfl, rfl, rfl⟩
  obtain ⟨t', h₁, h₂, h₃, h₄⟩ := Nat.find_spec hP
  exact ⟨t', h₁, h₂, h₃, fun t'' hv hy hr => h₄ ▸ Nat.find_le ⟨t'', hv, hy, hr, rfl⟩⟩

end RoseTree

namespace ContextFreeGrammar

variable {T : Type*} (g : ContextFreeGrammar T)

/-! ### The branching bound -/

/-- The branching bound of a grammar: the longest right-hand side, and at least `2`. -/
noncomputable def maxBranch : ℕ := max 2 (g.rules.sup fun r => r.output.length)

/-- The pumping constant `maxBranch ^ (rules.card + 1)`: a valid tree with more terminals has a
path through two nodes with the same nonterminal. -/
noncomputable def pumpingConstant : ℕ := g.maxBranch ^ (g.rules.card + 1)

theorem two_le_maxBranch : 2 ≤ g.maxBranch := le_max_left _ _

theorem pumpingConstant_pos : 0 < g.pumpingConstant :=
  Nat.pow_pos (by have := g.two_le_maxBranch; omega)

theorem length_output_le_maxBranch {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    r.output.length ≤ g.maxBranch :=
  le_trans (Finset.le_sup (f := fun r : ContextFreeRule T g.NT => r.output.length) hr)
    (le_max_right _ _)

variable {g}

/-- A valid tree of height `h` has at most `maxBranch ^ h` terminals. -/
theorem _root_.RoseTree.ValidFor.length_yield_le {t : RoseTree (Symbol T g.NT)}
    (ht : t.ValidFor g) : t.yield.length ≤ g.maxBranch ^ t.height := by
  induction ht with
  | terminal a => simp [RoseTree.leaf]
  | nonterminal A cs hrule _ ih =>
    cases cs with
    | nil => simp
    | cons c cs =>
      set h := (RoseTree.node (.nonterminal A) (c :: cs)).height with hh
      have hpos : 0 < h :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) (RoseTree.height_lt_of_mem (c := c) (by simp))
      have hb : 0 < g.maxBranch := by have := g.two_le_maxBranch; omega
      rw [RoseTree.yield_node_nonterminal, List.length_flatten, List.map_map]
      calc ((c :: cs).map (List.length ∘ RoseTree.yield)).sum
          ≤ ((c :: cs).map fun _ => g.maxBranch ^ (h - 1)).sum := by
            refine List.sum_le_sum fun d hd => ?_
            refine (ih d hd).trans (Nat.pow_le_pow_right hb ?_)
            have := RoseTree.height_lt_of_mem (t := RoseTree.node (.nonterminal A) (c :: cs)) hd
            omega
        _ = (c :: cs).length * g.maxBranch ^ (h - 1) := by
            rw [List.map_const', List.sum_const_nat]
        _ ≤ g.maxBranch * g.maxBranch ^ (h - 1) :=
            Nat.mul_le_mul_right _ (by simpa using g.length_output_le_maxBranch hrule)
        _ = g.maxBranch ^ h := by rw [← Nat.pow_succ']; congr 1; omega

/-! ### Soundness and completeness -/

private theorem derives_flatten_yield {cs : List (RoseTree (Symbol T g.NT))}
    (h : ∀ c ∈ cs, g.Derives [c.value] (c.yield.map Symbol.terminal)) :
    g.Derives (cs.map RoseTree.value) ((cs.map RoseTree.yield).flatten.map Symbol.terminal) := by
  induction cs with
  | nil => exact Relation.ReflTransGen.refl
  | cons c cs ih =>
    rw [List.map_cons, List.map_cons, List.flatten_cons, List.map_append, ← List.singleton_append]
    exact ((h c (List.mem_cons_self ..)).append_right _).trans
      ((ih fun d hd => h d (List.mem_cons_of_mem _ hd)).append_left _)

/-- **Soundness.** A valid tree derives its yield from its root symbol. -/
theorem _root_.RoseTree.ValidFor.derives {t : RoseTree (Symbol T g.NT)} (ht : t.ValidFor g) :
    g.Derives [t.value] (t.yield.map Symbol.terminal) := by
  induction ht with
  | terminal a => simp [RoseTree.leaf]; exact Relation.ReflTransGen.refl
  | nonterminal A cs hrule _ ih =>
    rw [RoseTree.value_node, RoseTree.yield_node_nonterminal]
    exact (Produces.single ⟨⟨A, cs.map RoseTree.value⟩, hrule,
      ContextFreeRule.Rewrites.input_output⟩).trans (derives_flatten_yield ih)

/-- A rewriting step at any position. -/
private theorem Rewrites.at_position {r : ContextFreeRule T g.NT} (p q : List (Symbol T g.NT)) :
    r.Rewrites (p ++ [Symbol.nonterminal r.input] ++ q) (p ++ r.output ++ q) := by
  induction p with
  | nil => simpa using ContextFreeRule.Rewrites.head q
  | cons x xs ih => simpa using ContextFreeRule.Rewrites.cons x ih

/-- **Forest existence.** A sentential form deriving a word is the list of root symbols of a
list of valid trees whose yields concatenate to the word. -/
private theorem exists_forest {sf : List (Symbol T g.NT)} {w : List T}
    (h : g.Derives sf (w.map Symbol.terminal)) :
    ∃ ts : List (RoseTree (Symbol T g.NT)), ts.map RoseTree.value = sf ∧
      (∀ t ∈ ts, t.ValidFor g) ∧ (ts.map RoseTree.yield).flatten = w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨w.map fun a => RoseTree.leaf (.terminal a), ?_, ?_, ?_⟩
    · simp [Function.comp_def, RoseTree.leaf]
    · rintro t ht
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp ht
      exact .terminal a
    · induction w <;> simp_all
  | head hstep _ ih =>
    obtain ⟨ts, hroot, hvalid, hyield⟩ := ih
    obtain ⟨r, hr, hrew⟩ := hstep
    obtain ⟨p, q, hsf, hc⟩ := hrew.exists_parts
    subst hsf hc
    have hlen : p.length + r.output.length ≤ ts.length := by
      have := congrArg List.length hroot; simp at this; omega
    refine ⟨ts.take p.length ++ [RoseTree.node (.nonterminal r.input)
      ((ts.drop p.length).take r.output.length)] ++ ts.drop (p.length + r.output.length),
      ?_, ?_, ?_⟩
    · have h1 : (ts.take p.length).map RoseTree.value = p := by
        rw [List.map_take, hroot]; simp
      have h2 : ((ts.drop p.length).take r.output.length).map RoseTree.value = r.output := by
        rw [List.map_take, List.map_drop, hroot]; simp
      have h3 : (ts.drop (p.length + r.output.length)).map RoseTree.value = q := by
        rw [List.map_drop, hroot]; simp
      simp only [List.map_append, List.map_cons, List.map_nil, RoseTree.value_node, h1, h3]
    · intro t ht
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with (ht | rfl) | ht
      · exact hvalid t (List.mem_of_mem_take ht)
      · refine .nonterminal r.input _ ?_ fun c hc =>
          hvalid c (List.mem_of_mem_drop (List.mem_of_mem_take hc))
        rw [List.map_take, List.map_drop, hroot]; simpa using hr
      · exact hvalid t (List.mem_of_mem_drop ht)
    · have hsplit : ts = ts.take p.length ++ (ts.drop p.length).take r.output.length ++
          ts.drop (p.length + r.output.length) := by
        rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
      conv_rhs => rw [← hyield, hsplit]
      simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil, RoseTree.yield_node_nonterminal]

/-- **Completeness.** Every word of the language has a valid derivation tree from the start
symbol. -/
theorem exists_valid_tree (g : ContextFreeGrammar T) {w : List T} (hw : w ∈ g.language) :
    ∃ t : RoseTree (Symbol T g.NT), t.ValidFor g ∧ t.yield = w ∧
      t.value = .nonterminal g.initial := by
  obtain ⟨ts, hroot, hvalid, hyield⟩ := exists_forest (g := g) hw
  obtain ⟨t, rfl⟩ : ∃ t, ts = [t] := by
    rcases ts with _ | ⟨t, _ | ⟨_, _⟩⟩ <;> simp at hroot
    exact ⟨t, rfl⟩
  exact ⟨t, hvalid t (List.mem_singleton_self t), by simpa using hyield, by simpa using hroot⟩

end ContextFreeGrammar
