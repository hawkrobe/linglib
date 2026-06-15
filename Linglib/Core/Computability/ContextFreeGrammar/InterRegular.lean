import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Pi

/-!
# Closure of `IsContextFree` under intersection with regular languages

The intersection of a context-free language `L` with a regular language `R` is
context-free. Headline theorem in [hopcroft-motwani-ullman-2000]
Theorem 7.27 (p. 286); originally proved in [bar-hillel-perles-shamir-1961].

Two textbook constructions exist for this theorem:

1. **PDA-product** (HMU 2000 §7.3.4): take a PDA `P` for `L` and a DFA `A` for
   `R`, build a single PDA `P'` with state set `Q_P × Q_A` running them in
   lockstep. Cleaner and shorter than (2), but requires PDA infrastructure
   (PDA type + bidirectional CFG↔PDA equivalence) which mathlib does not
   currently have.

2. **Grammar-level Bar-Hillel triple-product** (BPS 1961, the original):
   build a new CFG `G'` directly from `G` and `A`, with state-pair-annotated
   nonterminals `Q × V × Q ⊕ Unit`. Heavier construction (more rules, more
   bookkeeping) but reachable from mathlib's `ContextFreeGrammar` substrate
   without adding PDAs. **This file mechanizes (2).** If mathlib later gains
   `Mathlib.Computability.PushdownAutomaton`, an alternate proof via (1)
   becomes available; this construction stays as the direct grammar-level
   proof.

The (2) construction:
* **Start rules**: for each accepting state `qf ∈ F`, a rule
  `inr () → [.nonterminal (.inl (q₀, S, qf))]`. The `inr ()` start symbol
  branches into "the input must drive M from `q₀` to some accepting `qf`."
* **Derivation rules**: for each `G`-rule `A → β` and each path of intermediate
  states `q₀, q₁, ..., qₖ` through the nonterminals of `β`, a rule
  `(p, A, q) → annotate β` where the annotated body tracks state transitions
  through terminals (deterministic) and nonterminals (chosen path).

Owns the `ContextFreeGrammar.product` definition and proves
`Language.IsContextFree.inter_isRegular`. Together with the parallel
homomorphism-closure proof in `Map.lean`, this dissolves the closure axioms
previously in `Closure.lean`.
-/

universe u

variable {T : Type u}

namespace ContextFreeRule

-- ============================================================================
-- Splitting lemma for Rewrites: a single-rule rewrite of `u₁ ++ u₂` happens
-- either entirely inside `u₁` or entirely inside `u₂`.
-- ============================================================================

/-- A single-rule rewrite of a concatenation `u₁ ++ u₂` happens entirely in
    `u₁` or entirely in `u₂`. The output decomposes correspondingly. -/
lemma Rewrites.append_split {N : Type*} {r : ContextFreeRule T N} :
    ∀ {u₁ u₂ v : List (Symbol T N)}, r.Rewrites (u₁ ++ u₂) v →
    (∃ v₁, v = v₁ ++ u₂ ∧ r.Rewrites u₁ v₁) ∨
    (∃ v₂, v = u₁ ++ v₂ ∧ r.Rewrites u₂ v₂) := by
  intro u₁ u₂ v hrw
  induction u₁ generalizing v with
  | nil =>
    right
    exact ⟨v, by simp, by simpa using hrw⟩
  | cons head u₁_tail ih =>
    rw [List.cons_append] at hrw
    cases hrw with
    | head s =>
      -- head = .nonterminal r.input, u₁_tail ++ u₂ = s, v = r.output ++ s.
      left
      refine ⟨r.output ++ u₁_tail, ?_, .head u₁_tail⟩
      simp [List.append_assoc]
    | cons x hrw_rest =>
      -- v = head :: v_rest, hrw_rest : r.Rewrites (u₁_tail ++ u₂) v_rest.
      cases ih hrw_rest with
      | inl h =>
        obtain ⟨v₁, hv_eq, hrw₁⟩ := h
        left
        refine ⟨head :: v₁, ?_, .cons head hrw₁⟩
        simp [hv_eq]
      | inr h =>
        obtain ⟨v₂, hv_eq, hrw₂⟩ := h
        right
        refine ⟨v₂, ?_, hrw₂⟩
        simp [hv_eq]

end ContextFreeRule

namespace ContextFreeGrammar

/-- A single-step rewrite of `s₁ ++ s₂` happens entirely in `s₁` or entirely in
    `s₂`. -/
lemma Produces.append_split {G : ContextFreeGrammar T}
    {s₁ s₂ v : List (Symbol T G.NT)} (hp : G.Produces (s₁ ++ s₂) v) :
    (∃ t₁, v = t₁ ++ s₂ ∧ G.Produces s₁ t₁) ∨
    (∃ t₂, v = s₁ ++ t₂ ∧ G.Produces s₂ t₂) := by
  obtain ⟨r, hr_mem, hrw⟩ := hp
  cases hrw.append_split with
  | inl h =>
    obtain ⟨v₁, hv_eq, hrw₁⟩ := h
    exact .inl ⟨v₁, hv_eq, ⟨r, hr_mem, hrw₁⟩⟩
  | inr h =>
    obtain ⟨v₂, hv_eq, hrw₂⟩ := h
    exact .inr ⟨v₂, hv_eq, ⟨r, hr_mem, hrw₂⟩⟩

/-- **Splitting lemma for derivations.** A derivation `s₁ ++ s₂ ⇒* t` decomposes
    into per-side derivations: `s₁ ⇒* t₁`, `s₂ ⇒* t₂`, with `t = t₁ ++ t₂`. -/
lemma Derives.append_split {G : ContextFreeGrammar T} :
    ∀ {s₁ s₂ t : List (Symbol T G.NT)}, G.Derives (s₁ ++ s₂) t →
    ∃ t₁ t₂, t = t₁ ++ t₂ ∧ G.Derives s₁ t₁ ∧ G.Derives s₂ t₂ := by
  intro s₁ s₂ t hd
  induction hd with
  | refl => exact ⟨s₁, s₂, rfl, .refl _, .refl _⟩
  | tail _ step ih =>
    obtain ⟨u₁, u₂, rfl, hd₁, hd₂⟩ := ih
    cases step.append_split with
    | inl h =>
      obtain ⟨t₁, hv_eq, hp₁⟩ := h
      exact ⟨t₁, u₂, hv_eq, hd₁.trans_produces hp₁, hd₂⟩
    | inr h =>
      obtain ⟨t₂, hv_eq, hp₂⟩ := h
      exact ⟨u₁, t₂, hv_eq, hd₁, hd₂.trans_produces hp₂⟩

end ContextFreeGrammar

-- ============================================================================
-- The Bar-Hillel construction: product of a CFG with a DFA
-- ============================================================================

open scoped Classical

namespace ContextFreeGrammar

variable {σ : Type}

/-- The product nonterminal type: state-pair-annotated G-nonterminals plus a
    fresh start symbol `inr ()`. Defined as `def` (not `abbrev`) to keep the
    type display stable through `(G.product M).NT` projections. -/
def productNT (G : ContextFreeGrammar T) (σ : Type) : Type := σ × G.NT × σ ⊕ Unit

/-- Count the number of nonterminal symbols in a list of symbols. -/
def nonterminalCount {N : Type*} (out : List (Symbol T N)) : ℕ :=
  out.countP (fun s => match s with | .nonterminal _ => true | _ => false)

/-- Annotate `out` from start state `start`, using `path` as the chosen exit
    states for nonterminals (in order). Returns the end state and annotated
    output. If `path` is too short, falls back to `start` for missing exit
    states (those configurations don't produce well-formed Bar-Hillel rules and
    are filtered out by the rule-generation enumeration). -/
def annotateOutput {G : ContextFreeGrammar T} (M : DFA T σ) :
    σ → List (Symbol T G.NT) → List σ →
    σ × List (Symbol T (productNT G σ))
  | start, [], _ => (start, [])
  | start, .terminal a :: rest, path =>
    let res := annotateOutput M (M.step start a) rest path
    (res.1, .terminal a :: res.2)
  | start, .nonterminal A :: rest, q :: path_rest =>
    let res := annotateOutput M q rest path_rest
    (res.1, .nonterminal (.inl (start, A, q)) :: res.2)
  | start, .nonterminal A :: rest, [] =>
    let res := annotateOutput M start rest []
    (res.1, .nonterminal (.inl (start, A, start)) :: res.2)

/-- The G' rule for a chosen `(start, path)` of state choices applied to a
    G-rule `r`. -/
def generatedRule {G : ContextFreeGrammar T} (M : DFA T σ) (r : ContextFreeRule T G.NT)
    (start : σ) (path : List σ) : ContextFreeRule T (productNT G σ) :=
  let res := annotateOutput M start r.output path
  { input := .inl (start, r.input, res.1), output := res.2 }

/-- All G' rules generated from a single G-rule. Enumerates over all
    `(start, path)` with `path` a list of length `nonterminalCount r.output`. -/
noncomputable def rulesFromRule {G : ContextFreeGrammar T} (M : DFA T σ)
    [Fintype σ] [DecidableEq σ] (r : ContextFreeRule T G.NT) :
    Finset (ContextFreeRule T (productNT G σ)) :=
  (Finset.univ : Finset (σ × (Fin (nonterminalCount r.output) → σ))).image fun sp =>
    generatedRule M r sp.1 (List.ofFn sp.2)

/-- The start rules: for each accepting state `qf`, branch the start symbol
    `.inr ()` into `[.nonterminal (.inl (M.start, G.initial, qf))]`. -/
noncomputable def startRules (M : DFA T σ) [Fintype σ] (G : ContextFreeGrammar T) :
    Finset (ContextFreeRule T (productNT G σ)) :=
  ((Finset.univ : Finset σ).filter (· ∈ M.accept)).image fun qf =>
    { input := .inr (),
      output := [.nonterminal (.inl (M.start, G.initial, qf))] }

/-- The Bar-Hillel triple-product CFG: generates `G.language ∩ M.accepts`. -/
noncomputable def product [Fintype σ] [DecidableEq σ]
    (G : ContextFreeGrammar T) (M : DFA T σ) :
    ContextFreeGrammar T where
  NT := productNT G σ
  initial := .inr ()
  rules := startRules M G ∪ G.rules.biUnion (rulesFromRule M)

end ContextFreeGrammar

-- ============================================================================
-- Projects: G' symbol-list projects to G symbol-list.
-- Used in the forward direction to recover the underlying G-derivation.
-- ============================================================================

/-- A G' symbol-list `s'` projects to a G symbol-list `s` if every `.terminal`
    matches and every `.nonterminal (.inl (_, A, _))` projects to
    `.nonterminal A`. The constructor doesn't allow `.nonterminal (.inr ())`,
    enforcing that projection is only defined for "post-start" sentential
    forms. -/
inductive Projects {G : ContextFreeGrammar T} {σ : Type} :
    List (Symbol T (ContextFreeGrammar.productNT G σ)) →
    List (Symbol T G.NT) → Prop
  | nil : Projects [] []
  | terminal {a : T} {rest : List _} {rest' : List _} (h : Projects rest rest') :
      Projects (.terminal a :: rest) (.terminal a :: rest')
  | nonterminal {p : σ} {A : G.NT} {q : σ} {rest : List _} {rest' : List _}
      (h : Projects rest rest') :
      Projects (.nonterminal (.inl (p, A, q)) :: rest) (.nonterminal A :: rest')

namespace Projects

variable {G : ContextFreeGrammar T} {σ : Type}

/-- Projection respects concatenation. -/
lemma append {s'₁ s'₂ : List (Symbol T (ContextFreeGrammar.productNT G σ))}
    {s₁ s₂ : List (Symbol T G.NT)}
    (h₁ : Projects s'₁ s₁) (h₂ : Projects s'₂ s₂) :
    Projects (s'₁ ++ s'₂) (s₁ ++ s₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | terminal _ ih => exact .terminal ih
  | nonterminal _ ih => exact .nonterminal ih

/-- A projection of `s'` to a concatenation `s₁ ++ s₂` decomposes accordingly. -/
lemma split_right {s' : List (Symbol T (ContextFreeGrammar.productNT G σ))}
    {s₁ s₂ : List (Symbol T G.NT)} (h : Projects s' (s₁ ++ s₂)) :
    ∃ s'₁ s'₂, s' = s'₁ ++ s'₂ ∧ Projects s'₁ s₁ ∧ Projects s'₂ s₂ := by
  induction s₁ generalizing s' with
  | nil => exact ⟨[], s', by simp, .nil, by simpa using h⟩
  | cons head s₁_rest ih =>
    rw [List.cons_append] at h
    cases h with
    | @terminal a rest rest' h_rest =>
      obtain ⟨s'₁, s'₂, hs'_eq, hp₁, hp₂⟩ := ih h_rest
      refine ⟨.terminal a :: s'₁, s'₂, ?_, .terminal hp₁, hp₂⟩
      simp [hs'_eq]
    | @nonterminal p A q rest rest' h_rest =>
      obtain ⟨s'₁, s'₂, hs'_eq, hp₁, hp₂⟩ := ih h_rest
      refine ⟨.nonterminal (.inl (p, A, q)) :: s'₁, s'₂, ?_, .nonterminal hp₁, hp₂⟩
      simp [hs'_eq]

/-- A projection from a concatenation `s'₁ ++ s'₂` to `s` decomposes the target
    correspondingly. -/
lemma split_left {s : List (Symbol T G.NT)}
    {s'₁ s'₂ : List (Symbol T (ContextFreeGrammar.productNT G σ))}
    (h : Projects (s'₁ ++ s'₂) s) :
    ∃ s₁ s₂, s = s₁ ++ s₂ ∧ Projects s'₁ s₁ ∧ Projects s'₂ s₂ := by
  induction s'₁ generalizing s with
  | nil =>
    refine ⟨[], s, by simp, .nil, ?_⟩
    simpa using h
  | cons head s'₁_rest ih =>
    rw [List.cons_append] at h
    cases h with
    | @terminal a rest rest' h_rest =>
      obtain ⟨s₁, s₂, hs_eq, hp₁, hp₂⟩ := ih h_rest
      refine ⟨.terminal a :: s₁, s₂, ?_, .terminal hp₁, hp₂⟩
      simp [hs_eq]
    | @nonterminal p A q rest rest' h_rest =>
      obtain ⟨s₁, s₂, hs_eq, hp₁, hp₂⟩ := ih h_rest
      refine ⟨.nonterminal A :: s₁, s₂, ?_, .nonterminal hp₁, hp₂⟩
      simp [hs_eq]

/-- The projection of a list of terminals (G'-side) to the same list of terminals (G-side). -/
lemma map_terminal (w : List T) :
    Projects (w.map (Symbol.terminal (N := ContextFreeGrammar.productNT G σ)))
             (w.map (Symbol.terminal (N := G.NT))) := by
  induction w with
  | nil => exact .nil
  | cons a w' ih => exact .terminal ih

/-- If `s'` projects to `w.map .terminal`, then `s'` is itself a list of
    terminals (matching `w`). -/
lemma eq_map_terminal_of_projects {s' : List (Symbol T (ContextFreeGrammar.productNT G σ))}
    {w : List T} (h : Projects s' (w.map .terminal)) :
    s' = w.map .terminal := by
  induction w generalizing s' with
  | nil =>
    cases h
    rfl
  | cons a w' ih =>
    rw [List.map_cons] at h
    cases h with
    | terminal h_rest =>
      rw [List.map_cons]
      simp [ih h_rest]

end Projects

-- ============================================================================
-- Consistent: a G' symbol-list traces a DFA path from `p` to `q`.
-- ============================================================================

/-- A G' symbol-list is `Consistent M p s' q` if walking through it from state
    `p` (advancing via `M.step` for terminals, jumping via the nonterminal's
    annotated state pair) ends at state `q`. -/
inductive Consistent {G : ContextFreeGrammar T} {σ : Type} (M : DFA T σ) :
    σ → List (Symbol T (ContextFreeGrammar.productNT G σ)) → σ → Prop
  | nil (p : σ) : Consistent M p [] p
  | terminal {p q : σ} (a : T) {rest : List _}
      (h : Consistent M (M.step p a) rest q) :
      Consistent M p (.terminal a :: rest) q
  | nonterminal {p p' q : σ} (A : G.NT) {rest : List _}
      (h : Consistent M p' rest q) :
      Consistent M p (.nonterminal (.inl (p, A, p')) :: rest) q

namespace Consistent

variable {G : ContextFreeGrammar T} {σ : Type} {M : DFA T σ}

/-- Consistency composes along concatenation. -/
lemma append {p q r : σ}
    {s'₁ s'₂ : List (Symbol T (ContextFreeGrammar.productNT G σ))}
    (h₁ : Consistent M p s'₁ q) (h₂ : Consistent M q s'₂ r) :
    Consistent M p (s'₁ ++ s'₂) r := by
  induction h₁ with
  | nil _ => simpa using h₂
  | terminal a _ ih => exact .terminal a (ih h₂)
  | nonterminal A _ ih => exact .nonterminal A (ih h₂)

/-- Consistency splits along concatenation. -/
lemma split {p r : σ}
    {s'₁ s'₂ : List (Symbol T (ContextFreeGrammar.productNT G σ))}
    (h : Consistent M p (s'₁ ++ s'₂) r) :
    ∃ q, Consistent M p s'₁ q ∧ Consistent M q s'₂ r := by
  induction s'₁ generalizing p with
  | nil => exact ⟨p, .nil p, by simpa using h⟩
  | cons head s'₁_rest ih =>
    rw [List.cons_append] at h
    cases h with
    | terminal a h_rest =>
      obtain ⟨q, h₁, h₂⟩ := ih h_rest
      exact ⟨q, .terminal a h₁, h₂⟩
    | nonterminal A h_rest =>
      obtain ⟨q, h₁, h₂⟩ := ih h_rest
      exact ⟨q, .nonterminal A h₁, h₂⟩

/-- A list of terminals is consistent from `p` to `M.evalFrom p w`. -/
lemma map_terminal (p : σ) (w : List T) :
    Consistent (G := G) M p (w.map .terminal) (M.evalFrom p w) := by
  induction w generalizing p with
  | nil => exact .nil p
  | cons a w' ih =>
    rw [List.map_cons, DFA.evalFrom_cons]
    exact .terminal a (ih (M.step p a))

/-- If a list of terminals is consistent from `p` to `q`, then `q = M.evalFrom p w`. -/
lemma eval_of_terminal {p q : σ} {w : List T}
    (h : Consistent (G := G) M p (w.map .terminal) q) :
    q = M.evalFrom p w := by
  induction w generalizing p with
  | nil => cases h; rfl
  | cons a w' ih =>
    rw [List.map_cons] at h
    cases h with
    | terminal _ h_rest =>
      rw [DFA.evalFrom_cons]
      exact ih h_rest

end Consistent

-- ============================================================================
-- Properties of annotateOutput and generatedRule
-- ============================================================================

namespace ContextFreeGrammar

variable {G : ContextFreeGrammar T} {σ : Type} {M : DFA T σ}

/-- The annotated output projects back to the original output. -/
lemma annotateOutput_projects (start : σ) (out : List (Symbol T G.NT)) (path : List σ) :
    Projects (annotateOutput M start out path).2 out := by
  induction out generalizing start path with
  | nil => exact .nil
  | cons head rest ih =>
    cases head with
    | terminal a =>
      simp [annotateOutput]
      exact .terminal (ih (M.step start a) path)
    | nonterminal A =>
      cases path with
      | nil =>
        simp [annotateOutput]
        exact .nonterminal (ih start [])
      | cons q path_rest =>
        simp [annotateOutput]
        exact .nonterminal (ih q path_rest)

/-- The annotated output is consistent from the start state to the returned end
    state. -/
lemma annotateOutput_consistent (start : σ) (out : List (Symbol T G.NT))
    (path : List σ) :
    Consistent (G := G) M start (annotateOutput M start out path).2
                                (annotateOutput M start out path).1 := by
  induction out generalizing start path with
  | nil => exact .nil _
  | cons head rest ih =>
    cases head with
    | terminal a =>
      simp [annotateOutput]
      exact .terminal a (ih (M.step start a) path)
    | nonterminal A =>
      cases path with
      | nil =>
        simp [annotateOutput]
        exact .nonterminal A (ih start [])
      | cons q path_rest =>
        simp [annotateOutput]
        exact .nonterminal A (ih q path_rest)

/-- A generated rule has the expected input shape. -/
@[simp] lemma generatedRule_input (r : ContextFreeRule T G.NT) (start : σ)
    (path : List σ) :
    (generatedRule M r start path).input =
      .inl (start, r.input, (annotateOutput M start r.output path).1) := rfl

/-- A generated rule has the expected output shape. -/
@[simp] lemma generatedRule_output (r : ContextFreeRule T G.NT) (start : σ)
    (path : List σ) :
    (generatedRule M r start path).output =
      (annotateOutput M start r.output path).2 := rfl

/-- Membership in `startRules`: every start rule is parametrized by some
    `qf ∈ M.accept`. -/
lemma mem_startRules [Fintype σ] {r : ContextFreeRule T (productNT G σ)} :
    r ∈ startRules M G ↔
      ∃ qf : σ, qf ∈ M.accept ∧
      r = { input := .inr (),
            output := [.nonterminal (.inl (M.start, G.initial, qf))] } := by
  simp only [startRules, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨qf, hqf, rfl⟩; exact ⟨qf, hqf, rfl⟩
  · rintro ⟨qf, hqf, rfl⟩; exact ⟨qf, hqf, rfl⟩

/-- Membership in `rulesFromRule`: every derivation rule is parametrized by
    some `(start, path)` choice. -/
lemma mem_rulesFromRule [Fintype σ] [DecidableEq σ]
    {r : ContextFreeRule T G.NT} {r' : ContextFreeRule T (productNT G σ)} :
    r' ∈ rulesFromRule M r ↔
      ∃ (start : σ) (path_fn : Fin (nonterminalCount r.output) → σ),
      r' = generatedRule M r start (List.ofFn path_fn) := by
  simp only [rulesFromRule, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨start, path_fn⟩, h⟩; exact ⟨start, path_fn, h.symm⟩
  · rintro ⟨start, path_fn, rfl⟩; exact ⟨⟨start, path_fn⟩, rfl⟩

end ContextFreeGrammar

namespace Projects

variable {G : ContextFreeGrammar T} {σ : Type}

/-- A projected G' symbol-list contains no `.nonterminal (.inr _)` symbols. -/
lemma not_inr_mem {s' : List (Symbol T (ContextFreeGrammar.productNT G σ))}
    {s : List (Symbol T G.NT)} (h : Projects s' s) (u : Unit) :
    Symbol.nonterminal (.inr u) ∉ s' := by
  induction h with
  | nil => intro hmem; exact List.not_mem_nil hmem
  | terminal _ ih =>
    intro hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · cases heq
    · exact ih hmem'
  | nonterminal _ ih =>
    intro hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · injection heq with hsym
      cases hsym
    · exact ih hmem'

/-- A G' symbol-list projecting to a singleton G-nonterminal is itself a
    singleton (with appropriate state annotation). -/
lemma singleton_nonterminal {s' : List (Symbol T (ContextFreeGrammar.productNT G σ))}
    {A : G.NT} (h : Projects s' [.nonterminal A]) :
    ∃ p q : σ, s' = [.nonterminal (.inl (p, A, q))] := by
  cases h with
  | nonterminal h_rest =>
    cases h_rest
    refine ⟨_, _, rfl⟩

/-- The dual: a singleton .nonterminal (.inl ...) on the left projects to
    the corresponding .nonterminal A. -/
lemma of_singleton_nonterminal {p q : σ} {A : G.NT} {s : List (Symbol T G.NT)}
    (h : Projects [.nonterminal (.inl (p, A, q))] s) :
    s = [.nonterminal A] := by
  cases h with
  | nonterminal h_rest =>
    cases h_rest
    rfl

/-- If a list of terminals on the left projects to `s`, then `s` is the same
    list of terminals on the G side. -/
lemma eq_of_map_terminal_left {w : List T} {s : List (Symbol T G.NT)}
    (h : Projects (w.map (Symbol.terminal (N := ContextFreeGrammar.productNT G σ))) s) :
    s = w.map .terminal := by
  induction w generalizing s with
  | nil => cases h; rfl
  | cons a w' ih =>
    rw [List.map_cons] at h
    cases h with
    | terminal h_rest =>
      rw [List.map_cons, ih h_rest]

end Projects

-- ============================================================================
-- Forward direction: G' language ⊆ G ⊓ M
-- ============================================================================

namespace ContextFreeGrammar

variable {G : ContextFreeGrammar T} {σ : Type} [Fintype σ] [DecidableEq σ] {M : DFA T σ}

/-- One step of the G' Produces relation lifts to a one-step G Produces, given
    a Projects + Consistent annotation of the source. The target inherits the
    annotation. -/
lemma product_produces_lift {s' t' : List (Symbol T (productNT G σ))}
    {s : List (Symbol T G.NT)} {p q : σ}
    (step : (G.product M).Produces s' t')
    (hp : Projects s' s) (hc : Consistent M p s' q) :
    ∃ t, G.Produces s t ∧ Projects t' t ∧ Consistent M p t' q := by
  obtain ⟨r', hr'_mem, hrw⟩ := step
  -- Type-coerce r' so we work consistently in the productNT type.
  let r'' : ContextFreeRule T (productNT G σ) := r'
  have hrw'' : r''.Rewrites s' t' := hrw
  have hr''_mem : r'' ∈ startRules M G ∪ G.rules.biUnion (rulesFromRule M) := hr'_mem
  rw [Finset.mem_union, Finset.mem_biUnion] at hr''_mem
  rcases hr''_mem with h_start | ⟨r, hr_mem, h_in_rules⟩
  · -- Start rule case: contradiction with Projects (no .inr ()).
    rw [mem_startRules] at h_start
    obtain ⟨qf, _hqf, hr''_eq⟩ := h_start
    exfalso
    have h_input : r''.input = .inr () := by rw [hr''_eq]
    have hmem : Symbol.nonterminal r''.input ∈ s' := hrw''.nonterminal_input_mem
    rw [h_input] at hmem
    exact hp.not_inr_mem () hmem
  · -- Derivation rule case.
    rw [mem_rulesFromRule] at h_in_rules
    obtain ⟨start, path_fn, hr''_eq⟩ := h_in_rules
    set path := List.ofFn path_fn with hpath_def
    set ann := (annotateOutput M start r.output path).2 with hann_def
    set end_st := (annotateOutput M start r.output path).1 with hend_def
    have hr_input : r''.input = .inl (start, r.input, end_st) := by
      rw [hr''_eq]; rfl
    have hr_output : r''.output = ann := by
      rw [hr''_eq]; rfl
    obtain ⟨pre, post, hs'_eq, ht'_eq⟩ := hrw''.exists_parts
    -- hs'_eq : s' = pre ++ [.nonterminal r''.input] ++ post
    -- ht'_eq : t' = pre ++ r''.output ++ post
    -- Substitute r''.input and r''.output.
    rw [hr_input] at hs'_eq
    rw [hr_output] at ht'_eq
    -- Decompose Projects via the source split.
    rw [hs'_eq] at hp
    obtain ⟨pre_mid_g, post_g, hs_eq, hp_pre_mid, hp_post⟩ := Projects.split_left hp
    obtain ⟨pre_g, mid_g, hpre_mid_eq, hp_pre, hp_mid⟩ := Projects.split_left hp_pre_mid
    have hmid_eq := hp_mid.of_singleton_nonterminal
    -- Decompose Consistent. The list is (pre ++ [.nonterminal ...]) ++ post
    -- (left-assoc), so the first split separates that, the second splits pre vs middle.
    rw [hs'_eq] at hc
    obtain ⟨p'', hc_pre_mid, hc_post⟩ := hc.split
    obtain ⟨p', hc_pre, hc_mid⟩ := hc_pre_mid.split
    cases hc_mid with
    | @nonterminal _ _ _ A _ h_inner =>
      cases h_inner
      refine ⟨pre_g ++ r.output ++ post_g, ?_, ?_, ?_⟩
      · refine ⟨r, hr_mem, ?_⟩
        rw [hs_eq, hpre_mid_eq, hmid_eq]
        exact ContextFreeRule.rewrites_of_exists_parts r pre_g post_g
      · rw [ht'_eq]
        refine (hp_pre.append (?_ : Projects ann r.output)).append hp_post
        exact annotateOutput_projects start r.output path
      · rw [ht'_eq, List.append_assoc]
        refine hc_pre.append (?_ : Consistent M start (ann ++ post) q)
        refine (annotateOutput_consistent start r.output path).append ?_
        exact hc_post

/-- Multi-step lift: given Projects + Consistent annotation, lift any G'
    derivation to a G derivation, preserving annotations. -/
lemma product_derives_lift {s' t' : List (Symbol T (productNT G σ))}
    (hd : (G.product M).Derives s' t') {s : List (Symbol T G.NT)} {p q : σ}
    (hp : Projects s' s) (hc : Consistent M p s' q) :
    ∃ t, G.Derives s t ∧ Projects t' t ∧ Consistent M p t' q := by
  induction hd with
  | refl => exact ⟨s, .refl _, hp, hc⟩
  | tail _ step ih =>
    obtain ⟨t_mid, hd_mid, hp_mid, hc_mid⟩ := ih
    obtain ⟨t, hp_step, hp_t, hc_t⟩ :=
      product_produces_lift step hp_mid hc_mid
    exact ⟨t, hd_mid.trans_produces hp_step, hp_t, hc_t⟩

/-- **Forward inclusion** (Bar-Hillel): every word generated by `G.product M`
    is in `G.language ⊓ M.accepts`. -/
theorem product_language_le (G : ContextFreeGrammar T) (M : DFA T σ) :
    (G.product M).language ≤ G.language ⊓ M.accepts := by
  intro w hw
  -- hw : (G.product M).Derives [.nonterminal (.inr ())] (w.map .terminal)
  show w ∈ G.language ∧ w ∈ M.accepts
  -- The first step must apply a start rule.
  rcases hw.eq_or_head with heq | ⟨v, hstep, hrest⟩
  · -- refl: [.nonterminal (.inr ())] = w.map .terminal — impossible.
    exfalso
    cases w with
    | nil => simp [show ((G.product M).initial : productNT G σ) = .inr () from rfl] at heq
    | cons a w' => simp at heq
  · -- The first step is a Produces.
    obtain ⟨r', hr'_mem, hrw⟩ := hstep
    -- (G.product M).rules definitionally equals startRules ∪ G.rules.biUnion rulesFromRule.
    -- Explicit retyping is needed because r' has type ContextFreeRule T (G.product M).NT
    -- but (productNT G σ) is the projected element type of the union.
    let r'' : ContextFreeRule T (productNT G σ) := r'
    have hr'_mem' : r'' ∈ startRules M G ∪ G.rules.biUnion (rulesFromRule M) := hr'_mem
    rw [Finset.mem_union, Finset.mem_biUnion] at hr'_mem'
    rcases hr'_mem' with h_start | ⟨r, hr_mem, h_in_rules⟩
    · -- Start rule case (the expected branch).
      rw [mem_startRules] at h_start
      obtain ⟨qf, hqf, rfl⟩ := h_start
      -- The rewrite turns [.nonterminal (.inr ())] into [.nonterminal (.inl (M.start, G.initial, qf))].
      -- After: v = [.nonterminal (.inl (M.start, G.initial, qf))].
      have hv_eq : v = [.nonterminal (.inl (M.start, G.initial, qf))] := by
        obtain ⟨pre, post, hs_eq, ht_eq⟩ := hrw.exists_parts
        -- pre ++ [.nonterminal r'.input] ++ post = [.nonterminal (G.product M).initial]
        -- Both sides equal [.nonterminal (.inr ())]; this forces pre = post = [].
        have hlen := congr_arg List.length hs_eq
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        have hpre : pre = [] := List.length_eq_zero_iff.mp (by omega)
        have hpost : post = [] := List.length_eq_zero_iff.mp (by omega)
        rw [hpre, hpost, List.nil_append, List.append_nil] at ht_eq
        exact ht_eq
      subst hv_eq
      -- Now apply product_derives_lift on the rest.
      have hp : Projects (G := G) (σ := σ)
                  [.nonterminal (.inl (M.start, G.initial, qf))]
                  [.nonterminal G.initial] := by
        exact .nonterminal .nil
      have hc : Consistent (G := G) M M.start
                  [.nonterminal (.inl (M.start, G.initial, qf))] qf := by
        exact .nonterminal _ (.nil _)
      obtain ⟨t, hG_d, hp_t, hc_t⟩ := product_derives_lift hrest hp hc
      have ht_eq : t = w.map .terminal := hp_t.eq_of_map_terminal_left
      refine ⟨?_, ?_⟩
      · -- w ∈ G.language: G.Derives [.nonterminal G.initial] (w.map .terminal).
        show G.Derives [.nonterminal G.initial] (w.map .terminal)
        rw [← ht_eq]; exact hG_d
      · -- w ∈ M.accepts: M.eval w ∈ M.accept.
        show M.eval w ∈ M.accept
        have : qf = M.evalFrom M.start w := hc_t.eval_of_terminal
        rw [DFA.eval, ← this]; exact hqf
    · -- Derivation rule case: contradiction (start step must rewrite .inr ()).
      exfalso
      rw [mem_rulesFromRule] at h_in_rules
      obtain ⟨start, path_fn, hr''_eq⟩ := h_in_rules
      have hr_input : r''.input = .inl (start, r.input,
          (annotateOutput M start r.output (List.ofFn path_fn)).1) := by
        rw [hr''_eq]; rfl
      have hrw'' : r''.Rewrites [.nonterminal (.inr ())] v := by
        show r''.Rewrites _ _
        change r''.Rewrites [.nonterminal (G.product M).initial] v
        exact hrw
      have hmem : Symbol.nonterminal r''.input ∈
          ([.nonterminal (.inr ())] : List (Symbol T (productNT G σ))) :=
        hrw''.nonterminal_input_mem
      rw [hr_input] at hmem
      simp only [List.mem_singleton, Symbol.nonterminal.injEq] at hmem
      cases hmem

end ContextFreeGrammar

-- ============================================================================
-- Backward direction: G ⊓ M ⊆ G' language
-- ============================================================================

namespace ContextFreeGrammar

-- Lemmas in this section don't need finiteness on σ; introduce Fintype/DecidableEq
-- below, after the path-extraction substrate.
variable {G : ContextFreeGrammar T} {σ : Type} {M : DFA T σ}

/-- Extract the list of nonterminal "exit states" from a G' symbol-list, in
    order. Used to invert `annotateOutput` — given a consistent annotation,
    the path of exit-state choices is recoverable. -/
private def extractPath : List (Symbol T (productNT G σ)) → List σ
  | [] => []
  | .terminal _ :: rest => extractPath rest
  | .nonterminal (.inl (_, _, q)) :: rest => q :: extractPath rest
  | .nonterminal (.inr _) :: rest => extractPath rest

private lemma extractPath_length_of_projects {β' : List (Symbol T (productNT G σ))}
    {out : List (Symbol T G.NT)} (hp : Projects β' out) :
    (extractPath β').length = nonterminalCount out := by
  induction hp with
  | nil => rfl
  | terminal h ih =>
    simp only [extractPath, nonterminalCount, List.countP_cons]
    rw [ih]
    simp [nonterminalCount]
  | nonterminal h ih =>
    simp only [extractPath, List.length_cons, nonterminalCount,
               List.countP_cons]
    rw [ih]
    simp [nonterminalCount]

/-- Reconstruction lemma: given a `Projects + Consistent` annotation `β'` of
    `out`, walking `annotateOutput` along the extracted path recovers `β'` and
    the end state. -/
private lemma annotateOutput_reconstruct
    {p q : σ} {out : List (Symbol T G.NT)}
    {β' : List (Symbol T (productNT G σ))}
    (hp : Projects β' out) (hc : Consistent M p β' q) :
    annotateOutput M p out (extractPath β') = (q, β') := by
  induction hp generalizing p with
  | nil =>
    cases hc
    rfl
  | @terminal a rest rest' h ih =>
    cases hc with
    | terminal _ hc' =>
      simp only [extractPath, annotateOutput]
      rw [ih hc']
  | @nonterminal p₀ A q₀ rest rest' h ih =>
    cases hc with
    | @nonterminal p p' q' A _ hc' =>
      simp only [extractPath, annotateOutput]
      rw [ih hc']

/-- Any consistent annotation corresponds to an `(start, path_fn)` choice in
    the rule-generation enumeration. -/
private lemma exists_path_fn_of_consistent {r : ContextFreeRule T G.NT}
    {p q : σ} {β' : List (Symbol T (productNT G σ))}
    (hp : Projects β' r.output) (hc : Consistent M p β' q) :
    ∃ path_fn : Fin (nonterminalCount r.output) → σ,
      generatedRule M r p (List.ofFn path_fn) =
        { input := .inl (p, r.input, q), output := β' } := by
  have hlen : (extractPath β').length = nonterminalCount r.output :=
    extractPath_length_of_projects hp
  refine ⟨fun i => (extractPath β').get (i.cast hlen.symm), ?_⟩
  have h_ofFn : List.ofFn (fun i : Fin (nonterminalCount r.output) =>
      (extractPath β').get (i.cast hlen.symm)) = extractPath β' := by
    apply List.ext_get
    · simp only [List.length_ofFn, hlen]
    · intro i hi₁ hi₂
      simp only [List.get_ofFn, Fin.cast_mk]
  rw [h_ofFn]
  unfold generatedRule
  rw [annotateOutput_reconstruct hp hc]

-- From here on, finiteness on σ is needed for `Finset.mem_*` and the rule-set
-- membership proofs.
variable [Fintype σ] [DecidableEq σ]

/-- The G' rule corresponding to any consistent annotation of a G-rule's body
    is in `(G.product M).rules`. -/
lemma mem_rules_of_consistent {r : ContextFreeRule T G.NT}
    (hr_mem : r ∈ G.rules) {p q : σ} {β' : List (Symbol T (productNT G σ))}
    (hp : Projects β' r.output) (hc : Consistent M p β' q) :
    ({ input := .inl (p, r.input, q), output := β' } :
        ContextFreeRule T (productNT G σ)) ∈
      (G.product M).rules := by
  show _ ∈ (startRules M G ∪ G.rules.biUnion (rulesFromRule M))
  rw [Finset.mem_union]
  right
  rw [Finset.mem_biUnion]
  refine ⟨r, hr_mem, ?_⟩
  rw [mem_rulesFromRule]
  obtain ⟨path_fn, h_eq⟩ := exists_path_fn_of_consistent hp hc
  exact ⟨p, path_fn, h_eq.symm⟩

/-- The start rule for an accepting state `qf` is in `(G.product M).rules`. -/
lemma start_rule_mem (G : ContextFreeGrammar T) (M : DFA T σ) {qf : σ}
    (hqf : qf ∈ M.accept) :
    ({ input := .inr (),
       output := [.nonterminal (.inl (M.start, G.initial, qf))] } :
        ContextFreeRule T (productNT G σ)) ∈
      (G.product M).rules := by
  show _ ∈ (startRules M G ∪ G.rules.biUnion (rulesFromRule M))
  rw [Finset.mem_union]
  left
  rw [mem_startRules]
  exact ⟨qf, hqf, rfl⟩

-- ============================================================================
-- Backward main lemma: lift any G derivation to G' via head induction.
-- ============================================================================
-- (Same `namespace ContextFreeGrammar` continues from above — no re-opening.)

/-- **Annotation-existence lemma** (the heart of the backward direction).
    For any G derivation of `s` to `(w.map .terminal)`, and any starting
    DFA state `p`, there exists a Projects+Consistent annotation `s'` of `s`
    such that `(G.product M).Derives s' (w.map .terminal)`.

    Proved by `head_induction_on` on the G derivation: the refl case takes
    `s' = w.map .terminal`; the head case constructs the annotation by
    extracting a Projects+Consistent decomposition of the IH's annotation
    of `mid` (the post-step sentential form), then applies the corresponding
    G' rule (which exists by `mem_rules_of_consistent`). -/
lemma exists_annotation_of_derives {s : List (Symbol T G.NT)} {w : List T}
    (h_drv : G.Derives s (w.map .terminal)) (p : σ) :
    ∃ s' : List (Symbol T (productNT G σ)),
      Projects s' s ∧ Consistent M p s' (M.evalFrom p w) ∧
      (G.product M).Derives s' (w.map .terminal) := by
  induction h_drv using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- s = w.map .terminal. Take s' to be the same list at the productNT level.
    refine ⟨w.map .terminal, Projects.map_terminal w, Consistent.map_terminal p w, ?_⟩
    exact .refl _
  | @head s mid step rest ih =>
    -- step : G.Produces s mid; rest : G.Derives mid (w.map .terminal); ih : ∃ ann of mid.
    obtain ⟨mid', hp_mid, hc_mid, hd_mid⟩ := ih
    -- The step rewrites s to mid via some rule r ∈ G.rules.
    obtain ⟨r, hr_mem, hrw⟩ := step
    obtain ⟨pre, post, hs_eq, hmid_eq⟩ := hrw.exists_parts
    -- mid = pre ++ r.output ++ post.
    rw [hmid_eq] at hp_mid
    -- Decompose mid' along this 3-way concat (parsed as (pre ++ r.output) ++ post).
    obtain ⟨pre_ann, post', hmid'_eq, hp_pre_ann, hp_post⟩ := Projects.split_right hp_mid
    obtain ⟨pre', ann_r_output, hpre_ann_eq, hp_pre, hp_ann⟩ := Projects.split_right hp_pre_ann
    -- Decompose Consistent the same way: rewrite hc_mid using mid' decomposition.
    rw [hmid'_eq, hpre_ann_eq] at hc_mid
    obtain ⟨p_right, hc_pre_ann, hc_post⟩ := hc_mid.split
    obtain ⟨p_left, hc_pre, hc_ann⟩ := hc_pre_ann.split
    -- Construct s' = pre' ++ [.nonterminal (.inl (p_left, r.input, p_right))] ++ post'.
    refine ⟨pre' ++ [.nonterminal (.inl (p_left, r.input, p_right))] ++ post', ?_, ?_, ?_⟩
    · -- Projects s' s.
      rw [hs_eq]
      exact (hp_pre.append (.nonterminal .nil)).append hp_post
    · -- Consistent M p s' (M.evalFrom p w).
      exact (hc_pre.append (.nonterminal _ (.nil _))).append hc_post
    · -- (G.product M).Derives s' (w.map .terminal).
      -- Step: G' Produces s' mid' via rule {input := .inl (p_left, r.input, p_right), output := ann_r_output}.
      have h_rule_mem :
          ({ input := .inl (p_left, r.input, p_right), output := ann_r_output } :
              ContextFreeRule T (productNT G σ)) ∈ (G.product M).rules :=
        mem_rules_of_consistent hr_mem hp_ann hc_ann
      have h_rewrite : ({ input := .inl (p_left, r.input, p_right),
                          output := ann_r_output } :
              ContextFreeRule T (productNT G σ)).Rewrites
            (pre' ++ [.nonterminal (.inl (p_left, r.input, p_right))] ++ post')
            (pre' ++ ann_r_output ++ post') :=
        ContextFreeRule.rewrites_of_exists_parts _ pre' post'
      have h_step : (G.product M).Produces
            (pre' ++ [.nonterminal (.inl (p_left, r.input, p_right))] ++ post')
            (pre' ++ ann_r_output ++ post') :=
        ⟨_, h_rule_mem, h_rewrite⟩
      -- mid' = pre' ++ ann_r_output ++ post' by hmid'_eq + hpre_ann_eq.
      have h_mid' : mid' = pre' ++ ann_r_output ++ post' := by
        rw [hmid'_eq, hpre_ann_eq]
      rw [h_mid'] at hd_mid
      exact h_step.trans_derives hd_mid

/-- **Backward inclusion** (Bar-Hillel): every word in `G.language ⊓ M.accepts`
    is generated by `G.product M`. -/
theorem le_product_language (G : ContextFreeGrammar T) (M : DFA T σ) :
    G.language ⊓ M.accepts ≤ (G.product M).language := by
  rintro w ⟨hG, hM⟩
  -- hG : G.Derives [.nonterminal G.initial] (w.map .terminal)
  -- hM : M.eval w ∈ M.accept
  show (G.product M).Derives [.nonterminal (G.product M).initial] (w.map .terminal)
  -- (G.product M).initial = .inr ()
  -- Apply the start rule {input := .inr (), output := [.nonterminal (.inl (M.start, G.initial, qf))]}
  -- with qf = M.eval w.
  set qf := M.eval w with hqf_def
  have hqf : qf ∈ M.accept := hM
  -- Step 1: start rule application.
  have h_start_mem :
      ({ input := .inr (),
         output := [.nonterminal (.inl (M.start, G.initial, qf))] } :
            ContextFreeRule T (productNT G σ)) ∈ (G.product M).rules :=
    start_rule_mem G M hqf
  have h_start_rewrite :
      ({ input := .inr (),
         output := [.nonterminal (.inl (M.start, G.initial, qf))] } :
            ContextFreeRule T (productNT G σ)).Rewrites
        [.nonterminal (.inr ())] [.nonterminal (.inl (M.start, G.initial, qf))] := by
    have := ContextFreeRule.rewrites_of_exists_parts
      ({ input := .inr (),
         output := [.nonterminal (.inl (M.start, G.initial, qf))] } :
            ContextFreeRule T (productNT G σ)) [] []
    simpa using this
  have h_step : (G.product M).Produces
        ([.nonterminal (.inr ())] : List (Symbol T (productNT G σ)))
        [.nonterminal (.inl (M.start, G.initial, qf))] :=
    ⟨_, h_start_mem, h_start_rewrite⟩
  -- Step 2: lift the G derivation [.nonterminal G.initial] ⇒* (w.map .terminal) to G'.
  obtain ⟨s', hp_s', hc_s', hd_s'⟩ := exists_annotation_of_derives hG M.start
  -- s' annotates [.nonterminal G.initial]; by Projects.singleton, it's a single .nonterminal.
  obtain ⟨p₀, q₀, hs'_eq⟩ := hp_s'.singleton_nonterminal
  subst hs'_eq
  -- s' = [.nonterminal (.inl (p₀, G.initial, q₀))].
  -- From Consistent: [.nonterminal (.inl (p₀, G.initial, q₀))] is consistent from M.start to M.evalFrom M.start w.
  -- This forces p₀ = M.start and q₀ = M.evalFrom M.start w = qf.
  cases hc_s' with
  | @nonterminal _ _ _ A _ h_inner =>
    cases h_inner
    -- Now p₀ = M.start, q₀ = qf (by def).
    -- hd_s' : (G.product M).Derives [.nonterminal (.inl (M.start, G.initial, qf))] (w.map .terminal).
    -- Combine: start step + derivation.
    show (G.product M).Derives [.nonterminal (.inr ())] (w.map .terminal)
    exact h_step.trans_derives hd_s'

/-- **Bar-Hillel theorem**: `(G.product M).language = G.language ⊓ M.accepts`. -/
theorem product_language (G : ContextFreeGrammar T) (M : DFA T σ) :
    (G.product M).language = G.language ⊓ M.accepts :=
  le_antisymm (product_language_le G M) (le_product_language G M)

end ContextFreeGrammar

-- ============================================================================
-- Headline: closure of `IsContextFree` under intersection with regular languages.
-- ============================================================================

namespace Language.IsContextFree

/-- **CFL closure under intersection with a regular language**
    ([bar-hillel-perles-shamir-1961]; [hopcroft-motwani-ullman-2000]
    Theorem 7.27): if `L` is context-free and `R` is regular, then `L ∩ R` is
    context-free. -/
theorem inter_isRegular {α : Type*} {L R : Language α}
    (hL : L.IsContextFree) (hR : R.IsRegular) : (L ⊓ R).IsContextFree := by
  obtain ⟨G, rfl⟩ := hL
  -- R is regular: by `Language.IsRegular`, ∃ σ : Type (Type 0), Fintype σ, M : DFA, M.accepts = R.
  obtain ⟨σ, _hFin, M, hM⟩ := hR
  classical
  refine ⟨G.product M, ?_⟩
  rw [ContextFreeGrammar.product_language, hM]

end Language.IsContextFree
