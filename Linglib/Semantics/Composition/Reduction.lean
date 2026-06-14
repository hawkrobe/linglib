import Linglib.Semantics.Composition.Model
import Linglib.Core.Logic.FirstOrder.Binders
import Linglib.Semantics.Quantification.Basic
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Tactic.FinCases

/-!
# Reduction: the FO fragment of type-driven composition

Compiles the first-order fragment of [heim-kratzer-1998] trees into mathlib
`FirstOrder.Language.Formula`s and proves agreement with the engine: whenever
`compileFO` succeeds, the denotation `Tree.interp` composes is equivalent to
mathlib `Realize` of the compiled formula over the model — the same triangle
`Semantics/Dynamic/DRS/Reduction.lean` proves for DRT.

Trace indices are the formulas' free-variable type (`ℕ`), so the Heim-Kratzer
bind index *is* the variable name, and assignment update `g[n ↦ x]` on the
engine side is literally `Function.update` on the realize side. Quantifiers
bind exactly one trace, so closure is by the *computable* singleton binders
`Formula.all₁` / `Formula.ex₁` (mathlib's `iAlls`/`iExs` are noncomputable).

## Main declarations

* `FOWords`, `Model.lexiconFO` — the logical vocabulary over a naming-map
  lexicon; `FOWords.FreshFor`, `LexNaming.Disjoint` — well-formedness
* `compileFO` — the partial compiler over QR'd Heim-Kratzer tree shapes
* `interp_compileFO`, `holdsAt_iff_realize` — the agreement theorem
* `holdsAt_of_models` — consequence transfer (cross-model entailment from
  first-order consequence)

*Most* (and the other proportional determiners) is deliberately outside the
compiled fragment: its first-order undefinability is the planned
Barwise-Cooper payoff theorem, and the principled reason `compileFO` is
partial.
-/

universe u v

namespace Semantics.Composition

open FirstOrder Language
open FirstOrder.Language.Formula (all₁ ex₁)
open Core.Logic.Intensional
open Quantification (every_sem some_sem no_sem)
open Semantics.Montague (Lexicon)
open Semantics.Composition.Tree
open Syntax (Tree)

variable {L : Language.{u, v}}

/-! ### The logical vocabulary -/

/-- Word forms for the compiled logical vocabulary, parameterizable per
fragment/language. -/
structure FOWords where
  every : String := "every"
  some_ : String := "some"
  no : String := "no"
  not_ : String := "not"
  and_ : String := "and"
  or_ : String := "or"

/-- The logical vocabulary's lexicon entries: GQ denotations from
`Quantification`, truth-functional connectives from
`Core.Logic.Intensional`. The connectives flip arguments so that
`[t₁ [and t₂]]` composes to `⟦t₁⟧ ∧ ⟦t₂⟧`. -/
def FOWords.lexicon (fw : FOWords) (E W : Type) : Lexicon E W := fun s =>
  if s = fw.every then some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, every_sem⟩
  else if s = fw.some_ then some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, some_sem⟩
  else if s = fw.no then some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, no_sem⟩
  else if s = fw.not_ then some ⟨.t ⇒ .t, neg⟩
  else if s = fw.and_ then some ⟨.t ⇒ .t ⇒ .t, fun q p => conj p q⟩
  else if s = fw.or_ then some ⟨.t ⇒ .t ⇒ .t, fun q p => disj p q⟩
  else none

/-- A naming-map lexicon extended with the logical vocabulary. Content words
take priority; `FOWords.FreshFor` rules out collisions. -/
def Model.lexiconFO (m : Model L) (fw : FOWords) (nm : LexNaming L) (w : m.W) :
    Lexicon m.E m.W := fun s =>
  m.lexiconAt nm w s <|> fw.lexicon m.E m.W s

/-- The logical word forms are fresh for the naming maps. -/
def FOWords.FreshFor (fw : FOWords) (nm : LexNaming L) : Prop :=
  ∀ s ∈ [fw.every, fw.some_, fw.no, fw.not_, fw.and_, fw.or_],
    nm.names s = none ∧ nm.preds₁ s = none ∧ nm.preds₂ s = none

/-- Each word form names at most one kind of symbol, so the compiler's
classification of a word agrees with the lexicon's lookup order. -/
structure LexNaming.Disjoint (nm : LexNaming L) : Prop where
  names_of_preds₁ : ∀ s R, nm.preds₁ s = some R → nm.names s = none
  names_of_preds₂ : ∀ s R, nm.preds₂ s = some R → nm.names s = none
  preds₁_of_preds₂ : ∀ s R, nm.preds₂ s = some R → nm.preds₁ s = none

/-! ### The compiler

Recognized (QR'd Heim-Kratzer) shapes: name/trace–verb predication with
optional object, sentence negation `[not t]`, sentence coordination
`[t₁ [and t₂]]`, and quantified clauses `[[Q N] [bind k body]]`. Everything
else — in particular *most* — is outside the fragment and compiles to
`none`. -/

/-- Compile an entity subtree: a proper name or a trace. -/
def compileTerm (nm : LexNaming L) : Tree Unit String → Option (L.Term ℕ)
  | .terminal _ s => (nm.names s).map Constants.term
  | .trace k _ => some (Term.var k)
  | _ => none

/-- Compile a predicate subtree applied to a subject term: an intransitive
verb, or a transitive verb with a name/trace object. -/
def compilePred (nm : LexNaming L) (τ : L.Term ℕ) :
    Tree Unit String → Option (L.Formula ℕ)
  | .terminal _ v => (nm.preds₁ v).map fun R => R.formula₁ τ
  | .node _ [.terminal _ v, obj] =>
      (nm.preds₂ v).bind fun R =>
        (compileTerm nm obj).map fun τₒ => R.formula₂ τ τₒ
  | _ => none

/-- Compile the FO fragment of a tree to a first-order formula with trace
indices as free variables. Partial: `none` outside the fragment. -/
def compileFO (fw : FOWords) (nm : LexNaming L) :
    Tree Unit String → Option (L.Formula ℕ)
  | .node _ [.terminal _ s, r] =>
      if s = fw.not_ then (compileFO fw nm r).map BoundedFormula.not
      else (nm.names s).bind fun c => compilePred nm (Constants.term c) r
  | .node _ [.trace k _, r] => compilePred nm (Term.var k) r
  | .node _ [.node _ [.terminal _ q, .terminal _ nw], .bind k _ body] =>
      (nm.preds₁ nw).bind fun R =>
        (compileFO fw nm body).bind fun ψ =>
          if q = fw.every then some (all₁ k ((R.formula₁ (Term.var k)).imp ψ))
          else if q = fw.some_ then some (ex₁ k (R.formula₁ (Term.var k) ⊓ ψ))
          else if q = fw.no then
            some (all₁ k ((R.formula₁ (Term.var k)).imp ψ.not))
          else none
  | .node _ [l, .node _ [.terminal _ s, t₂] ] =>
      if s = fw.and_ then
        (compileFO fw nm l).bind fun φ₁ =>
          (compileFO fw nm t₂).map fun φ₂ => φ₁ ⊓ φ₂
      else if s = fw.or_ then
        (compileFO fw nm l).bind fun φ₁ =>
          (compileFO fw nm t₂).map fun φ₂ => φ₁ ⊔ φ₂
      else none
  | _ => none

/-! ### Lookup lemmas -/

/-- The six logical word forms are pairwise distinct. -/
def FOWords.Nodup (fw : FOWords) : Prop :=
  ([fw.every, fw.some_, fw.no, fw.not_, fw.and_, fw.or_] : List String).Nodup

section Lookups

variable (m : Model L) (fw : FOWords) (nm : LexNaming L) (w : m.W)

theorem Model.lexiconFO_names {s : String} {c : L.Constants}
    (h : nm.names s = some c) :
    m.lexiconFO fw nm w s = some ⟨.e, m.const c w⟩ := by
  simp [Model.lexiconFO, Model.lexiconAt, h]

theorem Model.lexiconFO_preds₁ {s : String} {R : L.Relations 1}
    (h : nm.preds₁ s = some R) (h₀ : nm.names s = none) :
    m.lexiconFO fw nm w s = some ⟨.e ⇒ .t, m.pred₁ext R w⟩ := by
  simp [Model.lexiconFO, Model.lexiconAt, h, h₀]

theorem Model.lexiconFO_preds₂ {s : String} {R : L.Relations 2}
    (h : nm.preds₂ s = some R) (h₀ : nm.names s = none)
    (h₁ : nm.preds₁ s = none) :
    m.lexiconFO fw nm w s = some ⟨.e ⇒ .e ⇒ .t, m.pred₂ext R w⟩ := by
  simp [Model.lexiconFO, Model.lexiconAt, h, h₀, h₁]

/-- At a word fresh for the naming maps, lookup falls through to the logical
vocabulary. -/
theorem Model.lexiconFO_fresh {s : String}
    (h₀ : nm.names s = none) (h₁ : nm.preds₁ s = none)
    (h₂ : nm.preds₂ s = none) :
    m.lexiconFO fw nm w s = fw.lexicon m.E m.W s := by
  simp [Model.lexiconFO, Model.lexiconAt, h₀, h₁, h₂]

end Lookups

namespace FOWords

variable {fw : FOWords}

private theorem nodup_ne (hnd : fw.Nodup) :
    (fw.some_ ≠ fw.every) ∧
    (fw.no ≠ fw.every ∧ fw.no ≠ fw.some_) ∧
    (fw.not_ ≠ fw.every ∧ fw.not_ ≠ fw.some_ ∧ fw.not_ ≠ fw.no) ∧
    (fw.and_ ≠ fw.every ∧ fw.and_ ≠ fw.some_ ∧ fw.and_ ≠ fw.no ∧
      fw.and_ ≠ fw.not_) ∧
    (fw.or_ ≠ fw.every ∧ fw.or_ ≠ fw.some_ ∧ fw.or_ ≠ fw.no ∧
      fw.or_ ≠ fw.not_ ∧ fw.or_ ≠ fw.and_) := by
  simp only [FOWords.Nodup, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, ⟨h10, h11, h12⟩, ⟨h13, h14⟩, h15, -⟩ := hnd
  exact ⟨Ne.symm h1, ⟨Ne.symm h2, Ne.symm h6⟩, ⟨Ne.symm h3, Ne.symm h7, Ne.symm h10⟩,
    ⟨Ne.symm h4, Ne.symm h8, Ne.symm h11, Ne.symm h13⟩,
    ⟨Ne.symm h5, Ne.symm h9, Ne.symm h12, Ne.symm h14, Ne.symm h15⟩⟩

variable (E W : Type)

theorem lexicon_every :
    fw.lexicon E W fw.every
      = some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, every_sem⟩ := by
  simp [FOWords.lexicon]

theorem lexicon_some (hnd : fw.Nodup) :
    fw.lexicon E W fw.some_
      = some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, some_sem⟩ := by
  obtain ⟨h1, _, _, _, _⟩ := nodup_ne hnd
  simp [FOWords.lexicon, h1]

theorem lexicon_no (hnd : fw.Nodup) :
    fw.lexicon E W fw.no
      = some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, no_sem⟩ := by
  obtain ⟨_, ⟨h1, h2⟩, _, _, _⟩ := nodup_ne hnd
  simp [FOWords.lexicon, h1, h2]

theorem lexicon_not (hnd : fw.Nodup) :
    fw.lexicon E W fw.not_ = some ⟨.t ⇒ .t, neg⟩ := by
  obtain ⟨_, _, ⟨h1, h2, h3⟩, _, _⟩ := nodup_ne hnd
  simp [FOWords.lexicon, h1, h2, h3]

theorem lexicon_and (hnd : fw.Nodup) :
    fw.lexicon E W fw.and_
      = some ⟨.t ⇒ .t ⇒ .t, fun q p => conj p q⟩ := by
  obtain ⟨_, _, _, ⟨h1, h2, h3, h4⟩, _⟩ := nodup_ne hnd
  simp [FOWords.lexicon, h1, h2, h3, h4]

theorem lexicon_or (hnd : fw.Nodup) :
    fw.lexicon E W fw.or_
      = some ⟨.t ⇒ .t ⇒ .t, fun q p => disj p q⟩ := by
  obtain ⟨_, _, _, _, ⟨h1, h2, h3, h4, h5⟩⟩ := nodup_ne hnd
  simp [FOWords.lexicon, h1, h2, h3, h4, h5]

/-- Extract the naming-map-freshness triple for a logical word. -/
theorem FreshFor.at {nm : LexNaming L} (h : fw.FreshFor nm) {s : String}
    (hs : s ∈ [fw.every, fw.some_, fw.no, fw.not_, fw.and_, fw.or_]) :
    nm.names s = none ∧ nm.preds₁ s = none ∧ nm.preds₂ s = none :=
  h s hs

end FOWords

/-! ### Realization at a model's world

`Model` carries structures as terms, so `Realize` needs the instance fixed
per world; `realizeAt`/`termAt` package that. -/

/-- Realize a formula over the model's structure at world `w`. -/
def Model.realizeAt (m : Model L) (w : m.W) (φ : L.Formula ℕ)
    (g : Core.Assignment m.E) : Prop :=
  letI := m.interp w
  φ.Realize g

/-- Realize a term over the model's structure at world `w`. -/
def Model.termAt (m : Model L) (w : m.W) (τ : L.Term ℕ)
    (g : Core.Assignment m.E) : m.E :=
  letI := m.interp w
  τ.realize g

section RealizeAt

variable (m : Model L) (w : m.W) (g : Core.Assignment m.E)

theorem Model.termAt_var (k : ℕ) : m.termAt w (Term.var k) g = g k := rfl

theorem Model.termAt_const (c : L.Constants) :
    m.termAt w (Constants.term c) g = m.const c w := by
  letI := m.interp w
  exact Term.realize_constants

theorem Model.realizeAt_not (φ : L.Formula ℕ) :
    m.realizeAt w φ.not g ↔ ¬ m.realizeAt w φ g := by
  letI := m.interp w
  exact Formula.realize_not

theorem Model.realizeAt_inf (φ ψ : L.Formula ℕ) :
    m.realizeAt w (φ ⊓ ψ) g ↔ m.realizeAt w φ g ∧ m.realizeAt w ψ g := by
  letI := m.interp w
  exact Formula.realize_inf

theorem Model.realizeAt_sup (φ ψ : L.Formula ℕ) :
    m.realizeAt w (φ ⊔ ψ) g ↔ m.realizeAt w φ g ∨ m.realizeAt w ψ g := by
  letI := m.interp w
  exact Formula.realize_sup

theorem Model.realizeAt_imp (φ ψ : L.Formula ℕ) :
    m.realizeAt w (φ.imp ψ) g ↔ (m.realizeAt w φ g → m.realizeAt w ψ g) := by
  letI := m.interp w
  exact Formula.realize_imp

theorem Model.realizeAt_all₁ (k : ℕ) (φ : L.Formula ℕ) :
    m.realizeAt w (all₁ k φ) g ↔
      ∀ x : m.E, m.realizeAt w φ (Function.update g k x) := by
  letI := m.interp w
  exact FirstOrder.Language.Formula.realize_all₁

theorem Model.realizeAt_ex₁ (k : ℕ) (φ : L.Formula ℕ) :
    m.realizeAt w (ex₁ k φ) g ↔
      ∃ x : m.E, m.realizeAt w φ (Function.update g k x) := by
  letI := m.interp w
  exact FirstOrder.Language.Formula.realize_ex₁

/-- Atomic agreement, unary: realization of `R(τ)` is the model-sourced
extensional predicate at the term's value. -/
theorem Model.realizeAt_formula₁ (R : L.Relations 1) (τ : L.Term ℕ) :
    m.realizeAt w (R.formula₁ τ) g ↔ m.pred₁ext R w (m.termAt w τ g) := by
  letI := m.interp w
  rw [Model.realizeAt, Formula.realize_rel₁]
  exact iff_of_eq (congrArg _ (funext fun i => by fin_cases i; rfl))

/-- Atomic agreement, binary: realization of `R(τ₁, τ₂)` is the model-sourced
object-first relation at the terms' values (subject first in the vector). -/
theorem Model.realizeAt_formula₂ (R : L.Relations 2) (τ₁ τ₂ : L.Term ℕ) :
    m.realizeAt w (R.formula₂ τ₁ τ₂) g ↔
      m.pred₂ext R w (m.termAt w τ₂ g) (m.termAt w τ₁ g) := by
  letI := m.interp w
  rw [Model.realizeAt, Formula.realize_rel₂]
  exact iff_of_eq (congrArg _ (funext fun i => by fin_cases i <;> rfl))

end RealizeAt

/-! ### Engine reduction helpers (at `M = Id`) -/

section EngineHelpers

variable {E W : Type}

/-- Forward FA at `Id`, with the applicative collapsed. -/
private theorem interpBinary_fa {σ τ : Ty} (f : Denot E W (σ ⇒ τ)) (x : Denot E W σ) :
    interpBinary (M := Id) ⟨σ ⇒ τ, f⟩ ⟨σ, x⟩ = some ⟨τ, f x⟩ := by
  rw [interpBinary_eq, tryFA_forward]
  rfl

/-- Backward FA at `Id`: entity subject, unary predicate. -/
private theorem interpBinary_e_et (x : Denot E W .e) (P : Denot E W (.e ⇒ .t)) :
    interpBinary (M := Id) ⟨.e, x⟩ ⟨.e ⇒ .t, P⟩ = some ⟨.t, P x⟩ := rfl

/-- Backward FA at `Id`: sentence subject, sentential operator. -/
private theorem interpBinary_t_tt (p : Denot E W .t) (F : Denot E W (.t ⇒ .t)) :
    interpBinary (M := Id) ⟨.t, p⟩ ⟨.t ⇒ .t, F⟩ = some ⟨.t, F p⟩ := rfl

private theorem predAbs_id_dist :
    PredAbs.dist? (M := Id) (E := E) (W := W) = some (fun _ f => f) := rfl

/-- Congruence for truth-valued results: an `Iff` lifts through
`some ⟨.t, ·⟩`. -/
private theorem some_t_congr {p q : Denot E W .t} (h : p ↔ q) :
    (some ⟨.t, p⟩ : Option (TypedDenot E W)) = some ⟨.t, q⟩ :=
  congrArg (fun r => (some ⟨.t, r⟩ : Option (TypedDenot E W))) (propext h)

/-- The `.bind` node at `Id`, given the body's interpretation at the outer
assignment: it denotes an entity predicate agreeing pointwise with the body
at updated assignments. -/
private theorem interp_bind_exists (lex : Lexicon E W) (g : Core.Assignment E)
    (k : ℕ) (c : Unit) (body : Tree Unit String) {p : Denot E W .t}
    (hbody : Tree.interp E W lex g body = some ⟨.t, p⟩) :
    ∃ F : Denot E W (.e ⇒ .t),
      Tree.interp E W lex g (.bind k c body) = some ⟨.fn .e .t, F⟩ ∧
      ∀ (x : E) (px : Denot E W .t),
        Tree.interp E W lex (Function.update g k x) body = some ⟨.t, px⟩ →
        F x = px := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · conv_lhs => rw [Tree.interp]
    rw [predAbs_id_dist, hbody]
    rfl
  · intro x px hx
    simp only [hx]
    rfl

end EngineHelpers

/-! ### Agreement -/

section Agreement

variable (m : Model L) (fw : FOWords) (nm : LexNaming L) (w : m.W)

/-- Entity-subtree agreement: a compiled term's engine value is its
realization over the model. -/
theorem interp_compileTerm (g : Core.Assignment m.E) :
    ∀ {t : Tree Unit String} {τ : L.Term ℕ}, compileTerm nm t = some τ →
      Tree.interp m.E m.W (m.lexiconFO fw nm w) g t
        = some ⟨.e, m.termAt w τ g⟩
  | .terminal _ s, τ, h => by
      simp only [compileTerm, Option.map_eq_some_iff] at h
      obtain ⟨c, hc, rfl⟩ := h
      rw [interp_terminal, interpTerminal_lookup, m.lexiconFO_names fw nm w hc,
        Option.map_some, m.termAt_const]
  | .trace k _, τ, h => by
      simp only [compileTerm, Option.some.injEq] at h
      subst h
      rfl

/-- Predication agreement: subject term + predicate subtree compose to the
compiled atom's realization. -/
theorem interp_compilePred (hdj : nm.Disjoint) (g : Core.Assignment m.E)
    {subj : Tree Unit String} {τ : L.Term ℕ}
    (hsubj : compileTerm nm subj = some τ) :
    ∀ {r : Tree Unit String} {φ : L.Formula ℕ}, compilePred nm τ r = some φ →
      ∀ c : Unit,
        Tree.interp m.E m.W (m.lexiconFO fw nm w) g (.node c [subj, r])
          = some ⟨.t, m.realizeAt w φ g⟩
  | .terminal _ v, φ, h, c => by
      simp only [compilePred, Option.map_eq_some_iff] at h
      obtain ⟨R, hR, rfl⟩ := h
      rw [interp_node_binary, interp_compileTerm m fw nm w g hsubj, Option.bind_some,
        interp_terminal, interpTerminal_lookup,
        m.lexiconFO_preds₁ fw nm w hR (hdj.names_of_preds₁ v R hR),
        Option.map_some, Option.bind_some, interpBinary_e_et]
      exact some_t_congr (m.realizeAt_formula₁ w g R τ).symm
  | .node _ [.terminal _ v, obj], φ, h, c => by
      simp only [compilePred, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨R, hR, τₒ, hobj, rfl⟩ := h
      rw [interp_node_binary, interp_compileTerm m fw nm w g hsubj, Option.bind_some,
        interp_node_binary, interp_terminal, interpTerminal_lookup,
        m.lexiconFO_preds₂ fw nm w hR (hdj.names_of_preds₂ v R hR)
          (hdj.preds₁_of_preds₂ v R hR),
        Option.map_some, Option.bind_some,
        interp_compileTerm m fw nm w g hobj, Option.bind_some,
        interpBinary_fa, Option.bind_some, interpBinary_e_et]
      exact some_t_congr (m.realizeAt_formula₂ w g R τ τₒ).symm

/-- Composition of a quantified clause `[[Q N] [bind k body]]` from the
lexicon lookups of the quantifier and restrictor words and the `.bind`
node's interpretation. -/
private theorem interp_quantClause {g : Core.Assignment m.E} {q nw : String}
    {Q : Denot m.E m.W ((.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t)}
    {N F : Denot m.E m.W (.e ⇒ .t)} {k : ℕ} {body : Tree Unit String}
    {a a₁ a₂ a₃ a₄ : Unit}
    (hQ : m.lexiconFO fw nm w q = some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, Q⟩)
    (hN : m.lexiconFO fw nm w nw = some ⟨.e ⇒ .t, N⟩)
    (hbind : Tree.interp m.E m.W (m.lexiconFO fw nm w) g (.bind k a₄ body)
      = some ⟨.fn .e .t, F⟩) :
    Tree.interp m.E m.W (m.lexiconFO fw nm w) g
        (.node a [.node a₁ [.terminal a₂ q, .terminal a₃ nw], .bind k a₄ body])
      = some ⟨.t, Q N F⟩ := by
  rw [interp_node_binary, interp_node_binary, interp_terminal,
    interpTerminal_lookup, hQ, Option.map_some, Option.bind_some,
    interp_terminal, interpTerminal_lookup, hN, Option.map_some,
    Option.bind_some, interpBinary_fa, Option.bind_some, hbind,
    Option.bind_some, interpBinary_fa]

/-- **The agreement theorem**: whenever the compiler succeeds, the engine's
composed denotation *is* the realization of the compiled formula over the
model at `w` — the DRT triangle for type-driven composition. -/
theorem interp_compileFO (hnd : fw.Nodup) (hfr : fw.FreshFor nm)
    (hdj : nm.Disjoint) (t : Tree Unit String) :
    ∀ {φ : L.Formula ℕ} (g : Core.Assignment m.E), compileFO fw nm t = some φ →
      Tree.interp m.E m.W (m.lexiconFO fw nm w) g t
        = some ⟨.t, m.realizeAt w φ g⟩ := by
  induction t using compileFO.induct fw with
  | case1 a a₁ r ih =>
    -- negation [not r]
    intro φ g h
    simp only [compileFO, ↓reduceIte, Option.map_eq_some_iff] at h
    obtain ⟨ψ, hψ, rfl⟩ := h
    have hfr₁ := hfr.at (s := fw.not_) (by simp)
    rw [interp_node_binary, interp_terminal, interpTerminal_lookup,
      m.lexiconFO_fresh fw nm w hfr₁.1 hfr₁.2.1 hfr₁.2.2,
      FOWords.lexicon_not m.E m.W hnd, Option.map_some, Option.bind_some,
      ih g hψ, Option.bind_some, interpBinary_fa]
    congr 1
  | case2 a a₁ s r hs =>
    -- name-subject predication
    intro φ g h
    simp only [compileFO, if_neg hs, Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, hpred⟩ := h
    exact interp_compilePred m fw nm w hdj g
      (by simp [compileTerm, hc]) hpred a
  | case3 a k a₁ r =>
    -- trace-subject predication
    intro φ g h
    simp only [compileFO] at h
    exact interp_compilePred m fw nm w hdj g (by simp [compileTerm]) h a
  | case4 a a₁ a₂ q a₃ nw k a₄ body ih =>
    -- quantified clause [[Q N] [bind k body]]
    intro φ g h
    simp only [compileFO, Option.bind_eq_some_iff] at h
    obtain ⟨R, hR, ψ, hψ, hq⟩ := h
    obtain ⟨F, hbind, hF⟩ :=
      interp_bind_exists (m.lexiconFO fw nm w) g k a₄ body (ih g hψ)
    have hquant : ∀ x : m.E,
        F x = m.realizeAt w ψ (Function.update g k x) := fun x =>
      hF x _ (ih (Function.update g k x) hψ)
    have hrestr : ∀ x : m.E,
        m.realizeAt w (Relations.formula₁ R (Term.var k)) (Function.update g k x)
          ↔ m.pred₁ext R w x := by
      intro x
      rw [m.realizeAt_formula₁, m.termAt_var, Function.update_self]
    have hN := m.lexiconFO_preds₁ fw nm w hR (hdj.names_of_preds₁ _ _ hR)
    by_cases hq1 : q = fw.every
    · rw [if_pos hq1] at hq
      cases hq
      subst hq1
      have hfr₁ := hfr.at (s := fw.every) (by simp)
      rw [interp_quantClause m fw nm w
        ((m.lexiconFO_fresh fw nm w hfr₁.1 hfr₁.2.1 hfr₁.2.2).trans
          (FOWords.lexicon_every m.E m.W)) hN hbind]
      refine some_t_congr ?_
      rw [m.realizeAt_all₁ w g]
      simp only [Quantification.every_sem, m.realizeAt_imp]
      exact forall_congr' fun x =>
        imp_congr (hrestr x).symm (by rw [hquant x])
    · rw [if_neg hq1] at hq
      by_cases hq2 : q = fw.some_
      · rw [if_pos hq2] at hq
        cases hq
        subst hq2
        have hfr₁ := hfr.at (s := fw.some_) (by simp)
        rw [interp_quantClause m fw nm w
          ((m.lexiconFO_fresh fw nm w hfr₁.1 hfr₁.2.1 hfr₁.2.2).trans
            (FOWords.lexicon_some m.E m.W hnd)) hN hbind]
        refine some_t_congr ?_
        rw [m.realizeAt_ex₁ w g]
        simp only [Quantification.some_sem, m.realizeAt_inf]
        exact exists_congr fun x =>
          and_congr (hrestr x).symm (by rw [hquant x])
      · rw [if_neg hq2] at hq
        by_cases hq3 : q = fw.no
        · rw [if_pos hq3] at hq
          cases hq
          subst hq3
          have hfr₁ := hfr.at (s := fw.no) (by simp)
          rw [interp_quantClause m fw nm w
            ((m.lexiconFO_fresh fw nm w hfr₁.1 hfr₁.2.1 hfr₁.2.2).trans
              (FOWords.lexicon_no m.E m.W hnd)) hN hbind]
          refine some_t_congr ?_
          rw [m.realizeAt_all₁ w g]
          simp only [Quantification.no_sem, m.realizeAt_imp,
            m.realizeAt_not]
          exact forall_congr' fun x =>
            imp_congr (hrestr x).symm (by rw [hquant x])
        · rw [if_neg hq3] at hq
          simp at hq
  | case5 a l a₁ a₂ t₂ hl₁ hl₂ ihl iht =>
    -- coordination [l [and t₂]]
    intro φ g h
    simp only [compileFO, ↓reduceIte, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
    have hfr₁ := hfr.at (s := fw.and_) (by simp)
    rw [interp_node_binary, ihl g h₁, Option.bind_some, interp_node_binary,
      interp_terminal, interpTerminal_lookup,
      m.lexiconFO_fresh fw nm w hfr₁.1 hfr₁.2.1 hfr₁.2.2,
      FOWords.lexicon_and m.E m.W hnd, Option.map_some, Option.bind_some,
      iht g h₂, Option.bind_some, interpBinary_fa, Option.bind_some,
      interpBinary_t_tt]
    refine some_t_congr ?_
    rw [m.realizeAt_inf w g]
    exact Iff.rfl
  | case6 a l a₁ a₂ t₂ hl₁ hl₂ hne ihl iht =>
    -- coordination [l [or t₂]]
    intro φ g h
    simp only [compileFO, if_neg hne, ↓reduceIte, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
    have hfr₁ := hfr.at (s := fw.or_) (by simp)
    rw [interp_node_binary, ihl g h₁, Option.bind_some, interp_node_binary,
      interp_terminal, interpTerminal_lookup,
      m.lexiconFO_fresh fw nm w hfr₁.1 hfr₁.2.1 hfr₁.2.2,
      FOWords.lexicon_or m.E m.W hnd, Option.map_some, Option.bind_some,
      iht g h₂, Option.bind_some, interpBinary_fa, Option.bind_some,
      interpBinary_t_tt]
    refine some_t_congr ?_
    rw [m.realizeAt_sup w g]
    exact Iff.rfl
  | case7 a l a₁ a₂ s t₂ hl₁ hl₂ hs₁ hs₂ =>
    intro φ g h
    simp only [compileFO, if_neg hs₁, if_neg hs₂] at h
    simp at h
  | case8 t hex₁ hex₂ hex₃ hex₄ =>
    intro φ g h
    rw [compileFO.eq_def] at h
    split at h
    all_goals
      first
        | simp at h
        | exact (hex₁ _ _ _ _ rfl).elim
        | exact (hex₂ _ _ _ _ rfl).elim
        | exact (hex₃ _ _ _ _ _ _ _ _ _ rfl).elim
        | exact (hex₄ _ _ _ _ _ _ rfl).elim


end Agreement

/-! ### Truth and consequence transfer -/

section Consequence

variable (m : Model L) (fw : FOWords) (nm : LexNaming L) (w : m.W)

/-- Truth of a tree at a model's world under an assignment: it composes to a
true truth value. -/
def HoldsAt (lex : Lexicon m.E m.W) (g : Core.Assignment m.E)
    (t : Tree Unit String) : Prop :=
  ∃ p, Tree.interp m.E m.W lex g t = some ⟨.t, p⟩ ∧ p

theorem holdsAt_iff_realize (hnd : fw.Nodup) (hfr : fw.FreshFor nm)
    (hdj : nm.Disjoint) {t : Tree Unit String} {φ : L.Formula ℕ}
    (h : compileFO fw nm t = some φ) (g : Core.Assignment m.E) :
    HoldsAt m (m.lexiconFO fw nm w) g t ↔ m.realizeAt w φ g := by
  constructor
  · rintro ⟨p, hp, htrue⟩
    have := (interp_compileFO m fw nm w hnd hfr hdj t g h).symm.trans hp
    simp only [Option.some.injEq, TypedDenot.mk.injEq, heq_eq_eq,
      true_and] at this
    rw [this]
    exact htrue
  · intro hr
    exact ⟨_, interp_compileFO m fw nm w hnd hfr hdj t g h, hr⟩

/-- **Consequence transfer**: first-order consequence between compiled
formulas yields cross-model entailment between the trees — for every
composition model, world, and assignment. -/
theorem holdsAt_of_models (hnd : fw.Nodup) (hfr : fw.FreshFor nm)
    (hdj : nm.Disjoint) {t₁ t₂ : Tree Unit String} {φ₁ φ₂ : L.Formula ℕ}
    (h₁ : compileFO fw nm t₁ = some φ₁) (h₂ : compileFO fw nm t₂ = some φ₂)
    (hmod : ∀ (M : Type) (S : L.Structure M) (v : ℕ → M),
      @Formula.Realize L M S ℕ φ₁ v → @Formula.Realize L M S ℕ φ₂ v)
    (g : Core.Assignment m.E) :
    HoldsAt m (m.lexiconFO fw nm w) g t₁ →
      HoldsAt m (m.lexiconFO fw nm w) g t₂ := by
  rw [holdsAt_iff_realize m fw nm w hnd hfr hdj h₁ g,
    holdsAt_iff_realize m fw nm w hnd hfr hdj h₂ g]
  exact hmod m.E (m.interp w) g

end Consequence

end Semantics.Composition

namespace Semantics.Composition

/-- The default logical vocabulary is pairwise distinct. -/
theorem FOWords.nodup_default : ({} : FOWords).Nodup := by
  unfold FOWords.Nodup
  decide

end Semantics.Composition

/-! ### Bridge to mathlib `Theory` consequence

For universe-0 languages, composition models and mathlib's bundled models
coincide: tree entailment over nonempty-domain composition models *is*
first-order consequence over the empty theory, and compactness transfers
to families of trees. (`ModelType` requires nonempty carriers, hence the
nonempty-domain restriction — standard in the GQ literature.) -/

namespace Semantics.Composition

open FirstOrder Language
open Semantics.Montague (Lexicon)
open Syntax (Tree)

section TheoryBridge

variable {L₀ : Language.{0, 0}} (fw : FOWords) (nm : LexNaming L₀)

/-- A first-order structure as a one-world composition model. -/
def Model.ofStructure (M : Type) (S : L₀.Structure M) : Model L₀ :=
  ⟨M, Unit, fun _ => S⟩

private theorem modelEmpty (M : Type) [L₀.Structure M] : M ⊨ (∅ : L₀.Theory) :=
  ⟨fun _φ hφ => absurd hφ (by simp)⟩

/-- **Tree entailment is first-order consequence**: mathlib's `⊨ᵇ` over the
empty theory coincides with cross-model entailment between compiled trees,
over nonempty-domain composition models. -/
theorem models_imp_iff_entails (hnd : fw.Nodup) (hfr : fw.FreshFor nm)
    (hdj : nm.Disjoint) {t₁ t₂ : Tree Unit String} {φ₁ φ₂ : L₀.Formula ℕ}
    (h₁ : compileFO fw nm t₁ = some φ₁) (h₂ : compileFO fw nm t₂ = some φ₂) :
    (∅ : L₀.Theory) ⊨ᵇ φ₁.imp φ₂ ↔
      ∀ (m : Model L₀), Nonempty m.E → ∀ (w : m.W) (g : Core.Assignment m.E),
        HoldsAt m (m.lexiconFO fw nm w) g t₁ →
          HoldsAt m (m.lexiconFO fw nm w) g t₂ := by
  constructor
  · intro hmod m hne w g
    rw [holdsAt_iff_realize m fw nm w hnd hfr hdj h₁ g,
      holdsAt_iff_realize m fw nm w hnd hfr hdj h₂ g]
    letI := m.interp w
    haveI : m.E ⊨ (∅ : L₀.Theory) := inferInstance
    haveI : Nonempty m.E := hne
    have h := hmod ⟨m.E⟩ g default
    exact BoundedFormula.realize_imp.mp h
  · intro hent M v xs
    have hxs : xs = default := funext fun i => i.elim0
    subst hxs
    rw [BoundedFormula.realize_imp]
    have := hent (Model.ofStructure M M.struc) M.nonempty' () v
    rw [holdsAt_iff_realize (Model.ofStructure M M.struc) fw nm ()
        hnd hfr hdj h₁ v,
      holdsAt_iff_realize (Model.ofStructure M M.struc) fw nm ()
        hnd hfr hdj h₂ v] at this
    exact this

/-! ### Closed trees as sentences, and compactness -/

/-- **Compactness at the tree level**: a family of closed fragment trees is
jointly satisfiable in a nonempty-domain composition model iff every finite
subfamily is. The nontrivial direction is mathlib's compactness theorem
(`Theory.isSatisfiable_iff_isFinitelySatisfiable`, via ultraproducts). -/
theorem holdsAt_compactness (hnd : fw.Nodup) (hfr : fw.FreshFor nm)
    (hdj : nm.Disjoint) {ι : Type} (trees : ι → Tree Unit String)
    (φs : ι → L₀.Formula ℕ)
    (hc : ∀ i, compileFO fw nm (trees i) = some (φs i))
    (hcl : ∀ i, (φs i).freeVarFinset = ∅) :
    (∃ (m : Model L₀) (_ : Nonempty m.E) (w : m.W) (g : Core.Assignment m.E),
        ∀ i, HoldsAt m (m.lexiconFO fw nm w) g (trees i)) ↔
      ∀ s : Finset ι,
        ∃ (m : Model L₀) (_ : Nonempty m.E) (w : m.W) (g : Core.Assignment m.E),
          ∀ i ∈ s, HoldsAt m (m.lexiconFO fw nm w) g (trees i) := by
  constructor
  · rintro ⟨m, hne, w, g, hall⟩ s
    exact ⟨m, hne, w, g, fun i _ => hall i⟩
  · intro hfin
    have hsat : Theory.IsSatisfiable
        (L := L₀) (Set.range fun i => (φs i).toSentence (hcl i)) := by
      rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
      intro T₀ hT₀
      classical
      choose f hf using fun (x : T₀) => hT₀ x.2
      obtain ⟨m, hne, w, g, hs⟩ := hfin (Finset.univ.image f)
      letI := m.interp w
      haveI : Nonempty m.E := hne
      haveI : m.E ⊨ (T₀ : L₀.Theory) := by
        refine ⟨fun ψ hψ => ?_⟩
        obtain ⟨x, rfl⟩ : ∃ x : T₀, (φs (f x)).toSentence (hcl (f x)) = ψ :=
          ⟨⟨ψ, hψ⟩, hf ⟨ψ, hψ⟩⟩
        rw [Formula.realize_toSentence (v := g)]
        have hold := hs (f x) (Finset.mem_image_of_mem f (Finset.mem_univ x))
        rw [holdsAt_iff_realize m fw nm w hnd hfr hdj (hc (f x)) g] at hold
        exact hold
      exact Theory.Model.isSatisfiable m.E
    obtain ⟨N⟩ := hsat
    letI := N.struc
    haveI := N.nonempty'
    refine ⟨Model.ofStructure N N.struc, N.nonempty', (),
      fun _ => Classical.arbitrary N, fun i => ?_⟩
    rw [holdsAt_iff_realize (Model.ofStructure N N.struc) fw nm ()
      hnd hfr hdj (hc i) _]
    have : (N : Type) ⊨ (φs i).toSentence (hcl i) :=
      N.is_model.realize_of_mem _ (Set.mem_range_self i)
    exact (Formula.realize_toSentence (M := (N : Type)) (φs i) (hcl i)
      (fun _ => Classical.arbitrary N)).mp this

end TheoryBridge

end Semantics.Composition
