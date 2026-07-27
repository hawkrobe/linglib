import Linglib.Core.Computability.Subregular.Logic.BMRS
import Linglib.Core.Order.IterateFixedPoint
import Mathlib.Tactic.IntervalCases

/-!
# Yolyan & Comer 2026: Phonological Processes as Modal Transductions

[yolyan-comer-2026]: total BMRS — the Boolean monadic recursive schemes of
[bhaskar-jardine-chandlee-oakden-2020], rendered by `Subregular.Logic.BMRS` — is
expressively equivalent to the modal μ-calculus on words (Thm. 2), giving an
alternative proof that order-preserving BMRS captures the rational functions. `Formula`/`System` render the paper's §4 vectorial presentation of
[kozen-1983]'s μ-calculus over word models — a finite system of equations `Xⱼ = θⱼ`
read as the least fixed point of the induced monotone operator (Knaster–Tarski), which
by Bekić's theorem is equivalent to nested `μ`-binders but spares the binder
bookkeeping. This file formalizes the constructive core: the translation `tr`
(Def. 6) from vectorial modal formulas to BMRS expressions and its compositionality
(`eval_tr`, Remark 7) — `tr φ` evaluates to the truth value of `φ` wherever rule-head
calls agree with the recursion variables. Thm. 8 discharges that hypothesis for
*directed* systems by SCC induction (TODO: the directedness machinery); Thm. 2's
converse containment runs through MSO (out of scope until an MSO substrate exists).

The paper's two worked examples ground both formalisms: vowel nasalization ((2)–(4),
non-recursive) and progressive nasal spreading in Warao ((5)–(7), [osborn-1966]). The
modal form `N′ = μX.(N ∨ (¬T ∧ ♦X))` recurses under the *backward* modality `♦` =
`bdia` — a target inherits nasality from its predecessor. Both compute the Fig. 4/5
columns on /naote/ → [nãõte], and the BMRS and modal results agree
(`warao_agreement`); `warao_tr_agreement` runs Remark 7 end-to-end on the translated
program, with the rule-head hypothesis discharged by direct computation — the concrete
shape of Thm. 8's induction.
-/

namespace YolyanComer2026

open Subregular.Logic Subregular.Logic.BMRS

variable {α : Type*} {n : ℕ}

/-! ### The vectorial modal μ-calculus on words (§4)

Formulas are the negation-free fragment `μML꜀₊` — the ambient of Thm. 8 — extended with
negated *label* atoms (`nlabel`), which keeps negation off recursion variables (so
monotonicity is structural) while covering processes like Warao nasal spreading
`N′ = μX.(N ∨ (¬T ∧ ♦X))`. -/

/-- Quantifier-free modal formulas over labels `α` and `n` recursion variables:
negation-free apart from **class atoms** (`nlabel`), so recursion variables occur only
positively. `label`/`nlabel` test the current position's symbol against a `Finset` class
(featural predicates like V or N are single atoms; a symbol test is the singleton case).
`initial`/`final` are the edge tests (the literature's `min`/`max`); `dia` (`◇`) reads
the successor position, `bdia` (`♦`) the predecessor. -/
inductive Formula (α : Type*) (n : ℕ) where
  | tru
  | fls
  | initial
  | final
  | label (s : Finset α)
  | nlabel (s : Finset α)
  | var (X : Fin n)
  | and (φ ψ : Formula α n)
  | or (φ ψ : Formula α n)
  | dia (φ : Formula α n)
  | bdia (φ : Formula α n)
  deriving DecidableEq

/-- Satisfaction at a pointed word `(w, i)` under a valuation `U` of the recursion
variables. -/
def Formula.Realize (w : WordModel α) (U : Fin n → Set ℕ) : ℕ → Formula α n → Prop
  | _, .tru => True
  | _, .fls => False
  | i, .initial => i = 0
  | i, .final => i + 1 = w.length
  | i, .label s => ∃ a ∈ s, w[i]? = some a
  | i, .nlabel s => ∀ a ∈ s, w[i]? ≠ some a
  | i, .var X => i ∈ U X
  | i, .and φ ψ => φ.Realize w U i ∧ ψ.Realize w U i
  | i, .or φ ψ => φ.Realize w U i ∨ ψ.Realize w U i
  | i, .dia φ => ∃ j, w.succ? i = some j ∧ φ.Realize w U j
  | i, .bdia φ => ∃ j, w.pred? i = some j ∧ φ.Realize w U j

section RealizeSimp

variable {w : WordModel α} {U : Fin n → Set ℕ} {i : ℕ} {s : Finset α} {φ ψ : Formula α n}

@[simp] theorem Formula.realize_tru : (Formula.tru : Formula α n).Realize w U i := trivial

@[simp] theorem Formula.realize_fls : ¬ (Formula.fls : Formula α n).Realize w U i :=
  not_false

@[simp] theorem Formula.realize_initial :
    (Formula.initial : Formula α n).Realize w U i ↔ i = 0 := .rfl

@[simp] theorem Formula.realize_final :
    (Formula.final : Formula α n).Realize w U i ↔ i + 1 = w.length := .rfl

@[simp] theorem Formula.realize_label :
    (Formula.label s : Formula α n).Realize w U i ↔ ∃ a ∈ s, w[i]? = some a := .rfl

@[simp] theorem Formula.realize_nlabel :
    (Formula.nlabel s : Formula α n).Realize w U i ↔ ∀ a ∈ s, w[i]? ≠ some a := .rfl

@[simp] theorem Formula.realize_var {X : Fin n} :
    (Formula.var X : Formula α n).Realize w U i ↔ i ∈ U X := .rfl

@[simp] theorem Formula.realize_and :
    (φ.and ψ).Realize w U i ↔ φ.Realize w U i ∧ ψ.Realize w U i := .rfl

@[simp] theorem Formula.realize_or :
    (φ.or ψ).Realize w U i ↔ φ.Realize w U i ∨ ψ.Realize w U i := .rfl

@[simp] theorem Formula.realize_dia :
    φ.dia.Realize w U i ↔ ∃ j, w.succ? i = some j ∧ φ.Realize w U j := .rfl

@[simp] theorem Formula.realize_bdia :
    φ.bdia.Realize w U i ↔ ∃ j, w.pred? i = some j ∧ φ.Realize w U j := .rfl

end RealizeSimp

instance Formula.instDecidableRealize [DecidableEq α] (w : WordModel α)
    (U : Fin n → Set ℕ) [∀ X, DecidablePred (· ∈ U X)] :
    ∀ (i : ℕ) (φ : Formula α n), Decidable (φ.Realize w U i)
  | _, .tru => .isTrue trivial
  | _, .fls => .isFalse not_false
  | i, .initial => inferInstanceAs (Decidable (i = 0))
  | i, .final => inferInstanceAs (Decidable (i + 1 = w.length))
  | i, .label s => inferInstanceAs (Decidable (∃ a ∈ s, w[i]? = some a))
  | i, .nlabel s => inferInstanceAs (Decidable (∀ a ∈ s, w[i]? ≠ some a))
  | i, .var X => inferInstanceAs (Decidable (i ∈ U X))
  | i, .and φ ψ =>
      @instDecidableAnd _ _ (instDecidableRealize w U i φ) (instDecidableRealize w U i ψ)
  | i, .or φ ψ =>
      @instDecidableOr _ _ (instDecidableRealize w U i φ) (instDecidableRealize w U i ψ)
  | i, .dia φ =>
      match h : w.succ? i with
      | none => .isFalse (by simp [Formula.realize_dia, h])
      | some j =>
          @decidable_of_iff _ _ (by simp [Formula.realize_dia, h])
            (instDecidableRealize w U j φ)
  | i, .bdia φ =>
      match h : w.pred? i with
      | none => .isFalse (by simp [Formula.realize_bdia, h])
      | some j =>
          @decidable_of_iff _ _ (by simp [Formula.realize_bdia, h])
            (instDecidableRealize w U j φ)

/-- Satisfaction is monotone in the valuation: recursion variables occur only
positively. -/
theorem Formula.Realize.mono {w : WordModel α} {U V : Fin n → Set ℕ} (hUV : U ≤ V) :
    ∀ {φ : Formula α n} {i : ℕ}, φ.Realize w U i → φ.Realize w V i
  | .tru, _, h => h
  | .fls, _, h => h
  | .initial, _, h => h
  | .final, _, h => h
  | .label _, _, h => h
  | .nlabel _, _, h => h
  | .var X, _, h => hUV X h
  | .and _ _, _, h => ⟨h.1.mono hUV, h.2.mono hUV⟩
  | .or _ _, _, h => h.imp (·.mono hUV) (·.mono hUV)
  | .dia _, _, ⟨j, hj, h⟩ => ⟨j, hj, h.mono hUV⟩
  | .bdia _, _, ⟨j, hj, h⟩ => ⟨j, hj, h.mono hUV⟩

/-- A vectorial formula: a finite system of equations `Xⱼ = θⱼ` plus a designated
variable. -/
structure System (α : Type*) (n : ℕ) where
  /-- The right-hand side of each equation. -/
  eqs : Fin n → Formula α n
  /-- The designated variable whose satisfaction is the system's. -/
  out : Fin n

namespace System

variable (χ : System α n) (w : WordModel α)

/-- The monotone operator a system induces on valuations (the paper's `F_w^χ`). -/
def op : (Fin n → Set ℕ) →o (Fin n → Set ℕ) where
  toFun U X := {i | (χ.eqs X).Realize w U i}
  monotone' _ _ hUV _ _ h := h.mono hUV

@[simp] theorem mem_op {U : Fin n → Set ℕ} {X : Fin n} {i : ℕ} :
    i ∈ χ.op w U X ↔ (χ.eqs X).Realize w U i := .rfl

/-- The least-fixed-point valuation (Knaster–Tarski). -/
noncomputable def sem : Fin n → Set ℕ := OrderHom.lfp (χ.op w)

/-- `sem` is a fixed point of the system operator. -/
theorem op_sem : χ.op w (χ.sem w) = χ.sem w := (χ.op w).map_lfp

/-- `sem` is below every prefixed point. -/
theorem sem_le {U : Fin n → Set ℕ} (hU : χ.op w U ≤ U) : χ.sem w ≤ U :=
  (χ.op w).lfp_le hU

/-- **Iteration certificate**: an iterate of `⊥` fixed by the operator is `sem`. The
computable route to the least fixed point — no continuity needed. -/
theorem sem_eq_iterate {k : ℕ} (h : χ.op w ((χ.op w)^[k] ⊥) = (χ.op w)^[k] ⊥) :
    χ.sem w = (χ.op w)^[k] ⊥ :=
  OrderHom.lfp_eq_iterate_bot _ h

/-- `w, i ⊨ χ`: the designated variable holds at `i` in the least fixed point. -/
def Sat (i : ℕ) : Prop := i ∈ χ.sem w χ.out

end System

/-- The single BMRS index variable. -/
private abbrev x : Term Unit := .var ()

/-! ### Segments and feature classes

The examples' segments, with the paper's overlapping feature predicates N, V, T as
class tests (a nasalized vowel satisfies both V and N — a partition alphabet cannot
represent the nasalization output, which is why `label` atoms are class tests). -/

/-- Segments occurring in the paper's examples. -/
inductive Seg
  | n | a | o | t | e | b
  deriving DecidableEq, Repr

/-- N: nasal sounds. -/
def nas : Finset Seg := {.n}

/-- V: vowels. -/
def vow : Finset Seg := {.a, .o, .e}

/-- T: voiceless stops (the spreading blocker). -/
def stop : Finset Seg := {.t}

/-- /naote/, the Fig. 4 input. -/
def naote : WordModel Seg := [.n, .a, .o, .t, .e]

/-- /bæn/, the vowel-nasalization input. -/
def baen : WordModel Seg := [.b, .a, .n]

/-! ### Vowel nasalization ((2)–(4)): a vowel nasalizes before a nasal -/

/-- Output predicates of the nasalization program. -/
inductive NasHead
  | V' | N'
  deriving DecidableEq

/-- (3): `V′(x) = V(x)`; `N′(x) = if V(x) then N(s(x)) else N(x)`. -/
def nasalization : Program Seg NasHead
  | .V' => .label vow x
  | .N' => .ite (.label vow x) (.label nas x.succ) (.label nas x)

/-- Fig. 3: on /bæn/ the output columns are V′ = ⊥⊤⊥ and N′ = ⊥⊤⊤ — [bæ̃n], the æ
nasalized by the following n. -/
theorem nasalization_columns :
    ((List.range 3).map fun i => evalFuel nasalization baen 8 i (.call .V' x)) =
        [some false, some true, some false] ∧
      ((List.range 3).map fun i => evalFuel nasalization baen 8 i (.call .N' x)) =
        [some false, some true, some true] := by
  decide

/-- (4): the modal form `N′ = (V ∧ ◇N) ∨ N` — non-recursive, so no fixed point is
involved. -/
def nasalizationChi : System Seg 1 where
  eqs _ := ((Formula.label vow).and (.dia (.label nas))).or (.label nas)
  out := 0

/-- The modal (4) marks exactly positions 1 and 2 of /bæn/ nasal, agreeing with the
BMRS N′ column. -/
theorem nasalizationChi_sat : ∀ i, nasalizationChi.Sat baen i ↔ i = 1 ∨ i = 2 := by
  intro i
  simp only [System.Sat]
  rw [← nasalizationChi.op_sem baen]
  match i with
  | 0 | 1 | 2 => simp [System.mem_op, nasalizationChi, vow, nas, baen, WordModel.succ?]
  | k + 3 =>
    have hnone : baen[k + 3]? = none := List.getElem?_eq_none (by simp [baen])
    simp [System.mem_op, nasalizationChi, vow, nas, hnone,
      WordModel.succ?_eq_some_iff]

/-! ### Warao nasal spreading ((5)–(7)): nasality spreads rightward until a stop -/

/-- The single output predicate of the spreading program. -/
inductive WHead
  | N'
  deriving DecidableEq

/-- (6): `N′(x) = if N(x) then ⊤ else if T(x) then ⊥ else if min(x) then ⊥ else
N′(p(x))` — recursive through the predecessor: spreading is progressive. -/
def warao : Program Seg WHead
  | .N' => .ite (.label nas x) .tru
      (.ite (.label stop x) .fls
        (.ite (.initial x) .fls (.call .N' x.pred)))

/-- Fig. 4: on /naote/ the output column is N′ = ⊤⊤⊤⊥⊥ — [nãõte], spreading blocked by
the t. -/
theorem warao_column :
    ((List.range 5).map fun i => evalFuel warao naote 32 i (.call .N' x)) =
      [some true, some true, some true, some false, some false] := by
  decide

/-- (7): the modal form `N′ = μX.(N ∨ (¬T ∧ ♦X))`. -/
def waraoChi : System Seg 1 where
  eqs _ := (Formula.label nas).or ((Formula.nlabel stop).and (.bdia (.var 0)))
  out := 0

/-- The least fixed point on /naote/: nasality holds exactly at positions 0, 1, 2. -/
abbrev waraoU : Fin 1 → Set ℕ := fun _ => {i | i < 3}

/-- `waraoU` is a prefixed point of the system operator. -/
theorem warao_op_le : waraoChi.op naote waraoU ≤ waraoU := by
  intro X i hi
  obtain rfl : X = 0 := Subsingleton.elim X 0
  simp only [System.mem_op, waraoChi, Formula.realize_or, Formula.realize_and,
    Formula.realize_label, Formula.realize_nlabel, Formula.realize_bdia,
    Formula.realize_var] at hi
  rcases hi with ⟨sg, hsg, hw⟩ | ⟨hT, j, hj, hj3⟩
  · obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hw
    have hlt5 : i < 5 := by simpa [naote] using hlt
    have : i = 0 := by
      interval_cases i <;> simp_all [nas, naote]
    simp [this]
  · rw [WordModel.pred?_eq_some_iff] at hj
    obtain ⟨rfl, hjlen⟩ := hj
    have hj3 : j < 3 := hj3
    rcases Nat.lt_or_ge j 2 with h2 | h2
    · show j + 1 < 3
      omega
    · obtain rfl : j = 2 := by omega
      exact absurd rfl (hT .t (by decide) : naote[3]? ≠ some Seg.t)

/-- The three nasal positions are in the least fixed point (unfolding `op_sem` once per
step of the spread). -/
theorem warao_le_sem : waraoU ≤ waraoChi.sem naote := by
  have hmem : ∀ i, waraoChi.sem naote 0 i =
      (waraoChi.eqs 0).Realize naote (waraoChi.sem naote) i := fun i =>
    congrFun (congrFun (waraoChi.op_sem naote).symm 0) i
  have h0 : 0 ∈ waraoChi.sem naote 0 := by
    show waraoChi.sem naote 0 0
    rw [hmem]
    exact Or.inl ⟨.n, by decide, rfl⟩
  have h1 : 1 ∈ waraoChi.sem naote 0 := by
    show waraoChi.sem naote 0 1
    rw [hmem]
    exact Or.inr ⟨show ∀ sg ∈ stop, naote[1]? ≠ some sg by decide, 0, by decide, h0⟩
  have h2 : 2 ∈ waraoChi.sem naote 0 := by
    show waraoChi.sem naote 0 2
    rw [hmem]
    exact Or.inr ⟨show ∀ sg ∈ stop, naote[2]? ≠ some sg by decide, 1, by decide, h1⟩
  intro X i hi
  obtain rfl : X = 0 := Subsingleton.elim X 0
  have hi3 : i < 3 := hi
  interval_cases i
  exacts [h0, h1, h2]

/-- The modal semantics on /naote/, exactly. -/
theorem warao_sem : waraoChi.sem naote = waraoU :=
  le_antisymm (waraoChi.sem_le naote warao_op_le) warao_le_sem

/-- Fig. 5: the modal (7) marks exactly positions 0, 1, 2 of /naote/. -/
theorem warao_sat {i : ℕ} : waraoChi.Sat naote i ↔ i < 3 := by
  rw [System.Sat, warao_sem]
  exact Iff.rfl

/-- **Fig. 4/5 agreement**: the BMRS program (6) and the modal formula (7) compute the
same nasality column on /naote/. -/
theorem warao_agreement (i : ℕ) (hi : i < 5) :
    evalFuel warao naote 32 i (.call .N' x) = some true ↔ waraoChi.Sat naote i := by
  rw [warao_sat]
  interval_cases i <;> decide

/-! ### The translation (Def. 6) and its compositionality (Remark 7) -/

/-- Def. 6: translate a vectorial modal formula into a BMRS expression whose rule heads
are the recursion variables. Modalities substitute a moved term into the translated
body; class-negated atoms translate by (3.8)-negation (the evident extension of the
paper's clauses, which cover positive atoms). -/
def tr : Formula α n → Expr α (Fin n)
  | .tru => .tru
  | .fls => .fls
  | .initial => .initial x
  | .final => .final x
  | .label s => .label s x
  | .nlabel s => .ite (.label s x) .fls .tru
  | .var X => .call X x
  | .and φ ψ => .ite (tr φ) (tr ψ) .fls
  | .or φ ψ => .ite (tr φ) .tru (tr ψ)
  | .dia φ => .ite (.final x) .fls ((tr φ).subst x.succ)
  | .bdia φ => .ite (.initial x) .fls ((tr φ).subst x.pred)

/-- The translated program of a system: one rule per recursion variable. -/
def System.trProgram (χ : System α n) : Program α (Fin n) := fun X => tr (χ.eqs X)

/-- **Remark 7** (compositionality of the translation): wherever rule-head calls agree
with the recursion variables, `tr φ` evaluates to the truth value of `φ`. Thm. 8's
SCC induction discharges the hypothesis for directed systems. -/
theorem eval_tr [DecidableEq α] {P : Program α (Fin n)} {w : WordModel α}
    {U : Fin n → Set ℕ} [∀ X, DecidablePred (· ∈ U X)]
    (hcall : ∀ X, ∀ j < w.length, Eval P w j (.call X x) (decide (j ∈ U X)))
    (φ : Formula α n) :
    ∀ {i : ℕ}, i < w.length → Eval P w i (tr φ) (decide (φ.Realize w U i)) := by
  induction φ with
  | tru =>
    intro i hi
    rw [decide_eq_true Formula.realize_tru]
    exact .tru
  | fls =>
    intro i hi
    rw [decide_eq_false Formula.realize_fls]
    exact .fls
  | initial =>
    intro i hi
    by_cases h : i = 0
    · subst h
      rw [decide_eq_true (Formula.realize_initial.mpr rfl)]
      exact .initial_true (by rw [tden_var hi])
    · rw [decide_eq_false (h ∘ Formula.realize_initial.mp)]
      exact .initial_false (tden_var hi) (by omega)
  | final =>
    intro i hi
    by_cases h : i + 1 = w.length
    · rw [decide_eq_true (Formula.realize_final.mpr h)]
      exact .final_true (by rw [tden_var hi]; congr 1; omega)
    · rw [decide_eq_false (h ∘ Formula.realize_final.mp)]
      exact .final_false (tden_var hi) (by omega)
  | label s =>
    intro i hi
    by_cases h : ∃ a ∈ s, w[i]? = some a
    · rw [decide_eq_true (Formula.realize_label.mpr h)]
      obtain ⟨a, has, ha⟩ := h
      exact .label_true (tden_var hi) ha has
    · rw [decide_eq_false (h ∘ Formula.realize_label.mp)]
      have hw : w[i]? = some (w[i]'hi) := List.getElem?_eq_getElem hi
      exact .label_false (tden_var hi) hw fun has => h ⟨_, has, hw⟩
  | nlabel s =>
    intro i hi
    by_cases h : ∃ a ∈ s, w[i]? = some a
    · obtain ⟨a, has, ha⟩ := h
      rw [decide_eq_false fun hall => hall a has ha]
      exact .ite_true (.label_true (tden_var hi) ha has) .fls
    · rw [decide_eq_true (p := (Formula.nlabel s).Realize w U i)
        fun a has ha => h ⟨a, has, ha⟩]
      have hw : w[i]? = some (w[i]'hi) := List.getElem?_eq_getElem hi
      exact .ite_false (.label_false (tden_var hi) hw fun has => h ⟨_, has, hw⟩) .tru
  | var X =>
    intro i hi
    have h := hcall X i hi
    rwa [show decide (i ∈ U X) = decide ((Formula.var X).Realize w U i) from
      decide_eq_decide.mpr Formula.realize_var.symm] at h
  | and φ ψ ihφ ihψ =>
    intro i hi
    by_cases h : φ.Realize w U i
    · rw [show decide ((φ.and ψ).Realize w U i) = decide (ψ.Realize w U i) from
        decide_eq_decide.mpr (by simp [h])]
      exact .ite_true (decide_eq_true h ▸ ihφ hi) (ihψ hi)
    · rw [decide_eq_false fun hc => h hc.1]
      exact .ite_false (decide_eq_false h ▸ ihφ hi) .fls
  | or φ ψ ihφ ihψ =>
    intro i hi
    by_cases h : φ.Realize w U i
    · rw [decide_eq_true (Formula.realize_or.mpr (Or.inl h))]
      exact .ite_true (decide_eq_true h ▸ ihφ hi) .tru
    · rw [show decide ((φ.or ψ).Realize w U i) = decide (ψ.Realize w U i) from
        decide_eq_decide.mpr (by simp [h])]
      exact .ite_false (decide_eq_false h ▸ ihφ hi) (ihψ hi)
  | dia φ ih =>
    intro i hi
    by_cases h : i + 1 = w.length
    · rw [decide_eq_false (by
        simp only [Formula.realize_dia, WordModel.succ?_eq_some_iff]
        rintro ⟨j, ⟨rfl, hj⟩, -⟩
        omega)]
      exact .ite_true (.final_true (by rw [tden_var hi]; congr 1; omega)) .fls
    · have hsucc : i + 1 < w.length := by omega
      rw [show decide (φ.dia.Realize w U i) = decide (φ.Realize w U (i + 1)) from
        decide_eq_decide.mpr (by simp [WordModel.succ?_eq_some_iff, hsucc])]
      exact .ite_false (.final_false (tden_var hi) (by omega))
        (Eval.subst (by rw [tden_succ_var, WordModel.succ?, if_pos hsucc]) (ih hsucc))
  | bdia φ ih =>
    intro i hi
    by_cases h : i = 0
    · subst h
      rw [decide_eq_false (by
        simp only [Formula.realize_bdia, WordModel.pred?_eq_some_iff]
        rintro ⟨j, ⟨hj, -⟩, -⟩
        omega)]
      exact .ite_true (.initial_true (by rw [tden_var hi])) .fls
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j < w.length := by omega
      rw [show decide (φ.bdia.Realize w U (j + 1)) = decide (φ.Realize w U j) from
        decide_eq_decide.mpr (by simp [WordModel.pred?_eq_some_iff, hj])]
      exact .ite_false (.initial_false (tden_var hi) (by omega))
        (Eval.subst (by rw [tden_pred_var hi]; simp [WordModel.pred?, hj]) (ih hj))

/-- Remark 7 run end-to-end on Warao: the translated program agrees with the modal
semantics on /naote/ (`waraoU = waraoChi.sem naote` by `warao_sem`), the rule-head
hypothesis discharged by direct computation — the concrete shape of Thm. 8. -/
theorem warao_tr_agreement (i : ℕ) (hi : i < 5) :
    Eval waraoChi.trProgram naote i (tr (waraoChi.eqs 0))
      (decide ((waraoChi.eqs 0).Realize naote waraoU i)) := by
  refine eval_tr (fun X j hj => ?_) _ hi
  obtain rfl : X = 0 := Subsingleton.elim X 0
  refine evalFuel_sound (n := 32) ?_
  have hj5 : j < 5 := by simpa [naote] using hj
  interval_cases j <;> decide

end YolyanComer2026
