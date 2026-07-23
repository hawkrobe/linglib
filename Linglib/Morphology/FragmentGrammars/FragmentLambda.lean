import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Linglib.Core.Probability.Posterior
import Linglib.Core.Probability.Constructions
import Linglib.Morphology.FragmentGrammars.FragmentGrammar

/-!
# Operational fragment-lambda: a stochastic-lazy unfold sampler

Operational counterpart to `FragmentGrammar.lean`'s joint density
`fg(F; F)` of [odonnell-2015] §3.1.8 (p. 94): the sampler that draws
from that density. The architecture follows the macro-expansion of
[odonnell-2015] §2.3.7 Figure 2.21 — `(fragment-lambda args body) ↦
(PYmem a b (lambda args (if (delay? args) (delay body) body)))` —
mapping each Church construct to a Lean component:

- `(PYmem a b _)` ⤳ `pypDraw` over `PYPState` with `PYM := StateT _ PMF`.
- `(if (delay? args) (delay body) body)` ⤳ `PMF.mix` halt-coin per
  §3.1.8 (p. 92).
- The `(delay body)` thunks ⤳ `LazyTree.fragment` constructor.

The single remaining `sorry` is on `fragmentLambdaDepth_marginalises_to_fg`
— the depth-→-∞ proportionality theorem, documented in detail at the
theorem itself. Probabilistic-fixed-point machinery on ω-CPPOs of
sub-probability measures is the missing infrastructure (mathlib-level
work). All other operational machinery and preservation theorems
(`pypDraw_preserves_wellFormed`, `fragmentLambdaDepth_preserves_wellFormed`)
are real proofs via the `PYM.Preserves` combinator algebra.

[odonnell-2015] §2.3.7, §3.1.8, §3.5.5 (hyperparameters: `a = 0.5`,
`b = 100`, `ψ_B = 50`).
-/

namespace Morphology.FragmentGrammars.Operational

/-! ## Pitman–Yor memoisation state

**Universe note**: types in this file live at `Type` (= `Type 0`) rather than
universe-polymorphic `Type u`. Universe polymorphism is blocked by the use of
`PYM α D Unit` in `modify`'s signature: `Unit : Type 0`, so universe-
polymorphizing `PYM` would require either `PUnit` (Type-polymorphic Unit) or
`ULift` threading throughout. Both are tractable; deferred until a downstream
consumer needs higher-universe support. Linguistic type domains (NTs,
terminals, rules) are all small types so `Type` is sufficient in practice. -/

/-- A Pitman–Yor memoisation slot for one input value. We track:
- `dishes` — the value sampled at the i-th distinct table
- `customerCounts` — how many customers have sat at each table

The lists are kept length-equal by the public API (`empty`, `seatCustomer`,
`addTable`); we don't enforce this as a structural invariant. Per
[odonnell-2015] footnote 14 (p. 60), multiple tables may share a dish,
which is why we keep `dishes` as a list rather than a set or finmap. -/
structure PYPSlot (D : Type) where
  dishes : List D
  customerCounts : List ℕ
  deriving Inhabited

namespace PYPSlot

variable {D : Type}

@[simp] def empty : PYPSlot D := ⟨[], []⟩

/-- Total customers seated at this slot (`N` in the book's notation). -/
@[simp] def numCustomers (s : PYPSlot D) : ℕ := s.customerCounts.sum

/-- Number of occupied tables at this slot (`K` in the book's notation). -/
@[simp] def numTables (s : PYPSlot D) : ℕ := s.dishes.length

/-- Seat one more customer at the existing table indexed by `i`.
Out-of-range indices leave the slot unchanged (`List.set` is a no-op
for out-of-bounds indices, and `getD 0 + 1 = 1` falls back to seating
a customer at a fresh single-element entry — but the `set` no-op means
the new entry is dropped, leaving customerCounts unchanged).

Implemented via `List.set` rather than `List.modify` because mathlib
has a developed membership API for the former (`List.mem_or_eq_of_mem_set`)
that lets us prove `seatCustomer_wellFormed` directly. -/
def seatCustomer (s : PYPSlot D) (i : ℕ) : PYPSlot D :=
  ⟨s.dishes, s.customerCounts.set i ((s.customerCounts[i]?.getD 0) + 1)⟩

/-- Open a fresh table with dish `v` and one initial customer. -/
def addTable (s : PYPSlot D) (v : D) : PYPSlot D :=
  ⟨s.dishes ++ [v], s.customerCounts ++ [1]⟩

@[simp] theorem numTables_addTable (s : PYPSlot D) (v : D) :
    (s.addTable v).numTables = s.numTables + 1 := by
  simp only [numTables, addTable, List.length_append, List.length_singleton]

@[simp] theorem numCustomers_addTable (s : PYPSlot D) (v : D) :
    (s.addTable v).numCustomers = s.numCustomers + 1 := by
  simp only [numCustomers, addTable, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]

@[simp] theorem dishes_addTable (s : PYPSlot D) (v : D) :
    (s.addTable v).dishes = s.dishes ++ [v] := rfl

/-- A `PYPSlot` is **well-formed** when every customer count is positive.
This invariant is *maintained by* (but not *enforced by*) the public API:
`empty` has empty `customerCounts` (vacuous); `addTable` appends `[1]`;
`seatCustomer` increments. Lifted to `PYPState` and used by the sampler
to discharge the otherwise-unreachable atomic-fallback branch in
`slotToFinpartition`. -/
def WellFormed (s : PYPSlot D) : Prop :=
  ∀ c ∈ s.customerCounts, 0 < c

theorem empty_wellFormed : (PYPSlot.empty : PYPSlot D).WellFormed := by
  intro c hc
  simp only [empty, List.not_mem_nil] at hc

theorem addTable_wellFormed {s : PYPSlot D} (h : s.WellFormed) (v : D) :
    (s.addTable v).WellFormed := by
  intro c hc
  simp only [addTable, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact h c hc
  · exact Nat.one_pos

/-- `seatCustomer` preserves wellformedness: each element of the
resulting `customerCounts` is either an unchanged original (positive
by `h`) or the newly-set value `(s.customerCounts[i]?.getD 0) + 1`
(at least 1 since `getD 0 ≥ 0`). -/
theorem seatCustomer_wellFormed {s : PYPSlot D} (h : s.WellFormed) (i : ℕ) :
    (s.seatCustomer i).WellFormed := by
  intro c hc
  -- (s.seatCustomer i).customerCounts = s.customerCounts.set i (newValue)
  -- where newValue = (s.customerCounts[i]?.getD 0) + 1
  show 0 < c
  rcases List.mem_or_eq_of_mem_set hc with h_orig | h_eq
  · exact h c h_orig
  · -- c = (s.customerCounts[i]?.getD 0) + 1 ≥ 0 + 1 = 1 > 0
    rw [h_eq]
    omega

end PYPSlot

/-- Pitman–Yor hyperparameters: discount `a ∈ [0, 1)` and concentration
`b > 0`. [odonnell-2015] §3.5.5 (p. 102) sets `a = 0.5`, `b = 100`.

**Note**: the standard PYP allows `b ≥ -a` (boundary case), including
negative `b` for `a > 0`. We restrict to `0 < b` to (a) match the book's
hyperparameter choice and (b) guarantee the new-table PYP weight
`K·a + b` is strictly positive at `K = 0` — needed as a positivity
witness for `PMF.normalize` via `tsum_ne_zero_iff`. The boundary case can be added
as a separate variant if a consumer needs it. -/
structure PYPHyper where
  discount : ℝ
  concentration : ℝ
  discount_nonneg : 0 ≤ discount
  discount_lt_one : discount < 1
  concentration_pos : 0 < concentration

/-- Global Pitman–Yor memoisation state: per-input slot states (one
"restaurant" per input value) plus shared hyperparameters. -/
structure PYPState (α D : Type) where
  slots : α → PYPSlot D
  hyper : PYPHyper

namespace PYPState

variable {α D : Type}

/-- Empty memoisation state (no customers anywhere). -/
def empty (h : PYPHyper) : PYPState α D :=
  ⟨fun _ => PYPSlot.empty, h⟩

/-- Update the slot at input `x`, leaving all others unchanged. -/
def updateSlot [DecidableEq α] (st : PYPState α D) (x : α) (s : PYPSlot D) :
    PYPState α D :=
  { st with slots := fun y => if y = x then s else st.slots y }

/-- All slots in an empty PYP state are `PYPSlot.empty`. -/
@[simp] theorem empty_slots (h : PYPHyper) (x : α) :
    (PYPState.empty (α := α) (D := D) h).slots x = PYPSlot.empty := rfl

/-- The empty PYP state's hyperparameters are exactly the input. -/
@[simp] theorem empty_hyper (h : PYPHyper) :
    (PYPState.empty (α := α) (D := D) h).hyper = h := rfl

/-- A `PYPState` is **well-formed** when every slot is well-formed. The
sampler's invariant: `pypDraw` and downstream `fragmentLambdaDepth`
preserve this — see `pypDraw_preserves_wellFormed` and
`fragmentLambdaDepth_preserves_wellFormed`. -/
def WellFormed (st : PYPState α D) : Prop :=
  ∀ x, (st.slots x).WellFormed

theorem empty_wellFormed (h : PYPHyper) :
    (PYPState.empty (α := α) (D := D) h).WellFormed := by
  intro x
  exact PYPSlot.empty_wellFormed

theorem updateSlot_wellFormed [DecidableEq α] {st : PYPState α D}
    (h_st : st.WellFormed) {x : α} {newSlot : PYPSlot D} (h_new : newSlot.WellFormed) :
    (st.updateSlot x newSlot).WellFormed := by
  intro y
  show (if y = x then newSlot else st.slots y).WellFormed
  by_cases hy : y = x
  · simp only [hy, if_true]; exact h_new
  · simp only [hy, if_false]; exact h_st y

end PYPState

/-! ## The PYP-memoised stochastic monad

`PYM α D γ` is the type of `γ`-valued stochastic computations whose state
is a Pitman–Yor memoisation table over inputs `α` storing dishes of type `D`.
This is the monad-stack equivalent of the `(PYmem a b _)` wrapper in
[odonnell-2015] Figure 2.21. -/

abbrev PYM (α D γ : Type) := StateT (PYPState α D) PMF γ

namespace PYM

variable {α D γ : Type}

/-- Lift a state-free PMF sample into PYM. -/
noncomputable def liftBase (p : PMF γ) : PYM α D γ :=
  fun st => p.bind (fun v => PMF.pure (v, st))

/-! ### `Preserves` algebra: state-property preservation through PYM combinators

A small algebra for proving that a `PYM` computation preserves a state-level
predicate `P : PYPState α D → Prop`. Closure laws under `pure`, `bind`,
`get`, `liftBase`, `modify`, `dite`, `mapM` let arbitrary `PYM` computations
built from these primitives discharge preservation mechanically.

Used in `pypDraw_preserves_wellFormed` and
`fragmentLambdaDepth_preserves_wellFormed` to discharge the WellFormed
invariant chain. The algebra is general (not tied to WellFormed); promoted
to `Linglib/Core/Probability/PYM.lean` once a second consumer needs it. -/

/-- A PYM computation **preserves** a state-property `P` if every output
state with positive probability satisfies `P`, given the input state does. -/
def Preserves (P : PYPState α D → Prop) (m : PYM α D γ) : Prop :=
  ∀ init, P init → ∀ p ∈ (m init).support, P p.2

namespace Preserves

variable {P : PYPState α D → Prop}

/-- `pure a` doesn't change state, so trivially preserves. -/
protected theorem pure (a : γ) : Preserves P (pure a : PYM α D γ) := by
  intro init h_init p hp
  rw [show (pure a : PYM α D γ) init = PMF.pure (a, init) from rfl,
      PMF.mem_support_pure_iff] at hp
  rw [hp]
  exact h_init

/-- `bind` preserves if both halves do. -/
protected theorem bind {δ : Type} {m : PYM α D γ} {f : γ → PYM α D δ}
    (h_m : Preserves P m) (h_f : ∀ a, Preserves P (f a)) :
    Preserves P (m >>= f) := by
  intro init h_init p hp
  rw [show (m >>= f : PYM α D δ) init = (m init).bind (fun as => f as.1 as.2) from rfl,
      PMF.mem_support_bind_iff] at hp
  obtain ⟨⟨a, s⟩, hs, hp⟩ := hp
  exact h_f a s (h_m init h_init (a, s) hs) p hp

/-- `get` reads state without changing it; preserves trivially. -/
protected theorem get : Preserves P (get : PYM α D (PYPState α D)) := by
  intro init h_init p hp
  rw [show (get : PYM α D (PYPState α D)) init = PMF.pure (init, init) from rfl,
      PMF.mem_support_pure_iff] at hp
  rw [hp]
  exact h_init

/-- `liftBase` doesn't change state (the PMF runs over its own values, state
threads through unchanged); preserves. -/
protected theorem liftBase (q : PMF γ) : Preserves P (PYM.liftBase q : PYM α D γ) := by
  intro init h_init p hp
  unfold liftBase at hp
  rw [PMF.mem_support_bind_iff] at hp
  obtain ⟨v, _, hv⟩ := hp
  rw [PMF.mem_support_pure_iff] at hv
  rw [hv]
  exact h_init

/-- `modify f` preserves `P` if `f` does. -/
protected theorem modify {f : PYPState α D → PYPState α D} (h_f : ∀ s, P s → P (f s)) :
    Preserves P (modify f : PYM α D Unit) := by
  intro init h_init p hp
  rw [show (modify f : PYM α D Unit) init = PMF.pure ((), f init) from rfl,
      PMF.mem_support_pure_iff] at hp
  rw [hp]
  exact h_f init h_init

/-- Dependent `if-then-else` preserves if both branches do. -/
protected theorem dite {c : Prop} [Decidable c]
    {m₁ : c → PYM α D γ} {m₂ : ¬c → PYM α D γ}
    (h₁ : ∀ hc, Preserves P (m₁ hc)) (h₂ : ∀ hc, Preserves P (m₂ hc)) :
    Preserves P (if hc : c then m₁ hc else m₂ hc) := by
  intro init h_init p hp
  by_cases hc : c
  · simp only [hc, dite_true] at hp; exact h₁ hc init h_init p hp
  · simp only [hc, dite_false] at hp; exact h₂ hc init h_init p hp

/-- Non-dependent `if-then-else` preserves if both branches do. -/
protected theorem ite {c : Prop} [Decidable c] {m₁ m₂ : PYM α D γ}
    (h₁ : Preserves P m₁) (h₂ : Preserves P m₂) :
    Preserves P (if c then m₁ else m₂) := by
  intro init h_init p hp
  by_cases hc : c
  · simp only [hc, if_true] at hp; exact h₁ init h_init p hp
  · simp only [hc, if_false] at hp; exact h₂ init h_init p hp

/-- `List.mapM` over a preserves-respecting body preserves `P`. -/
protected theorem mapM {δ : Type} {f : γ → PYM α D δ}
    (h_f : ∀ a, Preserves P (f a)) (l : List γ) :
    Preserves P (l.mapM f) := by
  induction l with
  | nil => rw [List.mapM_nil]; exact Preserves.pure _
  | cons a l' ih =>
    rw [List.mapM_cons]
    exact Preserves.bind (h_f a) (fun _ => Preserves.bind ih (fun _ => Preserves.pure _))

end Preserves

end PYM

/-! ## Pitman–Yor draw

Per [odonnell-2015] §2.3.3.2 (p. 59) and §3.1.6 (p. 89), the
(N+1)-th customer at a slot sits at:

- existing table `i` (1 ≤ i ≤ K) with weight `(yᵢ − a) / (N + b)`
- a fresh new table with weight `(K·a + b) / (N + b)`

where `yᵢ` is the count at table `i`, `N = Σyᵢ`, `K` = number of tables,
`a` = `hyper.discount`, `b` = `hyper.concentration`. -/

/-- Sample from the PYP at slot `x` with base distribution `base`.

Either reuse the dish at an existing table (with the §3.1.6 weights), or
sample a fresh dish from `base` and seat the new customer at a new table.
Both branches update the memo state appropriately.

The base distribution is `PYM`-typed (state-passing) rather than the
usual `PMF`-typed because in fragment-lambda the recursive children of
a fresh sample themselves invoke the memo (via `mem{L^B}` for B≠A in
the §3.1.8 equations). The slots for distinct inputs are independent,
so this state-threading is well-defined; a per-restaurant `PMF` base
would suffice if the children's states were marginalised first.

**Implementation note (exchangeability caveat).** When `base` itself
modifies state (recursive `pypDraw` calls add tables at other slots, or
even at the same slot if grammar recursion revisits `x`), the table
indices change between when this `pypDraw` decides "new table" and when
it actually adds the new dish. Operationally we add to the post-`base`
state. By PYP exchangeability the resulting joint distribution agrees
with a sequential interpretation; a faithful implementation would
either snapshot-then-restore or work in a memo-free `base : α → PMF D`. -/
noncomputable def pypDraw {α D : Type} [DecidableEq α] [Inhabited D]
    (base : α → PYM α D D) (x : α) : PYM α D D := do
  let st ← get
  let slot := st.slots x
  let K := slot.numTables
  let a := st.hyper.discount
  let b := st.hyper.concentration
  -- Per [odonnell-2015] §3.1.6 (p. 89): the (N+1)-th customer chooses
  -- table i (i < K) with weight `(yᵢ - a)`, or a fresh table with weight
  -- `K·a + b` (we omit the shared `(N + b)⁻¹` normaliser since `normalize`
  -- recomputes it).
  let weight : Fin (K + 1) → ENNReal := fun i =>
    if i.val < K then
      ENNReal.ofReal ((slot.customerCounts.getD i.val 0 : ℝ) - a)
    else
      ENNReal.ofReal ((K : ℝ) * a + b)
  -- Positivity witness: the new-table outcome at index `K` has weight
  -- `K·a + b ≥ b > 0` (since `K·a ≥ 0` from `a ≥ 0`, and `b > 0`).
  let new_idx : Fin (K + 1) := ⟨K, Nat.lt_succ_self K⟩
  have h_pos : weight new_idx ≠ 0 := by
    -- weight new_idx unfolds (since new_idx.val = K, condition K < K is false)
    -- to ENNReal.ofReal (K*a + b). Need K*a + b > 0 from a ≥ 0 + b > 0.
    show (if (new_idx : Fin (K+1)).val < K then _ else
           ENNReal.ofReal ((K : ℝ) * a + b)) ≠ 0
    rw [if_neg (Nat.lt_irrefl K)]
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have ha : 0 ≤ a := st.hyper.discount_nonneg
    have hb : 0 < b := st.hyper.concentration_pos
    have h_Ka : 0 ≤ (K : ℝ) * a := mul_nonneg (Nat.cast_nonneg K) ha
    linarith
  have h_finite : ∀ i, weight i ≠ ⊤ := fun i => by
    -- Both branches of weight produce `ENNReal.ofReal _`, which is always finite.
    show (if i.val < K then _ else _) ≠ ⊤
    split <;> exact ENNReal.ofReal_ne_top
  let choice ← PYM.liftBase (PMF.normalize weight
    (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨new_idx, h_pos⟩)
    (ENNReal.tsum_ne_top_of_fintype h_finite))
  if hi : choice.val < K then
    -- Existing table: read the dish at this index, seat one more customer there.
    let dish := slot.dishes.getD choice.val default
    modify (fun s => s.updateSlot x ((s.slots x).seatCustomer choice.val))
    pure dish
  else
    -- New table: invoke base distribution, append fresh dish as a new table.
    -- Note: `base x` may modify state (other slots, possibly same); we add
    -- to post-base state per the exchangeability caveat above.
    let dish ← base x
    modify (fun s => s.updateSlot x ((s.slots x).addTable dish))
    pure dish

/-! ## Lazy partial derivation trees -/

/-- A partial derivation tree under fragment-grammar generation. Three
constructors:

- `terminal t` — a fully-evaluated terminal symbol (the result of `unfold`
  reaching a terminal in [odonnell-2015] Figure 2.7, p. 52).
- `fragment x` — a non-terminal stored as a fragment-leaf: the type-level
  representation of the `(delay body)` thunks of Figure 2.21 (p. 71). When
  the body of `fragment-lambda` flips heads on the halt coin, the result
  at this position is `fragment x` rather than further recursion.
- `branch r x children` — a non-terminal expanded by rule `r`. The rule is
  stored alongside the NT and children so that downstream consumers
  (`samplesToCorpusCounts`) can credit halt-vs-recurse decisions to the
  specific (rule, position) pair, matching [odonnell-2015] §3.1.8's
  rule-indexed beta-binomial structure.

The third type parameter `R` is the rule type — typically
`ContextFreeRule T G.NT` for CFGs, abstract here so the same `LazyTree`
can be used by other generative formalisms (TAG, DM-PCFG variants).

The "complete" tree (no fragment-leaves anywhere) is the result of
forcing all delayed thunks until termination. -/
inductive LazyTree (α β R : Type) where
  | terminal : β → LazyTree α β R
  | fragment : α → LazyTree α β R
  | branch   : R → α → List (LazyTree α β R) → LazyTree α β R
  deriving Inhabited

namespace LazyTree

variable {α β R : Type}

/-- The fragment-leaf frontier: the non-terminals stored as halted
sub-derivations (the "open slots" of a fragment, in [odonnell-2015]
§3.1.8's terminology). -/
def fragmentLeaves : LazyTree α β R → List α
  | .terminal _        => []
  | .fragment x        => [x]
  | .branch _ _ kids   => kids.flatMap fragmentLeaves

/-- The terminal yield: the in-order sequence of terminal symbols
reachable without forcing any fragment-leaf. -/
def yield : LazyTree α β R → List β
  | .terminal t        => [t]
  | .fragment _        => []
  | .branch _ _ kids   => kids.flatMap yield

-- Note: rfl simp lemmas about fragmentLeaves/yield base cases would
-- require those defs to use structural mutual recursion (like
-- `collectHaltCounts`); the current `flatMap` formulation makes Lean
-- compile via WF recursion, opaque to `rfl`. Skipped pending refactor.

end LazyTree

/-! ## fragmentLambda — depth-bounded operational unfold

The depth bound is a structural-recursion device. The mathematically-
intended object is the depth-∞ limit, which terminates almost surely
when the recurse probability is bounded away from 1 (geometric depth).
Formalising the limit requires probabilistic-fixed-point machinery not
yet in mathlib; the bounded version is genuine and ships now.

The structure of [odonnell-2015] §3.1.8 (p. 93) is

```
G^a_FG(d)  = Σ mem{L^A}(s) · ∏ G^root_FG(s'_i)        -- PYP-wrap + recurse on holes
L^A(d)     = Σ θ_r ∏ [ν · G^root_FG + (1-ν) · 1]      -- biased halt-or-recurse
mem{L^A}  ~ PYP(a^A, b^A, L^A)                         -- Pitman-Yor memoization
```

We split this into two co-located functions:

- `stochasticLazyUnfoldDepth` — the un-memoised §2.3.5.2 model (`L^A` with
  children recursing back into the unfold itself, no PYP). This is
  [odonnell-2015] §2.3.5.2's `stochastic-lazy-unfold` (Figure 2.18,
  p. 68) — a recognised standalone sub-model in the book. Fully defined;
  kept here as the reference for the un-memoised model and as a sub-step
  for understanding the §3.1.8 architecture.
- `fragmentLambdaDepth` — the **faithful §3.1.8 model** (`G^FG = mem{L^A}`).
  Each call wraps with `pypDraw`; the inner body recurses on
  `fragmentLambdaDepth` itself for non-terminal children — children's
  draws also consult the memo, faithfully matching §3.1.8's mutual
  recursion. Lean accepts this as structural recursion through the
  `pypDraw` lambda + `mapM` + `if` (the recursive call is on `n`,
  structurally smaller than `n+1`).
-/

variable {α β R : Type} [DecidableEq α]

/-- Depth-bounded **stochastic-lazy unfold** per [odonnell-2015]
§2.3.5.2 (Figure 2.18, p. 68). At each call to non-terminal `x`:

1. **Halt-or-recurse step**: flip the biased coin (§3.1.8 `BINOMIAL(ν)`,
   p. 92). With probability `1 − recurseProb x`, halt and return
   `LazyTree.fragment x`. Otherwise sample a (rule, RHS) pair via
   `recurse x`, recursively expand each non-terminal child at the next-
   smaller depth, map each terminal to `LazyTree.terminal`, and assemble
   `LazyTree.branch rule x kids`.

The rule is stored on the branch so `samplesToCorpusCounts` can credit
halt-vs-recurse decisions to the specific (rule, position) pair —
matching the rule-indexed beta-binomial structure of §3.1.8.

Depth `0` always halts. Pure `PMF` (no PYP memo state) — the un-memoised
sub-model. The PYP-wrapped version is `fragmentLambdaDepth` below. -/
noncomputable def stochasticLazyUnfoldDepth
    (recurse : α → PMF (R × List (α ⊕ β)))
    (recurseProb : α → NNReal)
    (recurseProb_le : ∀ x, recurseProb x ≤ 1) :
    ℕ → α → PMF (LazyTree α β R)
  | 0,     x => PMF.pure (.fragment x)
  | n + 1, x => do
      let coin ← PMF.mix (recurseProb x) (recurseProb_le x) (PMF.pure false) (PMF.pure true)
      if coin then do
        let ⟨rule, rhs⟩ ← recurse x
        let kids ← rhs.mapM (fun
          | .inl nt   => stochasticLazyUnfoldDepth recurse recurseProb recurseProb_le n nt
          | .inr term => PMF.pure (.terminal term))
        PMF.pure (.branch rule x kids)
      else
        PMF.pure (.fragment x)

/-! ### `fragmentLambdaDepth` — the PYP-memoised §3.1.8 model

Wraps each non-terminal call with `pypDraw` so that previously-sampled
partial subtrees at the same non-terminal can be reused; recursive
children calls go back through `fragmentLambdaDepth` itself (PYP-wrapped),
faithfully matching [odonnell-2015] §3.1.8's mutual recursion
`G^FG = mem{L^A}` ↔ `L^A`-body-calls-`G^FG`-on-children.

The inner per-call body is factored as `fragmentLambdaStep` so the
preservation proof can apply combinator lemmas to a function with a
visible name and type; the two presentations are definitionally equal. -/

/-- The inner per-call body of `fragmentLambdaDepth`, factored out and
parameterised by the recursive callback `recur`. Captures the §3.1.8
biased halt-or-recurse step: flip a `BINOMIAL(ν)` coin; if recurse,
sample a (rule, RHS) and recurse on each non-terminal child via `recur`;
if halt, return `LazyTree.fragment y`.

Factoring this out as a named auxiliary makes
`fragmentLambdaDepth_preserves_wellFormed`'s induction proof tractable —
the elaborator can apply combinator lemmas to a function whose name and
type are visible, where it struggles with the inline `do`-block in the
original recursive def. The two presentations are definitionally equal. -/
private noncomputable def fragmentLambdaStep [Inhabited β]
    (recurse : α → PMF (R × List (α ⊕ β)))
    (recurseProb : α → NNReal)
    (recurseProb_le : ∀ x, recurseProb x ≤ 1)
    (recur : α → PYM α (LazyTree α β R) (LazyTree α β R)) :
    α → PYM α (LazyTree α β R) (LazyTree α β R) := fun y => do
  let coin ← PYM.liftBase
    (PMF.mix (recurseProb y) (recurseProb_le y) (PMF.pure false) (PMF.pure true))
  if coin then do
    let ⟨rule, rhs⟩ ← PYM.liftBase (recurse y)
    let kids ← rhs.mapM (fun
      | .inl nt   => recur nt
      | .inr term => pure (.terminal term))
    pure (.branch rule y kids)
  else
    pure (.fragment y)

noncomputable def fragmentLambdaDepth [Inhabited β]
    (recurse : α → PMF (R × List (α ⊕ β)))
    (recurseProb : α → NNReal)
    (recurseProb_le : ∀ x, recurseProb x ≤ 1) :
    ℕ → α → PYM α (LazyTree α β R) (LazyTree α β R)
  | 0,     x => pure (.fragment x)
  | n + 1, x =>
      pypDraw (fragmentLambdaStep recurse recurseProb recurseProb_le
                (fragmentLambdaDepth recurse recurseProb recurseProb_le n)) x

/-! ## Wellformedness preservation -/

/-- `pypDraw` preserves `PYPState.WellFormed`: every state in the support
of the output PMF is wellformed, given a wellformed input state and a
wellformed-preserving base distribution.

The proof would observe that `pypDraw`'s two branches are:
- existing-table: `seatCustomer i` (preserves wellformedness via
  `PYPSlot.seatCustomer_wellFormed`)
- new-table: `addTable dish` after sampling from `base` (preserves via
  `PYPSlot.addTable_wellFormed` + base's preservation hypothesis)

Combined with `PYPState.updateSlot_wellFormed`, both branches yield a
wellformed state. The PMF support is contained in the union of these
branches' images, so all output states are wellformed.

**Status: sorry**. As of `0.230.519`'s seatCustomer-discharge iteration,
the slot-level lemmas (`seatCustomer_wellFormed`, `addTable_wellFormed`)
are real proofs. The remaining obstacle is PMF.support reasoning through
the do-block: `pypDraw` is a chain of binds, and the support of a bind
is `{b | ∃ a ∈ p.support, b ∈ (f a).support}` (`PMF.mem_support_bind_iff`).
Proving the result via this chain is mechanical (~50-100 LOC) but
requires patient manipulation of `PMF.support_pure`, `support_bind`,
support of `PMF.normalize`, etc. -/
theorem pypDraw_preserves_wellFormed {α D : Type} [DecidableEq α] [Inhabited D]
    (base : α → PYM α D D) (x : α) (init : PYPState α D)
    (h_init : init.WellFormed)
    (h_base : ∀ y init', init'.WellFormed → ∀ p ∈ (base y init').support, p.2.WellFormed)
    : ∀ p ∈ (pypDraw base x init).support, p.2.WellFormed := by
  -- Compose the `PYM.Preserves` combinator algebra: get + liftBase don't
  -- change state; the dite splits on `choice.val < K`; both branches end
  -- with modify (preserving via slot lemmas) + pure.
  have h_pre : PYM.Preserves PYPState.WellFormed (pypDraw base x) := by
    unfold pypDraw
    refine PYM.Preserves.bind PYM.Preserves.get ?_; intro st
    refine PYM.Preserves.bind (PYM.Preserves.liftBase _) ?_; intro choice
    refine PYM.Preserves.dite ?_ ?_
    · -- existing-table branch
      intro _
      refine PYM.Preserves.bind (PYM.Preserves.modify ?_) (fun _ => PYM.Preserves.pure _)
      intro s h_s
      exact PYPState.updateSlot_wellFormed h_s
        (PYPSlot.seatCustomer_wellFormed (h_s x) _)
    · -- new-table branch
      intro _
      refine PYM.Preserves.bind ?_ ?_
      · -- base x preserves wellformedness — `h_base` specialised at x
        intro init' h_init' p' hp'
        exact h_base x init' h_init' p' hp'
      · intro dish
        refine PYM.Preserves.bind (PYM.Preserves.modify ?_) (fun _ => PYM.Preserves.pure _)
        intro s h_s
        exact PYPState.updateSlot_wellFormed h_s
          (PYPSlot.addTable_wellFormed (h_s x) _)
  exact h_pre init h_init

/-- `fragmentLambdaDepth` preserves `PYPState.WellFormed`: every state in
the support of the output PMF is wellformed, given a wellformed input
state. By induction on depth: depth 0 trivially preserves (no state
change, just `pure (.fragment x)`); depth `n+1` via
`pypDraw_preserves_wellFormed` with the inner body's preservation —
which itself follows by IH for non-terminal children's
`fragmentLambdaDepth ... n` calls.

When discharged, this theorem lets `samplesToCorpusCounts` and the
soundness theorem assume input-state wellformedness, which in turn lets
`slotToFinpartition` discharge its atomic-fallback branch via `absurd`
(the branch is unreachable for any state the sampler can produce). -/
theorem fragmentLambdaDepth_preserves_wellFormed
    {α β R : Type} [DecidableEq α] [Inhabited β]
    (recurse : α → PMF (R × List (α ⊕ β)))
    (recurseProb : α → NNReal) (recurseProb_le : ∀ x, recurseProb x ≤ 1)
    (n : ℕ) (start : α) (init : PYPState α (LazyTree α β R))
    (h_init : init.WellFormed) :
    ∀ p ∈ (fragmentLambdaDepth recurse recurseProb recurseProb_le n start init).support,
      p.2.WellFormed := by
  -- Strengthen: prove ∀ k start, Preserves WellFormed (fragmentLambdaDepth ... k start)
  -- by induction on k, then specialise.
  suffices h_pre : ∀ k start',
      PYM.Preserves PYPState.WellFormed
        (fragmentLambdaDepth recurse recurseProb recurseProb_le k start') from
    h_pre n start init h_init
  intro k
  induction k with
  | zero =>
    -- depth 0: fragmentLambdaDepth ... 0 start' = pure (.fragment start')
    intro start'; exact PYM.Preserves.pure _
  | succ k ih =>
    -- depth k+1: fragmentLambdaDepth ... (k+1) start'
    --   = pypDraw (fragmentLambdaStep ... (fragmentLambdaDepth ... k)) start'
    -- Apply pypDraw_preserves_wellFormed; the body is fragmentLambdaStep ... ih
    intro start' init' h_init' p hp
    apply pypDraw_preserves_wellFormed _ start' init' h_init' _ p hp
    -- h_base argument: fragmentLambdaStep ... ih preserves wellformedness
    intro y init'' h_init'' p'' hp''
    -- Build via combinators on fragmentLambdaStep
    have h_step : PYM.Preserves PYPState.WellFormed
        (fragmentLambdaStep recurse recurseProb recurseProb_le
           (fragmentLambdaDepth recurse recurseProb recurseProb_le k) y) := by
      unfold fragmentLambdaStep
      refine PYM.Preserves.bind (PYM.Preserves.liftBase _) ?_; intro coin
      refine PYM.Preserves.ite ?_ ?_
      · -- coin = true branch: liftBase recurse + mapM children + pure branch
        refine PYM.Preserves.bind (PYM.Preserves.liftBase _) ?_; intro ⟨_, rhs⟩
        refine PYM.Preserves.bind ?_ (fun _ => PYM.Preserves.pure _)
        apply PYM.Preserves.mapM
        intro c
        match c with
        | .inl nt => exact ih nt
        | .inr _  => exact PYM.Preserves.pure _
      · -- coin = false branch: pure (LazyTree.fragment y)
        exact PYM.Preserves.pure _
    exact h_step init'' h_init'' p'' hp''

/-! ## Halt-count extraction from samples -/

namespace LazyTree

-- For each branch in the tree, credit `(rule_used, position_in_rule)`
-- with `+1 recurse` if the child at that position is `.branch _ _ _`,
-- `+1 halt` if it is `.fragment _`. `.terminal _` contributes nothing.
-- Recursive contributions from each child subtree are summed in.
-- Defined via mutual recursion to make the recursion structural
-- (avoids WF-recursion opacity in `rfl`-style base-case lemmas).
mutual
/-- See module note above on `collectHaltCounts` semantics. -/
def collectHaltCounts {α β R : Type} [DecidableEq R] :
    LazyTree α β R → R → ℕ → ℕ × ℕ
  | .terminal _,         _, _ => (0, 0)
  | .fragment _,         _, _ => (0, 0)
  | .branch rule _ kids, r, i =>
    let here : ℕ × ℕ :=
      if r = rule then
        match kids[i]? with
        | .some (.branch _ _ _) => (1, 0)
        | .some (.fragment _)   => (0, 1)
        | _                     => (0, 0)
      else (0, 0)
    let from_kids := collectKidsHaltCounts kids r i
    (here.1 + from_kids.1, here.2 + from_kids.2)

/-- List-recursion helper for `collectHaltCounts`. -/
def collectKidsHaltCounts {α β R : Type} [DecidableEq R] :
    List (LazyTree α β R) → R → ℕ → ℕ × ℕ
  | [],      _, _ => (0, 0)
  | k :: ks, r, i =>
    let kc := collectHaltCounts k r i
    let rest := collectKidsHaltCounts ks r i
    (kc.1 + rest.1, kc.2 + rest.2)
end

@[simp] theorem collectHaltCounts_terminal {α β R : Type} [DecidableEq R]
    (t : β) (r : R) (i : ℕ) :
    (LazyTree.terminal t : LazyTree α β R).collectHaltCounts r i = (0, 0) := rfl

@[simp] theorem collectHaltCounts_fragment {α β R : Type} [DecidableEq R]
    (x : α) (r : R) (i : ℕ) :
    (LazyTree.fragment x : LazyTree α β R).collectHaltCounts r i = (0, 0) := rfl

-- Project a `LazyTree α β R` to a `CFGTree β α`. Returns `none` if the tree
-- contains any `.fragment` leaf (incomplete sub-derivation, no CFGTree image).
-- The rule field on `.branch` is dropped — CFGTree records derivations,
-- not which rule produced them.
mutual
/-- See module note above on `toCFGTree?` semantics. -/
def toCFGTree? {α β R : Type} : LazyTree α β R → Option (CFGTree β α)
  | .terminal t      => some (.leaf t)
  | .fragment _      => none
  | .branch _ x kids =>
    match toCFGTreesList kids with
    | some kids' => some (.node x kids')
    | none       => none

/-- List-recursion helper for `toCFGTree?`. -/
def toCFGTreesList {α β R : Type} :
    List (LazyTree α β R) → Option (List (CFGTree β α))
  | []      => some []
  | k :: ks =>
    match toCFGTree? k with
    | some k' =>
      match toCFGTreesList ks with
      | some ks' => some (k' :: ks')
      | none     => none
    | none    => none
end

@[simp] theorem toCFGTree?_terminal {α β R : Type} (t : β) :
    (LazyTree.terminal t : LazyTree α β R).toCFGTree? = some (.leaf t) := rfl

@[simp] theorem toCFGTree?_fragment {α β R : Type} (x : α) :
    (LazyTree.fragment x : LazyTree α β R).toCFGTree?
      = (none : Option (CFGTree β α)) := rfl

end LazyTree

/-! ## Soundness contract -/

variable {T : Type} [DecidableEq T] [Inhabited T]
  {G : ContextFreeGrammar T} [DecidableEq G.NT]

/-- Convert a `PYPSlot` to a sigma-pair `Σ n, OrderedFinpartition n`
suitable for `AdaptorGrammar.TableAssignment`. Three branches:

1. **Empty slot** (`numCustomers = 0`): returns `⟨0, default⟩` directly.
   Preserves the depth-0 lemma's `from rfl` chain (the empty case is
   defeq to `AdaptorGrammar.emptyTables G`'s entry).
2. **Non-empty wellformed slot** (`∀ c ∈ customerCounts, 0 < c`): builds
   a real `Composition s.numCustomers` and projects via the new
   `Composition.toOrderedFinpartition` (in `Linglib/Core/Probability/PitmanYor.lean`).
   The resulting partition faithfully captures the slot's table-grouping
   structure — what `pypFactor` actually depends on for its EPPF value.
3. **Non-empty non-wellformed slot** (a `customerCount` is `0`): falls
   back to `OrderedFinpartition.atomic`. This branch is *unreachable*
   under the sampler's invariant (`pypDraw`'s `addTable` initialises
   counts to `1`, `seatCustomer` increments). The `WellFormed` predicate
   on `PYPSlot` and `PYPState` and the preservation theorems
   `pypDraw_preserves_wellFormed` (proved via `PYM.Preserves` combinator
   algebra) and `fragmentLambdaDepth_preserves_wellFormed` (induction
   sorry'd, sketch in docstring) capture this invariant. When the
   depth-induction is discharged, this branch can be eliminated by taking
   `(_ : init.WellFormed)` as a hypothesis to `slotToFinpartition` and
   discharging the unreachable case via `absurd`.

The `numCustomers = 0` special case is load-bearing: without it, the
`Composition`-built partition for an empty slot is *not* definitionally
equal to `OrderedFinpartition.atomic 0 = default` (both are unique
inhabitants of `OrderedFinpartition 0` modulo `@[ext]`, but the `partSize`
functions are syntactically distinct: one is `(empty composition).blocksFun`,
the other is constant `1`). Splitting on `numCustomers = 0` keeps the
empty branch defeq to the prior shim, preserving the depth-0 lemma. -/
def slotToFinpartition {D : Type} (s : PYPSlot D) :
    Σ n, OrderedFinpartition n :=
  if _h0 : s.numCustomers = 0 then
    ⟨0, default⟩
  else if h : ∀ c ∈ s.customerCounts, 0 < c then
    let comp : Composition s.numCustomers :=
      ⟨s.customerCounts, fun {x} hx => h x hx, rfl⟩
    ⟨s.numCustomers, comp.toOrderedFinpartition⟩
  else
    ⟨s.numCustomers, OrderedFinpartition.atomic s.numCustomers⟩

@[simp] theorem slotToFinpartition_empty {D : Type} :
    slotToFinpartition (PYPSlot.empty : PYPSlot D)
      = ⟨0, default⟩ := rfl

/-- Convenient abbreviation for the corpus-counts triple consumed by
`FragmentGrammar.corpusProbGivenStorage`: derivation multiset + per-NT
table assignment + per-(rule, position) halt counts. -/
abbrev CorpusCounts (T : Type) [DecidableEq T] (G : ContextFreeGrammar T)
    [DecidableEq G.NT] : Type :=
  Multiset (CFGTree T G.NT) × AdaptorGrammar.TableAssignment G ×
  FragmentGrammar.HaltCounts G

/-- Extract corpus-counts triple `(D, Y, Z)` from a completed sample.
Maps a `LazyTree` (with PYP final state) into `CorpusCounts T G`:

- `D : Multiset (CFGTree T G.NT)` — the underlying derivation trees
- `Y : AdaptorGrammar.TableAssignment G` — table-level reuse counts
- `Z : FragmentGrammar.HaltCounts G` — recurse/halt counts per (rule, position)

**Status**:

- `Z` is real (via `LazyTree.collectHaltCounts`).
- `Y` is **faithful for sampler-reachable slots** (via `slotToFinpartition`
  using `Composition.toOrderedFinpartition`): for any slot the sampler
  can produce (where `customerCounts` are all positive — `addTable`
  initialises to `1`, `seatCustomer` increments), the resulting
  `OrderedFinpartition` has the *true* partition structure, and
  `pypFactor` evaluated on it gives its EPPF value. The atomic-fallback
  branch in `slotToFinpartition` is only reached for non-wellformed
  slots (impossible by sampler invariant; future work proves it).
- `D` is real (via `LazyTree.toCFGTree?`): if the tree projects to a complete
  `CFGTree` (no fragment-leaves), `D` is the singleton multiset of that
  derivation; otherwise (`.fragment` somewhere in the tree) `D` is empty —
  incomplete samples contribute no derivation. -/
noncomputable def samplesToCorpusCounts
    (tree : LazyTree G.NT T (ContextFreeRule T G.NT))
    (finalState : PYPState G.NT (LazyTree G.NT T (ContextFreeRule T G.NT))) :
    CorpusCounts T G :=
  (tree.toCFGTree?.elim 0 ({·} : CFGTree T G.NT → Multiset _),
   fun A => slotToFinpartition (finalState.slots A),
   fun r i => tree.collectHaltCounts r i)

/-- Depth-0 base case for the un-memoised unfold: returns
`PMF.pure (.fragment start)`. -/
@[simp] theorem stochasticLazyUnfoldDepth_zero
    (recurse : α → PMF (R × List (α ⊕ β)))
    (recurseProb : α → NNReal) (recurseProb_le : ∀ x, recurseProb x ≤ 1)
    (start : α) :
    stochasticLazyUnfoldDepth recurse recurseProb recurseProb_le 0 start
      = PMF.pure (.fragment start) := rfl
-- Note: `[DecidableEq α]` is included from the section variable but unused
-- here. `omit [DecidableEq α] in @[simp] theorem ...` works in mathlib but
-- triggers an `unexpected token 'omit'` parse error here, possibly due to
-- the `@[simp]` attribute interaction. Linter warning is benign.

/-- Depth-0 base case: the sampler at depth 0 is the trivial state-passing
pure of `LazyTree.fragment start`, with no state changes.

This is genuinely operational content: it pins down what the sampler
*does* at the depth-bound boundary, where every branch halts. Provable
by `rfl` because `pure` in the `PYM = StateT _ PMF` monad reduces
definitionally to `fun st => PMF.pure (·, st)`. -/
@[simp] theorem fragmentLambdaDepth_zero
    [Inhabited β]
    (recurse : α → PMF (R × List (α ⊕ β)))
    (recurseProb : α → NNReal) (recurseProb_le : ∀ x, recurseProb x ≤ 1)
    (start : α) (st : PYPState α (LazyTree α β R)) :
    fragmentLambdaDepth recurse recurseProb recurseProb_le 0 start st
      = PMF.pure (.fragment start, st) := rfl

/-- **Depth-0 soundness corollary**: at depth 0, for the trivial sample
`(LazyTree.fragment start, st)`, the PMF mass equals the §3.1.8 density
at the empty corpus / empty tables / empty halt-counts triple — both
equal to `1`.

A `.fragment` leaf has no branches, so `collectHaltCounts` returns the
zero pair for every `(rule, position)`, making `samplesToCorpusCounts.Z`
extensionally equal to `emptyHaltCounts G`. The depth-0 sample mass is
`1` (PMF.pure), and the empty-corpus density is `1` by
`corpusProbGivenStorage_empty`; equality holds.

This is a *real, fully-proved* slice of the soundness contract. The
general soundness theorem below remains `sorry`-marked. -/
theorem fragmentLambdaDepth_zero_marginalises
    (M : FragmentGrammar G)
    (recurse : G.NT → PMF (ContextFreeRule T G.NT × List (G.NT ⊕ T)))
    (recurseProb : G.NT → NNReal) (recurseProb_le : ∀ x, recurseProb x ≤ 1)
    (hyper : PYPHyper) (start : G.NT) :
    (fragmentLambdaDepth recurse recurseProb recurseProb_le 0 start
        (PYPState.empty hyper))
        ((LazyTree.fragment start : LazyTree G.NT T (ContextFreeRule T G.NT)),
         (PYPState.empty hyper : PYPState G.NT
            (LazyTree G.NT T (ContextFreeRule T G.NT))))
      = ENNReal.ofReal (M.corpusProbGivenStorage
          (samplesToCorpusCounts (.fragment start) (PYPState.empty hyper)).1
          (samplesToCorpusCounts (.fragment start) (PYPState.empty hyper)).2.1
          (samplesToCorpusCounts (.fragment start) (PYPState.empty hyper)).2.2) := by
  -- The Z-component is `fun r i => (0, 0)` — extensionally `emptyHaltCounts`.
  have h_Z : (samplesToCorpusCounts (.fragment start)
                (PYPState.empty hyper : PYPState G.NT
                  (LazyTree G.NT T (ContextFreeRule T G.NT)))).2.2
              = FragmentGrammar.emptyHaltCounts G := by
    funext r i
    simp only [samplesToCorpusCounts, LazyTree.collectHaltCounts_fragment,
               FragmentGrammar.emptyHaltCounts]
  rw [fragmentLambdaDepth_zero]
  show (PMF.pure _) _ = _
  rw [PMF.pure_apply]
  simp only [if_true]
  -- RHS reduces by samplesToCorpusCounts being (0, emptyTables, h_Z's RHS)
  show (1 : ENNReal) = ENNReal.ofReal _
  rw [show (samplesToCorpusCounts (.fragment start)
            (PYPState.empty hyper : PYPState G.NT
              (LazyTree G.NT T (ContextFreeRule T G.NT)))).1 = 0 from rfl,
      show (samplesToCorpusCounts (.fragment start)
            (PYPState.empty hyper : PYPState G.NT
              (LazyTree G.NT T (ContextFreeRule T G.NT)))).2.1
        = AdaptorGrammar.emptyTables G from rfl,
      h_Z, FragmentGrammar.corpusProbGivenStorage_empty,
      ENNReal.ofReal_one]

/-- The **marginal mass** the sampler puts on samples whose extracted
corpus-counts equal `target`. Defined via PMF pushforward (`PMF.map`)
along `samplesToCorpusCounts`, which avoids the function-equality
DecidableEq issue that an explicit `tsum + if-then-else` formulation
would face for `(Multiset × TableAssignment × HaltCounts)`.

The pushforward is `(samplerPMF.map extract) target = ∑' s, μ s · 1[extract s = target]`. -/
noncomputable def marginalAtCounts
    (samplerPMF : PMF (LazyTree G.NT T (ContextFreeRule T G.NT) ×
                       PYPState G.NT (LazyTree G.NT T (ContextFreeRule T G.NT))))
    (target : CorpusCounts T G) : ENNReal :=
  (samplerPMF.map (fun s => samplesToCorpusCounts s.1 s.2)) target

/-- **Soundness contract (general — proportionality form).** The marginal
mass the sampler puts at corpus-counts triple `(D, Y, Z)` is *proportional*
to the §3.1.8 density `M.corpusProbGivenStorage D Y Z`, with the same
proportionality constant for all triples. We express this as a ratio
identity (avoiding the partition function): for any two triples the cross-
products of their marginals and densities agree. This is necessary and
sufficient for the marginal to be a normalised version of the density.

**Why ratios rather than equality with a normaliser.** The natural
formulation `marginal D Y Z = ENNReal.ofReal (density D Y Z) / Z(M)`
requires defining `Z(M) = ∑'_(D,Y,Z) density D Y Z` — a sum over function
spaces (`TableAssignment`, `HaltCounts` are function types). Convergence
of this sum is a real-analysis problem (it sums beta/gamma integrals);
the partition function is essentially the marginal likelihood of the
fragment-grammar model, which is itself an open computational problem
([odonnell-2015] §3.2 introduces an MH sampler precisely because
this constant is intractable). The ratio formulation sidesteps `Z(M)`
entirely and captures the proportionality content directly.

**Why this still requires depth-→-∞.** At any finite depth `n`, the
sampler's marginals are *truncated* — supported only on samples that
halt within `n` recursion steps. The §3.1.8 density is the limiting
distribution; at finite depth the marginals only approximately match.
The proof requires:

1. Showing `(λ n, marginal at depth n) → (λ ε, density-up-to-ε)` (the
   depth-truncated marginals converge to the true §3.1.8 marginals as
   `n → ∞`). Almost-sure halting from `recurseProb x < 1` for all `x`
   gives geometric-tail bounds; pass to the limit via dominated
   convergence on `PMF`.
2. PYP exchangeability to handle the operational sampler's order-of-
   customer-arrival vs the §3.1.8 joint distribution's order-agnostic
   claim (see `pypDraw`'s exchangeability caveat).
3. Identifying the limit's marginal at `(D, Y, Z)` with the §3.1.8
   product formula — induction matching each PYP draw to its AG-factor
   contribution and each biased-coin flip to its beta-binomial-ratio
   contribution to `M.fgFactor`.

Step 1 needs probabilistic-fixed-point machinery for monotone PMF-valued
recursions (Knaster–Tarski / Kleene fixed point on ω-CPPOs of sub-
probability measures) absent from mathlib. The right formal home for
this is mathlib's measure-theory or analysis libraries, not linglib.
Steps 2 and 3 are mechanical once Step 1 is in place. -/
theorem fragmentLambdaDepth_marginalises_to_fg
    (M : FragmentGrammar G)
    (recurse : G.NT → PMF (ContextFreeRule T G.NT × List (G.NT ⊕ T)))
    (recurseProb : G.NT → NNReal) (recurseProb_le : ∀ x, recurseProb x ≤ 1)
    -- TODO: in a faithful version this is `G.NT → PYPHyper` (per-NT
    -- restaurants per [odonnell-2015] §3.1.7 `pyp : G.NT → PitmanYor`).
    -- The scaffold uses a single global hyper for clarity.
    (hyper : PYPHyper)
    (start : G.NT) (n : ℕ)
    (target target' : CorpusCounts T G) :
    let sampler := fragmentLambdaDepth recurse recurseProb recurseProb_le n start
                     (PYPState.empty hyper)
    marginalAtCounts sampler target *
      ENNReal.ofReal (M.corpusProbGivenStorage target'.1 target'.2.1 target'.2.2)
    = marginalAtCounts sampler target' *
      ENNReal.ofReal (M.corpusProbGivenStorage target.1 target.2.1 target.2.2) := by
  sorry

end Morphology.FragmentGrammars.Operational
