import Mathlib.Data.Set.Functor
import Mathlib.Data.Set.Card
import Linglib.Semantics.Composition.Cont
import Linglib.Data.Examples.Charlow2014

/-!
# Charlow 2014: on the semantics of exceptional scope

This file formalizes the dissertation's account of exceptional scope as side effects taking scope
after evaluation. Dynamic semantics in the stack-based style of [dekker-1994] is refactored as a
monad — `StateT (Stack E) Set`, output stacks of discourse referents plus nondeterminism, the
transformer of [liang-hudak-jones-1995] over `Set` — and scope-taking as the continuation monad
over it ([wadler-1994]), with Lift identified with `monadLift` and Lower with `ContT.eval`. A
scope island is a constituent that must be evaluated: `ContT.reset` ([danvy-filinski-1990])
discharges quantifiers but leaves nondeterministic and state-changing effects intact, so
indefinites, disjunctions ([rooth-partee-1982]), the drefs of proper names and the maximal drefs
of dynamic quantifiers all scope out of islands and feed binding — obeying the Binder Roof
Constraint of [brasoveanu-farkas-2011] — while *every* and *no* do not escape. The paper's
examples are rows in `Data/Examples/Charlow2014.json`, cited from the theorems deriving them.

The grammar is monadic application ([shan-2002]): `combine` sequences its daughters left to
right in any monad, and its per-monad unfoldings are the thesis's application rules — functional,
state-sensitive, nondeterministic ([kratzer-shimoyama-2002]'s rule), and their combinations. The
Identity, Reader, Set, Reader.Set, State and State.Set monads are Lean's `Id`, `ReaderT`, `Set`,
`ReaderT _ Set`, `StateT _ Id` and `StateT _ Set`; the Focus monad — Shan's pointed powerset, for
[rooth-1985]'s alternatives — is defined here with its monad laws. Continuation results are
`Prop`-valued, so "some output is true" is `holds`. Higher-order discourse referents (towers
stored on the stack, Ch. 5.2.4) would need an untyped stack and are not formalised; the stack is
`List E`.

## Main definitions

* `combine` — monadic application, the thesis's overloaded rule of use
* `Stack`, `StateSet`, `indef`, `pro`, `dref`, `holds`, `neg`, `cond`, `det`, `every`, `no` — the
  State.Set fragment
* `Tower`, `liftValue`, `bindShift`, `everyDP`, `noDP`, `eval₂` — scope-takers over it
* `distr`, `or`, `dynGQ` — distributivity, program disjunction, dynamic generalized quantifiers
* `Focus`, `Focus.fmark`, `Focus.only`, `Focus.also` — the pointed-powerset monad
* `ReaderSet` and its fragment — the Reader.Set rival

## Main results

* `combine_bind` — Rebracket: side effects propagate in linear order whatever the bracketing
* `dref_bind`, `bind_pro` — dref introduction and binding in State.Set
* `neg_dref_indef`, `neg_pro`, `cond_dref_indef`, `every_dref_indef` — negation and the operators
  built on it discharge nondeterminism and drefs but not pronouns
* `eval_combine_monadLift` — scopal application subsumes monadic application
* `reset_every`, `reset_indef_every`, `reset_every_indef`, `reset_every_pro` — what survives
  evaluation: indefinites and pronouns, not quantifiers, and not an indefinite an inverse-scoped
  quantifier discharged
* `exceptional_neg`, `exceptional_cond`, `exceptional_feeds_binding`, `brc_derivation` —
  exceptional scope over negation and conditionals, feeding anaphora, and the Binder Roof
  Constraint
* `monadLift_layered`, `indef_visits_indef_layered` — selective exceptional scope via layering
* `name_dref_inverse`, `dynGQ_neg` — name drefs and maximal drefs escape islands
* the `LawfulMonad Focus` instance and `Focus.only_focus_layered` — the Focus monad's laws and
  selective association with focus
* `ReaderSet.run_monadLift` — the reckoning: Reader.Set continuations see the input stack only,
  so the rival hosts exceptional scope but not exceptional binding

## References

* [charlow-2014]
* [dekker-1994]
* [liang-hudak-jones-1995]
* [wadler-1994]
* [danvy-filinski-1990]
* [rooth-partee-1982]
* [rooth-1985]
* [brasoveanu-farkas-2011]
* [schwarz-2001]
* [shan-2002]
* [shan-2004]
* [kratzer-shimoyama-2002]
* [barker-shan-2014]
-/


attribute [local instance] Set.monad

namespace Charlow2014

universe u

/-! ### Monadic application and Rebracket -/

section Monadic

variable {M : Type u → Type u} [Monad M] [LawfulMonad M] {α β γ δ : Type u}

/-- Monadic application over a value-level combination `f`: run `m`, then `n`,
then combine the values. Forward application is `combine (· ·)`, backward
`combine (λ x f => f x)`; the thesis's overloaded `A`. -/
def combine (f : α → β → γ) (m : M α) (n : M β) : M γ :=
  m >>= λ x => n >>= λ y => pure (f x y)

theorem combine_eq_seq (f : α → β → γ) (m : M α) (n : M β) :
    combine f m n = f <$> m <*> n := by
  simp only [combine, seq_eq_bind_map, ← bind_pure_comp, bind_assoc, pure_bind]

/-- Rebracket: sequencing a combined node is sequencing its daughters in linear
order, whatever the bracketing. -/
theorem combine_bind (f : α → β → γ) (m : M α) (n : M β) (k : γ → M δ) :
    combine f m n >>= k = m >>= λ x => n >>= λ y => k (f x y) := by
  simp [combine, bind_assoc]

theorem combine_pure_left (f : α → β → γ) (a : α) (n : M β) :
    combine f (pure a) n = f a <$> n := by
  simp [combine, ← bind_pure_comp]

theorem combine_pure_right (f : α → β → γ) (m : M α) (b : β) :
    combine f m (pure b) = (f · b) <$> m := by
  simp [combine, ← bind_pure_comp]

end Monadic

/-! ### Membership in `StateT σ Set` and `ReaderT σ Set` computations -/

section Membership

variable {σ α β : Type}

@[simp] theorem mem_bind (m : StateT σ Set α) (f : α → StateT σ Set β) (s : σ) (r : β × σ) :
    r ∈ (m >>= f) s ↔ ∃ q ∈ m s, r ∈ f q.1 q.2 := by
  show r ∈ StateT.bind m f s ↔ _
  simp [StateT.bind, Set.bind_def]

@[simp] theorem mem_map (f : α → β) (m : StateT σ Set α) (s : σ) (r : β × σ) :
    r ∈ (f <$> m) s ↔ ∃ q ∈ m s, r = (f q.1, q.2) := by
  simp only [← bind_pure_comp, mem_bind]; rfl

@[simp] theorem mem_pure (a : α) (s : σ) (r : α × σ) :
    r ∈ (pure a : StateT σ Set α) s ↔ r = (a, s) := Iff.rfl

@[simp] theorem mem_bind_reader (m : ReaderT σ Set α) (f : α → ReaderT σ Set β) (s : σ)
    (r : β) : r ∈ (m >>= f) s ↔ ∃ x ∈ m s, r ∈ f x s := by
  show r ∈ ReaderT.bind m f s ↔ _
  simp [ReaderT.bind, Set.bind_def]

@[simp] theorem mem_map_reader (f : α → β) (m : ReaderT σ Set α) (s : σ) (r : β) :
    r ∈ (f <$> m) s ↔ ∃ x ∈ m s, r = f x := by
  simp only [← bind_pure_comp, mem_bind_reader]; rfl

@[simp] theorem mem_pure_reader (a : α) (s : σ) (r : α) :
    r ∈ (pure a : ReaderT σ Set α) s ↔ r = a := Iff.rfl

/-- Truth values are `Prop`s, so a value pinned by a biconditional substitutes
away like one pinned by an equation. -/
@[simp] theorem forall_iff_imp {q : Prop} {P : Prop → Prop} : (∀ p, (p ↔ q) → P p) ↔ P q :=
  ⟨λ h => h q Iff.rfl, λ h _ hp => (propext hp).symm ▸ h⟩

@[simp] theorem exists_iff_and {q : Prop} {P : Prop → Prop} : (∃ p, (p ↔ q) ∧ P p) ↔ P q :=
  ⟨λ ⟨_, hp, h⟩ => propext hp ▸ h, λ h => ⟨q, Iff.rfl, h⟩⟩

end Membership

/-! ### The monads of Chapter 2

Application in each monad (Facts 2.2–2.5, 2.8, 2.11): functional application,
state-sensitive (`SSA`), nondeterministic (`NA`), state-sensitive
nondeterministic (`SSNA`, the rule of [kratzer-shimoyama-2002]), stateful, and
stateful nondeterministic application. -/

section Instances

variable {σ α β : Type}

theorem combine_id (f : α → β → σ) (m : Id α) (n : Id β) : combine f m n = f m n := rfl

theorem combine_readerT (f : α → β → σ) (m : ReaderT σ Id α) (n : ReaderT σ Id β) :
    combine f m n = λ s => f (m s) (n s) := rfl

theorem combine_set (f : α → β → σ) (m : Set α) (n : Set β) :
    combine f m n = {c | ∃ x ∈ m, ∃ y ∈ n, c = f x y} := by
  ext; simp [combine, Set.bind_def]

theorem combine_readerT_set (f : α → β → σ) (m : ReaderT σ Set α) (n : ReaderT σ Set β) :
    combine f m n = λ s => {c | ∃ x ∈ m s, ∃ y ∈ n s, c = f x y} := by
  funext s; ext; simp [combine]

theorem combine_stateT (f : α → β → σ) (m : StateT σ Id α) (n : StateT σ Id β) :
    combine f m n = λ s => ((f (m s).1 (n (m s).2).1), (n (m s).2).2) := rfl

theorem combine_stateT_set (f : α → β → σ) (m : StateT σ Set α) (n : StateT σ Set β) :
    combine f m n = λ s => {c | ∃ x ∈ m s, ∃ y ∈ n x.2, c = (f x.1 y.1, y.2)} := by
  funext s; ext; simp [combine]

end Instances

/-! ### Stacks and the State.Set monad

Discourse referents live on a stack; pronouns retrieve the most recent one
(`List.getLast?`). A sentence denotes a `StateSet E Prop`: from an input stack
to a set of value–output-stack pairs. -/

/-- The reference stack: drefs in order of introduction. -/
abbrev Stack (E : Type) := List E

/-- The State.Set monad: `StateT` over the `Set` monad. -/
abbrev StateSet (E : Type) := StateT (Stack E) Set

variable {E α β : Type}

/-- An indefinite: a nondeterministic individual satisfying `P`, stack unchanged. -/
def indef (P : E → Prop) : StateSet E E := λ s => {q | P q.1 ∧ q.2 = s}

/-- A pronoun: the topical (most recent) dref, stack unchanged. -/
def pro : StateSet E E := λ s => {q | s.getLast? = some q.1 ∧ q.2 = s}

/-- Dref introduction: run `m` and push its value onto the stack. -/
def dref (m : StateSet E E) : StateSet E E := m >>= λ a s => {(a, s ++ [a])}

/-- A dynamic proposition holds at `s` when some output carries a true value. -/
def holds (m : StateSet E Prop) (s : Stack E) : Prop := ∃ q ∈ m s, q.1

/-- Dynamic negation: a test on the input stack, returning it unchanged. -/
def neg (m : StateSet E Prop) : StateSet E Prop := λ s => {(¬ holds m s, s)}

/-- The conditional, from negation via `p → q ↔ ¬(p ∧ ¬q)`. -/
def cond (m n : StateSet E Prop) : StateSet E Prop :=
  neg (m >>= λ p => neg n >>= λ q => pure (p ∧ q))

/-- The indefinite determiner: the individuals whose restrictor holds, with the
restrictor's output stacks. -/
def det (c : E → StateSet E Prop) : StateSet E E :=
  λ s => {q | ∃ p, (p, q.2) ∈ c q.1 s ∧ p}

/-- `every`: `∀x. P x ⇒ Q x ↔ ¬∃x. P x ∧ ¬Q x`, a scope-taker over dynamic
properties. -/
def every (c : E → StateSet E Prop) (k : E → StateSet E Prop) : StateSet E Prop :=
  neg (det c >>= λ x => neg (k x))

/-- `no`: `every` without the inner negation. -/
def no (c : E → StateSet E Prop) (k : E → StateSet E Prop) : StateSet E Prop :=
  neg (det c >>= k)

@[simp] theorem pure_apply (a : α) (s : Stack E) : (pure a : StateSet E α) s = {(a, s)} := rfl

@[simp] theorem mem_indef (P : E → Prop) (s : Stack E) (q : E × Stack E) :
    q ∈ indef P s ↔ P q.1 ∧ q.2 = s := Iff.rfl

@[simp] theorem mem_pro (s : Stack E) (q : E × Stack E) :
    q ∈ pro s ↔ s.getLast? = some q.1 ∧ q.2 = s := Iff.rfl

@[simp] theorem mem_dref (m : StateSet E E) (s : Stack E) (q : E × Stack E) :
    q ∈ dref m s ↔ ∃ r ∈ m s, q = (r.1, r.2 ++ [r.1]) := by simp [dref]

@[simp] theorem neg_apply (m : StateSet E Prop) (s : Stack E) :
    neg m s = {(¬ holds m s, s)} := rfl

@[simp] theorem mem_det (c : E → StateSet E Prop) (s : Stack E) (q : E × Stack E) :
    q ∈ det c s ↔ ∃ p, (p, q.2) ∈ c q.1 s ∧ p := Iff.rfl

@[simp] theorem holds_pure (p : Prop) (s : Stack E) : holds (pure p) s ↔ p := by simp [holds]

@[simp] theorem holds_bind (m : StateSet E α) (k : α → StateSet E Prop) (s : Stack E) :
    holds (m >>= k) s ↔ ∃ q ∈ m s, holds (k q.1) q.2 := by
  simp only [holds, mem_bind]
  exact ⟨λ ⟨r, ⟨q, hq, hr⟩, h⟩ => ⟨q, hq, r, hr, h⟩, λ ⟨q, hq, r, hr, h⟩ => ⟨r, ⟨q, hq, hr⟩, h⟩⟩

@[simp] theorem holds_map (f : α → Prop) (m : StateSet E α) (s : Stack E) :
    holds (f <$> m) s ↔ ∃ q ∈ m s, f q.1 := by
  simp only [holds, mem_map]
  exact ⟨λ ⟨_, ⟨q, hq, rfl⟩, h⟩ => ⟨q, hq, h⟩, λ ⟨q, hq, h⟩ => ⟨_, ⟨q, hq, rfl⟩, h⟩⟩

@[simp] theorem holds_neg (m : StateSet E Prop) (s : Stack E) : holds (neg m) s ↔ ¬ holds m s := by
  simp [holds]

@[simp] theorem det_pure (P : E → Prop) : det (λ x => pure (P x)) = indef P := by
  funext s; ext ⟨x, s'⟩
  exact ⟨λ ⟨_, hp, h⟩ => by cases hp; exact ⟨h, rfl⟩, λ ⟨h, hs⟩ => ⟨_, by rw [mem_pure, hs], h⟩⟩

/-- Dref introduction simplifies away (Fact 2.12): what follows sees the stack
extended with the value. -/
theorem dref_bind (m : StateSet E E) (π : E → StateSet E α) :
    dref m >>= π = m >>= λ a s => π a (s ++ [a]) := by
  funext s; ext q; simp

/-- Binding (Fact 2.13): a pronoun in the immediate scope of a dref-introducing
program evaluates to that program's value. -/
theorem bind_pro (m : StateSet E E) (π : E → E → StateSet E α) :
    (dref m >>= λ ν => pro >>= λ u => π ν u) = dref m >>= λ ν => π ν ν := by
  funext s; ext q; simp

/-- A man met Polly: a nondeterministic man on the output stack. -/
theorem indef_met_name (man : E → Prop) (met : E → E → Prop) (p : E) :
    combine (λ x f => f x) (dref (indef man)) (combine (· ·) (pure met) (pure p)) =
      λ s => {q | ∃ x, man x ∧ q = (met p x, s ++ [x])} := by
  funext s; ext q; simp [combine]

/-- A man left; he was tired — cross-sentential binding with static conjunction. -/
theorem indef_left_pro_tired (man left tired : E → Prop) :
    combine (λ x f => f x) (combine (λ x f => f x) (dref (indef man)) (pure left))
      (combine (· ·) (pure λ q p => p ∧ q) (combine (λ x f => f x) pro (pure tired))) =
      dref (indef man) >>= λ x => pure (left x ∧ tired x) := by
  funext s; ext q; simp [combine]

/-! ### Dynamically closed operators -/

/-- It's false that a linguist left (Fact 3.2): negation discharges the
indefinite's nondeterminism and dref. -/
theorem neg_dref_indef (ling left : E → Prop) :
    neg (dref (indef ling) >>= λ x => pure (left x)) = pure (¬ ∃ x, ling x ∧ left x) := by
  funext s; simp

/-- Pronouns and negation (Fact 3.3): negation is not closed for anaphoric
sensitivity. -/
theorem neg_pro (m : E → StateSet E Prop) {s : Stack E} (h : s ≠ []) :
    neg (pro >>= m) s = (pro >>= λ x => neg (m x)) s := by
  have := List.getLast?_eq_some_getLast h
  ext q; simp [this]

/-- If someone walked, she ran (Fact 3.4): donkey binding into the consequent,
and the conditional is closed. -/
theorem cond_dref_indef (P w r : E → Prop) :
    cond (dref (indef P) >>= λ x => pure (w x)) (pro >>= λ y => pure (r y)) =
      pure (∀ x, P x → w x → r x) := by
  funext s; simp [cond]

/-- Every linguist met a historian (Fact 3.5). -/
theorem every_dref_indef (ling hist : E → Prop) (met : E → E → Prop) :
    every (λ x => pure (ling x)) (λ x => dref (indef hist) >>= λ y => pure (met y x)) =
      pure (∀ x, ling x → ∃ y, hist y ∧ met y x) := by
  funext s; simp [every]

/-- Every linguist rubbed her head (Fact 3.6): in-scope binding via the
quantified-over individual's dref, then discarded. -/
theorem every_dref_pro (ling : E → Prop) (rubbed : E → E → Prop) (head : E → E) :
    every (λ x => pure (ling x))
        (λ x => dref (pure x) >>= λ ν => pro >>= λ y => pure (rubbed (head y) ν)) =
      pure (∀ x, ling x → rubbed (head x) x) := by
  funext s; simp [every]

/-! ### Continuations over the State.Set monad

A tower `ContT β (StateSet E) α` returns an `α` in a computation of type
`StateSet E β`. `monadLift` is monadic Lift (`m ↑ = (m >>= ·)`), `ContT.eval`
Lower (application to `pure`), scopal application is `combine` in `ContT`. -/

/-- Towers: scope-takers over State.Set programs. -/
abbrev Tower (E β α : Type) := ContT β (StateSet E) α

/-- Scopal application is continuation-monadic application (Fact 3.7). -/
theorem combine_contT {ρ : Type} {M : Type → Type} [Monad M] {α β γ : Type} (f : α → β → γ)
    (m : ContT ρ M α) (n : ContT ρ M β) :
    combine f m n = λ k => m.run λ x => n.run λ y => k (f x y) := rfl

/-- Lift into the continuation monad over `Id` is the Montague lift. -/
theorem monadLift_id {ρ α : Type} (a : Id α) : (monadLift a : ContT ρ Id α) = λ k => k a := rfl

/-- Polly saw every linguist, statically: a generalized quantifier in object
position composes by scopal application and Lower discharges it. -/
theorem static_every {ling : E → Prop} (saw : E → E → Prop) (p : E) :
    ContT.eval (combine (λ x f => f x) (pure p : ContT Prop Id E)
      (combine (· ·) (pure saw) (λ k => ∀ x, ling x → k x))) =
      ∀ x, ling x → saw x p := rfl

/-- Scopal application subsumes monadic application (Fact 3.14): lifting,
combining, and lowering is combining in the underlying monad. -/
theorem eval_combine_monadLift {M : Type u → Type u} [Monad M] [LawfulMonad M]
    {α β γ : Type u} (f : α → β → γ) (m : M α) (n : M β) :
    ContT.eval (combine f (monadLift m : ContT γ M α) (monadLift n)) = combine f m n := by
  simp [combine, ContT.eval, Function.comp_def]

/-- A value coerced into a trivial program and lifted (Def. 2.9 with Lift):
`(liftValue a).run k = k a`, the Montague lift again (3.20). -/
def liftValue (a : α) : Tower E β α := monadLift (pure a : StateSet E α)

@[simp] theorem run_liftValue (a : α) (k : α → StateSet E β) : (liftValue a).run k = k a := by
  simp [liftValue]

/-- Universal DPs as scope-takers (Table 3.1). -/
def everyDP (P : E → Prop) : Tower E Prop E := every λ x => (pure (P x) : StateSet E Prop)

/-- Negative DPs as scope-takers (Table 3.1). -/
def noDP (P : E → Prop) : Tower E Prop E := no λ x => (pure (P x) : StateSet E Prop)

@[simp] theorem run_everyDP (P : E → Prop) (k : E → StateSet E Prop) :
    (everyDP P).run k = neg (indef P >>= λ x => neg (k x)) := by
  simp [everyDP, every, ContT.run]

@[simp] theorem run_noDP (P : E → Prop) (k : E → StateSet E Prop) :
    (noDP P).run k = neg (indef P >>= k) := by
  simp [noDP, no, ContT.run]

/-- John saw a linguist (3.23): the indefinite's nondeterminism survives Lower. -/
theorem name_saw_indef (j : E) (saw : E → E → Prop) (ling : E → Prop) :
    ContT.eval (combine (λ x f => f x) (liftValue j : Tower E Prop E)
      (combine (· ·) (liftValue saw) (monadLift (indef ling)))) =
      indef ling >>= λ x => pure (saw x j) := by
  funext s; ext q; simp [combine, ContT.eval]

/-- A man saw every linguist, surface scope (3.24): the universal is trapped in
the indefinite's scope. -/
theorem indef_saw_every (man ling : E → Prop) (saw : E → E → Prop) :
    ContT.eval (combine (λ x f => f x) (monadLift (indef man) : Tower E Prop E)
      (combine (· ·) (liftValue saw) (everyDP ling))) =
      indef man >>= λ x => pure (∀ y, ling y → saw y x) := by
  funext s; ext q; simp [combine, ContT.eval]

/-! ### Bind -/

/-- The Bind type-shifter (Def. 3.16): push the tower's value onto the stack
before continuing. -/
def bindShift (m : Tower E β E) : Tower E β E := λ k => m.run λ a => dref (pure a) >>= k

@[simp] theorem run_bindShift (m : Tower E β E) (k : E → StateSet E β) :
    (bindShift m).run k = m.run λ a => dref (pure a) >>= k := rfl

theorem dref_eq_bind (m : StateSet E E) : dref m = m >>= λ a => dref (pure a) := by
  funext s; ext q; simp

/-- Bind on a lifted program is dref introduction (Fact 3.15). -/
@[simp] theorem bindShift_monadLift (m : StateSet E E) :
    bindShift (monadLift m : Tower E β E) = monadLift (dref m) := by
  funext k
  show (monadLift m : Tower E β E).run _ = (monadLift (dref m) : Tower E β E).run k
  rw [ContT.run_monadLift, ContT.run_monadLift, dref_eq_bind, bind_assoc]

@[simp] theorem bindShift_liftValue (a : E) :
    bindShift (liftValue a : Tower E β E) = monadLift (dref (pure a)) :=
  bindShift_monadLift _

/-- DyS correspondence for indefinites (Fact 3.17): a Bind-shifted lifted
indefinite feeds its scope each satisfier with the extended stack. -/
theorem run_bindShift_monadLift_indef (P : E → Prop) (k : E → StateSet E β) :
    (bindShift (monadLift (indef P) : Tower E β E)).run k =
      λ s => ⋃ x, ⋃ (_ : P x), k x (s ++ [x]) := by
  funext s; ext q; simp

/-- DyS correspondence for pronouns (Fact 3.18). -/
theorem run_monadLift_pro (k : E → StateSet E β) :
    (monadLift pro : Tower E β E).run k = λ s => ⋃ x ∈ s.getLast?, k x s := by
  funext s; ext q; simp

/-- John rubbed his head (3.25): binding without coindexation. -/
theorem name_rubbed_pro_head (j : E) (rubbed : E → E → Prop) (head : E → E) :
    ContT.eval (combine (λ x f => f x) (bindShift (liftValue j) : Tower E Prop E)
      (combine (· ·) (liftValue rubbed)
        (combine (λ x f => f x) (monadLift pro) (liftValue head)))) =
      λ s => {(rubbed (head j) j, s ++ [j])} := by
  funext s; ext q; simp [combine, ContT.eval]

/-- John's mom saw him (3.26): binding without surface c-command. -/
theorem name_mom_saw_pro (j : E) (saw : E → E → Prop) (mom : E → E) :
    ContT.eval (combine (λ x f => f x)
      (combine (λ x f => f x) (bindShift (liftValue j) : Tower E Prop E) (liftValue mom))
      (combine (· ·) (liftValue saw) (monadLift pro))) =
      λ s => {(saw j (mom j), s ++ [j])} := by
  funext s; ext q; simp [combine, ContT.eval]

/-! ### Inverse scope

External Lift of a tower is `pure` one level up (Fact 3.19), internal Lift is
`Functor.map pure` (Def. 3.17), three-level combination is `combine` over
`combine` (Def. 3.18), and one-fell-swoop Lower runs the outer tower at
`ContT.eval`. -/

/-- Three-level Lower (Def. 3.19). -/
def eval₂ (m : Tower E β (Tower E β β)) : StateSet E β := m.run ContT.eval

@[simp] theorem eval₂_def (m : Tower E β (Tower E β β)) : eval₂ m = m.run ContT.eval := rfl

/-- A man saw every linguist, inverse scope (3.28): the universal discharges the
indefinite's nondeterminism and dref. -/
theorem every_over_indef (man ling : E → Prop) (saw : E → E → Prop) :
    eval₂ (combine (combine (λ x f => f x))
      (pure (bindShift (monadLift (indef man))) : Tower E Prop (Tower E Prop E))
      (combine (combine (· ·)) (pure (liftValue saw)) (pure <$> everyDP ling))) =
      pure (∀ y, ling y → ∃ x, man x ∧ saw y x) := by
  funext s; ext q; simp [combine, ContT.eval, Function.comp_def]

/-- Every owl that Al saw (3.30): the gap is a pronoun bound by the
determiner's dref, the relative pronoun conjunction. -/
theorem every_owl_that_saw (owl : E → Prop) (saw : E → E → Prop) (a : E)
    (k : E → StateSet E Prop) :
    every (λ x => dref (pure x) >>= λ ν => pro >>= λ y => pure (owl ν ∧ saw y a)) k =
      λ s => {(∀ ν, owl ν ∧ saw ν a → holds (k ν) (s ++ [ν]), s)} := by
  funext s; simp [every, and_assoc]

/-! ### Scope islands and exceptional scope

A scope island is a constituent that must be evaluated (Def. 4.2); evaluating
and re-lifting is `ContT.reset`, and `ContT.reset_monadLift` is Fact 4.1: Reset
is invisible to a lifted program, so whatever survives evaluation keeps taking
scope. A tower whose value is itself a program is finished by lifting the value
and lowering in one fell swoop, `ContT.eval (m >>= monadLift)`. -/

/-- Resetting a linguist left (Fact 4.2): nothing changes — indefinites escape
islands (`Examples.ex4_1a`). -/
theorem reset_indef_left (ling left : E → Prop) :
    ContT.reset (combine (λ x f => f x) (monadLift (indef ling) : Tower E Prop E)
      (liftValue left)) =
      (monadLift (indef ling >>= λ x => pure (left x)) : Tower E Prop Prop) := by
  unfold ContT.reset; congr 1; funext s; ext q; simp [combine, ContT.eval]

/-- Resetting every linguist left (Fact 4.4): the universal is discharged into a
truth condition on the bottom level — quantifiers do not escape
(`Examples.ex4_1b`, `Examples.ex4_1c`). -/
theorem reset_every (ling left : E → Prop) :
    ContT.reset (combine (λ x f => f x) (everyDP ling : Tower E Prop E) (liftValue left)) =
      (liftValue (∀ x, ling x → left x) : Tower E Prop Prop) := by
  unfold ContT.reset liftValue; congr 1; funext s; ext q; simp [combine, ContT.eval]

/-- Resetting a man met every linguist (Fact 4.5): the indefinite's
nondeterminism and dref survive, the universal does not. -/
theorem reset_indef_every (man ling : E → Prop) (met : E → E → Prop) :
    ContT.reset (combine (λ x f => f x) (bindShift (monadLift (indef man)) : Tower E Prop E)
      (combine (· ·) (liftValue met) (everyDP ling))) =
      (monadLift (dref (indef man) >>= λ x => pure (∀ y, ling y → met y x)) :
        Tower E Prop Prop) := by
  unfold ContT.reset; congr 1; funext s; ext q; simp [combine, ContT.eval]

/-- Resetting the inverse-scope reading (Fact 4.6): an indefinite an
inverse-scoped universal discharged cannot be reanimated. -/
theorem reset_every_indef (man ling : E → Prop) (met : E → E → Prop) :
    (monadLift (eval₂ (combine (combine (λ x f => f x))
      (pure (bindShift (monadLift (indef man))) : Tower E Prop (Tower E Prop E))
      (combine (combine (· ·)) (pure (liftValue met)) (pure <$> everyDP ling)))) :
        Tower E Prop Prop) =
      liftValue (∀ y, ling y → ∃ x, man x ∧ met y x) := by
  rw [every_over_indef]; rfl

/-- Resetting every linguist met her (Fact 4.7): the pronoun's stack
sensitivity survives the universal. -/
theorem reset_every_pro (ling : E → Prop) (met : E → E → Prop) (k : Prop → StateSet E α)
    {s : Stack E} (h : s ≠ []) :
    (ContT.reset (combine (λ x f => f x) (everyDP ling : Tower E Prop E)
      (combine (· ·) (liftValue met) (monadLift pro)))).run k s =
      (monadLift (pro >>= λ y => pure (∀ x, ling x → met y x)) : Tower E α Prop).run k s := by
  have := List.getLast?_eq_some_getLast h
  ext q; simp [ContT.reset, combine, ContT.eval, this]

/-- A man met every linguist, and he left (4.7): both sentences are Reset, and
the indefinite binds across them. -/
theorem exceptional_binding (man ling left : E → Prop) (met : E → E → Prop) :
    ContT.eval (combine (λ x f => f x)
      (ContT.reset (combine (λ x f => f x) (bindShift (monadLift (indef man)) : Tower E Prop E)
        (combine (· ·) (liftValue met) (everyDP ling))))
      (combine (· ·) (liftValue λ q p => p ∧ q)
        (ContT.reset (combine (λ x f => f x) (monadLift pro : Tower E Prop E)
          (liftValue left))))) =
      dref (indef man) >>= λ x => pure ((∀ y, ling y → met y x) ∧ left x) := by
  funext s; ext q; simp [combine, ContT.eval, ContT.reset]

/-- Exceptional scope over negation (4.8): after Reset the embedded indefinite's
nondeterminism outscopes `it wasn't the case that`. -/
theorem exceptional_neg (rel ling : E → Prop) (met : E → E → Prop) :
    ContT.eval ((combine (· ·) (liftValue neg : Tower E Prop (StateSet E Prop → StateSet E Prop))
      (pure <$> ContT.reset (combine (λ x f => f x) (monadLift (indef rel) : Tower E Prop E)
        (combine (· ·) (liftValue met) (everyDP ling))))) >>= monadLift) =
      indef rel >>= λ x => pure (¬ ∀ y, ling y → met y x) := by
  funext s; ext q; simp [combine, ContT.eval, ContT.reset]

/-- If a relative of mine dies, I'll be rich (4.9, `Examples.ex4_1a`): `∃ > if`
from a Reset antecedent. -/
theorem exceptional_cond (rel dies : E → Prop) (rich : Prop) :
    ContT.eval ((combine (· ·)
      (combine (· ·) (liftValue (cond (E := E)) : Tower E Prop _)
        (pure <$> ContT.reset (combine (λ x f => f x) (monadLift (indef rel) : Tower E Prop E)
          (liftValue dies))))
      (pure <$> liftValue rich)) >>= monadLift) =
      indef rel >>= λ x => pure (dies x → rich) := by
  funext s; ext q; simp [combine, ContT.eval, ContT.reset, cond]

/-- Exceptional scope feeds binding (4.11): the dref of a relative of mine
escapes the conditional and binds she. -/
theorem exceptional_feeds_binding (rel dies steelMagnate : E → Prop) (rich : Prop) :
    ContT.eval (combine (λ x f => f x)
      (monadLift (ContT.eval ((combine (· ·)
        (combine (· ·) (liftValue (cond (E := E)) : Tower E Prop _)
          (pure <$> ContT.reset (combine (λ x f => f x)
            (bindShift (monadLift (indef rel)) : Tower E Prop E) (liftValue dies))))
        (pure <$> liftValue rich)) >>= monadLift)) : Tower E Prop Prop)
      (combine (· ·) (liftValue λ q p => p ∧ q)
        (ContT.reset (combine (λ x f => f x) (monadLift pro : Tower E Prop E)
          (liftValue steelMagnate))))) =
      dref (indef rel) >>= λ x => pure ((dies x → rich) ∧ steelMagnate x) := by
  funext s; ext q; simp [combine, ContT.eval, ContT.reset, cond]

/-- The Binder Roof Constraint (4.12, `Examples.ex4_4`): giving a paper he wrote
scope over no candidate evaluates the pronoun outside the quantifier's scope. -/
theorem brc_derivation (cand : E → Prop) (paperBy submitted : E → E → Prop) :
    eval₂ (combine (combine (λ x f => f x))
      (pure (bindShift (noDP cand)) : Tower E Prop (Tower E Prop E))
      (combine (combine (· ·)) (pure (liftValue submitted))
        (pure <$> monadLift (pro >>= λ z => indef (paperBy z))))) =
      pro >>= λ z => indef (paperBy z) >>= λ y => pure (¬ ∃ x, cand x ∧ submitted y x) := by
  funext s; ext q; simp [combine, ContT.eval, Function.comp_def]

/-! ### Selective exceptional scope

Two indefinites on one island yield three fully evaluated programs: one
`StateSet E Prop` with the nondeterminism agglomerated, and two
`StateSet E (StateSet E Prop)` layerings. A layered program unfolds back into a
three-level tower after evaluation, so the indefinites scope separately. -/

/-- A persuasive lawyer visits a relative of mine, agglomerated. -/
theorem indef_visits_indef (law rel : E → Prop) (visits : E → E → Prop) :
    ContT.eval (combine (λ x f => f x) (monadLift (indef law) : Tower E Prop E)
      (combine (· ·) (liftValue visits) (monadLift (indef rel)))) =
      indef law >>= λ x => indef rel >>= λ y => pure (visits y x) := by
  funext s; ext q; simp [combine, ContT.eval]

/-- A persuasive lawyer visits a relative of mine, layered with the object
indefinite outermost (4.22), the structure behind `Examples.ex4_18b`. -/
theorem indef_visits_indef_layered (law rel : E → Prop) (visits : E → E → Prop) :
    ContT.eval (ContT.eval <$> combine (combine (λ x f => f x))
      (pure (monadLift (indef law)) : Tower E (StateSet E Prop) (Tower E Prop E))
      (combine (combine (· ·)) (pure (liftValue visits)) (pure <$> monadLift (indef rel)))) =
      indef rel >>= λ y => pure (indef law >>= λ x => pure (visits y x)) := by
  funext s; ext q; simp [combine, ContT.eval, Function.comp_def]

/-- Unfolding a layered program: lifting twice restores the three-level tower. -/
theorem monadLift_layered {M : Type u → Type u} [Monad M] [LawfulMonad M] {ρ α β : Type u}
    (m : M α) (f : α → M β) :
    (monadLift <$> (monadLift (m >>= λ y => pure (f y)) : ContT ρ M (M β)) :
      ContT ρ M (ContT ρ M β)) = λ c => m >>= λ y => c (monadLift (f y)) := by
  funext c
  show ContT.run _ c = _
  simp [ContT.run_map, ContT.run_monadLift, Function.comp_def]

/-! ### Plural indefinites and distributivity

Plural individuals are sets of atoms (Def. 4.3), atoms identified with
singletons. Plural indefinites are nondeterministic like singular ones, so their
existential scope escapes islands, while the distributivity operator is a
scope-taker discharged on evaluation. -/

section Plural

variable {A : Type}

/-- The distributivity operator (Def. 4.5): a tower quantifying over the atoms
of its plural argument. -/
def distr (R : Set A → α) (X : Set A) : Tower (Set A) Prop α :=
  λ k s => {(∀ x ∈ X, holds (k (R {x})) s, s)}

@[simp] theorem run_distr (R : Set A → α) (X : Set A) (k : α → StateSet (Set A) Prop) :
    (distr R X).run k = λ s => {(∀ x ∈ X, holds (k (R {x})) s, s)} := rfl

/-- A guard is standing in front of two buildings, distributive inverse scope
(4.17): guards vary with buildings, and the plural's nondeterminism outscopes
the distributed universal. -/
theorem indef_fronts_two_distr (guard bldgs : Set A → Prop) (fronts : Set A → Set A → Prop) :
    (combine (combine (combine (λ x f => f x)))
      (pure (pure (monadLift (indef guard))) :
        Tower (Set A) Prop (Tower (Set A) Prop (Tower (Set A) Prop (Set A))))
      ((pure <$> ·) <$> (distr fronts <$>
        monadLift (indef λ X => bldgs X ∧ X.ncard = 2)))).run (·.run ContT.eval) =
      indef (λ X => bldgs X ∧ X.ncard = 2) >>= λ Y =>
        pure (∀ y ∈ Y, ∃ x, guard x ∧ fronts {y} x) := by
  funext s; ext q; simp [combine, ContT.eval, Function.comp_def]

end Plural

/-! ### Disjunction

Program disjunction is `<|>` in `StateT _ Set` (Def. 4.6, the union of outputs);
`or` disjoins two scope-takers' results (Def. 4.7). Disjunctions are therefore
nondeterministic programs that survive Reset, bind donkey pronouns, and, being
polymorphic, scope over an operator that scopes over their disjuncts. -/

theorem orElse_apply (m n : StateSet E α) (s : Stack E) : (m <|> n) s = m s ∪ n s := rfl

@[simp] theorem mem_orElse (m n : StateSet E α) (s : Stack E) (q : α × Stack E) :
    q ∈ (m <|> n) s ↔ q ∈ m s ∨ q ∈ n s := Iff.rfl

theorem orElse_bind (m n : StateSet E α) (f : α → StateSet E β) :
    (m <|> n) >>= f = (m >>= f <|> n >>= f) := by
  funext s; ext q; simp [or_and_right, exists_or]

/-- Disjunction of scope-takers (Def. 4.7). -/
def or (m n : Tower E β α) : Tower E β α := λ k => m.run k <|> n.run k

@[simp] theorem run_or (m n : Tower E β α) (k : α → StateSet E β) :
    (or m n).run k = (m.run k <|> n.run k) := rfl

/-- Chomsky or May left (4.27): a dref in nondeterministic superposition. -/
theorem or_names_left (c m : E) (left : E → Prop) :
    ContT.eval (combine (λ x f => f x) (or (bindShift (liftValue c)) (bindShift (liftValue m)))
      (liftValue left : Tower E Prop (E → Prop))) =
      (dref (pure c) <|> dref (pure m)) >>= λ x => pure (left x) := by
  funext s; ext q; simp [combine, ContT.eval]

/-- Whenever I see Alf or hear Cal, I scream his name (4.28): the antecedent
is a proper subpart of each disjunct, and the disjunctive program still hosts
the dref. -/
theorem or_subparts (me a c : E) (see hear : E → E → Prop) :
    ContT.eval (combine (λ x f => f x) (liftValue me : Tower E Prop E)
      (or (combine (λ x f => f x) (bindShift (liftValue a)) (liftValue see))
        (combine (λ x f => f x) (bindShift (liftValue c)) (liftValue hear)))) =
      ((dref (pure a) >>= λ x => pure (see x me)) <|>
        dref (pure c) >>= λ x => pure (hear x me)) := by
  funext s; ext q; simp [combine, ContT.eval]

/-- Disjunction and the BRC (4.29, `Examples.ex4_23a`): disjoining externally
lifted indefinites puts program disjunction above the continuation and the
indefinites below it. -/
theorem or_pure_pure (steak burger : E → Prop) :
    or (pure (monadLift (indef steak)) : Tower E Prop (Tower E Prop E))
      (pure (monadLift (indef burger))) =
      λ c => c (monadLift (indef steak)) <|> c (monadLift (indef burger)) := rfl

/-! ### Drefs of proper names take exceptional scope

Anything Bind-shifted survives evaluation (Fact 1.4, Ch. 5.2), so a proper name
inside an island binds a sloppy pro-form outside it. -/

/-- Everyone thinks BILL will come (5.8, `Examples.ex5_7a`): Bill's dref takes
inverse scope over the dynamically closed `everyone`. -/
theorem name_dref_inverse (person : E → Prop) (thinks : Prop → E → Prop) (come : E → Prop)
    (b : E) :
    eval₂ (combine (combine (λ x f => f x))
      (pure (everyDP person) : Tower E Prop (Tower E Prop E))
      (combine (combine (· ·)) (pure (liftValue thinks))
        (pure <$> combine (λ x f => f x) (bindShift (liftValue b)) (liftValue come)))) =
      dref (pure b) >>= λ y => pure (∀ x, person x → thinks (come y) x) := by
  funext s; ext q; simp [combine, ContT.eval, Function.comp_def]

/-- ... we'll have to invite him: the escaped dref binds the consequent's
pronoun, so replacing BILL by John yields a meaning identical to the
antecedent's — Contrast is satisfiable. -/
theorem name_dref_cond (person : E → Prop) (thinks : Prop → E → Prop) (come invite : E → Prop)
    (b : E) :
    cond (dref (pure b) >>= λ y => pure (∀ x, person x → thinks (come y) x))
      (pro >>= λ z => pure (¬ invite z)) =
      pure ((∀ x, person x → thinks (come b) x) → ¬ invite b) := by
  funext s; simp [cond]

/-! ### Maximal drefs and dynamic generalized quantifiers

A dynamic GQ (Def. 5.3) returns its truth condition and pushes the refset — the
restrictor individuals satisfying the scope — as a plural dref. The stack holds
pluralities; the quantifier ranges over atoms. -/

section DynamicGQ

variable {A : Type}

/-- Dynamic GQ with a maximal refset dref (Def. 5.3). -/
def dynGQ (DET : Set A → Set A → Prop) (M : Set A) : Tower (Set A) Prop A :=
  λ k s => {(DET M {x | x ∈ M ∧ holds (k x) s}, s ++ [{x | x ∈ M ∧ holds (k x) s}])}

@[simp] theorem run_dynGQ (DET : Set A → Set A → Prop) (M : Set A) (k : A → StateSet (Set A) Prop) :
    (dynGQ DET M).run k =
      λ s => {(DET M {x | x ∈ M ∧ holds (k x) s}, s ++ [{x | x ∈ M ∧ holds (k x) s}])} := rfl

/-- Exactly one linguist left (5.19): true iff one linguist left, with the
linguists who left on the stack. -/
theorem dynGQ_left (ling left : Set A) :
    ContT.eval (combine (λ x f => f x) (dynGQ (λ _ N => N.ncard = 1) ling)
      (liftValue (· ∈ left))) =
      dref (pure (ling ∩ left)) >>= λ N => pure (N.ncard = 1) := by
  funext s; ext q; simp [combine, ContT.eval]

/-- Exactly one linguist left; she was tired (5.3.2): she is the maximal dref. -/
theorem dynGQ_pro (ling left : Set A) (tired : Set A → Prop) :
    ContT.eval (combine (λ x f => f x)
      (monadLift (dref (pure (ling ∩ left)) >>= λ N => pure (N.ncard = 1)) :
        Tower (Set A) Prop Prop)
      (combine (· ·) (liftValue λ q p => p ∧ q)
        (combine (λ x f => f x) (monadLift pro) (liftValue tired)))) =
      dref (pure (ling ∩ left)) >>= λ N => pure (N.ncard = 1 ∧ tired N) := by
  funext s; ext q; simp [combine, ContT.eval]

/-- It's absolutely false that no senators admire Cruz (5.24, `Examples.ex5_23`):
negation flips the truth value, and the refset dref survives for they. -/
theorem dynGQ_neg (sen admire : Set A) :
    ContT.eval ((combine (· ·) (liftValue (neg (E := Set A)) : Tower (Set A) Prop _)
      (pure <$> ContT.reset (combine (λ x f => f x) (dynGQ (λ _ N => N = ∅) sen)
        (liftValue (· ∈ admire))))) >>= monadLift) =
      dref (pure (sen ∩ admire)) >>= λ N => pure (¬ N = ∅) := by
  funext s; ext q; simp [combine, ContT.eval, ContT.reset]

end DynamicGQ

/-! ### The Focus monad

Rooth's two-dimensional focus semantics is the pointed-powerset monad
([shan-2002]): a value paired with its alternatives, sequencing the Identity
monad on the first coordinate and the Set monad on the second (Def. 5.6).
F-marking injects a value with its alternatives; `only`/`also` quantify over the
alternatives of a monadic VP (Def. 5.10). Focus effects are managed by scope like
any other, so they survive Reset and can be layered for selective association
across islands. -/

/-- The Focus monad: a value with its alternative set. -/
def Focus (α : Type u) := α × Set α

namespace Focus

instance : Monad Focus where
  pure a := (a, {a})
  bind m k := ((k m.1).1, ⋃ a ∈ m.2, (k a).2)

@[simp] theorem pure_def {α : Type u} (a : α) : (pure a : Focus α) = (a, {a}) := rfl

@[simp] theorem bind_def {α β : Type u} (m : Focus α) (k : α → Focus β) :
    m >>= k = ((k m.1).1, ⋃ a ∈ m.2, (k a).2) := rfl

/-- The monad laws (Appendix B.9). -/
instance : LawfulMonad Focus := LawfulMonad.mk'
  (id_map := λ m => Prod.ext rfl (Set.biUnion_of_singleton _))
  (pure_bind := λ _ _ => Prod.ext rfl (Set.biUnion_singleton _ _))
  (bind_assoc := λ _ _ _ => Prod.ext rfl (by ext; simp))

/-- Application in the Focus monad (Fact 5.4): pointwise on values, `NA` on
alternatives — Rooth's two interpretation functions at once. -/
theorem combine_def {α β γ : Type u} (f : α → β → γ) (m : Focus α) (n : Focus β) :
    combine f m n = (f m.1 n.1, {c | ∃ x ∈ m.2, ∃ y ∈ n.2, c = f x y}) := by
  simp only [combine, bind_def, pure_def]; exact Prod.ext rfl (by ext; simp)

variable {E W : Type}

/-- F-marking (Def. 5.7): a value with its contextual alternatives. -/
def fmark (alt : E → Set E) (a : E) : Focus E := (a, alt a)

/-- `only` (Def. 5.10): the VP's value is the sole true alternative. -/
def only (P : Focus (E → W → Prop)) : E → W → Prop :=
  λ x w => {Q | Q ∈ P.2 ∧ Q x w} = {P.1}

/-- `also` (Def. 5.10): some other alternative is true too. -/
def also (P : Focus (E → W → Prop)) : E → W → Prop :=
  λ x w => {P.1} ⊂ {Q | Q ∈ P.2 ∧ Q x w}

/-- JOHNᶠ left (5.30). -/
theorem fmark_left (alt : E → Set E) (j : E) (left : E → Prop) :
    ContT.eval (combine (λ x f => f x) (monadLift (fmark alt j) : ContT Prop Focus E)
      (monadLift (pure left : Focus (E → Prop)))) = (left j, {p | ∃ x ∈ alt j, p = left x}) := by
  simp [combine, ContT.eval, fmark]; exact Prod.ext rfl (by ext; simp)

/-- Sharon only met JOHNᶠ: association with focus at the VP. -/
theorem only_met_fmark (alt : E → Set E) (j : E) (met : E → E → W → Prop) :
    only (ContT.eval (combine (· ·) (monadLift (pure met : Focus (E → E → W → Prop)) :
        ContT (E → W → Prop) Focus _)
      (monadLift (fmark alt j)))) =
      λ x w => {Q | (∃ y ∈ alt j, Q = met y) ∧ Q x w} = {met j} := by
  funext x w; simp [only, combine, ContT.eval, fmark]

/-- Unselective association (5.4.3): `only` binds both foci in its scope. -/
theorem only_fmark_fmark (alt : E → Set E) (b s : E) (intro : E → E → E → W → Prop) :
    only (ContT.eval (combine (· ·)
      (combine (· ·) (monadLift (pure intro : Focus (E → E → E → W → Prop)) :
          ContT (E → W → Prop) Focus _)
        (monadLift (fmark alt b)))
      (monadLift (fmark alt s)))) =
      λ z w => {Q | (∃ x ∈ alt b, ∃ y ∈ alt s, Q = intro x y) ∧ Q z w} = {intro b s} := by
  funext z w; simp [only, combine, ContT.eval, fmark]

/-- Selective association (5.4.4, `Examples.ex5_27b`): with BILLᶠ externally and
SUEᶠ internally lifted, `only` catches Bill's alternatives at the inner level and
Sue's survive to `also`: `also > SUEᶠ > only > BILLᶠ`. -/
theorem only_focus_layered (alt : E → Set E) (b s : E) (intro : E → E → E → W → Prop) :
    ContT.eval (combine (· ·)
      (monadLift (pure only : Focus (Focus (E → W → Prop) → E → W → Prop)) :
        ContT (E → W → Prop) Focus _)
      (ContT.eval <$> combine (combine (· ·))
        (combine (combine (· ·))
          (pure (monadLift (pure intro : Focus (E → E → E → W → Prop))) :
            ContT (E → W → Prop) Focus (ContT (E → W → Prop) Focus _))
          (pure (monadLift (fmark alt b))))
        (pure <$> monadLift (fmark alt s)))) =
      (only (combine (· ·) (combine (· ·) (pure intro) (fmark alt b)) (pure s)),
        {P | ∃ y ∈ alt s,
          P = only (combine (· ·) (combine (· ·) (pure intro) (fmark alt b)) (pure y))}) := by
  simp [combine, ContT.eval, fmark, Function.comp_def]
  exact Prod.ext rfl (by ext; simp)

/-- Focus effects survive Reset: an instance of `ContT.reset_monadLift`. -/
theorem reset_fmark (alt : E → Set E) (j : E) (left : E → Prop) :
    ContT.reset (combine (λ x f => f x) (monadLift (fmark alt j) : ContT Prop Focus E)
      (monadLift (pure left : Focus (E → Prop)))) =
      (monadLift (fmark alt j >>= λ x => pure (left x)) : ContT Prop Focus Prop) := by
  unfold ContT.reset; congr 1; simp [combine, ContT.eval]

end Focus

/-- Two underlying monads (5.4.5): Focus effects on the top level and State.Set
effects on the second evaluate to a layered `Focus (StateSet E Prop)`. -/
theorem focus_over_stateSet (alt : E → Set E) (p : E) (ling : E → Prop) (met : E → E → Prop) :
    ContT.eval (ContT.eval <$> combine (combine (λ x f => f x))
      (pure (monadLift (indef ling)) : ContT (StateSet E Prop) Focus (Tower E Prop E))
      (combine (combine (· ·)) (pure (liftValue met))
        (pure <$> monadLift (Focus.fmark alt p)))) =
      ((indef ling >>= λ x => pure (met p x),
        {π | ∃ y ∈ alt p, π = indef ling >>= λ x => pure (met y x)}) : Focus _) := by
  simp [combine, ContT.eval, Focus.fmark, Function.comp_def]
  exact Prod.ext rfl (by ext; simp)

/-! ### Alternative semantics: the Reader.Set monad

Swapping `StateT` for `ReaderT` over `Set` gives [kratzer-shimoyama-2002]-style
alternative semantics with scope-managed side effects: indefinites still take
selective exceptional scope, and Bind (Def. 5.21) handles in-scope binding
without the abstraction rule [shan-2004] criticised. But `pure` discards the
stack, so nothing binds out of an island: the account of exceptional scope lives
in the Set monad both share, the account of exceptional binding in State. -/

/-- The Reader.Set monad: `ReaderT` over the `Set` monad. -/
abbrev ReaderSet (E : Type) := ReaderT (Stack E) Set

namespace ReaderSet

variable {E α β : Type}

/-- An indefinite: a nondeterministic individual, insensitive to the stack. -/
def indef (P : E → Prop) : ReaderSet E E := λ _ => {x | P x}

/-- A pronoun: the topical dref. -/
def pro : ReaderSet E E := λ s => {x | s.getLast? = some x}

/-- Some output is true. -/
def holds (m : ReaderSet E Prop) (s : Stack E) : Prop := ∃ p ∈ m s, p

/-- Negation (Def. 5.18). -/
def neg (m : ReaderSet E Prop) : ReaderSet E Prop := λ s => {¬ holds m s}

/-- The universal (Def. 5.19). -/
def everyDP (P : E → Prop) : ContT Prop (ReaderSet E) E :=
  λ k => neg (indef P >>= λ x => neg (k x))

/-- The negative quantifier. -/
def noDP (P : E → Prop) : ContT Prop (ReaderSet E) E := λ k => neg (indef P >>= k)

/-- Bind for Reader.Set towers (Def. 5.21): the continuation reads the
extended stack. -/
def bindShift (m : ContT β (ReaderSet E) E) : ContT β (ReaderSet E) E :=
  λ k => m.run λ a s => k a (s ++ [a])

@[simp] theorem mem_indef (P : E → Prop) (s : Stack E) (x : E) : x ∈ indef P s ↔ P x := Iff.rfl

@[simp] theorem mem_pro (s : Stack E) (x : E) : x ∈ pro s ↔ s.getLast? = some x := Iff.rfl

@[simp] theorem neg_apply (m : ReaderSet E Prop) (s : Stack E) : neg m s = {¬ holds m s} := rfl

@[simp] theorem holds_pure (p : Prop) (s : Stack E) : holds (pure p) s ↔ p := by simp [holds]

@[simp] theorem holds_bind (m : ReaderSet E α) (k : α → ReaderSet E Prop) (s : Stack E) :
    holds (m >>= k) s ↔ ∃ x ∈ m s, holds (k x) s := by
  simp only [holds, mem_bind_reader]
  exact ⟨λ ⟨p, ⟨x, hx, hp⟩, h⟩ => ⟨x, hx, p, hp, h⟩, λ ⟨x, hx, p, hp, h⟩ => ⟨p, ⟨x, hx, hp⟩, h⟩⟩

@[simp] theorem holds_map (f : α → Prop) (m : ReaderSet E α) (s : Stack E) :
    holds (f <$> m) s ↔ ∃ x ∈ m s, f x := by
  simp only [holds, mem_map_reader]
  exact ⟨λ ⟨_, ⟨x, hx, rfl⟩, h⟩ => ⟨x, hx, h⟩, λ ⟨x, hx, h⟩ => ⟨_, ⟨x, hx, rfl⟩, h⟩⟩

@[simp] theorem holds_neg (m : ReaderSet E Prop) (s : Stack E) : holds (neg m) s ↔ ¬ holds m s := by
  simp [holds]

@[simp] theorem run_everyDP (P : E → Prop) (k : E → ReaderSet E Prop) :
    (everyDP P).run k = neg (indef P >>= λ x => neg (k x)) := rfl

@[simp] theorem run_noDP (P : E → Prop) (k : E → ReaderSet E Prop) :
    (noDP P).run k = neg (indef P >>= k) := rfl

@[simp] theorem run_bindShift (m : ContT β (ReaderSet E) E) (k : E → ReaderSet E β) :
    (bindShift m).run k = m.run λ a s => k a (s ++ [a]) := rfl

/-- Resetting a linguist left (Fact 5.7): the indefinite survives. -/
theorem reset_indef_left (ling left : E → Prop) :
    ContT.reset (combine (λ x f => f x) (monadLift (indef ling) : ContT Prop (ReaderSet E) E)
      (monadLift (pure left : ReaderSet E (E → Prop)))) =
      (monadLift (indef ling >>= λ x => pure (left x)) : ContT Prop (ReaderSet E) Prop) := by
  unfold ContT.reset; congr 1; funext s; ext; simp [combine, ContT.eval]

/-- Resetting every linguist left (Fact 5.8): the universal is discharged. -/
theorem reset_every (ling left : E → Prop) :
    ContT.reset (combine (λ x f => f x) (everyDP ling)
      (monadLift (pure left : ReaderSet E (E → Prop)))) =
      (monadLift (pure (∀ x, ling x → left x) : ReaderSet E Prop) :
        ContT Prop (ReaderSet E) Prop) := by
  unfold ContT.reset; congr 1; funext s; ext; simp [combine, ContT.eval]

/-- Layered `M (M Prop)` derivation of a semanticist met a phonologist (Fact 5.9). -/
theorem indef_met_indef_layered (sem phon : E → Prop) (met : E → E → Prop) :
    ContT.eval (ContT.eval (m := ReaderSet E) <$> combine (combine (λ x f => f x))
      (pure (monadLift (indef sem)) :
        ContT (ReaderSet E Prop) (ReaderSet E) (ContT Prop (ReaderSet E) E))
      (combine (combine (· ·)) (pure (monadLift (pure met : ReaderSet E (E → E → Prop))))
        (pure <$> monadLift (indef phon)))) =
      indef phon >>= λ y => pure (indef sem >>= λ x => pure (met y x)) := by
  funext s; ext; simp [combine, ContT.eval, Function.comp_def]

/-- Binding simplification (Fact 5.12): a pronoun read at an extended stack
evaluates to the new dref. -/
theorem bind_pro_append (π : E → ReaderSet E α) (s : Stack E) (a : E) :
    (pro >>= π) (s ++ [a]) = π a (s ++ [a]) := by
  ext; simp

/-- A linguist rubbed his head: in-scope binding via Bind. -/
theorem indef_rubbed_pro_head (ling : E → Prop) (rubbed : E → E → Prop) (head : E → E) :
    ContT.eval (combine (λ x f => f x)
      (bindShift (monadLift (indef ling)) : ContT Prop (ReaderSet E) E)
      (combine (· ·) (monadLift (pure rubbed : ReaderSet E (E → E → Prop)))
        (combine (λ x f => f x) (monadLift pro) (monadLift (pure head : ReaderSet E (E → E)))))) =
      indef ling >>= λ x => pure (rubbed (head x) x) := by
  funext s; ext; simp [combine, ContT.eval]

/-- A man told nobody about a book he wrote, with the object indefinite scoping
over `nobody` and its pronoun bound by the subject: the subject and object
indefinites take the top level, `nobody` the second. -/
theorem indef_told_no_indef_pro (man person : E → Prop) (bookBy : E → E → Prop)
    (told : E → E → E → Prop) :
    (combine (combine (λ x f => f x))
      (pure <$> bindShift (monadLift (indef man)) :
        ContT Prop (ReaderSet E) (ContT Prop (ReaderSet E) E))
      (combine (combine (· ·))
        (pure (combine (· ·) (monadLift (pure told : ReaderSet E (E → E → E → Prop)))
          (noDP person)) : ContT Prop (ReaderSet E) (ContT Prop (ReaderSet E) (E → E → Prop)))
        (pure <$> monadLift (pro >>= λ u => indef (bookBy u))))).run ContT.eval =
      indef man >>= λ x => indef (bookBy x) >>= λ z =>
        pure (¬ ∃ y, person y ∧ told y z x) := by
  funext s; ext; simp [combine, ContT.eval, Function.comp_def]

/-- The reckoning (5.5.4): a Reader.Set continuation is evaluated at the input
stack, so no dref made inside a lifted program reaches it. -/
theorem run_monadLift (m : ReaderSet E α) (k : α → ReaderSet E β) :
    (monadLift m : ContT β (ReaderSet E) α).run k = λ s => ⋃ x ∈ m s, k x s := by
  funext s; ext; simp

end ReaderSet

/-- ... whereas a State.Set continuation is evaluated at the lifted program's
output stack. -/
theorem run_monadLift (m : StateSet E α) (k : α → StateSet E β) :
    (monadLift m : Tower E β α).run k = λ s => ⋃ q ∈ m s, k q.1 q.2 := by
  funext s; ext; simp

end Charlow2014
