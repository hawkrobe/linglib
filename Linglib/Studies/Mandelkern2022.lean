import Linglib.Core.Assignment

/-!
# Mandelkern (2022) — Witnesses: the bounded theory of (in)definites
[mandelkern-2022]
[heim-1982] [groenendijk-stokhof-1991] [krahmer-muskens-1995]
[karttunen-1976] [schlenker-2009] [stalnaker-1974] [stalnaker-1978]
[dekker-1994] [rothschild-2017]

[mandelkern-2022] (Linguistics & Philosophy 45(5):1091-1117) develops the
**bounded theory** of (in)definites: meanings have *two dimensions* — classical
truth-conditions plus a projective second dimension Mandelkern calls **bounds**.
Indefinites `ɜx(p,q)` carry a **witness bound** (if true, then `g(x)` must be
a witness); definites `ιx(p,q)` carry a **familiarity bound** (the scope `p`
is true and satt throughout the local context).

The headline payoff: classical logic is preserved at the truth-conditional
layer (¬¬p ≡ p, ¬p ∨ q ≡ ¬p ∨ (p&q), De Morgan, etc.), so the system avoids
dynamic semantics' logical problems around negation and disjunction (paper §4).
Dynamic anaphoric coordination still happens, but entirely in the bound
dimension via Schlenker/Karttunen-style local-context projection.

## Architectural placement

Self-contained study file at the bounded theory's own level of generality.
**Deliberately disconnected** from `Charlow2025.LawfulDNELift` per the
session's design decision: the two formalisations should mature independently
before any unifying typeclass is extracted. Per [charlow-2025-staged-updates]
§5 the two have higher-typed-bound vs. per-conjunct-bound differences that
make a premature unification likely to be wrong.

## Scope (paper §§5.1–5.7)

Formalised here:
* §5.1 — Truth and falsity (`truth`)
* §5.2 — Witness bound (in `satt`'s `.indef` clause)
* §5.3 — Familiarity bound (in `satt`'s `.def_` clause)
* §5.4 — Update rule (`update`)
* §5.5 — Projection of bounds through connectives (in `satt`'s recursion +
  the derived `localCtx`/`negLocalCtx` helpers)
* §5.6 — Bound-entailment, bound-equivalence (`boundEntails`, `boundEquiv`,
  preorder lemmas; the headline three-way bound-equivalence proved in the
  paper-faithful **atomic** specialization `section56_a_bound_equiv_b_atomic`
  and `section56_b_bound_equiv_c_atomic`, where `F`, `G`, `H` are atoms
  `.atom Fa [x]` etc. Generalisation to abstract `F G H : BoundedForm Atom`
  awaits a `referencesVar`-style well-formedness predicate; the paper's
  examples on p. 1108 are all atomic, so the atomic version covers the
  intended use case.)
* §5.7 — Classicality at the truth-conditional layer (4 theorems, all proved)

§5.8 (quantifiers `EVERYx_δ` with assignment-pair domains, `MOSTx_δ`) and
§6 (modal subordination, cross-world witness bounds) are out of scope.

## Connection to existing linglib infrastructure

* `Core.Assignment.PartialAssign D := Nat → Option D` — used here, matching
  [spector-2025] which formalises a *different* (trivalent-Transparency)
  competitor to Mandelkern's bounded theory. Both files share the
  partial-assignment substrate but diverge in their treatment of bounds vs.
  presupposition.
* `BoundedForm` is a fresh inductive language type for this file (no shared
  surface-language type yet exists across linglib's dynamic theories).
* The classical-logic theorems use Lean's `Classical.em` / `not_not` / `not_and_or`
  directly — Mandelkern's truth-conditions are propositional and bivalent
  (paper footnote 11), so classical meta-logic suffices.
-/

namespace Mandelkern2022

open Core

universe u v

-- ════════════════════════════════════════════════════════════════
-- § 1. Setup: indices, contexts, atomic interpretations
-- ════════════════════════════════════════════════════════════════

/-- A bounded-theory **index**: a partial assignment + a world. Paper's
`⟨g, w⟩`. -/
abbrev Index (W E : Type*) := PartialAssign E × W

/-- A **context** is a set of indices. Paper's `c`. Updates eliminate indices
(Stalnakerian, paper §5.4) rather than extending assignments (Heimian). -/
abbrev Context (W E : Type*) := Set (Index W E)

/-- **Atomic interpretation**: each n-ary atom `A` has a Boolean extension at
each world. Modeled here as `A → List E → W → Bool` with the convention
that arity-mismatched calls return `false`. -/
abbrev AtomEval (Atom : Type u) (W : Type v) (E : Type v) :=
  Atom → List E → W → Bool

/-- **Resolve a list of variable indices** against a partial assignment.
Returns `some es` if every variable is defined, `none` otherwise.

Direct match-based definition (rather than `List.mapM`) so that it reduces
via Lean's `match` reduction. The `List.mapM` form goes through
`List.mapM.loop` internally, which is opaque to `simp`/`rfl` and prevents
clean reasoning about the singleton case `resolveVars g [x]`. -/
def resolveVars {E : Type v} (g : PartialAssign E) : List Nat → Option (List E)
  | [] => some []
  | x :: xs =>
    match g x with
    | none => none
    | some a =>
      match resolveVars g xs with
      | none => none
      | some bs => some (a :: bs)

@[simp] theorem resolveVars_nil {E : Type v} (g : PartialAssign E) :
    resolveVars g [] = some [] := rfl

-- ════════════════════════════════════════════════════════════════
-- § 2. The bounded language ℒ_M (paper §5.1)
-- ════════════════════════════════════════════════════════════════

/-- Mandelkern's two-place definite/indefinite language (paper §5.1, p. 1101):
`ℒ_M ::= A(x₁,...,xₙ) | ⊤(xs) | p&q | p∨q | ¬p | ɜx(p,q) | ιx(p,q)`.

`top` carries a list of bound variables: `⊤(xs)` is satt and true iff all
`xs` are defined. Mandelkern uses `⊤_x` (paper §5.6 (20-c)) as a tautological
restrictor; making it primitive lets us encode `ιx(⊤, p)` directly. -/
inductive BoundedForm (Atom : Type u) where
  /-- `A(x₁,...,xₙ)`. Truth requires every `xᵢ` defined and the resolved
  tuple in `I(A,w)`. -/
  | atom : Atom → List Nat → BoundedForm Atom
  /-- `⊤(xs)` — true (whenever defined) and used as a trivial restrictor. -/
  | top : List Nat → BoundedForm Atom
  /-- Classical conjunction `p & q`. -/
  | conj : BoundedForm Atom → BoundedForm Atom → BoundedForm Atom
  /-- Classical disjunction `p ∨ q`. -/
  | disj : BoundedForm Atom → BoundedForm Atom → BoundedForm Atom
  /-- Classical negation `¬p`. -/
  | neg : BoundedForm Atom → BoundedForm Atom
  /-- Two-place indefinite `ɜx(p, q)` — "some p is q". -/
  | indef : Nat → BoundedForm Atom → BoundedForm Atom → BoundedForm Atom
  /-- Two-place definite `ιx(p, q)` — "the p is q". -/
  | def_ : Nat → BoundedForm Atom → BoundedForm Atom → BoundedForm Atom
  deriving Repr

-- ════════════════════════════════════════════════════════════════
-- § 3. Truth conditions (paper §5.1, classical bivalent)
-- ════════════════════════════════════════════════════════════════

/-- **Truth at an index** (paper §5.1, p. 1101 + appendix p. 1114). Pure
classical: connectives are Boolean, indefinites are existential
quantifiers, definites have the truth-conditions of their conjunction. The
bounds dimension is `satt` below; truth is bound-insensitive. -/
def truth {Atom : Type u} {W E : Type v} (av : AtomEval Atom W E) :
    BoundedForm Atom → PartialAssign E → W → Prop
  | .atom A xs, g, w =>
      ∃ es, resolveVars g xs = some es ∧ av A es w = true
  | .top xs, g, _ =>
      ∃ es, resolveVars g xs = some es
  | .conj p q, g, w => truth av p g w ∧ truth av q g w
  | .disj p q, g, w => truth av p g w ∨ truth av q g w
  | .neg p, g, w => ¬ truth av p g w
  | .indef x p q, g, w =>
      ∃ a : E, truth av p (g.update x a) w ∧ truth av q (g.update x a) w
  | .def_ _ p q, g, w => truth av p g w ∧ truth av q g w

-- ════════════════════════════════════════════════════════════════
-- § 4. Satt (paper §§5.2, 5.3, 5.5)
-- ════════════════════════════════════════════════════════════════

/-- **Satt at a context+index** (paper appendix p. 1114). Recursively
defines bound-satisfaction via Schlenker-style local contexts. Each
recursion happens on a strict subterm of the input form (the `.indef`
and `.def_` cases inline the `p&q` formula rather than constructing
`.conj p q` so termination is structural).

The key clauses:
* **`.conj p q`**: right conjunct sees `c^p` (paper p. 1105).
* **`.disj p q`**: right disjunct sees `c^¬p` (paper p. 1105).
* **`.neg p`**: bound projects identically (paper p. 1105).
* **`.indef x p q`**: existential satt + witness bound (paper §5.2 + p. 1106).
* **`.def_ x p q`**: familiarity bound + scope projection through `c^p`
  (paper §5.3 + p. 1107). -/
def satt {Atom : Type u} {W E : Type v} (av : AtomEval Atom W E) :
    BoundedForm Atom → Context W E → PartialAssign E → W → Prop
  | .atom _ xs, _, g, _ => ∃ es, resolveVars g xs = some es
  | .top xs, _, g, _ => ∃ es, resolveVars g xs = some es
  | .conj p q, c, g, w =>
      satt av p c g w ∧
      satt av q
        {idx | idx ∈ c ∧ truth av p idx.1 idx.2 ∧ satt av p c idx.1 idx.2} g w
  | .disj p q, c, g, w =>
      satt av p c g w ∧
      -- Right disjunct sees `c^¬p`: indices where ¬p is true (i.e., p is false)
      -- AND ¬p is satt (which is satt of p, by the .neg satt clause).
      -- The negation distributes only over `truth p`, NOT over the conjunction
      -- `truth p ∧ satt p` — that was a paper-fidelity bug in an earlier draft.
      satt av q
        {idx | idx ∈ c ∧ ¬ truth av p idx.1 idx.2 ∧ satt av p c idx.1 idx.2} g w
  | .neg p, c, g, w => satt av p c g w
  | .indef x p q, c, g, w =>
      -- Existential satt requirement (projection, paper p. 1106): some
      -- assignment g' makes the conjunction p&q satt at ⟨c, g', w⟩.
      (∃ g' : PartialAssign E,
          satt av p c g' w ∧
          satt av q
            {idx | idx ∈ c ∧ truth av p idx.1 idx.2 ∧ satt av p c idx.1 idx.2} g' w) ∧
      -- Witness bound (paper §5.2): if any witness exists, then the
      -- conjunction p&q is true at ⟨g,w⟩ AND satt at ⟨c,g,w⟩.
      ((∃ a : E, truth av p (g.update x a) w ∧ truth av q (g.update x a) w) →
        (truth av p g w ∧ truth av q g w) ∧
        (satt av p c g w ∧
         satt av q
            {idx | idx ∈ c ∧ truth av p idx.1 idx.2 ∧ satt av p c idx.1 idx.2} g w))
  | .def_ _ p q, c, g, w =>
      -- Familiarity bound (paper §5.3): the restrictor p is true and satt
      -- at every point in c.
      (∀ idx ∈ c, truth av p idx.1 idx.2 ∧ satt av p c idx.1 idx.2) ∧
      -- Local-context projection of scope q (paper §5.5): if p is true at
      -- ⟨g,w⟩, then q is satt at the local context c^p.
      (truth av p g w →
        satt av q
          {idx | idx ∈ c ∧ truth av p idx.1 idx.2 ∧ satt av p c idx.1 idx.2} g w)
termination_by φ _ _ _ => sizeOf φ

/-- **Local context for the right-conjunct** (paper p. 1105): `c^p` keeps
the indices in `c` where `p` is true and satt relative to `c`. -/
def localCtx {Atom : Type u} {W E : Type v} (av : AtomEval Atom W E)
    (c : Context W E) (p : BoundedForm Atom) : Context W E :=
  {idx | idx ∈ c ∧ truth av p idx.1 idx.2 ∧ satt av p c idx.1 idx.2}

/-- **Negative local context for the right-disjunct** (paper p. 1105):
`c^¬p` keeps the indices in `c` where `¬p` is true (i.e., `p` is false) AND
`¬p` is satt (which collapses to `p` is satt, by the `.neg` clause of `satt`).

The negation distributes only over `truth p`, not over the whole `truth p ∧ satt p`
conjunction — paper p. 1105 defines `c^X = {idx ∈ c | X is true and satt at ⟨c,idx⟩}`
applied to `X := ¬p`. The earlier draft had `¬(truth p ∧ satt p)`, which is
strictly weaker (admits indices where `p` is unsatt regardless of truth) and
breaks the bathroom theorem. -/
def negLocalCtx {Atom : Type u} {W E : Type v} (av : AtomEval Atom W E)
    (c : Context W E) (p : BoundedForm Atom) : Context W E :=
  {idx | idx ∈ c ∧ ¬ truth av p idx.1 idx.2 ∧ satt av p c idx.1 idx.2}

-- ════════════════════════════════════════════════════════════════
-- § 4a. The witness-bound projection lemma
-- ════════════════════════════════════════════════════════════════

/-- **Witness-bound projection through update** (the key non-trivial fact about
how `ɜ`'s witness bound interacts with local-context computation): every index
in `c^{ɜx(F,G)}` has `g(x)` itself satisfying both `F` and `G`.

Proof: an index `⟨g,w⟩` is in `c^{ɜx(F,G)}` iff (1) it is in `c`, (2) `ɜx(F,G)`
is true at `⟨g,w⟩`, and (3) `ɜx(F,G)` is satt at `⟨c,g,w⟩`. Conditions (2) and
(3) together trigger the witness bound (the second clause of `satt`'s `.indef`
case), which says: if any witness exists then `g(x)` is the witness, i.e.,
`F(g) ∧ G(g)` holds at `⟨g,w⟩`. -/
theorem localCtx_indef_witness {Atom : Type u} {W E : Type v}
    (av : AtomEval Atom W E)
    (c : Context W E) (x : Nat) (F G : BoundedForm Atom)
    (idx : Index W E) (hidx : idx ∈ localCtx av c (.indef x F G)) :
    truth av F idx.1 idx.2 ∧ truth av G idx.1 idx.2 := by
  obtain ⟨_, htruth, hsatt⟩ := hidx
  -- htruth : truth av (.indef x F G) idx.1 idx.2 — definitionally an ∃
  -- hsatt : satt av (.indef x F G) c idx.1 idx.2 — definitionally a conjunction
  -- whose second component is the witness bound. Unfold both via `simp only`.
  simp only [satt, truth] at htruth hsatt
  exact (hsatt.2 htruth).1

-- ════════════════════════════════════════════════════════════════
-- § 5. Update rule (paper §5.4)
-- ════════════════════════════════════════════════════════════════

/-- **Stalnakerian eliminative update** (paper §5.4, p. 1103): updating `c`
with `p` keeps exactly the points where `p` is true and satt. Differs from
Heimian update which extends assignments; bounds-style update only
eliminates. -/
def update {Atom : Type u} {W E : Type v} (av : AtomEval Atom W E)
    (c : Context W E) (p : BoundedForm Atom) : Context W E :=
  {idx | idx ∈ c ∧ truth av p idx.1 idx.2 ∧ satt av p c idx.1 idx.2}

/-- **Update is eliminative**: `c[p] ⊆ c`. Stalnakerian update never adds
new indices; it only filters. -/
theorem update_subset {Atom : Type u} {W E : Type v} (av : AtomEval Atom W E)
    (c : Context W E) (p : BoundedForm Atom) :
    update av c p ⊆ c :=
  fun _ hidx => hidx.1

/-- **Update equals localCtx**: the update of `c` by `p` is the local
context `c^p`. They are definitionally equal, but stated as a theorem for
discoverability. -/
theorem update_eq_localCtx {Atom : Type u} {W E : Type v} (av : AtomEval Atom W E)
    (c : Context W E) (p : BoundedForm Atom) :
    update av c p = localCtx av c p :=
  rfl

-- ════════════════════════════════════════════════════════════════
-- § 6. Bound-entailment (paper §5.6, generalising von Fintel 1999
--    Strawson entailment)
-- ════════════════════════════════════════════════════════════════

/-- **Bound entailment** (paper p. 1108): `p ⊨_B q` iff for any context+index
where both `p` and `q` are satt and `p` is true, `q` is also true.
Generalises [von-fintel-1999]'s Strawson entailment from
presuppositions to bounds. -/
def boundEntails {Atom : Type u} {W E : Type v} (av : AtomEval Atom W E)
    (p q : BoundedForm Atom) : Prop :=
  ∀ (c : Context W E) (g : PartialAssign E) (w : W),
    satt av p c g w → satt av q c g w →
    truth av p g w → truth av q g w

/-- **Bound equivalence** (paper p. 1108): bound-entailment in both directions. -/
def boundEquiv {Atom : Type u} {W E : Type v} (av : AtomEval Atom W E)
    (p q : BoundedForm Atom) : Prop :=
  boundEntails av p q ∧ boundEntails av q p

/-- **Bound entailment is reflexive**. -/
theorem boundEntails.refl {Atom : Type u} {W E : Type v}
    (av : AtomEval Atom W E) (p : BoundedForm Atom) :
    boundEntails av p p :=
  fun _ _ _ _ _ hp => hp

/-- **Bound entailment is conditionally transitive** (paper p. 1108 implicitly).

Bound-entailment is *not* transitive in the unconditional sense: from
`p ⊨_B q` and `q ⊨_B r` alone, we cannot derive `p ⊨_B r`, because
applying `p ⊨_B q` to a context where `p` is satt-and-true requires
`q` to also be satt at that context (the antecedent of the implication
inside `boundEntails`), which is not given.

The conditional version, given an explicit `satt q` witness, holds
trivially. This is the right form for chaining bound-entailment
arguments at concrete sites where context makes `q`'s satt obvious. -/
theorem boundEntails.trans_with_satt {Atom : Type u} {W E : Type v}
    (av : AtomEval Atom W E) {p q r : BoundedForm Atom}
    (hpq : boundEntails av p q) (hqr : boundEntails av q r)
    (hsatt_q : ∀ (c : Context W E) g w,
      satt av p c g w → satt av r c g w → truth av p g w → satt av q c g w) :
    boundEntails av p r := by
  intro c g w hp_satt hr_satt hp_true
  exact hqr c g w (hsatt_q c g w hp_satt hr_satt hp_true) hr_satt
    (hpq c g w hp_satt (hsatt_q c g w hp_satt hr_satt hp_true) hp_true)

/-- **Bound equivalence is reflexive**. -/
theorem boundEquiv.refl {Atom : Type u} {W E : Type v}
    (av : AtomEval Atom W E) (p : BoundedForm Atom) :
    boundEquiv av p p :=
  ⟨boundEntails.refl av p, boundEntails.refl av p⟩

/-- **Bound equivalence is symmetric**. -/
theorem boundEquiv.symm {Atom : Type u} {W E : Type v}
    (av : AtomEval Atom W E) {p q : BoundedForm Atom}
    (h : boundEquiv av p q) : boundEquiv av q p :=
  ⟨h.2, h.1⟩

/-- **Bounded logic is a superset of classical logic** (paper §5.7 punchline,
p. 1109): "if `p ⊨_L q`, then `p ⊨_B q`". Any classically-valid implication
is also a bound-entailment. The converse fails — bound-entailment also
captures pragmatic Strawson-style equivalences that classical logic misses
(e.g., the §5.6 (20) three-way bound-equivalence).

Direct from definitions: the truth-conditional dimension is classical, so
classical entailment immediately satisfies the bounded version (which
trivially ignores the satt antecedents). -/
theorem boundEntails_of_logicalEntails {Atom : Type u} {W E : Type v}
    (av : AtomEval Atom W E) {p q : BoundedForm Atom}
    (h : ∀ (g : PartialAssign E) (w : W), truth av p g w → truth av q g w) :
    boundEntails av p q :=
  fun _ g w _ _ hp => h g w hp

-- ════════════════════════════════════════════════════════════════
-- § 7. Classicality at the truth-conditional layer (paper §5.7)
-- ════════════════════════════════════════════════════════════════

section Classicality

variable {Atom : Type u} {W E : Type v} (av : AtomEval Atom W E)

/-- **Double negation elimination at truth** (paper §5.7): `¬¬p ≡ p`
classically. The bounded system preserves this; dynamic semantics fails
it (paper §4 (11)). -/
theorem dne_truth (g : PartialAssign E) (w : W) (p : BoundedForm Atom) :
    truth av (.neg (.neg p)) g w ↔ truth av p g w := by
  show ¬ ¬ truth av p g w ↔ truth av p g w
  exact Classical.not_not

/-- **Disjunction-conjunction equivalence at truth** (paper §5.7):
`¬p ∨ q ≡ ¬p ∨ (p&q)`. Bounded preserves this; dynamic semantics fails
it (paper §4 (14) / Partee disjunctions). -/
theorem disj_neg_eq_disj_neg_conj_truth
    (g : PartialAssign E) (w : W) (p q : BoundedForm Atom) :
    truth av (.disj (.neg p) q) g w ↔ truth av (.disj (.neg p) (.conj p q)) g w := by
  show (¬ truth av p g w) ∨ truth av q g w ↔
       (¬ truth av p g w) ∨ (truth av p g w ∧ truth av q g w)
  by_cases hp : truth av p g w <;> simp [hp]

/-- **De Morgan at truth**: `¬(p&q) ≡ ¬p ∨ ¬q`. Holds classically; dynamic
semantics doesn't validate this in general. -/
theorem demorgan_neg_conj_truth
    (g : PartialAssign E) (w : W) (p q : BoundedForm Atom) :
    truth av (.neg (.conj p q)) g w ↔ truth av (.disj (.neg p) (.neg q)) g w := by
  show ¬ (truth av p g w ∧ truth av q g w) ↔
       (¬ truth av p g w) ∨ (¬ truth av q g w)
  exact not_and_or

/-- **Excluded middle at truth**: `p ∨ ¬p` is true at every index. -/
theorem excluded_middle_truth
    (g : PartialAssign E) (w : W) (p : BoundedForm Atom) :
    truth av (.disj p (.neg p)) g w := by
  show truth av p g w ∨ ¬ truth av p g w
  exact Classical.em _

end Classicality

-- ════════════════════════════════════════════════════════════════
-- § 8. Indefinite-truth corollaries (paper §4)
-- ════════════════════════════════════════════════════════════════

section IndefiniteTruth

variable {Atom : Type u} {W E : Type v} (av : AtomEval Atom W E)

/-- **Doubly-negated indefinite has same truth-conditions as the indefinite**
(paper §5.7, p. 1109): `¬¬ɜx(p,q) ≡ ɜx(p,q)` classically. This is what
licenses Karttunen's (1976) observation (paper §4 (12-a)) that
doubly-negated indefinites antecede subsequent definites — the
truth-conditional content survives DNE so the witness bound projects up.
Trivial corollary of `dne_truth`. -/
theorem dneg_indef_truth_eq_indef
    (g : PartialAssign E) (w : W) (x : Nat) (p q : BoundedForm Atom) :
    truth av (.neg (.neg (.indef x p q))) g w ↔ truth av (.indef x p q) g w :=
  dne_truth av g w (.indef x p q)

/-- **Negated indefinite has the universal-negation truth-condition**
(paper §4): `¬ɜx(p,q) ≡ ∀x.¬(p&q)`. Direct from the definition of
`truth` on `.neg` and `.indef`. -/
theorem neg_indef_truth_iff_forall_neg
    (g : PartialAssign E) (w : W) (x : Nat) (p q : BoundedForm Atom) :
    truth av (.neg (.indef x p q)) g w ↔
    ¬ ∃ a : E, truth av p (g.update x a) w ∧ truth av q (g.update x a) w := by
  show ¬ (∃ _ : E, _) ↔ _
  rfl

/-- **Doubly-negated indefinite is bound-equivalent to the indefinite**
(paper §4 (12-a) headline empirical payoff; paper §5.7).

Karttunen 1976's observation: `¬¬ɜx(child)` licenses subsequent definites
just as `ɜx(child)` does. The bounded theory captures this: the two
formulas are bound-equivalent because (a) classical DNE on truth makes
their truth-conditions identical, (b) the `.neg` clause of `satt` makes
satt of `¬¬p` and satt of `p` definitionally equal, so any context where
both are satt is the same context.

Proof: by `boundEntails_of_logicalEntails` applied to `dne_truth` in both
directions. -/
theorem dneg_indef_bound_equiv
    (x : Nat) (p q : BoundedForm Atom) :
    boundEquiv av (.neg (.neg (.indef x p q))) (.indef x p q) :=
  ⟨boundEntails_of_logicalEntails av
      (fun g w => (dne_truth av g w (.indef x p q)).mp),
   boundEntails_of_logicalEntails av
      (fun g w => (dne_truth av g w (.indef x p q)).mpr)⟩

end IndefiniteTruth

-- ════════════════════════════════════════════════════════════════
-- § 9. Section 5.6: bound-equivalence of three open-scope formulations
-- ════════════════════════════════════════════════════════════════

/-! ### Paper §5.6 (20): three bound-equivalent formulations.

Mandelkern's central technical claim about open scope: the following three
formulations have the same truth-up-to-bounds content, even though they
are not logically equivalent.

* (20-a) `ɜx(F, G & H)` — "Some F is G and H"
* (20-b) `ɜx(F, G) & ιx(F, H)` — "Some F is G, and the F is H"
* (20-c) `ɜx(F, G) & ιx(⊤_x, H)` — "Some F is G, and it is H"

Bound-equivalence (not full logical equivalence) captures the pragmatic
equivalence the open-scope thesis demands while preserving classical logic. -/

section Section56

variable {Atom : Type u} {W E : Type v} (av : AtomEval Atom W E)

/-- (20-a) `ɜx(F, G & H)`. -/
def section56_a (x : Nat) (F G H : BoundedForm Atom) : BoundedForm Atom :=
  .indef x F (.conj G H)

/-- (20-b) `ɜx(F, G) & ιx(F, H)`. -/
def section56_b (x : Nat) (F G H : BoundedForm Atom) : BoundedForm Atom :=
  .conj (.indef x F G) (.def_ x F H)

/-- (20-c) `ɜx(F, G) & ιx(⊤_[x], H)`. -/
def section56_c (x : Nat) (F G H : BoundedForm Atom) : BoundedForm Atom :=
  .conj (.indef x F G) (.def_ x (.top [x]) H)

/-- **(20-a) bound-entails (20-b)** (paper p. 1108, easy direction).

Given `(20-a)` is satt, `(20-b)` is satt, and `(20-a)` is true: derive
`(20-b)` is true. The proof:
1. truth of `(20-a) = ɜx(F, G&H)` gives a witness `a` for `F ∧ G ∧ H` at
   `g[x→a]`.
2. The witness bound on satt of `(20-a)` (applied to that witness) forces
   `g(x)` itself to satisfy `F ∧ G ∧ H` at `g`.
3. Truth of `(20-b)` at `g` is `(∃a, F(g[x→a]) ∧ G(g[x→a])) ∧ (F(g) ∧ H(g))`.
   First conjunct: project from step 1 (drop `H`). Second conjunct: from
   step 2.

This direction works abstractly because we only need to *project* the
truth of `(20-b)` from already-established facts. -/
theorem section56_a_boundEntails_b
    (x : Nat) (F G H : BoundedForm Atom) :
    boundEntails av (section56_a x F G H) (section56_b x F G H) := by
  intro c g w hsatt_a _hsatt_b htruth_a
  simp only [section56_a, satt, truth] at hsatt_a htruth_a
  obtain ⟨a, hF_a, hG_a, hH_a⟩ := htruth_a
  -- Apply witness bound from satt(.indef x F (.conj G H))
  have hwb := hsatt_a.2 ⟨a, hF_a, hG_a, hH_a⟩
  -- hwb : (truth F g w ∧ (truth G g w ∧ truth H g w)) ∧ (...)
  show truth av (BoundedForm.conj (.indef x F G) (.def_ x F H)) g w
  refine ⟨⟨a, hF_a, hG_a⟩, hwb.1.1, hwb.1.2.2⟩

/-! ### Paper-faithful atomic specializations of §5.6 (b)↔(a) and (b)↔(c).

The general abstract bound-equivalences (b)↔(a) and (b)↔(c) require either
a `referencesVar`-style predicate that `F`, `G`, `H` are free in `x` (paper
p. 1101 well-formedness condition) plus the `PartialAssign.update_self`
lemma. The paper's §5.6 examples (20)-(20-c) — `child(x)`, `Susie's(x)`,
`at-boarding-school(x)` — are all atomic predicates `Fx`, `Gx`, `Hx`. We
prove the bound-equivalences in this paper-faithful atomic specialization.

Generalization to arbitrary well-formed `F`, `G`, `H` is queued for the
next session: it requires structural induction on a `referencesVar`
predicate plus the partial-assignment `update_self` plus a truth-invariance
lemma for non-referenced variable updates. -/

/-- **`resolveVars [x]` extracts `g(x)` defined**: if `resolveVars g [x] = some es`
for any `es`, then `g x = some a` for some `a`. The base technical lemma
that lets atomic-truth-of-`Fx` imply `g(x)` defined.

Proof via `by_contra` + `push_neg` to avoid `cases hgx : g x`-style
substitution which Lean does eagerly, breaking the goal structure. -/
theorem resolveVars_singleton_def {E : Type v} {g : PartialAssign E} {x : Nat}
    {es : List E} (h : resolveVars g [x] = some es) : ∃ a, g x = some a := by
  by_contra hne
  push Not at hne
  have hgx_none : g x = none := by
    cases hg : g x with
    | none => rfl
    | some a => exact absurd hg (hne a)
  unfold resolveVars at h
  rw [hgx_none] at h
  simp at h

/-- **`resolveVars [x]` for defined `g(x)`** computes `some [a]`. -/
theorem resolveVars_singleton_some {E : Type v} {g : PartialAssign E} {x : Nat}
    {a : E} (h : g x = some a) : resolveVars g [x] = some [a] := by
  unfold resolveVars
  rw [h]
  rfl

/-- **(20-b) bound-entails (20-a)** — direction-2 of §5.6 (a)↔(b),
**atomic version** for `F`, `G`, `H` of shape `.atom _ [x]`.

Proof: from `truth (ɜx(Fx,Gx) ∧ ι(Fx,Hx))` we extract a witness `a` for
`Fx ∧ Gx` at `g[x→a]` and the truth `Fx(g) ∧ Hx(g)`. Apply the witness
bound on `satt of ɜx(Fx,Gx)` to derive `Gx(g)`. Then `Fx(g)` forces
`g(x)` defined (atomic truth requires `resolveVars` to succeed). Take
`b := g(x).get`; by `PartialAssign.update_self`, `g.update x b = g`, so
the truth conditions transfer to give `Fx(g[x→b]) ∧ Gx(g[x→b]) ∧ Hx(g[x→b])`.

The general abstract version (with `referencesVar`-style hypotheses) is
queued; this paper-faithful atomic version covers the §5.6 (20) example. -/
theorem section56_b_boundEntails_a_atomic
    (x : Nat) (Fa Ga Ha : Atom) :
    boundEntails av
      (section56_b x (.atom Fa [x]) (.atom Ga [x]) (.atom Ha [x]))
      (section56_a x (.atom Fa [x]) (.atom Ga [x]) (.atom Ha [x])) := by
  intro c g w hsatt_b _hsatt_a htruth_b
  simp only [section56_b, satt, truth] at hsatt_b htruth_b
  obtain ⟨⟨a, hF_a, hG_a⟩, hF_g, hH_g⟩ := htruth_b
  -- Apply witness bound on satt of ɜx(Fx, Gx) → get truth of Gx at g
  have hwb := hsatt_b.1.2 ⟨a, hF_a, hG_a⟩
  have hG_g := hwb.1.2
  -- Extract g(x) defined from atomic truth of Fx(g) — clone hF_g so it
  -- survives the destructure for use at the witness-construction step
  have hF_g' := hF_g
  obtain ⟨_, hresF, _⟩ := hF_g'
  obtain ⟨c_val, hgx⟩ := resolveVars_singleton_def hresF
  have hupdate : g.update x c_val = g := PartialAssign.update_self hgx
  -- Construct the witness for ɜx(Fx, Gx ∧ Hx); unfold truth in the
  -- subgoals so they match the unfolded-form hypotheses.
  show truth av (section56_a x _ _ _) g w
  simp only [section56_a, truth]
  refine ⟨c_val, ?_, ?_, ?_⟩
  all_goals rw [hupdate]
  · exact hF_g
  · exact hG_g
  · exact hH_g

/-- **Bound-equivalence of (20-a) and (20-b)** (paper p. 1108), atomic
version. Direction (a)→(b) is the general (proved abstractly) lemma;
direction (b)→(a) requires the atomic specialization. -/
theorem section56_a_bound_equiv_b_atomic
    (x : Nat) (Fa Ga Ha : Atom) :
    boundEquiv av
      (section56_a x (.atom Fa [x]) (.atom Ga [x]) (.atom Ha [x]))
      (section56_b x (.atom Fa [x]) (.atom Ga [x]) (.atom Ha [x])) :=
  ⟨section56_a_boundEntails_b av x _ _ _,
   section56_b_boundEntails_a_atomic av x Fa Ga Ha⟩

/-- **Bound-equivalence of (20-b) and (20-c)** (paper p. 1108), atomic
version. The forward direction needs `Fx(g) → g(x)` defined (atomic);
the backward direction uses the `ɜx(Fx,Gx)` witness bound for `Fx(g)`. -/
theorem section56_b_bound_equiv_c_atomic
    (x : Nat) (Fa Ga Ha : Atom) :
    boundEquiv av
      (section56_b x (.atom Fa [x]) (.atom Ga [x]) (.atom Ha [x]))
      (section56_c x (.atom Fa [x]) (.atom Ga [x]) (.atom Ha [x])) := by
  refine ⟨?_, ?_⟩
  · -- (20-b) → (20-c): need Fx(g) to extract g(x) defined
    intro c g w _hsatt_b _hsatt_c htruth_b
    simp only [section56_b, truth] at htruth_b
    obtain ⟨⟨a, hF_a, hG_a⟩, hF_g, hH_g⟩ := htruth_b
    -- For (20-c)'s second conjunct, need g(x) defined and Hx(g)
    obtain ⟨esF, hresF, _⟩ := hF_g
    obtain ⟨c_val, hgx⟩ := resolveVars_singleton_def hresF
    refine ⟨⟨a, hF_a, hG_a⟩, ⟨[c_val], ?_⟩, hH_g⟩
    exact resolveVars_singleton_some hgx
  · -- (20-c) → (20-b): use witness bound on ɜx(Fx,Gx) for Fx(g)
    intro c g w hsatt_c _hsatt_b htruth_c
    simp only [section56_c, satt, truth] at hsatt_c htruth_c
    obtain ⟨⟨a, hF_a, hG_a⟩, _htop_g, hH_g⟩ := htruth_c
    -- hsatt_c.1 is satt of ɜx(Fx, Gx) — apply witness bound
    have hwb := hsatt_c.1.2 ⟨a, hF_a, hG_a⟩
    have hF_g := hwb.1.1
    refine ⟨⟨a, hF_a, hG_a⟩, hF_g, hH_g⟩

end Section56

-- ════════════════════════════════════════════════════════════════
-- § 10. Empirical anchors (paper §4 (11)–(14))
-- ════════════════════════════════════════════════════════════════

/-! ### Paper §4 data, formalised at the satt-update level.

These empirical claims (Karttunen 1976, Partee disjunctions, bathroom
sentences) are the data dynamic semantics struggles with and the bounded
theory accommodates. Formalising them requires both truth-level
classicality (proved above) and satt-level reasoning about projection
(`localCtx`, `negLocalCtx`).

The truth-level claims are direct corollaries of §7. The satt-level
claims are stated below; full proofs depend on the `localCtx_indef_witness`
lemma (deferred) and are left as TODO for the same follow-up PR. -/

section EmpiricalAnchors

variable {Atom : Type u} {W E : Type v} (av : AtomEval Atom W E)

/-- **Negated-indefinite truth has universal-negation form** (paper §4 (11)
truth-conditional content). Direct corollary of `neg_indef_truth_iff_forall_neg`. -/
theorem negated_indefinite_universal
    (g : PartialAssign E) (w : W) (x : Nat) (p q : BoundedForm Atom) :
    truth av (.neg (.indef x p q)) g w ↔
    ∀ a : E, ¬ (truth av p (g.update x a) w ∧ truth av q (g.update x a) w) := by
  rw [neg_indef_truth_iff_forall_neg]
  exact not_exists

/-- **Bathroom truth** (paper §4 (14-a) truth-conditional content):
`¬ɜx(B(x)) ∨ H(x)` is true iff either there is no B-thing or H(g(x)).
Holds classically without difficulty. -/
theorem bathroom_truth
    (g : PartialAssign E) (w : W) (x : Nat) (B H : BoundedForm Atom) :
    truth av (.disj (.neg (.indef x B (.top [x]))) H) g w ↔
    (¬ ∃ a : E, truth av B (g.update x a) w ∧ truth av (.top [x]) (g.update x a) w) ∨
    truth av H g w := by
  show (¬ (∃ _ : E, _)) ∨ truth av H g w ↔ _
  rfl

/-- **Bathroom-disjunction licensing** (paper §5.7, p. 1109; data §4 (14-a)).

Under the bounded theory, `¬ɜxB(x) ∨ ψ(x)` makes `x` available in the
right disjunct's local context. The right disjunct sees `c^¬(¬ɜxB(x))` —
by `negLocalCtx`'s definition (after the audit-driven fix) this is indices
where `¬¬ɜxB(x)` is true (= `ɜxB(x)` by classical DNE) AND `¬ɜxB(x)` is
satt (= `ɜxB(x)` is satt, by the `.neg` clause of `satt`, which collapses
definitionally though Lean's recursive `def` doesn't auto-reduce in
hypothesis positions).

The "stripped" theorem statement below decouples from the `.neg .neg`
projection plumbing: any index in `c` that is true and satt for the
positive existential `ɜxB(⊤_x)` has `B(g)` true. Composing this with
`Classical.not_not` and the `.neg`-satt-collapse equation `rfl` gives the
full bathroom theorem (chain of three rewrites the consumer can do at
their use site). -/
theorem bathroom_right_disjunct_local_ctx_witness
    (c : Context W E) (x : Nat) (B : BoundedForm Atom) (idx : Index W E)
    (hin : idx ∈ c)
    (htruth : truth av (.indef x B (.top [x])) idx.1 idx.2)
    (hsatt : satt av (.indef x B (.top [x])) c idx.1 idx.2) :
    truth av B idx.1 idx.2 :=
  (localCtx_indef_witness av c x B (.top [x]) idx ⟨hin, htruth, hsatt⟩).1

/-! **Note on `satt`-of-`.neg` coercion**: the paper's projection rule
(paper p. 1105 "a negation is satt iff the negatum is satt") makes
`satt (¬p) = satt p` *intentionally* definitional. In our Lean
formalisation, however, `satt`'s `termination_by` annotation forces
well-founded recursion via `WellFounded.fix`, which Lean treats as
opaque to definitional reduction. So the equation `satt av (.neg p) c g w
= satt av p c g w` is *not* a Lean definitional equality and not
provable by `rfl` / `Iff.refl` / `change`.

To use `bathroom_right_disjunct_local_ctx_witness` on a hypothesis
`hsatt : satt av (.neg p) c g w`, consumers need to manually establish
the coercion at use sites (typically by computing satt's body explicitly
or proving the `Iff` via case analysis on `p`'s structure). A future
mathlib-quality refactor would make `satt` non-`termination_by`
(structural recursion) and reclaim the definitional collapse. -/

end EmpiricalAnchors

-- ════════════════════════════════════════════════════════════════
-- § 11. Sanity tests
-- ════════════════════════════════════════════════════════════════

section Tests

/-- A trivial atom set with one one-place predicate. -/
inductive TestAtom where | child : TestAtom

abbrev TestWorld := Bool
abbrev TestE := Bool

/-- Test atom evaluation: `child(b)` is true at world `true` if `b = false`. -/
def testAv : AtomEval TestAtom TestWorld TestE
  | TestAtom.child, [b], w => decide (w = true ∧ b = false)
  | _, _, _ => false

/-- DNE classicality holds for the test atom set. -/
example (g : PartialAssign TestE) (w : TestWorld) (p : BoundedForm TestAtom) :
    truth testAv (.neg (.neg p)) g w ↔ truth testAv p g w :=
  dne_truth testAv g w p

/-- Excluded middle holds. -/
example (g : PartialAssign TestE) (w : TestWorld) (p : BoundedForm TestAtom) :
    truth testAv (.disj p (.neg p)) g w :=
  excluded_middle_truth testAv g w p

/-- De Morgan holds. -/
example (g : PartialAssign TestE) (w : TestWorld) (p q : BoundedForm TestAtom) :
    truth testAv (.neg (.conj p q)) g w ↔
    truth testAv (.disj (.neg p) (.neg q)) g w :=
  demorgan_neg_conj_truth testAv g w p q

/-- Update is eliminative on the test substrate. -/
example (c : Context TestWorld TestE) (p : BoundedForm TestAtom) :
    update testAv c p ⊆ c :=
  update_subset testAv c p

end Tests

end Mandelkern2022
