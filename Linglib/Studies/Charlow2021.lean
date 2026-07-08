import Linglib.Semantics.Dynamic.Core.DynamicTy2
import Linglib.Semantics.Dynamic.Connectives.CCP
import Linglib.Semantics.Composition.Continuation
import Linglib.Semantics.Mereology
import Mathlib.Control.Monad.Writer
import Mathlib.Data.List.Sublists

/-!
# Charlow (2021): post-suppositions and semantic theory

Formalizes [charlow-2021]'s account of cumulative readings of modified
numerals — "exactly three boys saw exactly five movies" — which gives a
compositional re-formulation of [brasoveanu-2013]'s post-suppositional
analysis and measures it against the rival repairs the paper canvasses.

The empirical problem: in the pointwise dynamic system (§2), the only
derivable reading is the *pseudo-cumulative* one, where one quantifier's
cardinality test is trapped inside the other's maximization operator.
Speakers judge the sentence false when four boys participated but some
three-boy subgroup saw exactly five movies — the *cumulative* reading, in
which both cardinality tests take widest scope. Four repairs are formalized
side by side:

| Repair | Type | Cumulative reading |
|--------|------|--------------------|
| Tower GQs (§3) | `Cont (Update S) (Update S → Update S)` | ✓ derived by scope-taking |
| Completeness typing (§4) | `Completeness` annotations | pseudo-cumulative ruled ill-typed |
| Post-suppositions (§5, App. B) | `PostSupp S A` (Writer monad) | ✓ via deferred cardinality tests |
| Update semantics (§6) | `StateCCP W E` | ✓ via non-distributive `Mvar_u` |

## Main declarations

* `cumulativeReading`, `pseudoCumulativeReading`: decidable model-checks over
  the finite witness scenarios; `scenarioB_pseudo_true` exhibits the
  pointwise system's overgeneration.
* `Evar`, `Mvar`, `CardTest`, `exactlyN_pw`: pointwise dynamic GQ operators;
  `pseudoCumulative` and `cumulative` are the two competing LFs.
* `TowerGQ`, `exactlyN_tower`: scope-taking GQs via the substrate `Cont`
  monad; `cumulativeTower_eq_cumulative` proves the tower derivation yields
  `cumulative`.
* `Completeness`, `subtypeOf`: the complete/incomplete type discipline;
  `pseudo_cumulative_illtyped` rules out the bad LF.
* `PostSupp`: bi-dimensional meanings as mathlib's `WriterT (Update S) Id`,
  with `Monad`/`LawfulMonad` from the scoped `Monoid (Update S)` instance;
  `reify_cumulativePostsup` proves reification recovers `cumulative`.
* `Evar_u`, `Mvar_u`, `CardTest_u`: state-level (update-theoretic) GQs;
  `Mvar_u_nondistributive` isolates the non-distributivity that produces
  cumulative readings, while `exactlyN_u_distributive` shows the
  single-quantifier pipeline is nevertheless distributive.

## Implementation notes

Suffix conventions track the paper's systems: `_pw` pointwise, `_tower`,
`_postsup`, `_u` update-theoretic. The post-suppositional architecture
(cardinality tests as a distinguished class of meanings discharged after
maximization) is [brasoveanu-2013]'s; Charlow's contribution is the
compositional packaging — §5.1's bi-dimensional pairs, implemented in
Appendix B as a Writer monad.

## References

* [charlow-2021]
* [brasoveanu-2013] (the post-suppositional architecture)
* [muskens-1996], [brasoveanu-2007] (the pointwise substrate)
* [barker-shan-2014] (tower notation)
-/

namespace Charlow2021

open Semantics.Dynamic.Core
open Semantics.Composition.Continuation
open scoped Semantics.Dynamic.Core.DynProp

/-! ### Witness models: the cumulative-reading puzzle

"Exactly three boys saw exactly five movies." Scenario A (3 boys, 5 movies)
verifies both readings. Scenario B (4 boys, 6 movies, with a 3-boy subgroup
that saw exactly 5) falsifies the cumulative reading while verifying the
pseudo-cumulative one; speakers judge the sentence false there. Both
scenarios are the paper's Figure 1, after [brasoveanu-2013]; `scenarioB_saw`
is one witness graph consistent with the paper's Scenario B constraints. -/

inductive Boy3 where | b1 | b2 | b3
  deriving DecidableEq, Repr

inductive Movie5 where | m1 | m2 | m3 | m4 | m5
  deriving DecidableEq, Repr

inductive Boy4 where | b1 | b2 | b3 | b4
  deriving DecidableEq, Repr

inductive Movie6 where | m1 | m2 | m3 | m4 | m5 | m6
  deriving DecidableEq, Repr

/-- Scenario A seeing relation: b1 saw m1, m2; b2 saw m3, m4; b3 saw m5. -/
def scenarioA_saw : Boy3 → Movie5 → Bool
  | .b1, .m1 => true | .b1, .m2 => true
  | .b2, .m3 => true | .b2, .m4 => true
  | .b3, .m5 => true
  | _, _ => false

/-- Scenario B seeing relation: four boys collectively saw six movies, but
the subgroup {b1, b2, b3} saw exactly five. -/
def scenarioB_saw : Boy4 → Movie6 → Bool
  | .b1, .m1 => true | .b1, .m2 => true
  | .b2, .m3 => true | .b2, .m4 => true
  | .b3, .m5 => true
  | .b4, .m6 => true
  | _, _ => false

/-- Cumulative reading as a global count: exactly `nBoys` boys saw a movie
and exactly `nMovies` movies were seen. -/
def cumulativeReading {B M : Type*} (saw : B → M → Bool)
    (allBoys : List B) (allMovies : List M) (nBoys nMovies : ℕ) : Bool :=
  let activeBoys := allBoys.filter (λ b => allMovies.any (saw b))
  let seenMovies := allMovies.filter (λ m => allBoys.any (saw · m))
  activeBoys.length == nBoys && seenMovies.length == nMovies

/-- Pseudo-cumulative reading: some `nBoys`-sized subset of the boys
collectively saw exactly `nMovies` movies (not required to be the maximal
such group). -/
def pseudoCumulativeReading {B M : Type*} (saw : B → M → Bool)
    (allBoys : List B) (allMovies : List M) (nBoys nMovies : ℕ) : Bool :=
  allBoys.sublists.any λ bs =>
    bs.length == nBoys &&
      (allMovies.filter (λ m => bs.any (saw · m))).length == nMovies

-- Domain enumerations for the two scenarios.
def allBoys3 : List Boy3 := [.b1, .b2, .b3]
def allMovies5 : List Movie5 := [.m1, .m2, .m3, .m4, .m5]
def allBoys4 : List Boy4 := [.b1, .b2, .b3, .b4]
def allMovies6 : List Movie6 := [.m1, .m2, .m3, .m4, .m5, .m6]

/-- Scenario A verifies the cumulative reading: 3 boys saw, 5 movies seen. -/
theorem scenarioA_cumulative_true :
    cumulativeReading scenarioA_saw allBoys3 allMovies5 3 5 = true := by decide

/-- Scenario A also verifies the pseudo-cumulative reading. -/
theorem scenarioA_pseudo_true :
    pseudoCumulativeReading scenarioA_saw allBoys3 allMovies5 3 5 = true := by decide

/-- Scenario B falsifies the cumulative reading: 4 boys saw (not 3) and
6 movies were seen (not 5). This matches speakers' judgments. -/
theorem scenarioB_cumulative_false :
    cumulativeReading scenarioB_saw allBoys4 allMovies6 3 5 = false := by decide

/-- Scenario B verifies the pseudo-cumulative reading — the pointwise
system's overgeneration: {b1, b2, b3} saw exactly five movies. -/
theorem scenarioB_pseudo_true :
    pseudoCumulativeReading scenarioB_saw allBoys4 allMovies6 3 5 = true := by decide

/-! ### Pointwise dynamic GQs (§2)

[muskens-1996]/[brasoveanu-2007]-style operators over the pointwise
`Update S := S → S → Prop`. The pointwise system derives only the
pseudo-cumulative LF; the cumulative LF is the target the repairs below
must reach. -/

section Pointwise

variable {S E : Type*} [AssignmentStructure S E] [PartialOrder E] [Fintype E]

/-- Existential dref introduction (eq. 17): introduce a referent satisfying
`P` at dref `v`. -/
def Evar (v : Dref S E) (P : E → Prop) : Update S :=
  λ i j => ∃ x, P x ∧ j = AssignmentStructure.extend i v x

/-- Mereological maximization (eq. 18): retain outputs of `D` whose `v`-value
is maximal among the `v`-values of all outputs of `D`. -/
def Mvar (v : Dref S E) (D : Update S) : Update S :=
  λ i j => D i j ∧ Maximal (λ x => ∃ k, D i k ∧ v k = x) (v j)

/-- Cardinality test (eq. 19): test (identity on assignments) that the atom
count of `v` equals `n`. -/
def CardTest (v : Dref S E) (n : ℕ) : Update S :=
  λ i j => i = j ∧ Mereology.atomCount E (v j) = n

/-- Transitive verb as a test that `R` holds between two drefs. -/
def sawDRS (u v : Dref S E) (R : E → E → Prop) : Update S :=
  test (λ i => R (u i) (v i))

/-- Composed pointwise "exactly n" with trivial nuclear scope:
`E^v P ; M_v(E^v P) ; n_v` (the flat counterpart of the scope-taking
dynamic-GQ entry, eq. 3). -/
def exactlyN_pw (v : Dref S E) (P : E → Prop) (n : ℕ) : Update S :=
  dseq (dseq (Evar v P) (Mvar v (Evar v P))) (CardTest v n)

/-- The pseudo-cumulative LF (5): the object's cardinality test is trapped
inside the subject's maximization. -/
def pseudoCumulative (v u : Dref S E) (boys movies : E → Prop)
    (saw' : E → E → Prop) : Update S :=
  dseq
    (Mvar v (dseq
      (dseq (Evar v boys) (Mvar u (dseq (Evar u movies) (sawDRS u v saw'))))
      (CardTest u 5)))
    (CardTest v 3)

/-- The cumulative LF (6): both cardinality tests scope outside both
maximizations. -/
def cumulative (v u : Dref S E) (boys movies : E → Prop)
    (saw' : E → E → Prop) : Update S :=
  dseq (dseq
    (Mvar v (dseq (Evar v boys) (Mvar u (dseq (Evar u movies) (sawDRS u v saw')))))
    (CardTest u 5))
    (CardTest v 3)

end Pointwise

/-! ### Higher-order (tower) GQs (§3)

A modified numeral denotes a *scope-taking* dynamic meaning rather than a
flat `Update S`. The flat continuized type `Cont (Update S) (Update S)`
does not suffice: its continuation receives an already-maximized update, so
the nuclear scope can only attach outside maximization. -/

section Tower

variable {S E : Type*} [AssignmentStructure S E] [PartialOrder E] [Fintype E]

/-- Higher-order dynamic GQ type, `(Q → t) → t` with `Q ::= (e→t)→t`
(eq. 24), rendered via the substrate continuation monad with answer type
`Update S` and the scope argument flattened to `Update S → Update S` (the
dref is supplied by the GQ itself). §3.4 introduces [barker-shan-2014]-style
tower notation for these meanings. -/
abbrev TowerGQ (S : Type*) := Cont (Update S) (Update S → Update S)

/-- "Exactly n" as a higher-order GQ (eq. 24):
`λc. c (λk. M_v(E^v P ; k v)) ; n_v`, with the scope-taker rendered as
`Update S → Update S`. The cardinality test is evaluated after the
higher-order scope argument `c` — the key that unlocks cumulative readings. -/
def exactlyN_tower (v : Dref S E) (P : E → Prop) (n : ℕ) : TowerGQ S :=
  λ k => dseq (k (λ body => Mvar v (dseq (Evar v P) body))) (CardTest v n)

/-- Higher-order derivation of "exactly 3 boys saw exactly 5 movies"
(eq. 27, derived in §3.3 by β-reduction of the linearized terms; §3.4's
towers are notational sugar for the same derivation): `sawDRS` threads
inside both maximizations while both cardinality tests land outside. -/
def cumulativeTower (v u : Dref S E) (boys movies : E → Prop)
    (saw' : E → E → Prop) : Update S :=
  exactlyN_tower v boys 3 (λ fv =>
    exactlyN_tower u movies 5 (λ fu =>
      fv (fu (sawDRS u v saw'))))

/-- The tower derivation produces exactly the cumulative LF (6) — the
reading the pointwise system cannot reach. -/
theorem cumulativeTower_eq_cumulative (v u : Dref S E)
    (boys movies : E → Prop) (saw' : E → E → Prop) :
    cumulativeTower v u boys movies saw' = cumulative v u boys movies saw' := rfl

end Tower

/-! ### Completeness typing (§4)

A type discipline distinguishing complete (`T`) from incomplete (`t`)
dynamic meanings: maximization traffics in incomplete meanings, cardinality
tests output complete ones, and `t ⊏ T` but not `T ⊏ t`. The
pseudo-cumulative LF then fails to type-check. -/

/-- Completeness level: incomplete (`t`, awaiting a cardinality test) vs
complete (`T`, ready for discourse integration). -/
inductive Completeness where
  | incomplete
  | complete
  deriving DecidableEq, Repr

/-- Subtyping: `t ⊏ T` (incomplete promotes to complete) but not `T ⊏ t`. -/
def subtypeOf : Completeness → Completeness → Prop
  | .incomplete, _ => True
  | .complete, .complete => True
  | .complete, .incomplete => False

instance : DecidableRel subtypeOf := λ a b => by
  cases a <;> cases b <;> simp only [subtypeOf] <;> infer_instance

@[inherit_doc] scoped infix:50 " ⊏ " => subtypeOf

/-- `E^v` outputs an incomplete meaning. -/
def Evar_type : Completeness := .incomplete

/-- `M_v` outputs an incomplete meaning (and demands incomplete input). -/
def Mvar_type : Completeness := .incomplete

/-- A cardinality test outputs a complete meaning. -/
def CardTest_type : Completeness := .complete

/-- Dynamic conjunction preserves completeness. -/
def dynConj_type (c : Completeness) : Completeness := c

/-- The cumulative LF is well-typed (eq. 45): the nested maximizations yield
an incomplete meaning, which the outer cardinality tests accept since `t ⊏ T`. -/
theorem cumulative_welltyped :
    subtypeOf (dynConj_type (dynConj_type Mvar_type)) CardTest_type := by decide

/-- The pseudo-cumulative LF is ill-typed (eq. 46): a cardinality test
(complete) cannot feed maximization, which demands incomplete input. -/
theorem pseudo_cumulative_illtyped : ¬ subtypeOf CardTest_type Mvar_type := by
  decide

/-! ### Post-suppositional GQs (§5, Appendix B)

[brasoveanu-2013]'s post-suppositional architecture in [charlow-2021]'s
compositional packaging: a bi-dimensional meaning pairs an at-issue value
with post-suppositional content — an `Update` accumulated via dynamic
conjunction and discharged at the discourse level after scope-taking
(§5.1) — implemented in Appendix B as a Writer monad over the monoid
`(Update S, dseq, test ⊤)`. -/

section PostSuppositional

universe u

/-- Bi-dimensional meaning (§5.1): an at-issue value paired with accumulated
post-suppositional content — mathlib's Writer monad `WriterT (Update S) Id`
over the monoid `(Update S, ⨟, test ⊤)`. The `Monad`/`LawfulMonad` instances
come from mathlib via the scoped `Monoid (Update S)` instance, and agree with
the paper's `pure`/`bind` (Appendix B, eqs. 120–121): `pure` carries the
trivial post-supposition; `bind` accumulates post-suppositions via `dseq`. -/
abbrev PostSupp (S A : Type u) : Type u := WriterT (Update S) Id A

namespace PostSupp

variable {S A B : Type u}

/-- Construct a bi-dimensional meaning from an at-issue value and a
post-supposition. -/
protected def mk (a : A) (w : Update S) : PostSupp S A := WriterT.mk (a, w)

/-- The at-issue value. -/
def val (p : PostSupp S A) : A := p.run.1

/-- Accumulated post-suppositional content. -/
def postsup (p : PostSupp S A) : Update S := p.run.2

@[simp] theorem val_mk (a : A) (w : Update S) : (PostSupp.mk a w).val = a := rfl

@[simp] theorem postsup_mk (a : A) (w : Update S) :
    (PostSupp.mk a w).postsup = w := rfl

@[simp] theorem val_pure (a : A) : (pure a : PostSupp S A).val = a := rfl

@[simp] theorem postsup_pure (a : A) :
    (pure a : PostSupp S A).postsup = test (λ _ => True) := rfl

@[simp] theorem val_bind (m : PostSupp S A) (f : A → PostSupp S B) :
    (m >>= f).val = (f m.val).val := rfl

@[simp] theorem postsup_bind (m : PostSupp S A) (f : A → PostSupp S B) :
    (m >>= f).postsup = dseq m.postsup (f m.val).postsup := rfl

/-- Reification (the bullet operator, eq. 58): sequence the at-issue update
with its accumulated post-supposition. -/
def reify (p : PostSupp S (Update S)) : Update S := dseq p.val p.postsup

@[simp] theorem reify_pure (D : Update S) :
    (pure D : PostSupp S (Update S)).reify = D :=
  dseq_test D _ (λ _ => trivial)

/-- Truth of a bi-dimensional meaning at an assignment (eq. 56): the reified
update is true at `i` in the substrate sense. -/
def trueAt (p : PostSupp S (Update S)) (i : S) : Prop :=
  Semantics.Dynamic.Core.closure p.reify i

end PostSupp

variable {S E : Type*} [AssignmentStructure S E] [PartialOrder E] [Fintype E]

/-- "Exactly n" as a bi-dimensional meaning (eq. 53): maximized dref
introduction at issue; the cardinality test deferred as a post-supposition. -/
def exactlyN_postsup (v : Dref S E) (P : E → Prop) (n : ℕ) :
    PostSupp S (Update S) :=
  PostSupp.mk (Mvar v (Evar v P)) (CardTest v n)

/-- Bi-dimensional derivation of "exactly 3 boys saw exactly 5 movies":
nested maximizations at issue; both cardinality tests accumulate
post-suppositionally (under `bind`, tests from different quantifiers simply
`dseq`-accumulate, independent of scope). -/
def cumulativePostsup (v u : Dref S E) (boys movies : E → Prop)
    (saw' : E → E → Prop) : PostSupp S (Update S) :=
  PostSupp.mk
    (Mvar v (dseq (Evar v boys) (Mvar u (dseq (Evar u movies) (sawDRS u v saw')))))
    (dseq (CardTest u 5) (CardTest v 3))

/-- Reifying the bi-dimensional derivation recovers exactly the cumulative
LF (6): deferring cardinality tests as post-suppositions yields the
cumulative reading. -/
theorem reify_cumulativePostsup (v u : Dref S E) (boys movies : E → Prop)
    (saw' : E → E → Prop) :
    (cumulativePostsup v u boys movies saw').reify =
      cumulative v u boys movies saw' :=
  (dseq_assoc _ _ _).symm

end PostSuppositional

/-! ### Update-theoretic GQs (§6)

The same operators defined directly over `StateCCP W E := State W E → State W E`.
`Mvar_u` maximizes over **the entire context**, not per-assignment; this
makes it non-distributive, which is what produces cumulative readings
without towers, typing, or post-suppositions. -/

section UpdateTheoretic

variable {W E : Type*}

/-- Existential dref introduction at the state level (eq. 74): for each
world–assignment pair in the context, non-deterministically extend the
assignment at position `v` with an entity satisfying `P`. -/
def Evar_u (v : ℕ) (P : E → Prop) : StateCCP W E :=
  λ s => {p | ∃ q ∈ s, p.1 = q.1 ∧ ∃ (x : E), P x ∧ p.2 = Function.update q.2 v x}

/-- Mereological maximization at the state level (eq. 78): apply `K`, then
retain only output pairs whose `v`-value is maximal **across the entire
output state**. This is the non-distributive operator. -/
def Mvar_u (v : ℕ) (K : StateCCP W E) [PartialOrder E] : StateCCP W E :=
  λ s =>
    let out := K s
    {p ∈ out | Maximal (λ x => ∃ q ∈ out, q.2 v = x) (p.2 v)}

/-- Cardinality test at the state level (eq. 75): filter the context for
pairs where the atom count of `v` equals `n`. -/
def CardTest_u (v : ℕ) (n : ℕ) [PartialOrder E] [Fintype E] : StateCCP W E :=
  λ s => {p ∈ s | Mereology.atomCount E (p.2 v) = n}

/-- Dynamic sequencing at the state level (eq. 80): function composition,
`s[L ; R] := R (L s)`. -/
def dseq_u (L R : StateCCP W E) : StateCCP W E := R ∘ L

/-- Relational test at the state level (eq. 73, the paper's entry for
*saw*): filter for assignments where `R (g v₁) (g v₂)` holds. -/
def RelTest (v₁ v₂ : ℕ) (R : E → E → Prop) : StateCCP W E :=
  λ s => {p ∈ s | R (p.2 v₁) (p.2 v₂)}

/-- Single-quantifier "exactly n" pipeline, `E^v P ; M_v(E^v P) ; n_v` — the
trivial-scope instantiation of the scope-taking update GQ (eq. 81). -/
def exactlyN_u (v : ℕ) (P : E → Prop) (n : ℕ) [PartialOrder E] [Fintype E] :
    StateCCP W E :=
  dseq_u (dseq_u (Evar_u v P) (Mvar_u v (Evar_u v P))) (CardTest_u v n)

/-- Update-theoretic meaning of "exactly `nSubj` `PSubj` `R` exactly `nObj`
`PObj`" (eq. 82): `M_v(E^v P_subj ; M_u(E^u P_obj ; R u v) ; n_obj) ; n_subj`.
This has the same shape as the pointwise pseudo-cumulative LF (5) — the
object's cardinality test sits inside `M_v` — yet because `Mvar_u`
maximizes over the whole context it correctly represents the cumulative
reading (the paper's (83)/(84) contrast). -/
def sentenceMeaning_u (v u : ℕ) (PSubj PObj : E → Prop)
    (R : E → E → Prop) (nSubj nObj : ℕ)
    [PartialOrder E] [Fintype E] : StateCCP W E :=
  let inner := Mvar_u u (dseq_u (Evar_u u PObj) (RelTest u v R))
  dseq_u
    (Mvar_u v (dseq_u (dseq_u (Evar_u v PSubj) inner) (CardTest_u u nObj)))
    (CardTest_u v nSubj)

/-- `M_v` is not distributive: it surveys the entire context to determine
which assignments carry maximal `v`-values. With two pairs whose `v`-values
are `a < b`, whole-context maximization discards the `a`-pair, but
per-element processing keeps both. -/
theorem Mvar_u_nondistributive [PartialOrder E] [Nonempty W]
    (a b : E) (hab : a < b) :
    ∃ (v : ℕ) (K : StateCCP W E), ¬ IsDistributive (Mvar_u v K) := by
  obtain ⟨w⟩ := ‹Nonempty W›
  refine ⟨0, id, fun h => ?_⟩
  let g₁ : Core.Assignment E := Function.const _ a
  let g₂ : Core.Assignment E := Function.const _ b
  let s : State W E := {(w, g₁), (w, g₂)}
  -- (w, g₁) is NOT in Mvar_u 0 id s: a is not maximal because b > a is also present
  have hnotmem : (w, g₁) ∉ Mvar_u 0 id s := by
    simp only [Mvar_u, id, Set.mem_sep_iff]
    intro ⟨_, _, hmax⟩
    have : a = b := le_antisymm (le_of_lt hab) (hmax ⟨(w, g₂), Or.inr rfl, rfl⟩ (le_of_lt hab))
    exact absurd this (ne_of_lt hab)
  -- But (w, g₁) IS in the per-element union: a is maximal in {(w, g₁)}
  have hmem : (w, g₁) ∈ ({p | ∃ i ∈ s, p ∈ Mvar_u 0 id {i}} : Set _) := by
    refine ⟨(w, g₁), Set.mem_insert _ _, Set.mem_sep (Set.mem_singleton _) ⟨⟨(w, g₁), rfl, rfl⟩, ?_⟩⟩
    intro y ⟨q, hq, hqv⟩ hle
    cases Set.mem_singleton_iff.mp hq
    exact hqv ▸ le_refl _
  exact hnotmem (h s ▸ hmem)

/-- Cardinality tests are distributive: they inspect one pair at a time. -/
theorem CardTest_u_distributive [PartialOrder E] [Fintype E]
    (v : ℕ) (n : ℕ) :
    IsDistributive (CardTest_u (W := W) (E := E) v n) := by
  intro s
  ext p
  simp only [CardTest_u, Set.mem_setOf_eq]
  constructor
  · intro ⟨hp, hcard⟩
    exact ⟨p, hp, ⟨Set.mem_singleton p, hcard⟩⟩
  · intro ⟨i, hi, hpi, hcard⟩
    have : p = i := by
      simp only [Set.mem_singleton_iff] at hpi
      exact hpi
    subst this
    exact ⟨hi, hcard⟩

/-- `Evar_u v P` is idempotent, because
`Function.update (Function.update g v x) v y = Function.update g v y`. -/
private theorem evar_u_idempotent (v : ℕ) (P : E → Prop) (s : State W E) :
    Evar_u v P (Evar_u v P s) = Evar_u v P s := by
  ext ⟨w, g⟩; simp only [Evar_u, Set.mem_setOf_eq]; constructor
  · intro ⟨q₁, hq₁, hw₁, y, hPy, hg₁⟩
    obtain ⟨q₂, hq₂s, hw₂, x, _, hg₂⟩ := hq₁
    exact ⟨q₂, hq₂s, hw₂ ▸ hw₁, y, hPy, by rw [hg₁, hg₂, Function.update_idem]⟩
  · intro ⟨q, hqs, hw, x, hPx, hg⟩
    exact ⟨⟨q.1, Function.update q.2 v x⟩, ⟨q, hqs, rfl, x, hPx, rfl⟩, hw, x, hPx,
           by rw [hg, Function.update_idem]⟩

/-- Congruence for `Maximal`: pointwise-equivalent predicates give
equivalent maximality. -/
private theorem maximal_congr {α : Type*} [PartialOrder α] {P Q : α → Prop}
    (h : ∀ x, P x ↔ Q x) (y : α) :
    Maximal P y ↔ Maximal Q y :=
  ⟨fun ⟨hp, hm⟩ => ⟨(h y).mp hp, fun z hz hle => hm ((h z).mpr hz) hle⟩,
   fun ⟨hq, hm⟩ => ⟨(h y).mpr hq, fun z hz hle => hm ((h z).mp hz) hle⟩⟩

/-- The `v`-values after `Evar_u v P s` are exactly `{x | P x}` (for
nonempty input). -/
private theorem evar_u_vvals (v : ℕ) (P : E → Prop) (s : State W E) (y : E)
    (hs : s.Nonempty) :
    (∃ q ∈ Evar_u v P s, q.2 v = y) ↔ P y := by
  simp only [Evar_u, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨_, _⟩, ⟨_, _, _, x, hPx, hg⟩, hv⟩
    rw [hg, Function.update_self] at hv; rwa [← hv]
  · intro hPy
    obtain ⟨⟨w₀, g₀⟩, hw₀⟩ := hs
    exact ⟨⟨w₀, Function.update g₀ v y⟩, ⟨⟨w₀, g₀⟩, hw₀, rfl, y, hPy, rfl⟩,
           Function.update_self v y g₀⟩

/-- The `v`-values after `Evar_u v P {i}` are exactly `{x | P x}`. -/
private theorem evar_u_vvals_single (v : ℕ) (P : E → Prop)
    (i : W × Core.Assignment E) (y : E) :
    (∃ q ∈ Evar_u v P ({i} : Set _), q.2 v = y) ↔ P y := by
  simp only [Evar_u, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨_, _⟩, ⟨_, _, _, x, hPx, hg⟩, hv⟩
    rw [hg, Function.update_self] at hv; rwa [← hv]
  · intro hPy
    exact ⟨⟨i.1, Function.update i.2 v y⟩, ⟨i, rfl, rfl, y, hPy, rfl⟩,
           Function.update_self v y i.2⟩

/-- The composed "exactly n" pipeline is distributive despite containing the
non-distributive `Mvar_u`: `Evar_u` normalizes the `v`-values to `{x | P x}`
regardless of input, so maximization selects the same elements whether
processing the full state or per-element. Cumulative readings arise from the
non-distributivity of `Mvar_u` itself (`Mvar_u_nondistributive`), not from
the single-quantifier pipeline. -/
theorem exactlyN_u_distributive [PartialOrder E] [Fintype E]
    (v : ℕ) (P : E → Prop) (n : ℕ) :
    IsDistributive (exactlyN_u (W := W) (E := E) v P n) := by
  intro s; ext ⟨w, g⟩
  simp only [exactlyN_u, dseq_u, Function.comp,
             CardTest_u, Mvar_u, Set.mem_sep_iff, evar_u_idempotent]
  constructor
  · -- (⊆) Full pipeline → per-element
    intro ⟨⟨hmem, hmax⟩, hcount⟩
    obtain ⟨q, hqs, hwq, x, hPx, hgq⟩ := hmem
    refine ⟨q, hqs, ⟨⟨⟨q, rfl, hwq, x, hPx, hgq⟩,
      (maximal_congr (fun y => (evar_u_vvals v P s y ⟨q, hqs⟩).trans
        (evar_u_vvals_single v P q y).symm) _).mp hmax⟩, hcount⟩⟩
  · -- (⊇) Per-element → full pipeline
    intro ⟨i, his, ⟨⟨hmem_i, hmax_i⟩, hcount_i⟩⟩
    obtain ⟨r, hr_eq, hwr, x, hPx, hgr⟩ := hmem_i
    have hri : r = i := hr_eq; rw [hri] at hwr hgr
    exact ⟨⟨⟨i, his, hwr, x, hPx, hgr⟩,
      (maximal_congr (fun y => (evar_u_vvals_single v P i y).trans
        (evar_u_vvals v P s y ⟨i, his⟩).symm) _).mp hmax_i⟩, hcount_i⟩

end UpdateTheoretic

/-! ### Comparing the repairs

The tower and post-suppositional derivations provably recover the
cumulative LF (`cumulativeTower_eq_cumulative`, `reify_cumulativePostsup`);
completeness typing instead rules the pseudo-cumulative LF out
(`pseudo_cumulative_illtyped`); update semantics derives cumulativity from
the non-distributivity of `Mvar_u` (`Mvar_u_nondistributive`) with no
apparatus beyond `StateCCP`. -/

/-- Dependent indefinites (§7.2) outrun distributive update semantics: not
every state-level CCP is distributive. Witness: the constant CCP
`λ _ => Set.univ` maps `∅` to `Set.univ`, but per-element processing of `∅`
yields `∅`. -/
theorem dependent_indefinites_need_extra {W E : Type*} [Nonempty W] [Nonempty E] :
    ¬ ∀ (depIndef : Semantics.Dynamic.Core.StateCCP W E),
      Semantics.Dynamic.Core.IsDistributive depIndef := by
  intro h
  have h0 := h (fun _ => Set.univ) ∅
  simp only [Set.mem_empty_iff_false, false_and, exists_false, Set.setOf_false] at h0
  exact Set.univ_nonempty.ne_empty h0

end Charlow2021
