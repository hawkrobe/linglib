import Mathlib.Order.Monotone.Defs
import Linglib.Theories.Semantics.Entailment.Basic
import Linglib.Theories.Semantics.Entailment.AntiAdditivity
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Core.Semantics.Presupposition

/-!
# Strawson Entailment
@cite{von-fintel-1999} @cite{strawson-1952}

Strawson-DE: a weakened downward entailingness that checks DE inferences
only when presuppositions of the conclusion are satisfied. This rescues
the Fauconnier-Ladusaw analysis for four "recalcitrant" NPI licensors:
`only` (§2), adversative attitude verbs (§3), superlatives (§4.2), and
conditional antecedents (§4.1). These are not classically DE but do
license NPIs; Strawson-DE explains why.

## Polymorphism

The substrate is polymorphic over `{W : Type*}`. The operators
(`onlyFull`, `sorryFull`, `gladFull`, `superlativeAssert`, `condNecessity`)
take a polymorphic world type and the corresponding presupposition /
ordering / modal-base parameters in their natural mathlib types
(`Set W`, `W → Set W`, `W → Prop`). Concrete counterexamples (proofs of
the form "X is *not* classically DE") are specialized to the 4-element
`World` enum from `Entailment/Basic.lean` as a witness type, since
non-DE-ness is an *existence* claim about some inhabited domain.

## Hierarchy

AM ⊂ AA ⊂ DE ⊂ Strawson-DE (each strict — see
`strawsonDE_strictly_weaker_than_DE`).
-/

namespace Semantics.Entailment.StrawsonEntailment

open Semantics.Entailment
open Semantics.Entailment.Polarity
open Semantics.Entailment.AntiAdditivity

-- ============================================================================
-- §1 Core definitions (polymorphic)
-- ============================================================================

/--
**Strawson-DE** (@cite{von-fintel-1999}, Definition 14, p. 104).

A function `f : Set W → Set W` is Strawson-DE with respect to a
world-relativized definedness predicate `defined` iff: for all `p ⊆ q`,
at every world `w` where `defined p w` holds (i.e. the presupposition
of `f(p)` is satisfied at `w`), we have `f q w → f p w`.

The definedness predicate is world-relativized because presuppositions
are world-relative: "sorry that p" presupposes p at the evaluation
world, not at all worlds. For "only" the presupposition happens to be
world-independent, but the type accommodates factive attitudes.
-/
def IsStrawsonDE {α β : Type*} (f : Set α → Set β)
    (defined : Set α → β → Prop) : Prop :=
  ∀ p q : Set α, p ⊆ q → ∀ w : β, defined p w → f q w → f p w

/--
**Strawson-valid inference** (@cite{von-fintel-1999}, Definition 19, p. 105).

An inference from premises to conclusion is Strawson-valid iff it is
classically valid once we add the premise that all presuppositions of
the conclusion are satisfied.
-/
def StrawsonValid {W : Type*} (premises : List (Set W)) (conclusion : Set W)
    (presupSatisfied : Prop) : Prop :=
  presupSatisfied →
    (∀ w, (∀ p ∈ premises, p w) → conclusion w)

-- ============================================================================
-- §2 Hierarchy: classical → Strawson
-- ============================================================================

/-- Classical DE implies Strawson-DE (for any definedness predicate).
    The `defined p w` hypothesis is simply ignored. Polymorphic over
    domain and codomain to match `IsAntiAdditive`'s shape. -/
theorem antitone_implies_strawsonDE {α β : Type*} (f : Set α → Set β)
    (hAnti : Antitone f) (defined : Set α → β → Prop) :
    IsStrawsonDE f defined :=
  fun _p _q hpq _w _hdef hfqw => hAnti hpq hfqw

/-- Convenience: `IsDownwardEntailing` (the toy-`World` abbrev) implies
    Strawson-DE. -/
theorem de_implies_strawsonDE (f : Set World → Set World) (hDE : IsDownwardEntailing f)
    (defined : Set World → World → Prop) : IsStrawsonDE f defined :=
  antitone_implies_strawsonDE f hDE defined

/-- Anti-additive ⇒ Strawson-DE. -/
theorem antiAdditive_implies_strawsonDE (f : Set World → Set World)
    (hAA : IsAntiAdditive f) (defined : Set World → World → Prop) :
    IsStrawsonDE f defined :=
  de_implies_strawsonDE f hAA.antitone defined

/-- Anti-morphic ⇒ Strawson-DE. -/
theorem antiMorphic_implies_strawsonDE (f : Set World → Set World)
    (hAM : IsAntiMorphic f) (defined : Set World → World → Prop) :
    IsStrawsonDE f defined :=
  de_implies_strawsonDE f hAM.antitone defined

/--
**Strawson anti-additive** — the Strawson-relativized version of
anti-additivity. Required by strong NPIs ("lift a finger", "in years"):
@cite{gajewski-2011}, @cite{chierchia-2013} ch. 3, @cite{crnic-2014}.

`f` is Strawson-AA iff for all `p, q` and worlds `w` where both `f p`'s
and `f q`'s presuppositions are satisfied, `f (p ∪ q) w ↔ f p w ∧ f q w`.

The Strawson move on AA is the same as on DE: the equality is checked
"under the assumption that all presuppositions of the statements
involved are satisfied" (vF Definition 19, p. 105). Strong NPIs are
licensed in Strawson-AA contexts but not in mere-Strawson-DE contexts —
this is the asymmetry that distinguishes "any" (weak, needs only DE) from
"lift a finger" (strong, needs AA).
-/
def IsStrawsonAntiAdditive {α β : Type*} (f : Set α → Set β)
    (defined : Set α → β → Prop) : Prop :=
  ∀ p q : Set α, ∀ w : β, defined p w → defined q w →
    (f (p ∪ q) w ↔ f p w ∧ f q w)

/-- Classical anti-additivity ⇒ Strawson-AA (definedness is ignored).
    Polymorphic over `{α β : Type*}` to match `IsStrawsonAntiAdditive`'s shape. -/
theorem antiAdditive_implies_strawsonAA {α β : Type*} (f : Set α → Set β)
    (hAA : IsAntiAdditive f) (defined : Set α → β → Prop) :
    IsStrawsonAntiAdditive f defined := by
  intro p q w _ _
  exact hAA p q w

/-- Strawson-AA ⇒ Strawson-DE.

    Anti-additivity is strictly stronger than DE classically; the same
    strict inclusion holds in the Strawson-relativized world (modulo
    suitable presupposition handling). -/
theorem strawsonAA_implies_strawsonDE {W : Type*} (f : Set W → Set W)
    (defined : Set W → W → Prop)
    (hAA : IsStrawsonAntiAdditive f defined)
    (hDefSubset : ∀ p q : Set W, p ⊆ q → ∀ w, defined p w → defined q w) :
    IsStrawsonDE f defined := by
  intro p q hpq w hdefp hfqw
  -- Show q = p ∪ q (since p ⊆ q)
  have hUnion : p ∪ q = q := by
    ext x; constructor
    · rintro (hp | hq)
      · exact hpq hp
      · exact hq
    · intro hq; exact Or.inr hq
  -- defined q w follows from definedness monotonicity and p ⊆ q
  have hdefq : defined q w := hDefSubset p q hpq w hdefp
  -- transport f q w to f (p ∪ q) w via p ∪ q = q
  have hfunion : f (p ∪ q) w := by rw [hUnion]; exact hfqw
  exact (hAA p q w hdefp hdefq |>.mp hfunion).1

/-- The full hierarchy: AM → AA → DE → Strawson-DE. -/
structure FullHierarchy (f : Set World → Set World)
    (defined : Set World → World → Prop) where
  am : IsAntiMorphic f
  aa : IsAntiAdditive f := am.1
  de : IsDownwardEntailing f := aa.antitone
  strawsonDE : IsStrawsonDE f defined := de_implies_strawsonDE f de defined

/-- Negation satisfies the full hierarchy. -/
def pnot_fullHierarchy (defined : Set World → World → Prop) :
    FullHierarchy pnot defined :=
  { am := pnot_isAntiMorphic }

-- ============================================================================
-- §3 `only` (Horn's asymmetric analysis; @cite{horn-1996})
-- ============================================================================

/-!
### `only`

Horn's analysis: "Only x VP" decomposes into:
- **Presupposition** (positive): `∃ y, x y ∧ VP y` — some witness exists
  (Horn's amended 1996/1997 version, vF footnote 2 p. 104).
- **Assertion** (negative): `∀ y, x y ∨ ¬ VP y` — no `y ≠ x` satisfies VP.

Von Fintel's key observation: `only` is NOT classically DE
(`onlyFull_not_de` below; vF ex. 11 p. 101) but IS Strawson-DE
(`onlyFull_isStrawsonDE`; vF ex. 18 p. 104).
-/

/--
"Only x VP" as a `PrProp`: Horn's asymmetric decomposition.
-/
def onlyPrProp {W : Type*} (x : W → Prop) (scope : Set W) :
    Core.Presupposition.PrProp W where
  presup := fun _ => ∃ y, x y ∧ scope y
  assertion := fun _ => ∀ y, x y ∨ ¬ scope y

/--
The full "only" meaning: presupposition + assertion combined.

"Only x VP" is true at w iff x satisfies VP AND no one else does.
By construction, `onlyFull x scope w ↔ (onlyPrProp x scope).presup w ∧
(onlyPrProp x scope).assertion w` (`Iff.rfl`).
-/
def onlyFull {W : Type*} (x : W → Prop) (scope : Set W) : Set W :=
  fun _w => (∃ y, x y ∧ scope y) ∧ (∀ y, x y ∨ ¬ scope y)

theorem onlyFull_eq_prprop {W : Type*} (x : W → Prop) (scope : Set W) (w : W) :
    onlyFull x scope w ↔
    (onlyPrProp x scope).presup w ∧ (onlyPrProp x scope).assertion w :=
  Iff.rfl

/--
Ex. 18 (p. 104): `onlyFull` is Strawson-DE in its scope.

When the presupposition is satisfied (the focused individual `x`
satisfies the scope `P`), then `P ⊆ Q`, "no `y ≠ x` satisfies `Q`"
implies "no `y ≠ x` satisfies `P`" — because `P ⊆ Q` makes the
exclusion easier to satisfy.

The definedness predicate is world-independent (existential
presupposition), so the world argument is unused.
-/
theorem onlyFull_isStrawsonDE {W : Type*} (x : W → Prop) :
    IsStrawsonDE (onlyFull x) (fun scope _w => ∃ w', x w' ∧ scope w') := by
  intro p q hpq w ⟨wx, hx_true, hp_wx⟩ h
  obtain ⟨_h_any, h_all⟩ := h
  refine ⟨⟨wx, hx_true, hp_wx⟩, ?_⟩
  intro y
  rcases h_all y with hxy | hnq
  · left; exact hxy
  · right; intro hpy; exact hnq (hpq hpy)

/--
@cite{gajewski-2011} Appendix 1 / eqs. 37-38: `onlyFull` is **Strawson-AA**.

This is the load-bearing puzzle of @cite{gajewski-2011}: vF's recalcitrant
Strawson-DE operators are also Strawson-AA, yet they don't license strong
NPIs (`either`, `in weeks`, punctual `until`). So Strawson-AA is too weak
as a characterization of strong-NPI licensors — Gajewski argues the
operative property is DE assessed on the meaning enriched with the
licenser's direct implicature, and the apparent AA-requirement is just
"DE + scalar endpoint" in disguise (Conjecture 48).

Definedness predicate: existence of a witness for *both* `p` and `q`
individually (the conjunctive form of Strawson biconditional definedness).
-/
theorem onlyFull_isStrawsonAA {W : Type*} (x : W → Prop) :
    IsStrawsonAntiAdditive (onlyFull x)
      (fun scope _w => ∃ w', x w' ∧ scope w') := by
  intro p q w hdefp hdefq
  constructor
  · -- forward: only(p ∪ q) → only(p) ∧ only(q)
    rintro ⟨_, h_no_other⟩
    refine ⟨⟨hdefp, ?_⟩, ⟨hdefq, ?_⟩⟩
    · intro y
      rcases h_no_other y with hy | hy
      · left; exact hy
      · right; intro hp; exact hy (Or.inl hp)
    · intro y
      rcases h_no_other y with hy | hy
      · left; exact hy
      · right; intro hq; exact hy (Or.inr hq)
  · -- reverse: only(p) ∧ only(q) → only(p ∪ q)
    rintro ⟨⟨_, h_no_other_p⟩, ⟨_, h_no_other_q⟩⟩
    obtain ⟨wp, hwpx, hwpp⟩ := hdefp
    refine ⟨⟨wp, hwpx, Or.inl hwpp⟩, ?_⟩
    intro y
    rcases h_no_other_p y with hy | hy
    · left; exact hy
    · rcases h_no_other_q y with hy' | hy'
      · left; exact hy'
      · right; intro h
        rcases h with hp | hq
        · exact hy hp
        · exact hy' hq

/--
Ex. 11 (p. 101): `onlyFull` is NOT classically DE.

Concrete counterexample over the toy 4-element `World`: take
`p = ∅` and `q = {w0}` with focus on `w0`. Then `p ⊆ q` and `onlyFull
(· = w0) q w0` holds (w0 satisfies q and is the only such), but `onlyFull
(· = w0) p w0` fails (the existence presup that someone satisfies p is
unmet). Classical DE would require the conclusion to hold.
-/
theorem onlyFull_not_de : ¬ IsDownwardEntailing (onlyFull (· = World.w0)) := by
  intro hDE
  let p : Set World := fun _ => False
  let q : Set World := fun w => w = .w0
  have hle : p ≤ q := fun _ h => h.elim
  have hq_only : onlyFull (· = World.w0) q World.w0 := by
    refine ⟨⟨World.w0, rfl, rfl⟩, ?_⟩
    intro y
    by_cases h : y = World.w0
    · left; exact h
    · right; intro hy; cases h hy
  have h : onlyFull (· = World.w0) p World.w0 := @hDE p q hle World.w0 hq_only
  rcases h with ⟨⟨_, _, hp_y⟩, _⟩
  exact hp_y

-- ============================================================================
-- §4 Adversative attitudes (vF §3, @cite{heim-1992}, @cite{kadmon-landman-1993})
-- ============================================================================

/-!
### Adversative/Factive Attitudes

Polymorphic over world type `W` and two parameters:
- `dox : W → Set W` — the agent's doxastic accessibility (DOX in
  @cite{heim-1992} / vF eq. 41-50). `dox w` is the set of worlds
  compatible with what the agent at `w` believes.
- `bestOf : W → Set W` — the worlds in `dox w` that maximally satisfy
  the attitude's preference / expectation ordering. Intended to be
  instantiated with `Semantics.Modality.Kratzer.bestWorlds f g w`.

Both `sorryFull` and `gladFull` use *doxastic factivity* (vF eq. 50/53):
"α is sorry/glad that p" presupposes that the agent at `w` believes `p`,
i.e. `dox w ⊆ p`. This is more faithful to vF §3.2-3.3 than the
evaluation-world factivity `p w` an earlier draft used.

Two `glad` semantics are provided: `gladFull` (K&L eq. 50, the analysis
vF *cites*), and `gladFullVF` (vF eq. 52, the analysis vF *prefers*).
Both are UE in the complement (`gladFull_isUE`, `gladFullVF_isUE`), so
the headline NPI-licensing prediction is the same; they differ on the
factual content of the gladness claim (cf. vF p. 124's Honda Civic
example). For `sorry` the analogous K&L vs vF distinction is collapsed
in the substrate's `sorryFull` (both eq. 50/53 styles produce
Strawson-DE; the substrate uses the simpler additive form).
-/

/-- `sorry` denotation with doxastic factivity (vF eq. 50/53).
    `α is sorry that p` at `w` iff (i) the agent at `w` believes `p`
    (factivity through belief: `dox w ⊆ p`) AND (ii) in `α`'s preferred
    worlds, `p` does NOT hold (adversative preference). -/
def sorryFull {W : Type*} (dox : W → Set W) (bestOf : W → Set W)
    (p : Set W) : Set W :=
  fun w => (∀ w' ∈ dox w, p w') ∧ ∀ w' ∈ bestOf w, ¬ p w'

/-- `glad` (K&L eq. 50): factivity + congruent preference.
    "α is glad that p" at `w` iff agent at `w` believes `p` AND in `α`'s
    preferred worlds, `p` also holds. -/
def gladFull {W : Type*} (dox : W → Set W) (bestOf : W → Set W)
    (p : Set W) : Set W :=
  fun w => (∀ w' ∈ dox w, p w') ∧ ∀ w' ∈ bestOf w, p w'

/-- `glad` (von Fintel eq. 52, the replacement vF prefers over K&L eq. 50).
    `α is glad that p` at `w` iff every belief world is strictly preferred
    (under `lt` from the perspective of `w`) to every relevant non-`p`
    world: i.e., `DOX(α, w) <_g (relevant w − p)`.

    Both `gladFull` and `gladFullVF` are UE in `p`. They differ on cases
    like vF's Honda-Civic example (p. 124): when the agent buys a Honda
    Civic and discovers it's a lemon, the K&L version makes "I'm glad I
    bought a Honda Civic" automatic from "I wanted a Honda Civic and got
    one"; the vF version permits the reasonable "I wanted to but I'm not
    glad I did" because the actual world is now worse than the belief
    worlds at the time of evaluation. -/
def gladFullVF {W : Type*} (dox : W → Set W) (relevant : W → Set W)
    (lt : W → W → W → Prop) (p : Set W) : Set W :=
  fun w => ∀ w₁ ∈ dox w, ∀ w₂ ∈ relevant w, ¬ p w₂ → lt w w₂ w₁

/-- Ex. 28b (p. 111): `sorry` IS Strawson-DE in its complement.
    Definedness is doxastic factivity (`dox w ⊆ p`). Given doxastic
    factivity of `p` and `p ⊆ q`: doxastic factivity of `q` is
    inherited (every dox-world satisfies q since it satisfies p);
    for all best worlds, `¬q w'` (from `sorry q`) gives `¬p w'` by
    contraposition of `p ⊆ q`. -/
theorem sorryFull_isStrawsonDE {W : Type*} (dox bestOf : W → Set W) :
    IsStrawsonDE (sorryFull dox bestOf) (fun p w => ∀ w' ∈ dox w, p w') := by
  intro p q hpq w hdef h
  obtain ⟨_, hAllNotQ⟩ := h
  refine ⟨hdef, ?_⟩
  intro w' hw' hpw'
  exact hAllNotQ w' hw' (hpq hpw')

/-- @cite{gajewski-2011} Appendix 1: `sorry` is **Strawson-AA**.
    Definedness: doxastic factivity of *both* p and q. Forward direction
    needs definedness to extract the doxastic-factivity component for
    each conjunct; reverse direction needs only `p ⊆ p ∪ q` and the
    contraposition on best worlds. -/
theorem sorryFull_isStrawsonAA {W : Type*} (dox bestOf : W → Set W) :
    IsStrawsonAntiAdditive (sorryFull dox bestOf)
      (fun p w => ∀ w' ∈ dox w, p w') := by
  intro p q w hdefp hdefq
  constructor
  · -- forward: sorry(p ∪ q) → sorry(p) ∧ sorry(q)
    rintro ⟨_, h_all_not_pq⟩
    refine ⟨⟨hdefp, ?_⟩, ⟨hdefq, ?_⟩⟩
    · intro w' hw' hpw'; exact h_all_not_pq w' hw' (Or.inl hpw')
    · intro w' hw' hqw'; exact h_all_not_pq w' hw' (Or.inr hqw')
  · -- reverse: sorry(p) ∧ sorry(q) → sorry(p ∪ q)
    rintro ⟨⟨_, h_all_not_p⟩, ⟨_, h_all_not_q⟩⟩
    refine ⟨?_, ?_⟩
    · intro w' hw'; exact Or.inl (hdefp w' hw')
    · intro w' hw' h
      rcases h with hp | hq
      · exact h_all_not_p w' hw' hp
      · exact h_all_not_q w' hw' hq

/-- Ex. 30 (p. 111): `sorry` is NOT classically DE. Concrete witness over
    toy `World`: `dox w := {w}` (agent believes only actual world),
    `bestOf w := {w1}`, `p = ∅`, `q = {w0}`. Then `sorry q w0` holds but
    `sorry p w0` fails (doxastic factivity of empty p fails). -/
theorem sorryFull_not_de :
    ¬ IsDownwardEntailing
      (sorryFull (fun (w : World) => ({w} : Set World))
                 (fun (_ : World) => ({World.w1} : Set World))) := by
  intro hDE
  let p : Set World := fun _ => False
  let q : Set World := fun w => w = .w0
  have hle : p ≤ q := fun _ h => h.elim
  have hq_sorry : sorryFull (fun (w : World) => ({w} : Set World))
      (fun (_ : World) => ({World.w1} : Set World)) q World.w0 := by
    refine ⟨?_, ?_⟩
    · intro w' hw'; rcases hw' with rfl; rfl
    · intro w' hw'; rcases hw' with rfl; intro h; cases h
  have h : sorryFull (fun (w : World) => ({w} : Set World))
      (fun (_ : World) => ({World.w1} : Set World)) p World.w0 :=
    @hDE p q hle World.w0 hq_sorry
  exact h.1 World.w0 rfl

/-- `sorry` is Strawson-DE but NOT classically DE — the canonical adversative example. -/
theorem sorryFull_strictly_strawsonDE :
    IsStrawsonDE
      (sorryFull (fun (w : World) => ({w} : Set World))
                 (fun (_ : World) => ({World.w1} : Set World)))
      (fun p w => ∀ w' ∈ ({w} : Set World), p w') ∧
    ¬ IsDownwardEntailing
      (sorryFull (fun (w : World) => ({w} : Set World))
                 (fun (_ : World) => ({World.w1} : Set World))) :=
  ⟨sorryFull_isStrawsonDE _ _, sorryFull_not_de⟩

/-- `glad` (K&L eq. 50) is UE in its complement. -/
theorem gladFull_isUE {W : Type*} (dox bestOf : W → Set W) :
    Monotone (gladFull dox bestOf) := by
  intro p q hpq w h
  obtain ⟨hdef, hAll⟩ := h
  exact ⟨fun w' hw' => hpq (hdef w' hw'), fun w' hw' => hpq (hAll w' hw')⟩

/-- `glad` (vF eq. 52) is UE in its complement. -/
theorem gladFullVF_isUE {W : Type*} (dox relevant : W → Set W)
    (lt : W → W → W → Prop) : Monotone (gladFullVF dox relevant lt) := by
  intro p q hpq w h w₁ hw₁ w₂ hw₂ hnq
  -- ¬ q w₂ → ¬ p w₂ (contraposition of p ⊆ q)
  exact h w₁ hw₁ w₂ hw₂ (fun hp => hnq (hpq hp))

-- ============================================================================
-- §5 Superlatives (vF §4.2)
-- ============================================================================

/-!
### Superlatives

vF eq. 79 (p. 139) presupposes `Q(α) = True` — the *designated subject*
α satisfies the restriction Q. The substrate parameterizes by the
individual `α : W` directly (rather than by a predicate `subject : W →
Prop`), so the presupposition is the literal `restriction α`. The
assertion encodes "no other y in the restriction outranks α" via
absence of a non-α witness in the restriction.

The substrate elides scales/degrees: a faithful eq. 79 formalization
would need a `Degree` type and a relation `α has_higher_P_than y at d`.
The current encoding tracks the Strawson-DE *structure* without the
ordinal content, which suffices for the NPI-licensing prediction.
-/

/-- Presupposition of superlative (vF eq. 79): the designated subject α
    satisfies the restriction. World-independent. -/
def superlativePresup {W : Type*} (α : W) (restriction : Set W)
    (_w : W) : Prop :=
  restriction α

/-- Superlative assertion: the designated subject α satisfies the
    restriction, and no `y ≠ α` in the restriction "outranks" α
    (encoded here as absence of a non-α witness — placeholder for
    a real degree order). -/
def superlativeAssert {W : Type*} (α : W) (restriction : Set W) : Set W :=
  fun _w => restriction α ∧ ∀ y, y = α ∨ ¬ restriction y

/-- Ex. 77 (p. 139): superlatives are Strawson-DE in the restriction position.
    Adding a restriction can only improve the subject's rank, *given* that
    α satisfies the new restriction. -/
theorem superlative_isStrawsonDE {W : Type*} (α : W) :
    IsStrawsonDE (superlativeAssert α) (superlativePresup α) := by
  intro p q hpq w hdef h
  obtain ⟨_, h_all_q⟩ := h
  refine ⟨hdef, ?_⟩
  intro y
  rcases h_all_q y with heq | hnq
  · left; exact heq
  · right; intro hp_y; exact hnq (hpq hp_y)

/-- @cite{gajewski-2011} Appendix 1: superlatives are **Strawson-AA** in
    the restriction position. The "α is/isn't outranked" universal
    composes through union/intersection like `onlyFull`'s "no other y
    satisfies the scope." Definedness: `restriction α` for both p and q. -/
theorem superlative_isStrawsonAA {W : Type*} (α : W) :
    IsStrawsonAntiAdditive (superlativeAssert α) (superlativePresup α) := by
  intro p q w hdefp hdefq
  constructor
  · -- forward: superlative(p ∪ q) → superlative(p) ∧ superlative(q)
    rintro ⟨_, h_all_pq⟩
    refine ⟨⟨hdefp, ?_⟩, ⟨hdefq, ?_⟩⟩
    · intro y
      rcases h_all_pq y with heq | hnpq
      · left; exact heq
      · right; intro hp; exact hnpq (Or.inl hp)
    · intro y
      rcases h_all_pq y with heq | hnpq
      · left; exact heq
      · right; intro hq; exact hnpq (Or.inr hq)
  · -- reverse: superlative(p) ∧ superlative(q) → superlative(p ∪ q)
    rintro ⟨⟨_, h_all_p⟩, ⟨_, h_all_q⟩⟩
    refine ⟨Or.inl hdefp, ?_⟩
    intro y
    rcases h_all_p y with heq | hnp
    · left; exact heq
    · rcases h_all_q y with heq | hnq
      · left; exact heq
      · right; intro h
        rcases h with hp | hq
        · exact hnp hp
        · exact hnq hq

-- ============================================================================
-- §6 Conditional antecedents (vF §4.1)
-- ============================================================================

/-!
### Conditional Antecedents
@cite{kratzer-1986}

`condNecessity domain α β`: "if α, must β" is true at `w` iff `β` holds
at all α-worlds in `domain w`. This is the *idle-ordering* subcase of
the Kratzer restrictor analysis. The full Kratzer conditional with a
non-trivial preference ordering lives in
`Theories/Semantics/Conditionals/Restrictor.lean::conditionalNecessity`
and is *not* monotone in its antecedent — that is the §4 puzzle vF
addresses via dynamic context shifts in @cite{von-fintel-2000}. The
substrate's `condNecessity` here proves the easy idle case so consumer
files have a stable handle.

For the genuine non-monotonicity counterexample (vF ex. 70-73), see
`Conditionals/Restrictor.lean::restrictor_monotone` for the idle-base
case and `Conditionals/Counterfactual.lean` for the Stalnaker-Lewis
similarity-based operator.
-/

/-- Conditional necessity via domain restriction (idle ordering source). -/
def condNecessity {W : Type*} (domain : W → Set W) (α β : Set W) : Set W :=
  fun w => ∀ w' ∈ domain w, α w' → β w'

/-- The antecedent position of `condNecessity` is classically DE
    (Antitone in the polymorphic sense). -/
theorem conditional_antecedent_antitone {W : Type*} (domain : W → Set W)
    (β : Set W) : Antitone (fun α => condNecessity domain α β) := by
  intro α₁ α₂ hle w h w' hw'_mem hw'_α₁
  exact h w' hw'_mem (hle hw'_α₁)

/-- Specialization of `conditional_antecedent_antitone` to the toy
    `World` for use with the `IsDownwardEntailing` abbrev. -/
theorem conditional_antecedent_DE (domain : World → Set World) (β : Set World) :
    IsDownwardEntailing (fun α => condNecessity domain α β) :=
  conditional_antecedent_antitone domain β

/-- Conditional antecedents are *a fortiori* Strawson-DE. -/
theorem conditional_antecedent_strawsonDE {W : Type*} (domain : W → Set W)
    (β : Set W) (defined : Set W → W → Prop) :
    IsStrawsonDE (fun α => condNecessity domain α β) defined :=
  antitone_implies_strawsonDE _ (conditional_antecedent_antitone domain β) defined

/-- Conditional antecedents are *classically* anti-additive in the
    antecedent: `(P ∪ Q)-restricted modal base = (P-restricted) ∪
    (Q-restricted)`, so universal-over-restriction-implies-consequent
    distributes appropriately. -/
theorem condNecessity_isAntiAdditive {W : Type*} (domain : W → Set W) (β : Set W) :
    IsAntiAdditive (fun α => condNecessity domain α β) := by
  intro p q w
  constructor
  · intro h
    exact ⟨fun w' hw' hp => h w' hw' (Or.inl hp),
           fun w' hw' hq => h w' hw' (Or.inr hq)⟩
  · rintro ⟨hp, hq⟩ w' hw' h_pq
    rcases h_pq with hp' | hq'
    · exact hp w' hw' hp'
    · exact hq w' hw' hq'

/-- Conditional antecedents are Strawson-AA with trivial definedness
    (since they are classically AA). -/
theorem condNecessity_isStrawsonAA {W : Type*} (domain : W → Set W) (β : Set W) :
    IsStrawsonAntiAdditive (fun α => condNecessity domain α β)
      (fun _ _ => True) :=
  antiAdditive_implies_strawsonAA _ (condNecessity_isAntiAdditive domain β) _

/-- @cite{gajewski-2011} Appendix 1's actual `would` SAA result.

    vF's `would` has the same truth conditions as `condNecessity` but
    with the non-vacuity presupposition `D_i(w) ∩ p ≠ ∅` (the modal
    base intersected with the antecedent is non-empty). The SAA proof
    is identical to the classical AA result; the non-vacuity is what
    matters for non-trivial Strawson reasoning, not for the AA equation
    itself. -/
theorem wouldFull_isStrawsonAA {W : Type*} (domain : W → Set W) (q : Set W) :
    IsStrawsonAntiAdditive (fun p => condNecessity domain p q)
      (fun p w => ∃ w' ∈ domain w, p w') :=
  antiAdditive_implies_strawsonAA _ (condNecessity_isAntiAdditive domain q) _

-- ============================================================================
-- §7 Bridge theorems (toy-`World` instantiations)
-- ============================================================================

/-- Negation is Strawson-DE. -/
theorem pnot_isStrawsonDE (defined : Set World → World → Prop) :
    IsStrawsonDE pnot defined :=
  de_implies_strawsonDE pnot pnot_isDownwardEntailing defined

/-- "No student" is Strawson-DE. -/
theorem no_student_isStrawsonDE (defined : Set World → World → Prop) :
    IsStrawsonDE no_student defined :=
  de_implies_strawsonDE no_student no_isDE_scope defined

/-- "At most 2 students" is Strawson-DE. -/
theorem atMost2_isStrawsonDE (defined : Set World → World → Prop) :
    IsStrawsonDE atMost2_student defined :=
  de_implies_strawsonDE atMost2_student atMost_isDE_scope defined

/-- Strawson-DE is *strictly* weaker than DE: `onlyFull` is the canonical
    witness — Strawson-DE without classical DE. -/
theorem strawsonDE_strictly_weaker_than_DE :
    ∃ f defined, IsStrawsonDE f defined ∧ ¬ IsDownwardEntailing f :=
  ⟨onlyFull (· = World.w0),
   fun scope _w => ∃ w', (w' = World.w0) ∧ scope w',
   onlyFull_isStrawsonDE _,
   onlyFull_not_de⟩

-- ============================================================================
-- §8 Additional operators (vF coverage gaps)
-- ============================================================================

/-!
### `since` (Iatridou, vF §2.2 exs. 20-22)

"It's been five years since I saw a bird of prey in this area." Same
dialectical structure as `only`: licenses NPIs but is not classically
DE; adding the temporal presupposition (the bird-sighting) restores
the inference.

`pastEvent w` is the set of past worlds (5 years ago); `sinceWindow w`
is the set of intermediate worlds (between past event and now). The
operator says: there was an event in `pastEvent` that satisfied `p`,
and no `sinceWindow` world has satisfied `p`.
-/

/-- `since(p)` denotation. -/
def sinceFull {W : Type*} (pastEvent sinceWindow : W → Set W) (p : Set W) :
    Set W :=
  fun w => (∃ w' ∈ pastEvent w, p w') ∧ (∀ w' ∈ sinceWindow w, ¬ p w')

/-- `since` is Strawson-DE in `p`. Definedness: there is a past
    `p`-event (the temporal presupposition). With `p ⊆ q`, the past
    `p`-event is *a fortiori* a past `q`-event; the no-since-then-q
    constraint contraposes to no-since-then-p. -/
theorem sinceFull_isStrawsonDE {W : Type*} (pastEvent sinceWindow : W → Set W) :
    IsStrawsonDE (sinceFull pastEvent sinceWindow)
      (fun p w => ∃ w' ∈ pastEvent w, p w') := by
  intro p q hpq w ⟨wx, hwx_mem, hp_wx⟩ h
  obtain ⟨_, hAllNotQ⟩ := h
  refine ⟨⟨wx, hwx_mem, hp_wx⟩, ?_⟩
  intro w' hw' hpw'
  exact hAllNotQ w' hw' (hpq hpw')

/-!
### `regret`, `amazed`, `surprised` (vF §3 siblings of `sorry`)

vF p. 114: "For attitudes like *want, wish, glad, regret, sorry* the
ordering will be one of 'preference'. For attitudes like *expect,
amazed, surprised* the ordering will be one of 'expectation/likelihood'."

The difference is in the ordering source supplied to `bestOf`, not in
the operator's structure. We define `regretFull`, `amazedFull`,
`surprisedFull` as aliases of `sorryFull` with the understanding that
their `bestOf` will be instantiated with different ordering sources at
the use site. The Strawson-DE proof is shared.
-/

/-- `regret`: preference-based adversative attitude (vF §3 sibling of `sorry`).
    Same structure; `bestOf` carries the preference ordering source. -/
abbrev regretFull {W : Type*} := @sorryFull W

/-- `amazed`: expectation-based adversative attitude.
    `bestOf` carries an expectation/likelihood ordering source. -/
abbrev amazedFull {W : Type*} := @sorryFull W

/-- `surprised`: expectation-based adversative attitude. -/
abbrev surprisedFull {W : Type*} := @sorryFull W

/-!
### `want` (vF §3.2 eq. 45, pp. 116-118)

`α wants p` iff in `α`'s preferred worlds (drawn from a doxastic modal
base `dox`), `p` holds. This is UE — the headline result vF defends in
§3.2 against Asher (1987) / Heim (1992) non-monotonicity puzzles
(Concorde, couch).
-/

/-- `want(p)` denotation: in α's preferred worlds among `dox w`, `p` holds. -/
def wantFull {W : Type*} (bestOf : W → Set W) (p : Set W) : Set W :=
  fun w => ∀ w' ∈ bestOf w, p w'

/-- `want` is upward entailing in its complement (vF §3.2 headline). -/
theorem wantFull_isUE {W : Type*} (bestOf : W → Set W) :
    Monotone (wantFull bestOf) := by
  intro p q hpq w h w' hw'
  exact hpq (h w' hw')

/-!
### `wish` (Iatridou; vF Curveball #1, pp. 127-129)

`α wishes p` ≈ `α thinks: if p were the case, α would be glad that p`.
Iatridou's analysis (eq. 59) embeds a counterfactual conditional inside
the attitude, making `wish` non-monotonic in p. We do not formalize
this analysis — its non-monotonicity is itself the puzzle vF flags as a
threat to the K&L claim that `wish that p` ≡ `sorry that ¬p`.

A simpler "wish ≡ sorry-of-negation" placeholder is recoverable as
`fun p => sorryFull dox bestOf (compl p)`, which preserves DE-ness on
the K&L side; this is what `wishFull_simple` below offers.
-/

/-- A simplified `wish(p) ≡ sorry(¬p)` denotation (the K&L analysis vF
    discusses on p. 126; Iatridou's counterfactual analysis is more
    complex and breaks monotonicity — see module docstring). -/
def wishFull_simple {W : Type*} (dox bestOf : W → Set W) (p : Set W) : Set W :=
  sorryFull dox bestOf (fun w => ¬ p w)

/-!
### `IsWDE` — Asher 1987 Weakened Downward Entailment
@cite{asher-1987}

vF p. 112 (footnote 8) cites Asher's WDE as a sibling of Strawson-DE.
Asher's schema:

  α regrets that φ
  ⟦φ⟧ ⇒ ⟦ψ⟧
  α believes that ψ
  ⊢ α regrets that ψ

This is the *upward* direction (φ → ψ) with a doxastic side condition
on the conclusion's complement (`believes ψ`). Compare Strawson-DE,
which is the *downward* direction with a presupposition side condition
on the conclusion. The two schemas are not equivalent; vF (p. 112,
footnote 8) writes "the intent of defining something like Strawson
Entailment is clear" but the formal apparatus differs.
-/

/-- Asher's WDE: f(p) plus belief in q implies f(q), when p ⊆ q. -/
def IsWDE {W : Type*} (f : Set W → Set W) (believes : Set W → W → Prop) : Prop :=
  ∀ p q : Set W, p ⊆ q → ∀ w, believes q w → f p w → f q w

/-- Classical UE (Monotone) implies WDE: the doxastic side condition is
    redundant when monotonicity already holds. -/
theorem monotone_implies_WDE {W : Type*} (f : Set W → Set W)
    (hMono : Monotone f) (believes : Set W → W → Prop) :
    IsWDE f believes :=
  fun _p _q hpq _w _hbel hfp => hMono hpq hfp

end Semantics.Entailment.StrawsonEntailment
