import Linglib.Core.Logic.Trivalent.Basic
import Linglib.Core.Logic.Assignment

/-!
# Spector 2025: Trivalence and Transparency
[spector-2025]

A non-dynamic approach to anaphora combining trivalent semantics
(Middle Kleene, [peters-1979], [beaver-krahmer-2001])
with Schlenker's Transparency Principle ([schlenker-2007],
[schlenker-2008a]).

## Key Results Formalized

1. **Forward anaphora in conjunction** (§3.2): `∃xT(x) ∧ P(x̲)` satisfies
   Transparency — the free variable in the second conjunct is licensed
   by the existential in the first.

2. **Reverse conjunction fails** (§3.2): `P(x̲) ∧ ∃xT(x)` does NOT
   satisfy Transparency in the null context — cataphora across conjunction
   is correctly predicted to be infelicitous.

3. **Bathroom sentences** (§3.3): `¬∃xB(x) ∨ H(x̲)` satisfies
   Transparency — the classic "either there's no bathroom or it's
   upstairs" pattern is correctly predicted to be felicitous.

4. **Reverse bathroom fails** (§3.3): `H(x̲) ∨ ¬∃xB(x)` does NOT
   satisfy Transparency in the null context.

5. **Semantic adequacy**: The trivalent semantics delivers the correct
   truth-at-a-world conditions (§2.1).

## Note on Middle Kleene conjunction

The paper's Table 1 shows `0 ∧ # = #` for conjunction, but the paper's
text (§2.1) states: "If φ is not undefined, then the truth values of
φ ∧ ψ are the same as in the Strong Kleene truth-tables." Strong Kleene
gives `false ∧ # = false`. The §3.2 proofs depend on this: the reverse
conjunction counterexample requires `meetMiddle false # = false`. We
follow the text and the proofs (Table 1 appears to contain an error
in the conjunction column for `0 ∧ #`).

## Architecture

The trivalent semantics uses partial assignments (`PartialAssign D`)
and plural assignments (`PluralAssign D`) from `Core.Assignment`.
Predicate application yields `#` when the variable is unvalued.
The existential quantifier uses [mandelkern-2022]'s witness
condition: `∃xφ` is true at `(w,g)` only if `g(x)` witnesses `φ`,
undefined if classically true but `g(x)` is not a witness.
-/

namespace Spector2025

open Core
open Trivalent (ofBool isDefined meetMiddle joinMiddle)

universe u

variable {D : Type u} {W : Type*}

-- ════════════════════════════════════════════════════════════════
-- Trivalent Predicate Semantics
-- ════════════════════════════════════════════════════════════════

/-- Interpretation function: maps predicates to extensions at worlds. -/
abbrev Interp (W : Type*) (D : Type u) := W → D → Bool

/-- Evaluate a one-place predicate on a partial assignment.
    §2.1:
    - `1` if `g(x) ∈ I(P,w)`
    - `0` if `g(x) ≠ #` and `g(x) ∉ I(P,w)`
    - `#` if `g(x) = #` -/
def evalPred (I : Interp W D) (g : PartialAssign D) (x : Nat)
    (w : W) : Trivalent :=
  match g x with
  | some d => Trivalent.ofBool (I w d)
  | none => .indet

/-- The `U(x)` predicate as a Trivalent value.
    Always bivalent: `true` if valued, `false` if not. -/
def valuedT3 (g : PartialAssign D) (x : Nat) : Trivalent :=
  Trivalent.ofBool (g.valued x)

/-- `U(x)` is never undefined. -/
theorem valuedT3_defined (g : PartialAssign D) (x : Nat) :
    (valuedT3 g x).isDefined := by
  simp [valuedT3, PartialAssign.valued, Trivalent.isDefined]
  cases g x <;> trivial

/-- When `g` values `x`, evaluating a predicate at `x` is bivalent. -/
theorem evalPred_valued (I : Interp W D) (g : PartialAssign D) (x : Nat) (w : W)
    (h : g.valued x = true) :
    (evalPred I g x w).isDefined := by
  simp [evalPred, PartialAssign.valued] at *
  cases hg : g x with
  | none => simp [hg] at h
  | some d => simp [Trivalent.ofBool, Trivalent.isDefined]; cases I w d <;> trivial

/-- When `g` does not value `x`, evaluating a predicate at `x` is undefined. -/
theorem evalPred_unvalued (I : Interp W D) (g : PartialAssign D) (x : Nat) (w : W)
    (h : g.valued x = false) :
    evalPred I g x w = .indet := by
  simp [evalPred, PartialAssign.valued] at *
  cases hg : g x with
  | none => rfl
  | some _ => simp [hg] at h

-- ════════════════════════════════════════════════════════════════
-- Trivalent at a World
-- §2.1, definition (6)
-- ════════════════════════════════════════════════════════════════

/-- A sentence φ is true at a world w iff there is an assignment g
    such that ⟦φ⟧^{w,g} = 1.

    §2.1: "A sentence φ is true at a world w
    if and only if there is an assignment function g such that
    ⟦φ⟧^{w,g} = 1." This bridges trivalent assignment-level
    semantics to world-level truth conditions. -/
def trueAtWorld (φ : W → PartialAssign D → Trivalent) (w : W) : Prop :=
  ∃ g : PartialAssign D, φ w g = .true

-- ════════════════════════════════════════════════════════════════
-- §2.2: Contexts and the Transparency Principle
-- ════════════════════════════════════════════════════════════════

/-! ### Abstract Transparency

Originally split out into `Semantics/Presupposition/Transparency.lean`,
but Spector 2025 is the only consumer; per the project's N≥2 promotion
discipline this co-locates the abstract API with its sole user until a
second consumer (e.g., a future Mandelkern 2022 study file) lands.

Schlenker (2007, 2008a) introduced the Transparency Principle in a
dynamic-with-local-contexts setting; Spector reuses the *condition* in
a static partial-assignment setting (§2.2). The definitions below stay
parametric in the assignment carrier so that the §6 plural-assignment
variants can reuse the same shape.
-/

/-- A context is a set of world-assignment pairs.
    §2.2.1: "We view a context C as a set of world-assignment pairs (w,g)." -/
abbrev Ctx (W : Type*) (D : Type u) := W → PartialAssign D → Prop

/-- The null context: all world-assignment pairs.
    §2.2.1: "the null context which contains all possible
    world-assignment pairs." -/
def nullCtx : Ctx W D := λ _ _ => True

/-- Stalnakerian update: intersect context with sentence's truth set.
    §2.2.1: "if a sentence S is accepted as true in context C, then the
    resulting context is simply C intersected with the set of
    world-assignment pairs where S is true." -/
def stalnakerUpdate (C : Ctx W D) (S : W → PartialAssign D → Trivalent) :
    Ctx W D :=
  λ w g => C w g ∧ S w g = .true

/-- Two trivalent sentences agree throughout a context. -/
def agreeIn (C : Ctx W D) (S1 S2 : W → PartialAssign D → Trivalent) : Prop :=
  ∀ w g, C w g → S1 w g = S2 w g

/-- A trivalent sentence over world-assignment pairs. -/
abbrev Sent (W : Type*) (D : Type u) := W → PartialAssign D → Trivalent

/-- A sentence frame: a sentence with a hole for a sub-sentence. -/
abbrev Frame (W : Type*) (D : Type u) := Sent W D → Sent W D

/-- The Transparency Principle (symmetric version).

    §2.2.2 / §6.3: For a sentence S containing a free (underlined)
    variable x, form S1 by replacing P(x̲) with `U(x) ∧ φ` and S2 by
    replacing P(x̲) with `φ`. Transparency is satisfied in context C iff
    S1 and S2 agree throughout C for every formula φ.

    We formalize this as: given a sentence-with-hole `frame` and a
    presupposition predicate `presup`, Transparency holds iff for every
    `φ`, `frame (meetMiddle presup φ)` and `frame φ` agree in C.

    The `frame` represents the sentence with a hole where the
    presuppositional element occurs. The presupposition (e.g., `U(x)`)
    is conjoined via Middle Kleene conjunction. -/
def transparent (C : Ctx W D) (frame : Frame W D)
    (presup : Sent W D) : Prop :=
  ∀ φ : Sent W D,
    agreeIn C (frame (λ w g => Trivalent.meetMiddle (presup w g) (φ w g)))
              (frame φ)

/-- Transparency holds trivially when the presupposition is always true
    in the context (since `meetMiddle true v = v`). -/
theorem transparent_of_presup_true (C : Ctx W D) (frame : Frame W D)
    (presup : Sent W D)
    (hframe : ∀ (φ₁ φ₂ : Sent W D), (∀ w g, C w g → φ₁ w g = φ₂ w g) →
              ∀ w g, C w g → frame φ₁ w g = frame φ₂ w g)
    (hpresup : ∀ w g, C w g → presup w g = .true) :
    transparent C frame presup := by
  intro φ w g hC
  exact hframe _ _
    (λ w' g' hC' => by simp [Trivalent.meetMiddle_true_left, hpresup w' g' hC']) w g hC

/-- The Novelty Condition: an existential quantifier introducing
    variable x can only occur once in a discourse.

    §4 / [heim-1982]: "If x is a variable, an occurrence of ∃x can
    only occur once in a whole discourse." This prevents
    ∃xP(x).∃xQ(x) from collapsing to ∃x(P(x) ∧ Q(x)).

    Currently has no consumer in this file — see **Deferred work** at
    the end of the file. -/
def noveltyCondition (usedVars : List Nat) (newVar : Nat) : Prop :=
  newVar ∉ usedVars

-- ════════════════════════════════════════════════════════════════
-- Parametric Transparency (assignment-type-agnostic)
-- ════════════════════════════════════════════════════════════════

/-!
### Parametric Transparency

§6.3 observes that the Transparency proofs are
parametric in the assignment type — the same Middle Kleene reasoning
works for individual assignments `g` and plural assignments `G`.
We factor this out: the proofs below are stated over abstract Trivalent
values, independent of assignment representation.
-/

/-- Parametric forward conjunction Transparency: `meetMiddle E (meetMiddle presup φ) =
    meetMiddle E φ` whenever `E = true → presup = true`. Independent of
    assignment type — works for both individual and plural systems.

    §3.2, §6.3: The three cases are:
    - `E = false`: `meetMiddle false _ = false` (left zero)
    - `E = #`: `meetMiddle # _ = #` (left absorbs)
    - `E = true`: witness gives `presup = true`, so `meetMiddle true φ = φ` -/
theorem conj_transparency_parametric : ∀ (E presup φ : Trivalent),
    (E = .true → presup = .true) →
    Trivalent.meetMiddle E (Trivalent.meetMiddle presup φ) =
    Trivalent.meetMiddle E φ
  | .true, _, φ, hw => by rw [hw rfl, Trivalent.meetMiddle_true_left, Trivalent.meetMiddle_true_left]
  | .false, _, _, _ => by simp [Trivalent.meetMiddle]
  | .indet, _, _, _ => rfl

/-- Parametric bathroom Transparency: `joinMiddle negE (meetMiddle presup φ) =
    joinMiddle negE φ` whenever `negE = false → presup = true`. -/
theorem disj_transparency_parametric : ∀ (negE presup φ : Trivalent),
    (negE = .false → presup = .true) →
    Trivalent.joinMiddle negE (Trivalent.meetMiddle presup φ) =
    Trivalent.joinMiddle negE φ
  | .true, _, _, _ => by simp [Trivalent.joinMiddle]
  | .indet, _, _, _ => rfl
  | .false, _, φ, hw => by rw [hw rfl, Trivalent.meetMiddle_true_left]

-- ════════════════════════════════════════════════════════════════
-- §3.2: Anaphora in Conjunctive Sentences
-- ════════════════════════════════════════════════════════════════

section Conjunction

/-!
### Forward anaphora: `∃xT(x) ∧ P(x̲)`

Consider "A table is in the room and it is purple," translated as
`∃xT(x) ∧ P(x̲)`. The Transparency question is: does
`∃xT(x) ∧ (U(x) ∧ φ)` always have the same truth value as
`∃xT(x) ∧ φ`?

The frame is `F(ψ) = ∃xT(x) ∧ ψ`, and the presupposition is `U(x)`.

**Proof** (§3.2): Consider `(w,g)`.
- If `∃xT(x)` is false at `(w,g)`: both sentences are false
  (Middle Kleene: `false ∧ _ = false`).
- If `∃xT(x)` is `#` at `(w,g)`: both sentences are `#`
  (Middle Kleene: `# ∧ _ = #`).
- If `∃xT(x)` is true at `(w,g)`: then `g` values `x`, so `U(x) = true`,
  so `meetMiddle true φ = φ`, so both sentences equal `∃xT(x) ∧ φ`.
-/

/-- Forward conjunction Transparency: `∃xT(x) ∧ P(x̲)` satisfies
    Transparency in every context.

    §3.2: The abstract pattern is: if `E = true`
    implies `presup = true` (the witness connection), then the frame
    `F(ψ) = meetMiddle E ψ` satisfies Transparency for `presup`.

    Derived from `conj_transparency_parametric`. -/
theorem forward_conj_transparency
    (E presup : W → PartialAssign D → Trivalent)
    (hwitness : ∀ w g, E w g = .true → presup w g = .true)
    (C : Ctx W D) :
    ∀ (φ : Sent W D) (w : W) (g : PartialAssign D), C w g →
      Trivalent.meetMiddle (E w g) (Trivalent.meetMiddle (presup w g) (φ w g)) =
      Trivalent.meetMiddle (E w g) (φ w g) :=
  fun φ w g _ => conj_transparency_parametric (E w g) (presup w g) (φ w g) (hwitness w g)

/-- Reverse conjunction Transparency FAILS: `P(x̲) ∧ ∃xT(x)` does NOT
    satisfy Transparency in the null context.

    §3.2: Take `φ = P(x)`. If `g` does not value `x`,
    then `φ ∧ ∃xT(x)` is `#` (left undefined absorbs), but
    `(U(x) ∧ φ) ∧ ∃xT(x)` is `false ∧ ∃xT(x) = false` (since `U(x) = false`
    and `meetMiddle false # = false`). The key asymmetry of Middle Kleene:
    `meetMiddle false # = false` but `meetMiddle # _ = #`. -/
theorem reverse_conj_transparency_fails :
    ∃ (W : Type) (D : Type) (E presup φ : W → PartialAssign D → Trivalent)
      (w : W) (g : PartialAssign D),
      Trivalent.meetMiddle (Trivalent.meetMiddle (presup w g) (φ w g)) (E w g) ≠
      Trivalent.meetMiddle (φ w g) (E w g) := by
  -- presup = U(x) = false (unvalued), φ = P(x) = # (unvalued), E = ∃xT(x) = true
  -- LHS: meetMiddle (meetMiddle false #) true = meetMiddle false true = false
  -- RHS: meetMiddle # true = #
  refine ⟨Unit, Unit, λ _ _ => .true, λ _ _ => .false, λ _ _ => .indet,
          (), λ _ => none, ?_⟩
  simp [Trivalent.meetMiddle]

end Conjunction

-- ════════════════════════════════════════════════════════════════
-- §3.3: Anaphora in Disjunctive Sentences (Bathroom Sentences)
-- ════════════════════════════════════════════════════════════════

section Bathroom

/-!
### Bathroom sentences: `¬∃xB(x) ∨ H(x̲)`

"Either there is no bathroom, or it is hidden," translated as
`¬∃xB(x) ∨ H(x̲)`. The Transparency question is: does
`¬∃xB(x) ∨ (U(x) ∧ φ)` always have the same truth value as
`¬∃xB(x) ∨ φ`?

The frame is `F(ψ) = joinMiddle (¬∃xB(x)) ψ`, and the presupposition
is `U(x)`.

**Proof** (§3.3): Consider `(w,g)`.
- If `¬∃xB(x)` is true at `(w,g)`: `joinMiddle true _ = true` (SK).
- If `¬∃xB(x)` is `#` at `(w,g)`: `joinMiddle # _ = #` (left absorbs).
- If `¬∃xB(x)` is false at `(w,g)`: then `∃xB(x)` is true, so `g`
  values `x`, so `U(x) = true`, so `meetMiddle true φ = φ`, and
  both disjunctions reduce to `joinMiddle false φ`.
-/

/-- Bathroom sentence Transparency: `¬∃xB(x) ∨ H(x̲)` satisfies
    Transparency in every context.

    The key insight: `¬E` being false means `E` is true, which (by the
    witness condition) means `g` values `x`, making `U(x)` redundant.
    Derived from `disj_transparency_parametric`. -/
theorem bathroom_transparency
    (negE presup : W → PartialAssign D → Trivalent)
    (hwitness : ∀ w g, negE w g = .false → presup w g = .true)
    (C : Ctx W D) :
    ∀ (φ : Sent W D) (w : W) (g : PartialAssign D), C w g →
      Trivalent.joinMiddle (negE w g) (Trivalent.meetMiddle (presup w g) (φ w g)) =
      Trivalent.joinMiddle (negE w g) (φ w g) :=
  fun φ w g _ => disj_transparency_parametric (negE w g) (presup w g) (φ w g) (hwitness w g)

/-- Reverse bathroom Transparency FAILS: `H(x̲) ∨ ¬∃xB(x)` does NOT
    satisfy Transparency in the null context.

    §3.3: Consider `g` that does not value `x` and a
    tautological `φ`. Then `φ ∨ ¬∃xB(x)` has `φ = #` (unvalued), so
    `joinMiddle # (¬∃xB(x)) = #`. But `(U(x) ∧ φ) ∨ ¬∃xB(x)` has
    `U(x) = false`, so `meetMiddle false # = false`, and
    `joinMiddle false (¬∃xB(x))` can be `true` — a difference. -/
theorem reverse_bathroom_transparency_fails :
    ∃ (W : Type) (D : Type) (negE presup φ : W → PartialAssign D → Trivalent)
      (w : W) (g : PartialAssign D),
      Trivalent.joinMiddle (Trivalent.meetMiddle (presup w g) (φ w g)) (negE w g) ≠
      Trivalent.joinMiddle (φ w g) (negE w g) := by
  -- presup = false (U(x) unvalued), φ = # (P(x) unvalued), negE = true
  -- LHS: joinMiddle (meetMiddle false #) true = joinMiddle false true = true
  -- RHS: joinMiddle # true = #
  refine ⟨Unit, Unit, λ _ _ => .true, λ _ _ => .false, λ _ _ => .indet,
          (), λ _ => none, ?_⟩
  simp [Trivalent.joinMiddle, Trivalent.meetMiddle]

end Bathroom

-- ════════════════════════════════════════════════════════════════
-- §2.1: Semantic Adequacy — Bathroom Trivalent Conditions
-- ════════════════════════════════════════════════════════════════

section BathroomTruthConditions

/-!
### Bathroom truth-condition equivalence

§2.1 proves that the trivalent sentence
`¬∃xB(x) ∨ F(x)` is true at a world `w` (in the sense of
definition (6): ∃g such that the sentence is `.true` at `(w,g)`)
if and only if the classical sentence `¬∃xB(x) ∨ ∃x(B(x) ∧ F(x))`
is true at `w`.

This is the key *semantic adequacy* result: the trivalent system
delivers the correct truth conditions, not just correct felicity
predictions.

**Proof outline** (two directions):

**(8) classically true → (7) true at some `(w,g)`**:
- Case 1: `∃xB(x)` classically false. Then for every `g`, `∃xB(x)`
  is false at `(w,g)`, so `¬∃xB(x)` is true, and `joinMiddle true _ = true`.
- Case 2: `∃x(B(x) ∧ F(x))` classically true. Pick witness `a`, set
  `g(x) = a`. Then `¬∃xB(x)` is false (since `g(x) = a` witnesses `B`),
  and `F(x)` is true. So `joinMiddle false true = true`.

**(7) true at some `(w,g)` → (8) classically true**:
- By Middle Kleene disjunction, either `¬∃xB(x)` is true at `(w,g)`
  (→ `∃xB(x)` classically false → first disjunct of (8)), or
  `¬∃xB(x)` is false and `F(x)` is true. In the latter case,
  `∃xB(x)` is true so `g(x) ∈ I(B,w)`, and `F(x)` true means
  `g(x) ∈ I(F,w)`, so `g(x)` witnesses `B(x) ∧ F(x)`.
-/

variable {D : Type} {W : Type}

/-- The trivalent sentence `¬∃xB(x) ∨ F(x)` evaluated at `(w,g)`,
    where `B` and `F` are one-place predicates and `x` is variable 0.

    Components:
    - `∃xB(x)`: true if `g(0) ∈ I(B,w)`, false if `∀d, d ∉ I(B,w)`,
      `#` if classically true but `g(0)` not a witness
    - `¬∃xB(x)`: negation (flips true/false, preserves `#`)
    - `F(x)`: `evalPred F g 0 w` (true/false/`#` depending on `g(0)`)
    - Overall: `joinMiddle (neg (∃xB(x))) (F(x))` -/
def bathroomSent (B F : Interp W D) (dom : List D)
    (w : W) (g : PartialAssign D) : Trivalent :=
  let existsB : Trivalent :=
    if evalPred B g 0 w = .true then .true
    else if dom.all (λ d => B w d == false) then .false
    else .indet
  let negExistsB := Trivalent.neg existsB
  let fx := evalPred F g 0 w
  Trivalent.joinMiddle negExistsB fx

/-- Classical truth of `¬∃xB(x) ∨ ∃x(B(x) ∧ F(x))`: either no element
    satisfies `B`, or some element satisfies both `B` and `F`. -/
def bathroomClassical (B F : Interp W D) (dom : List D) (w : W) : Prop :=
  dom.all (λ d => B w d == false) ∨
  ∃ d, d ∈ dom ∧ B w d = true ∧ F w d = true

/-- **Direction 1**: If the classical bathroom disjunction holds,
    then the trivalent sentence is true at `w`.

    §2.1: We construct a specific `g` that
    makes the trivalent sentence `.true`.

    - If no bathrooms exist: any `g` works (¬∃xB(x) is true,
      `joinMiddle true _ = true`).
    - If a bathroom `a` exists with `F(a)`: set `g(0) = a`.
      Then ¬∃xB(x) is false (a witnesses B), F(x) = F(a) = true,
      and `joinMiddle false true = true`. -/
theorem bathroom_classical_to_trivalent (B F : Interp W D) (dom : List D) (w : W)
    (h : bathroomClassical B F dom w) :
    trueAtWorld (bathroomSent B F dom) w := by
  rcases h with hnoB | ⟨d, _, hBd, hFd⟩
  · -- Case 1: no bathrooms. Pick any g — ¬∃xB(x) is true.
    refine ⟨PartialAssign.empty, ?_⟩
    simp only [bathroomSent]
    have hne : ¬(evalPred B PartialAssign.empty 0 w = .true) := by
      simp only [evalPred, PartialAssign.empty]; decide
    rw [if_neg hne, if_pos hnoB]
    simp [Trivalent.neg, Trivalent.joinMiddle]
  · -- Case 2: witness d with B(d) and F(d). Set g(0) = some d.
    refine ⟨λ _ => some d, ?_⟩
    simp only [bathroomSent]
    have heval : evalPred B (λ _ => some d) 0 w = .true := by
      simp only [evalPred, Trivalent.ofBool, hBd]
    rw [if_pos heval]
    simp [evalPred, Trivalent.ofBool, hFd, Trivalent.neg, Trivalent.joinMiddle]

/-- **Direction 2**: If the trivalent bathroom sentence is true at `w`,
    then the classical disjunction holds.

    §2.1: By Middle Kleene disjunction, the sentence
    is `.true` at `(w,g)` only if either:
    (a) `¬∃xB(x)` is `.true` → `∃xB(x)` is `.false` → no bathrooms, or
    (b) `¬∃xB(x)` is `.false` and `F(x)` is `.true`. In case (b),
        `∃xB(x)` is `.true`, so `g(0) ∈ I(B,w)` (witness condition),
        and `F(x) = true` means `g(0) ∈ I(F,w)`. So `g(0)` witnesses
        `B(x) ∧ F(x)`.

    Requires `dom` to list all elements of `D` (completeness). -/
theorem bathroom_trivalent_to_classical (B F : Interp W D) (dom : List D) (w : W)
    (hdom : ∀ d : D, d ∈ dom)
    (h : trueAtWorld (bathroomSent B F dom) w) :
    bathroomClassical B F dom w := by
  obtain ⟨g, hg⟩ := h
  simp only [bathroomSent] at hg
  -- Case split on the value of g(0) — the variable assignment
  cases hg0 : g 0 with
  | none =>
    -- g(0) undefined: evalPred B g 0 w = .indet ≠ .true
    have hne : ¬(evalPred B g 0 w = .true) := by
      simp only [evalPred, hg0]; decide
    rw [if_neg hne] at hg
    -- Now case split on whether all d have B w d = false
    cases hall : List.all dom (fun d => B w d == false)
    · -- existsB = .indet, negExistsB = .indet, joinMiddle .indet _ = .indet
      have hne2 : ¬((List.all dom fun d => B w d == false) = true) := by
        rw [hall]; decide
      rw [if_neg hne2] at hg
      -- hg : joinMiddle (neg .indet) _ = .true, i.e. joinMiddle .indet _ = .true
      -- but joinMiddle .indet _ = .indet, contradiction
      simp only [Trivalent.neg, Trivalent.joinMiddle] at hg
      exact absurd hg (by decide)
    · -- existsB = .false, negExistsB = .true → classical left disjunct
      exact Or.inl hall
  | some d =>
    cases hBd : B w d with
    | false =>
      -- evalPred B g 0 w = .false ≠ .true
      have hne : ¬(evalPred B g 0 w = .true) := by
        simp only [evalPred, hg0, Trivalent.ofBool, hBd]; decide
      rw [if_neg hne] at hg
      cases hall : List.all dom (fun d => B w d == false)
      · have hne2 : ¬((List.all dom fun d => B w d == false) = true) := by
          rw [hall]; decide
        rw [if_neg hne2] at hg
        simp only [Trivalent.neg, Trivalent.joinMiddle] at hg
        exact absurd hg (by decide)
      · exact Or.inl hall
    | true =>
      -- evalPred B g 0 w = .true: g(0) witnesses B
      have heval : evalPred B g 0 w = .true := by
        simp only [evalPred, hg0, Trivalent.ofBool, hBd]
      rw [if_pos heval] at hg
      -- existsB = .true, negExistsB = .false, joinMiddle .false fx = fx
      simp only [Trivalent.neg, Trivalent.joinMiddle] at hg
      -- hg says evalPred F g 0 w = .true
      simp only [evalPred, hg0, Trivalent.ofBool] at hg
      cases hFd : F w d
      · simp only [hFd] at hg; exact absurd hg (by decide)
      · exact Or.inr ⟨d, hdom d, hBd, hFd⟩

/-- **Bathroom truth-condition equivalence** (the complete iff).

    §2.1: The trivalent sentence `¬∃xB(x) ∨ F(x)`
    is true at world `w` if and only if the classical sentence
    `¬∃xB(x) ∨ ∃x(B(x) ∧ F(x))` is classically true at `w`.

    This is the key *semantic adequacy* result: the non-standard
    trivalent semantics with partial assignments delivers exactly
    the classical truth conditions for bathroom sentences. -/
theorem bathroom_truth_equiv (B F : Interp W D) (dom : List D) (w : W)
    (hdom : ∀ d : D, d ∈ dom) :
    trueAtWorld (bathroomSent B F dom) w ↔ bathroomClassical B F dom w :=
  ⟨bathroom_trivalent_to_classical B F dom w hdom,
   bathroom_classical_to_trivalent B F dom w⟩

end BathroomTruthConditions

-- ════════════════════════════════════════════════════════════════
-- §3.1: Free Variables Without Antecedent
-- ════════════════════════════════════════════════════════════════

/-- A bare pronoun `P(x̲)` is infelicitous in the null context.

    §3.1: In the null context, Transparency requires
    that for every `φ`, `U(x) ∧ φ` and `φ` have the same truth value
    across all `(w,g)`. But take `g` with `g(x) = #` and `φ` always true:
    `meetMiddle false true = false ≠ true`, so Transparency fails.

    The identity frame `F(ψ) = ψ` represents a bare sentence. -/
theorem bare_pronoun_fails_null :
    ∃ (W : Type) (D : Type) (presup φ : W → PartialAssign D → Trivalent)
      (w : W) (g : PartialAssign D),
      True  -- null context membership
      ∧ Trivalent.meetMiddle (presup w g) (φ w g) ≠ φ w g := by
  refine ⟨Unit, Unit, λ _ _ => .false, λ _ _ => .true,
          (), λ _ => none, trivial, ?_⟩
  simp [Trivalent.meetMiddle]

/-! ### Empirical coverage from §3

Spector's predictions cover the following items in adjacent files; the
mapping is recorded here in prose so that future readers can find the
relevant theorems without our duplicating the data file's stipulations
in `rfl`-equality theorems.

`forward_conj_transparency` (above) handles forward intersentential
anaphora across conjunction (`∃xT(x) ∧ P(x̲)`). It corresponds to
the bound reading of `Geach1962.Examples.donkey_classic` and to the
veridical-basic case of `Hofmann2025`.

`reverse_conj_transparency_fails` (above) corresponds to the cataphora
side of the same data (Hofmann's `negatedBasic`).

`bathroom_transparency` (below) handles the bathroom-disjunction pattern
(`¬∃xB(x) ∨ H(x̲)`, Roberts 1989; Hofmann's `bathroomDisjunction`).
It also covers the conditional-donkey pattern
(`¬∃xF(x) ∨ B(x̲)`, `Geach1962.Examples.donkey_classic` /
`Heim1982.Examples.conditional_donkey`).

`reverse_bathroom_transparency_fails` (below) accounts for the wrong-order
bathroom (Hofmann's `wrongOrderBathroom`) and for separate-sentence
configurations like `negationBlocks` and `conjunctionBlocks` where the
mechanism is unavailable for distinct reasons (no joint frame; conjunction
uses `meetMiddle` not `joinMiddle`).
-/

-- ════════════════════════════════════════════════════════════════
-- §6: Plural Assignment Semantics (The Full System)
-- ════════════════════════════════════════════════════════════════

/-!
## The plural assignment system

The preliminary system (§§2–5) fails on covariation: `¬∃x¬∃yS(x,y)`
("everybody spoke to somebody") wrongly requires a *single* person
everyone spoke to. The full system (§6) replaces individual partial
assignments with **plural assignments** — sets of atomic assignments.

Key changes from the simplified system:
- Evaluation is relative to `(w, G)` where `G : PluralAssign D`
- `U(x)` is replaced by `atomic(x)`: `|G(x)| = 1` (all assignments
  in `G` that define `x` agree on its value)
- The universal quantifier `∀xφ` is now well-defined
- Quantificational subordination works via inter-variable dependencies
  recorded in `G`
-/

-- ════════════════════════════════════════════════════════════════
-- §6.0: PluralAssign substrate now lives in `Linglib.Core.Logic.Assignment`
-- [van-den-berg-1996] [nouwen-2003] [brasoveanu-2008]
-- ════════════════════════════════════════════════════════════════

/-! Plural assignments are imported from `Core.Assignment` (`open Core`
    brings `PluralAssign`, `singularAt`, `singular`, `restrict`, `defined`,
    `null`, `ofPred`, `singleton`, `sumDref` into scope). Spector's static
    reuse is one consumer; the PPCDRT substrate
    (`Semantics/Dynamic/PPCDRT/`) is the other — once linglib has
    ≥2 consumers of plural-assignment machinery it belongs in `Core`. -/

section PluralSemantics

variable {D : Type*} {W : Type*}

open Classical

/-- Plural sentence: evaluated relative to a world and a plural assignment. -/
abbrev PSent (W : Type*) (D : Type*) := W → PluralAssign D → Trivalent

/-- Alias for `PluralAssign.singularAt` — `G` assigns `x` uniquely to `d`.
    §6.2: `|G(x)| = 1` with `G(x) = d`. -/
abbrev singularAt (G : PluralAssign D) (x : Nat) (d : D) : Prop :=
  G.singularAt x d

/-- Evaluate a one-place predicate relative to `(w, G)`.
    §6.2:
    - `1` if `|G(x)| = 1` and `G(x) ∈ I(P,w)`
    - `0` if `|G(x)| = 1` and `G(x) ∉ I(P,w)`
    - `#` if `|G(x)| ≠ 1` -/
noncomputable def evalPredPlural (I : Interp W D) (G : PluralAssign D)
    (x : Nat) (w : W) : Trivalent :=
  if h : ∃ d, singularAt G x d then
    Trivalent.ofBool (I w (Classical.choose h))
  else .indet

/-- The `atomic(x)` predicate as a Trivalent value.
    §6.3: `⟦atomic(x)⟧^{w,G} = 1` if `|G(x)| = 1`,
    `0` otherwise. Always bivalent (never `#`). Replaces `U(x)` from
    the simplified system. -/
noncomputable def atomicT3 (G : PluralAssign D) (x : Nat) : Trivalent :=
  if G.singular x then .true else .false

/-- `atomic(x)` is always defined (bivalent). -/
theorem atomicT3_defined (G : PluralAssign D) (x : Nat) :
    (atomicT3 G x).isDefined := by
  unfold atomicT3
  by_cases h : G.singular x
  · simp [h, Trivalent.isDefined]
  · simp [h, Trivalent.isDefined]

/-- Plural existential quantifier with witness condition.
    §6.2:
    - `1` if `⟦φ⟧^{w,G} = 1`
    - `0` if for every atomic `a ∈ D`, `G_{x=a} ≠ ∅` and `⟦φ⟧^{w,G_{x=a}} = 0`
    - `#` otherwise -/
noncomputable def existsPlural (x : Nat) (φ : PSent W D) (dom : Set D)
    (w : W) (G : PluralAssign D) : Trivalent :=
  if φ w G = .true then .true
  else if (∀ a ∈ dom, (G.restrict x a).IsNonempty) ∧
          (∀ a ∈ dom, φ w (G.restrict x a) = .false) then .false
  else .indet

/-- Plural universal quantifier.
    §6.2:
    - `1` if for every atomic `a ∈ D`, `G_{x=a} ≠ ∅` and `⟦φ⟧^{w,G_{x=a}} = 1`
    - `0` if the coverage condition holds and some `a` gives `⟦φ⟧^{w,G_{x=a}} = 0`
    - `#` otherwise -/
noncomputable def forallPlural (x : Nat) (φ : PSent W D) (dom : Set D)
    (w : W) (G : PluralAssign D) : Trivalent :=
  if (∀ a ∈ dom, (G.restrict x a).IsNonempty) ∧
     (∀ a ∈ dom, φ w (G.restrict x a) = .true) then .true
  else if (∀ a ∈ dom, (G.restrict x a).IsNonempty) ∧
          (∃ a ∈ dom, φ w (G.restrict x a) = .false) then .false
  else .indet

end PluralSemantics

-- ════════════════════════════════════════════════════════════════
-- §6.3: Transparency Replicates for Plural System
-- ════════════════════════════════════════════════════════════════

section PluralTransparency

variable {D : Type*} {W : Type*}

/-- Forward conjunction Transparency in the plural system, derived from
    the parametric version. -/
theorem plural_forward_conj_transparency
    (E presup : W → PluralAssign D → Trivalent)
    (hwitness : ∀ w G, E w G = .true → presup w G = .true) :
    ∀ (φ : W → PluralAssign D → Trivalent) (w : W) (G : PluralAssign D),
      Trivalent.meetMiddle (E w G) (Trivalent.meetMiddle (presup w G) (φ w G)) =
      Trivalent.meetMiddle (E w G) (φ w G) :=
  fun φ w G => conj_transparency_parametric (E w G) (presup w G) (φ w G) (hwitness w G)

/-- Bathroom Transparency in the plural system, derived from
    the parametric version. -/
theorem plural_bathroom_transparency
    (negE presup : W → PluralAssign D → Trivalent)
    (hwitness : ∀ w G, negE w G = .false → presup w G = .true) :
    ∀ (φ : W → PluralAssign D → Trivalent) (w : W) (G : PluralAssign D),
      Trivalent.joinMiddle (negE w G) (Trivalent.meetMiddle (presup w G) (φ w G)) =
      Trivalent.joinMiddle (negE w G) (φ w G) :=
  fun φ w G => disj_transparency_parametric (negE w G) (presup w G) (φ w G) (hwitness w G)

end PluralTransparency

-- ════════════════════════════════════════════════════════════════
-- §6.3: Universal Quantifier Does Not License Anaphora
-- ════════════════════════════════════════════════════════════════

section UniversalAnaphora

/-!
### Universal doesn't introduce a discourse referent

§6.3 (pp.20–21): `∀xP(x) ∧ Q(x̲)` does NOT
satisfy Transparency in the null context. When `∀xP(x)` is true
at `(w,G)`, `G(x)` contains all atomic individuals in `D`, so
`|G(x)| ≠ 1` (assuming `|D| ≥ 2`), and therefore `atomic(x)` is
false. This means the universal quantifier cannot serve as the
antecedent of a singular pronoun.
-/

/-- The universal quantifier does not license subsequent singular
    anaphora. For two-element domains: `∀xP(x)` being true forces
    `|G(x)| > 1`, making `atomic(x)` false.

    §6.3: the sentences `∀xP(x) ∧ (atomic(x) ∧ φ)`
    and `∀xP(x) ∧ φ` can differ — taking `φ` tautological, the first
    is false (since `atomic(x)` is false when `|G(x)| > 1`) while
    the second is true. -/
theorem universal_doesnt_license_anaphora :
    ∃ (D : Type) (presup φ : PluralAssign D → Trivalent)
      (G : PluralAssign D),
      -- presup = atomic(x) = false (two values for x)
      -- φ = tautology = true
      Trivalent.meetMiddle (presup G) (φ G) ≠ φ G := by
  -- D = Bool, G has two assignments: one mapping x to true, one to false
  -- So |G(x)| = 2, atomic(x) = false
  refine ⟨Bool, λ _ => .false, λ _ => .true, ⟨λ _ => True⟩, ?_⟩
  simp [Trivalent.meetMiddle]

end UniversalAnaphora

-- ════════════════════════════════════════════════════════════════
-- §5/§6.4: Covariation — The Fix
-- ════════════════════════════════════════════════════════════════

section Covariation

/-!
### The covariation problem and its fix

§5: In the simplified (individual-assignment) system,
`¬∃x¬∃yS(x,y)` ("everybody spoke to somebody") is true at `(w,g)` iff
for all `a`, `(a, g(y)) ∈ I(S,w)`. This wrongly gives a *constant-witness*
reading: "everyone spoke to `g(y)`" — a single person.

§6.4: With plural assignments, the innermost ∃y
is evaluated relative to `G_{x=a}` for each `a`, so different `a`'s can
pair with different `b`'s. The sentence now correctly means
"for every `a` there exists `b` such that `(a,b) ∈ S`."
-/

variable {D : Type*} {W : Type*}

/-- The covariation fix: with plural assignments, the universal-existential
    pattern is correctly expressible.

    §6.4: If a world satisfies `∀x∃y S(x,y)`, we can
    build a plural assignment `G` that witnesses each `a`-`b` pair
    independently. This is impossible with individual assignments, where
    a single `g(y)` must work for all values of `x`. -/
theorem covariation_fixed
    (S : W → D → D → Bool) (dom : List D)
    (w : W)
    (hcovar : ∀ a : D, a ∈ dom → ∃ b : D, b ∈ dom ∧ S w a b = true) :
    -- There exists a plural assignment G with a witness for each a
    ∃ G : PluralAssign D,
      ∀ a ∈ dom, ∃ b ∈ dom, ∃ g : PartialAssign D, g ∈ G ∧
        g 0 = some a ∧ g 1 = some b ∧ S w a b = true := by
  -- Build G: for each a, include an assignment g_a with g(x)=a, g(y)=b
  -- where b is a's S-partner.
  let G : PluralAssign D := ⟨λ g => ∃ a ∈ dom, ∃ b ∈ dom,
    S w a b = true ∧ g 0 = some a ∧ g 1 = some b⟩
  refine ⟨G, λ a ha => ?_⟩
  obtain ⟨b, hb, hSab⟩ := hcovar a ha
  let g : PartialAssign D := λ n =>
    if n = 0 then some a else if n = 1 then some b else none
  exact ⟨b, hb, g, ⟨a, ha, b, hb, hSab, rfl, rfl⟩, rfl, rfl, hSab⟩

/-- In contrast, with individual assignments the covariation reading fails:
    a single assignment can only provide one witness for `y`, which must
    work for ALL values of `x`. -/
theorem covariation_fails_individual :
    -- A two-element domain where everyone spoke to someone,
    -- but no single person was spoken to by everyone
    ∃ (D W : Type) (S : W → D → D → Bool) (w : W)
      (_ : ∀ a : D, ∃ b : D, S w a b = true),
      -- No single partial assignment g witnesses this for all x
      ¬∃ g : PartialAssign D, ∀ a : D,
        ∃ b : D, g 1 = some b ∧ S w a b = true := by
  refine ⟨Bool, Unit, λ _ a b => a != b, (), ?_, ?_⟩
  · intro a; exact ⟨!a, by cases a <;> rfl⟩
  · intro ⟨g, hg⟩
    obtain ⟨b₁, hb₁, hs₁⟩ := hg true
    obtain ⟨b₂, hb₂, hs₂⟩ := hg false
    -- g(1) = some b₁ and g(1) = some b₂, so b₁ = b₂
    rw [hb₁] at hb₂; cases hb₂
    -- But S w true b₁ = true requires b₁ = false,
    -- and S w false b₁ = true requires b₁ = true. Contradiction.
    cases b₁ <;> simp_all

end Covariation

-- ════════════════════════════════════════════════════════════════
-- §7: Weak and Strong Trivalent
-- ════════════════════════════════════════════════════════════════

section WeakStrongTruth

variable {D : Type*} {W : Type*}

/-!
### Two notions of truth at a world

§7: Two modes of interpretation for donkey sentences:

- **Weak Trivalent**: `S` is weakly true at `w` if ∃G such that `S` is true
  at `(w,G)`. Generates *existential* (weak) readings.

- **Strong Trivalent**: `S` is strongly true at `w` if ∃G true at `(w,G)`
  AND no `G'` makes `S` false at `(w,G')`. Generates *universal* (strong)
  readings. Similar to [elliott-2023]'s strengthened reading and
  [champollion-bumford-henderson-2019]'s homogeneity approach.

For simple existentials `∃xP(x)`, weak and strong truth coincide.
They diverge for donkey sentences.
-/

/-- Weak truth at a world: ∃G such that the sentence is true at (w,G).
    §7 (46a). -/
def weakTruthP (φ : PSent W D) (w : W) : Prop :=
  ∃ G : PluralAssign D, φ w G = .true

/-- Strong truth at a world: weakly true AND not weakly false.
    §7 (46b). -/
def strongTruthP (φ : PSent W D) (w : W) : Prop :=
  (∃ G : PluralAssign D, φ w G = .true) ∧
  ¬∃ G : PluralAssign D, φ w G = .false

/-- Strong truth implies weak truth. -/
theorem strongTruth_implies_weakTruth (φ : PSent W D) (w : W)
    (h : strongTruthP φ w) : weakTruthP φ w :=
  h.1

/-! ### Reading preferences (§7) — empirical mapping

Spector argues (§7) that `weakTruthP` generates *weak* (existential)
readings by default and that `strongTruthP` generates *strong*
(universal) readings. Kanazawa's (1994) generalization picks one or the
other based on the monotonicity profile of the surrounding quantifier:
upward-entailing contexts (`some`) prefer weak; downward-entailing
contexts (`no`, the negated donkey) prefer strong.

End-to-end derivations of these readings on a concrete toy world
(corresponding to `Geach1962.Examples.donkey_classic` and Kanazawa's
negated donkey "No farmer who owns a donkey beats it") are deferred —
see §6.7 entry in the **Deferred work** docstring at the end of this
file.
-/

end WeakStrongTruth

-- ════════════════════════════════════════════════════════════════
-- §7: The Strong Trivalent Operator O
-- ════════════════════════════════════════════════════════════════

section StrongTruthOperator

variable {D : Type*} {W : Type*}

open Classical

/-!
### The Strong Trivalent Operator

§7 (55): The operator `O` internalizes Strong Trivalent
as an embeddable operator in the object language:

    ⟦O(S)⟧^{w,G} = 1 if ⟦S⟧^{w,G} = 1 and ¬∃G'. ⟦S⟧^{w,G'} = 0
    ⟦O(S)⟧^{w,G} = 0 if ⟦S⟧^{w,G} = 0 and ¬∃G'. ⟦S⟧^{w,G'} = 1
    ⟦O(S)⟧^{w,G} = # otherwise

This allows Strong Trivalent to be applied at specific syntactic positions
rather than globally. Key properties:
- If S₁ ≡ S₂ (logically equivalent), then O(S₁) ≡ O(S₂)
- O can *violate* Transparency when embedded, which is desirable:
  `∃xS(x) ∧ O(H(x̲))` is correctly predicted to be infelicitous
-/

/-- The Strong Trivalent Operator O.
    §7 (55). -/
noncomputable def strongTruthOp (φ : PSent W D)
    (w : W) (G : PluralAssign D) : Trivalent :=
  if φ w G = .true ∧ ¬∃ G', φ w G' = .false then .true
  else if φ w G = .false ∧ ¬∃ G', φ w G' = .true then .false
  else .indet

/-- O preserves logical equivalence: if φ₁ and φ₂ agree everywhere,
    O(φ₁) and O(φ₂) agree everywhere.
    §7 (57). -/
theorem strongTruthOp_preserves_equiv (φ₁ φ₂ : PSent W D)
    (hequiv : ∀ w G, φ₁ w G = φ₂ w G) :
    ∀ w G, strongTruthOp φ₁ w G = strongTruthOp φ₂ w G := by
  intro w G
  simp only [strongTruthOp, hequiv]

/-- O(S) is true at (w,G) implies S is true at (w,G). -/
theorem strongTruthOp_true_implies (φ : PSent W D) (w : W)
    (G : PluralAssign D) (h : strongTruthOp φ w G = .true) :
    φ w G = .true := by
  simp only [strongTruthOp] at h
  split at h
  · exact (‹_ ∧ _›).1
  · split at h <;> simp_all

/-- Strong truth at w ↔ weak truth of O(S) at w.
    Embedding O at matrix level recovers the Strong Trivalent interpretation. -/
theorem strongTruthOp_weakTruth_iff_strongTruth (φ : PSent W D) (w : W) :
    weakTruthP (strongTruthOp φ) w ↔ strongTruthP φ w := by
  constructor
  · intro ⟨G, hG⟩
    simp only [strongTruthOp] at hG
    split at hG
    · rename_i h; exact ⟨⟨G, h.1⟩, h.2⟩
    · split at hG <;> simp_all
  · intro ⟨⟨G, hGt⟩, hnf⟩
    refine ⟨G, ?_⟩
    simp only [strongTruthOp]
    have h : φ w G = .true ∧ ¬∃ G', φ w G' = .false := ⟨hGt, hnf⟩
    rw [if_pos h]

end StrongTruthOperator

-- ════════════════════════════════════════════════════════════════
-- Cross-System Comparison: Spector vs. DPL
-- ════════════════════════════════════════════════════════════════

section Comparison

/-!
### Spector's static system vs. Dynamic Predicate Logic

positions the system as a non-dynamic alternative to
DPL ([groenendijk-stokhof-1991]). Key comparison:

| Phenomenon | Spector | DPL |
|---|---|---|
| Forward conj `∃xP(x) ∧ Q(x)` | ✓ Transparency | ✓ assignment persistence |
| Reverse conj `Q(x) ∧ ∃xP(x)` | ✗ Middle Kleene | ✗ x not yet bound |
| Bathroom `¬∃xB(x) ∨ F(x)` | **✓ Transparency** | **✗ negation is test** |
| Neg blocks `¬∃xP(x). Q(x)` | ✗ no frame | ✗ negation is test |

The systems agree on 3/4 cases. The disagreement on bathroom sentences
is significant: standard DPL cannot handle them because negation is a
test that doesn't export assignments ([krahmer-muskens-1995]),
while Spector's Transparency-based approach handles them naturally via
Middle Kleene disjunction. The bathroom row is witnessed in Spector's
favour by `bathroom_transparency` together with
`reverse_bathroom_transparency_fails`; for an independent formalization
of the `¬∃xB(x) ∨ F(x)` truth conditions, see `bathroom_truth_equiv`.
-/

end Comparison

/-! ## Deferred work

Items from Spector (2025) that this file does not yet formalize. Each is
a real piece of the paper; collected here so future work has explicit
grep-able anchors.

- **§5 covariation failure proof.** `covariation_fails_individual` (above)
  proves a different statement (a single `g` cannot witness `y` for all
  `x`); the actual paper claim — that the simplified individual-assignment
  semantics produces a constant-witness reading for `¬∃x¬∃yS(x,y)` — is
  not yet derived.

- **§6.7 donkey sentence end-to-end.** The classical donkey sentence
  `∀x(¬(F(x) ∧ ∃y(D(y) ∧ O(x,y))) ∨ B(x,y))` and its weak existential
  reading are summarized in prose but not proved on a concrete toy world.
  Spector's Tables 4–5 use 7 individuals; a 4-individual `decide`-checked
  variant would suffice.

- **§7 Strong Trivalent examples (47), (54).** The operator `O` is defined
  and proved equivalence-preserving (`strongTruthOp_preserves_equiv`,
  `strongTruthOp_weakTruth_iff_strongTruth`); the central motivating
  examples (`Either it's not the case that Sue has a credit card and bought
  a cake with it…`, the donkey-disjunction `O` parse of (54-c)) are not.

- **Appendix functional variables.** Spector's solution to
  quantificational subordination over indefinites (`y_x(z)` functional
  variables, paper (64)–(66)) is entirely deferred.

- **Witness-condition substrate.** The Mandelkern (2022) witness
  condition is currently inlined into `existsT3` / `existsPlural` here
  (one-line stipulation each). A faithful Mandelkern 2022 study file
  would let those derive from the witness primitive instead. Deferred
  pending paper access; cite key `mandelkern-2022` exists in
  `references.bib` with role `cited`, sources `crossref`. Per Spector
  p. 10, Mandelkern's system is quadrivalent + uses local-context
  bound clauses + uses individual (not plural) assignments — a
  substantive stub, not a quick one.

- **`noveltyCondition` enforcement.** The definition (in
  `section AbstractTransparency` above) has no consumer; §4 examples
  like (16) — `∃xP(x).∃xQ(x)` collapsing to `∃x(P(x) ∧ Q(x))` — are
  not ruled out by any current theorem in this file.
-/

end Spector2025
