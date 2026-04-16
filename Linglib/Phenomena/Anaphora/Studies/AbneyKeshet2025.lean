import Linglib.Theories.Semantics.PIP.Composition
import Linglib.Theories.Semantics.PIP.Bridges
import Linglib.Phenomena.Anaphora.Studies.KeshetAbney2024

/-!
# Abney & Keshet (2025): PIP Compositional Operations

@cite{abney-keshet-2025} @cite{keshet-abney-2024}

The Glossa companion paper to @cite{keshet-abney-2024} enriches PIP with
explicit set-based compositional operations: sigma evaluation (Σxφ),
set-based generalized quantifiers (EVERY/SOME as set inclusion/intersection),
three-argument modals with modal bases, and the FX type-lifting operation
for restricted variables.

This file verifies these operations on finite models and demonstrates the
paper's predictions about quantificational subordination, strong donkey
anaphora, modal subordination, and the exists/sigma bridge.

## Worked Examples

1. **Sigma evaluation** — Σx(farmer(x)) = {alice, bob} on a finite model
2. **Sigma set algebra** — Σx(φ∧ψ) = Σxφ ∩ Σxψ instantiated
3. **GQ over sigma sets** — EVERY(Σf farmer, Σf (farmer∧buyer)) via `setEvery`
4. **Quantificational subordination** — Σx(farmer(x) ∧ bought-donkey(x)) ⊆ Σx(farmer(x))
5. **Exists↔sigma bridge** — ∃x(farmer(x)) ↔ (Σx(farmer(x))).Nonempty
6. **Strong donkey** — summation pronouns as exhaustive sigma sets
7. **FX thematic roles** — ↑AGENT accumulates assertions
8. **Paycheck pronouns** — sigma set varies with external free variable
9. **Modal subordination** — MUST/MIGHT on two-world intensional model
-/

namespace AbneyKeshet2025

open Semantics.PIP
open Semantics.PIP.Bridges (single plural setEvery_eq_pipEvery)


-- ============================================================
-- Model 1: Extensional Farmer/Donkey Domain (1 world, 4 entities)
-- ============================================================

/-- Four-entity domain: two farmers and two donkeys. -/
inductive Ent where
  | alice | bob | spot | rex
  deriving DecidableEq, Repr

/-- Single-world model (extensional fragment). -/
inductive W1 where
  | w0
  deriving DecidableEq, Repr, Inhabited

instance : FiniteDomain Ent where
  elements := [.alice, .bob, .spot, .rex]
  complete d := by cases d <;> simp

instance : Core.Proposition.FiniteWorlds W1 where
  worlds := [.w0]
  complete w := by cases w; simp


-- ============================================================
-- §1: Sigma Evaluation on Finite Model
-- ============================================================

section SigmaFinite

/-- Farmer predicate: true for alice and bob. -/
def farmerBody : Ent → PIPExprF W1 Ent
  | .alice | .bob => .pred (λ _ => true)
  | .spot | .rex => .pred (λ _ => false)

/-- Donkey predicate: true for spot and rex. -/
def donkeyBody : Ent → PIPExprF W1 Ent
  | .spot | .rex => .pred (λ _ => true)
  | .alice | .bob => .pred (λ _ => false)

/-- Alice is a farmer (in the sigma set). -/
theorem sigma_farmer_alice : Ent.alice ∈ sigmaEval farmerBody W1.w0 := rfl

/-- Bob is a farmer. -/
theorem sigma_farmer_bob : Ent.bob ∈ sigmaEval farmerBody W1.w0 := rfl

/-- Spot is not a farmer. -/
theorem sigma_farmer_not_spot : Ent.spot ∉ sigmaEval farmerBody W1.w0 := Bool.false_ne_true

/-- Rex is not a farmer. -/
theorem sigma_farmer_not_rex : Ent.rex ∉ sigmaEval farmerBody W1.w0 := Bool.false_ne_true

/-- Spot is a donkey. -/
theorem sigma_donkey_spot : Ent.spot ∈ sigmaEval donkeyBody W1.w0 := rfl

/-- Alice is not a donkey. -/
theorem sigma_donkey_not_alice : Ent.alice ∉ sigmaEval donkeyBody W1.w0 := Bool.false_ne_true

end SigmaFinite


-- ============================================================
-- §2: Sigma Set Algebra
-- ============================================================

section SigmaAlgebra

/-- Σx(farmer ∧ donkey) = Σx(farmer) ∩ Σx(donkey) — no entity is both. -/
theorem sigma_conj_farmer_donkey :
    sigmaEval (λ d => PIPExprF.conj (farmerBody d) (donkeyBody d)) W1.w0 =
    sigmaEval farmerBody W1.w0 ∩ sigmaEval donkeyBody W1.w0 :=
  sigmaEval_conj farmerBody donkeyBody W1.w0

/-- Σx(farmer ∨ donkey) = Σx(farmer) ∪ Σx(donkey) — all four entities. -/
theorem sigma_disj_farmer_donkey :
    sigmaEval (λ d => PIPExprF.disj (farmerBody d) (donkeyBody d)) W1.w0 =
    sigmaEval farmerBody W1.w0 ∪ sigmaEval donkeyBody W1.w0 :=
  sigmaEval_disj farmerBody donkeyBody W1.w0

/-- Verify: the farmer∧donkey intersection is empty. -/
theorem farmer_donkey_disjoint (d : Ent) :
    d ∉ sigmaEval (λ d => PIPExprF.conj (farmerBody d) (donkeyBody d)) W1.w0 := by
  cases d <;> exact Bool.false_ne_true

end SigmaAlgebra


-- ============================================================
-- §3: GQ over Sigma Sets — EVERY/SOME as set inclusion
-- ============================================================

section GQSigma

/-- "Bought a donkey" predicate: alice and bob each bought one. -/
def boughtDonkeyBody : Ent → PIPExprF W1 Ent
  | .alice | .bob => .pred (λ _ => true)
  | .spot | .rex => .pred (λ _ => false)

/--
EVERY(Σf farmer, Σf (farmer ∧ boughtDonkey)) — via `setEvery`.

"Every farmer bought a donkey" modeled as: the set of farmers is a
subset of the set of farmer-buyers. This connects to the GQ bridge
in `Bridges.lean` via `setEvery_eq_pipEvery`.
-/
theorem every_farmer_bought_donkey :
    setEvery
      (sigmaEval farmerBody W1.w0)
      (sigmaEval (λ d => PIPExprF.conj (farmerBody d) (boughtDonkeyBody d)) W1.w0) := by
  intro d hd
  -- d ∈ sigmaEval farmerBody means (farmerBody d).truth w0 = true
  -- For alice and bob, boughtDonkeyBody also returns true
  cases d with
  | alice => rfl
  | bob => rfl
  | spot => exact absurd hd Bool.false_ne_true
  | rex => exact absurd hd Bool.false_ne_true

/--
SOME(Σf donkey, Σf farmerBody) — no donkey is a farmer.
This demonstrates `setSome` negation: the intersection is empty.
-/
theorem no_donkey_is_farmer :
    ¬setSome (sigmaEval donkeyBody W1.w0) (sigmaEval farmerBody W1.w0) := by
  intro ⟨d, hd, hf⟩
  cases d with
  | alice => exact absurd hd Bool.false_ne_true
  | bob => exact absurd hd Bool.false_ne_true
  | spot => exact absurd hf Bool.false_ne_true
  | rex => exact absurd hf Bool.false_ne_true

end GQSigma


-- ============================================================
-- §4: Quantificational Subordination (paper §4.4)
-- ============================================================

section Subordination

/--
Quantificational subordination:

"Every farmer bought a donkey. He vaccinated it."

The subordinate quantifier's sigma set (farmers who bought a donkey
and vaccinated it) is a subset of the main quantifier's sigma set
(farmers). This follows from `sigma_subordination`.
-/
theorem farmer_buyer_subordination :
    sigmaEval (λ d => PIPExprF.conj (farmerBody d) (boughtDonkeyBody d)) W1.w0 ⊆
    sigmaEval farmerBody W1.w0 :=
  sigma_subordination farmerBody boughtDonkeyBody W1.w0

/-- All farmer-buyers are indeed farmers (pointwise verification). -/
theorem farmer_buyer_alice :
    Ent.alice ∈ sigmaEval (λ d => PIPExprF.conj (farmerBody d) (boughtDonkeyBody d)) W1.w0 := rfl

theorem farmer_buyer_spot_excluded :
    Ent.spot ∉ sigmaEval (λ d => PIPExprF.conj (farmerBody d) (boughtDonkeyBody d)) W1.w0 :=
  Bool.false_ne_true

end Subordination


-- ============================================================
-- §5: Exists↔Sigma Bridge
-- ============================================================

section ExistsSigma

/-- ∃x(farmer(x)) is true (at least one farmer exists). -/
theorem exists_farmer : (PIPExprF.exists_ farmerBody).truth W1.w0 = true := by native_decide

/-- The sigma bridge: ∃x(farmer(x)) ↔ nonempty sigma set. -/
theorem exists_farmer_bridge :
    (PIPExprF.exists_ farmerBody).truth W1.w0 = true ↔
    (sigmaEval farmerBody W1.w0).Nonempty :=
  exists_iff_sigma_nonempty farmerBody W1.w0

/-- ∀x(farmer(x)) is false (donkeys are not farmers). -/
theorem forall_farmer_false :
    (PIPExprF.forall_ farmerBody).truth W1.w0 = false := by native_decide

end ExistsSigma


-- ============================================================
-- §6: Strong Donkey — Summation Pronouns as Exhaustive Sigma
-- ============================================================

section StrongDonkey

/-!
Strong donkey anaphora via summation pronouns (paper's §4.3 analysis):

"Every farmer who bought a donkey vaccinated **them**."

The pronoun "them" is a summation pronoun: its denotation is the
sigma set of all farmer-buyers, not a single witness. As noted in
`PIP.Composition`, summation pronoun denotation IS `sigmaEval` — the
distinction from simple pronouns is presuppositional (PL vs SG),
handled by `PIP.Bridges.plural`.
-/

/-- Both alice and bob are in the sigma set — exhaustive, not a single witness. -/
theorem strong_donkey_alice :
    Ent.alice ∈ sigmaEval
      (λ d => PIPExprF.conj (farmerBody d) (boughtDonkeyBody d)) W1.w0 := rfl

theorem strong_donkey_bob :
    Ent.bob ∈ sigmaEval
      (λ d => PIPExprF.conj (farmerBody d) (boughtDonkeyBody d)) W1.w0 := rfl

/-- The sigma set has 2+ elements → plural presupposition satisfied. -/
theorem strong_donkey_plural :
    plural (sigmaEval (λ d => PIPExprF.conj (farmerBody d) (boughtDonkeyBody d)) W1.w0) :=
  ⟨.alice, .bob, Ent.noConfusion, rfl, rfl⟩

end StrongDonkey


-- ============================================================
-- §7: FX Operation — Thematic Roles
-- ============================================================

section FXRoles

/-- AGENT role predicate: alice and bob are agents. -/
def agentRole : Ent → W1 → Bool
  | .alice, _ | .bob, _ => true
  | .spot, _ | .rex, _ => false

/-- PATIENT role predicate: spot and rex are patients. -/
def patientRole : Ent → W1 → Bool
  | .spot, _ | .rex, _ => true
  | .alice, _ | .bob, _ => false

def buyEvent : W1 → Bool := λ _ => true

/-- ↑AGENT(buy)(alice) = true — alice is an agent of buying. -/
theorem fx_agent_alice : fxApply agentRole buyEvent Ent.alice W1.w0 = true := by decide

/-- ↑AGENT(buy)(spot) = false — spot is not an agent. -/
theorem fx_agent_spot : fxApply agentRole buyEvent Ent.spot W1.w0 = false := by decide

/-- Iterated FX: ↑PATIENT(↑AGENT(buy))(spot) = false — agent fails for spot. -/
theorem fx_double_spot :
    fxApply patientRole (fxApply agentRole buyEvent Ent.spot) Ent.spot W1.w0 = false := by decide

/-- ↑PATIENT(↑AGENT(buy))(alice, alice) — decomposes by fxApply_twice. -/
theorem fx_double_decomposes :
    fxApply patientRole (fxApply agentRole buyEvent Ent.alice) Ent.alice W1.w0 =
    (patientRole Ent.alice W1.w0 && agentRole Ent.alice W1.w0 && buyEvent W1.w0) :=
  fxApply_twice agentRole patientRole buyEvent Ent.alice W1.w0

end FXRoles


-- ============================================================
-- §8: Paycheck Pronouns (paper §4.2)
-- ============================================================

section PaycheckPronouns

/-!
Paycheck pronouns (paper's §4.2, Karttunen 1969, Jacobson 2000):

"Almost every girl brought the diorama she made to class.
 Very few of them forgot it at home."

The pronoun "it" is a summation pronoun whose antecedent formula
`D ≡ DIORAMA([d]) ∧ MADE(x, d)` contains a free variable `x`
bound by a *different* quantifier at the pronoun's use site vs its
antecedent's. The sigma set `ΣdD` varies with `x`: when x = alice,
it denotes alice's diorama(s); when x = bob, bob's diorama(s).

This is the defining property of paycheck pronouns. PIP handles them
via summation pronouns with formula labels that contain free variables.
Dynamic logics struggle with this because they only store individuals
already quantified over, not formulas with free variables.
-/

/-- Diorama predicate: d1 and d2 are dioramas. -/
def dioramaBody : Ent → PIPExprF W1 Ent
  | .spot => .pred (λ _ => true)   -- spot = "diorama d1"
  | .rex  => .pred (λ _ => true)   -- rex  = "diorama d2"
  | .alice | .bob => .pred (λ _ => false)

/--
"Made" relation parameterized by maker (external free variable x):
alice made spot (d1), bob made rex (d2).
-/
def madeBody (maker : Ent) : Ent → PIPExprF W1 Ent
  | d => .pred (λ _ => match maker, d with
    | .alice, .spot => true   -- alice made d1
    | .bob, .rex   => true    -- bob made d2
    | _, _         => false)

/--
Paycheck body: `D ≡ DIORAMA([d]) ∧ MADE(x, d)` with x as free variable.
The sigma set ΣdD depends on who x is.
-/
def paycheckBody (maker : Ent) (d : Ent) : PIPExprF W1 Ent :=
  .conj (dioramaBody d) (madeBody maker d)

/-- When x = alice, ΣdD = {spot} (alice's diorama). -/
theorem paycheck_alice_spot :
    Ent.spot ∈ sigmaEval (paycheckBody .alice) W1.w0 := rfl

theorem paycheck_alice_not_rex :
    Ent.rex ∉ sigmaEval (paycheckBody .alice) W1.w0 := Bool.false_ne_true

/-- When x = bob, ΣdD = {rex} (bob's diorama). -/
theorem paycheck_bob_rex :
    Ent.rex ∈ sigmaEval (paycheckBody .bob) W1.w0 := rfl

theorem paycheck_bob_not_spot :
    Ent.spot ∉ sigmaEval (paycheckBody .bob) W1.w0 := Bool.false_ne_true

/--
The paycheck property: the sigma set varies with the external free
variable. This is what distinguishes paycheck pronouns from ordinary
anaphora — the pronoun's denotation depends on who the binder is.
-/
theorem paycheck_varies :
    sigmaEval (paycheckBody .alice) W1.w0 ≠
    sigmaEval (paycheckBody .bob) W1.w0 := by
  intro h
  have : Ent.spot ∈ sigmaEval (paycheckBody .bob) W1.w0 :=
    h ▸ paycheck_alice_spot
  exact paycheck_bob_not_spot this

/-- Each maker's sigma set is a singleton — satisfying the SG presupposition. -/
theorem paycheck_alice_single :
    single (sigmaEval (paycheckBody .alice) W1.w0) :=
  ⟨.spot, Set.eq_singleton_iff_unique_mem.mpr
    ⟨rfl, fun d hd => by cases d <;> first | rfl | exact absurd hd Bool.false_ne_true⟩⟩

theorem paycheck_bob_single :
    single (sigmaEval (paycheckBody .bob) W1.w0) :=
  ⟨.rex, Set.eq_singleton_iff_unique_mem.mpr
    ⟨rfl, fun d hd => by cases d <;> first | rfl | exact absurd hd Bool.false_ne_true⟩⟩

end PaycheckPronouns


-- ============================================================
-- Model 2: Intensional Modal Domain (2 worlds)
-- ============================================================

/-- Two-world model for modal subordination. -/
inductive W2 where
  | actual | alt
  deriving DecidableEq, Repr, Inhabited

instance : Core.Proposition.FiniteWorlds W2 where
  worlds := [.actual, .alt]
  complete w := by cases w <;> simp


-- ============================================================
-- §9: Modal Subordination (paper's §4.5 analysis)
-- ============================================================

section ModalSubordination

/-!
Modal subordination (paper's §4.5, Roberts 1987 wolf example):

"A wolf might come in. It would eat you first."

  MIGHT(β_w, ΣwW)     where W ≡ (WOLF([x]) ∧ ENTERS(x))
  MUST(β_w, ΣwW, ΣwE) where E ≡ (W ∧ TIM([t]) ∧ EATS(x,t))

The nuclear scope of the first sentence is stored in label W. The
restriction of the second sentence's MUST is anaphoric to W — this
is modal subordination, parallel to quantificational subordination.
-/

/-- Modal base: actual can access alt, and alt accesses itself. -/
def modalBase : Set W2 := {.actual, .alt}

/-- Worlds where a wolf enters (only alt). -/
def wolfEntersW : Set W2 := {.alt}

/-- Worlds where the wolf eats Tim (also only alt). -/
def wolfEatsTimW : Set W2 := {.alt}

/--
MIGHT(β, ⊤, wolfEnters) — a wolf might enter.
The modal base intersected with the wolf-enters set is nonempty.
-/
theorem wolf_might_enter :
    mightBase modalBase Set.univ wolfEntersW :=
  ⟨.alt, ⟨Set.mem_insert_iff.mpr (Or.inr rfl), trivial⟩, rfl⟩

/--
MUST(β, wolfEnters, wolfEatsTim) — it would eat Tim.
Modal subordination: the restriction wolfEnters (from the first
sentence's label W) constrains MUST. Every wolf-entry world is
also a wolf-eats-Tim world.
-/
theorem wolf_must_eat_tim :
    mustBase modalBase wolfEntersW wolfEatsTimW := by
  intro w ⟨_, hw⟩
  -- w ∈ modalBase ∩ wolfEntersW, so w = .alt
  exact hw

/--
Modal duality instantiated: ¬MUST(β, ⊤, wolfEnters) because the
wolf doesn't enter at actual.
-/
theorem wolf_not_must_enter :
    ¬mustBase modalBase Set.univ wolfEntersW := by
  intro h
  have := h ⟨Set.mem_insert _ _, trivial⟩
  exact absurd this (show W2.actual ∉ wolfEntersW from fun h => nomatch h)

/--
Modal duality: ¬MUST ↔ MIGHT(complement). The wolf doesn't necessarily
enter, so it's possible it doesn't.
-/
theorem wolf_might_not_enter :
    mightBase modalBase Set.univ wolfEntersWᶜ := by
  rw [← modal_duality]
  exact wolf_not_must_enter

end ModalSubordination


end AbneyKeshet2025
