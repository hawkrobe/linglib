import Linglib.Core.Logic.Intensional.Rigidity
import Linglib.Features.Logophoricity
import Linglib.Syntax.Pronoun.Logophoric

/-!
# Pearson (2015): The interpretation of the logophoric pronoun in Ewe
[pearson-2015] [sells-1987] [percus-sauerland-2003] [charlow-sharvit-2014]
[chierchia-1990] [kratzer-2009] [lewis-1979-attitudes]

[pearson-2015] (*Nat Lang Semantics* 23(2)) gives the definitive modern semantics of the
Ewe logophoric pronoun *yè* — the carrier `ye : LogophoricPronoun`
(`Syntax/Pronoun/Logophoric.lean`, `requiredRole = .self`). The traditional Heim & von
Stechow view (after [chierchia-1990]) is that *yè* bears an `[log]` feature that must be
bound by the **individual abstractor** an attitude verb introduces in the embedded left
periphery — so *yè* obligatorily occurs under an attitude predicate and takes the **attitude
holder** as antecedent (this *is* the `.self` requirement: Sells' antecedent-must-be-a-self).
That view predicts *yè* is obligatorily **de se**.

[pearson-2015]'s fieldwork finding is that this prediction is **wrong**: *yè* is de se / de re
**ambiguous**. Her account keeps *yè* bound by the attitude abstractor (preserving the
distribution) but lets it additionally sit inside a **`resP`** — a covert constituent housing a
**concept generator** variable ([percus-sauerland-2003], [charlow-sharvit-2014]) — yielding the
de re reading. A concept generator maps a *res* to an individual concept; it is **suitable**
when *reliable* (returns the res in the actual world) and *acquaintance-based*, with Pearson's
revision that a variable over the attitude holder's **epistemic alternatives** is overwritten
with the attitude holder herself (eq. 82) — the clause that makes "John claims he is
delusional" (de re, true) diverge from "John claims Napoleon is delusional" (false).

## This file (core machinery + ambiguity theorem)

* `Concept` / `ConceptGenerator` — over `Core.Intension`; the general acquaintance/cover
  substrate is `Semantics/Reference/Acquaintance.lean`.
* `sayDeSe` (eq. 76) and `sayDeRe` (eq. 77) — the two denotations of *say*, with `Suitable`
  (eq. 82) the reliability-with-epistemic-overwrite + acquaintance-based condition.
* **Scenario 1** (eq. 75, §5.3): John says "whoever wrote this is clever", unaware he is the
  author. `ye_de_se_de_re_ambiguous` proves the de se LF is **false** while the de re LF is
  **true** — via an explicit witnessing "author" concept generator (`authorGen`). This is
  [pearson-2015]'s central finding, made true by construction.
* `ye_antecedent_is_attitude_holder` grounds the carrier: *yè*'s antecedent is the attitude
  holder in both readings, i.e. the carrier's `requiredRole = .self`.

The Napoleon contrast (§6), the *yè*-vs-PRO φ-feature asymmetry (§7.1, PRO is a φ-less
[kratzer-2009] minimal pronoun → no long-distance antecedent), and the full acquaintance
semantics are left to prose; here the acquaintance-based clause is modelled as
unique-image functionality, the load-bearing discriminating clause being reliability.
-/

namespace Pearson2015

open Core (Intension)
open Features.Logophoricity (LogophoricRole Logophoric)

/-! ### Concept generators ([percus-sauerland-2003], [charlow-sharvit-2014]) -/

/-- A (Lewis) centered attitude alternative: a world paired with the individual the
    attitude holder identifies as herself there ([lewis-1979-attitudes]). -/
abbrev Centered (W E : Type*) := W × E

/-- An individual concept à la [percus-sauerland-2003]: a function from centered worlds
    to individuals (`Core.Intension` over `Centered`). Acquaintance-based concepts are
    functions from world-individual pairs, not from worlds. -/
abbrev Concept (W E : Type*) := Intension (Centered W E) E

/-- A concept generator: from a *res* to an individual concept. -/
abbrev ConceptGenerator (W E : Type*) := E → Concept W E

/-- A centered property (type ⟨e,⟨s,t⟩⟩): holds of an individual at a world. -/
abbrev CProp (W E : Type*) := E → W → Prop

/-- The epistemic alternatives of the attitude holder = the de se centers of her
    attitude alternatives. -/
def epiAlt {W E : Type*} (alts : List (Centered W E)) : List E := alts.map Prod.snd

/-! ### `say` de se and de re ([pearson-2015] eq. 76, 77, 82) -/

/-- `⟦say^de se⟧` (eq. 76): the embedded property holds of the **de se center** at each
    attitude alternative. *yè* bound directly by the attitude abstractor. -/
def sayDeSe {W E : Type*} (alts : List (Centered W E)) (P : CProp W E) : Prop :=
  ∀ p ∈ alts, P p.2 p.1

/-- **Suitable** concept generator ([pearson-2015] eq. 82, here over a finite domain `dom`):

    (i) *reliability with epistemic-alternative overwrite* — for each res `u`, the concept
        returns `u` in the actual world, **or** `u` is an epistemic alternative of the holder
        and the concept returns the holder `x` (the clause discriminating the Napoleon case);
    (ii) *acquaintance-based* — there is a relation the de se center bears **uniquely** to the
        concept's value (modelled here as unique-image functionality). -/
def Suitable {W E : Type*} [DecidableEq E] (alts : List (Centered W E))
    (G : ConceptGenerator W E) (x : E) (w : W) (dom : List E) : Prop :=
  (∀ u ∈ dom, G u (w, x) = u ∨ (u ∈ epiAlt alts ∧ G u (w, x) = x)) ∧
  (∀ u ∈ dom, ∃ R : E → W → E → Prop,
      ∀ p ∈ (w, x) :: alts, R p.2 p.1 (G u p) ∧ ∀ z, R p.2 p.1 z → z = G u p)

/-- `⟦say^de re⟧` (eq. 77/79b): there is a **suitable** concept generator `G` such that at
    each attitude alternative `⟨w',y⟩`, the individual `G`'s concept (fed the de se center as
    res) picks out at `⟨w',y⟩` has the embedded property at `w'`. *yè* sits in a `resP`. -/
def sayDeRe {W E : Type*} [DecidableEq E] (alts : List (Centered W E))
    (P : CProp W E) (x : E) (w : W) (dom : List E) : Prop :=
  ∃ G : ConceptGenerator W E, Suitable alts G x w dom ∧ ∀ p ∈ alts, P (G p.2 p) p.1

/-! ### Scenario 1: the de se / de re ambiguity ([pearson-2015] eq. 75, §5.3)

John has found an old paper he wrote but does not recognise as his own; impressed, he says
"Whoever wrote this is clever." `John be yè le cleva` ('John said that *yè* was clever') is
judged **true** — yet John never self-ascribes cleverness. -/

/-- Worlds: `actual` (0) and `bel` (1), John's say-alternative world. -/
abbrev Wld := Fin 2
/-- Individuals: `john` (0) and `auth` (1), the author John takes to be someone else. -/
abbrev Ind := Fin 2

def actual : Wld := 0
def bel : Wld := 1
def john : Ind := 0
def auth : Ind := 1

/-- John's single say-alternative: world `bel`, de se center `john` (himself qua speaker). -/
def sayAlts : List (Centered Wld Ind) := [(bel, john)]

/-- The relevant res domain: just the attitude holder. -/
def dom : List Ind := [john]

/-- `clever` in the belief world `bel`: the author `auth` is clever, John is not — John
    ascribes cleverness to the author, failing to recognise the author as himself. -/
def cleverB : Wld → Ind → Bool
  | 1, 1 => true
  | _, _ => false

/-- Reducible so `decide` sees the underlying `Bool` test through the wrapper. -/
abbrev cleverP : CProp Wld Ind := fun y w => cleverB w y = true

/-- The "author of the paper" concept generator: **reliable** — it returns the res `john` in
    the actual world (John really is the author) — but the believed author `auth` in John's
    belief world (he does not recognise himself). The acquaintance-based "read the paper of". -/
def authorGen : ConceptGenerator Wld Ind :=
  fun _u p => if p.1 = actual then john else auth

/-! ### The ambiguity, derived -/

/-- The **de se** reading is **false**: at John's say-alternative ⟨bel, john⟩ the de se
    centre (john) is not clever — John did not self-ascribe cleverness. -/
theorem deSe_false : ¬ sayDeSe sayAlts cleverP := by unfold sayDeSe; decide

/-- The "author" concept generator is **suitable** for John: reliable (returns the res john in
    the actual world) and acquaintance-based (unique-image). -/
theorem authorGen_suitable : Suitable sayAlts authorGen john actual dom := by
  refine ⟨by decide, ?_⟩
  intro u _hu
  exact ⟨fun y w z => z = authorGen u (w, y), fun p _hp => ⟨rfl, fun _z hz => hz⟩⟩

/-- The **de re** reading is **true**: under the suitable "author" concept generator, at each
    say-alternative the individual it picks (the author) is clever — the de re reading rescues
    truth where de se fails. -/
theorem deRe_true : sayDeRe sayAlts cleverP john actual dom :=
  ⟨authorGen, authorGen_suitable, by decide⟩

/-- **yè is de se / de re ambiguous** ([pearson-2015]'s central finding): the same sentence is
    **false** on the de se LF (78) but **true** on the de re LF (79). The Heim & von Stechow
    prediction of obligatory de se is thereby refuted, by construction. -/
theorem ye_de_se_de_re_ambiguous :
    ¬ sayDeSe sayAlts cleverP ∧ sayDeRe sayAlts cleverP john actual dom :=
  ⟨deSe_false, deRe_true⟩

/-! ### Grounding the `LogophoricPronoun` carrier -/

/-- *yè*'s antecedent is the **attitude holder** in both readings ([pearson-2015]: bound by
    the attitude verb's individual abstractor) — exactly the carrier's `requiredRole = .self`
    (Sells: the antecedent must be at least a *self* = an attitude holder). The de se/de re
    ambiguity above is orthogonal: both readings keep the attitude holder as antecedent. -/
theorem ye_antecedent_is_attitude_holder :
    Logophoric.requiredRole ye = LogophoricRole.self := rfl

end Pearson2015
