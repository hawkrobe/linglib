import Mathlib.Order.Nat
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Questions.Bias

/-!
# Czech Three-Way Negation: Core Types

The three-way negation distinction in Czech polar questions
([stankova-2026]): the LF positions, the Table 1 diagnostics that
fingerprint them, and their evidential bias strengths. Kept free of
lexical entries so that Fragment files can reference these types
without importing them. NCI licensing by Agree follows [zeijlstra-2004].
-/

namespace Czech.Negation

open Semantics.Questions.Bias (EvidentialBiasStrength)

/-- The three LF positions for negation in Czech PQs ([stankova-2026], her (16)).

  [CP... [PolP ne- [ModP ne- [TP ne-]]]]
              OUTER MEDIAL INNER
-/
inductive Position where
  /-- Inner negation: in TP, propositional ¬p. Narrow scope.
      Licenses NCIs by Agree, licenses NPIs. Standard sentential negation. -/
  | inner
  /-- Medial negation: in ModP, scopes over □_ev. Wide scope but syntactically low.
      Non-propositional: part of evidential bias presupposition. -/
  | medial
  /-- Outer negation: in PolP, FALSUM operator. Widest scope.
      Maps to high negation (VSO word order). Obligatorily focused. -/
  | outer
  deriving DecidableEq, Repr, Fintype

/-- Numeric embedding: inner ↦ 0, medial ↦ 1, outer ↦ 2 (by scope width). -/
def Position.toNat : Position → Nat
  | .inner  => 0
  | .medial => 1
  | .outer  => 2

instance : LinearOrder Position :=
  LinearOrder.lift' Position.toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [Position.toNat])

/-- Diagnostics that distinguish the three negation readings (Table 1). -/
inductive Diagnostic where
  /-- ne- outscopes a PPI like *nějaký* 'some.DET.PPI' -/
  | ppiOutscoping
  /-- Negative concord item like *žádný* 'no.DET.NCI' is licensed -/
  | nciLicensed
  /-- Particle *náhodou* 'by chance' is compatible -/
  | nahodou
  /-- Particle *ještě* 'yet/still' is compatible (with telic predicates + neg) -/
  | jeste
  /-- Particle *fakt* 'really' is compatible -/
  | fakt
  deriving DecidableEq, Repr, Fintype

/-- [stankova-2026]'s Table 1: compatibility of each negation reading
with polarity items and particles.

This is the core empirical fingerprint: each negation position has a unique
Boolean signature across the five diagnostics. -/
def licenses : Position → Diagnostic → Bool
  | .outer,  .ppiOutscoping => true
  | .outer,  .nciLicensed   => false
  | .outer,  .nahodou       => true
  | .outer,  .jeste         => false
  | .outer,  .fakt          => false
  | .medial, .ppiOutscoping => true
  | .medial, .nciLicensed   => false
  | .medial, .nahodou       => false
  | .medial, .jeste         => false
  | .medial, .fakt          => true
  | .inner,  .ppiOutscoping => false
  | .inner,  .nciLicensed   => true
  | .inner,  .nahodou       => false
  | .inner,  .jeste         => true
  | .inner,  .fakt          => true

/-- Each Position has a unique 5-bit diagnostic signature.
    This is the formal statement that the diagnostic table (Table 1)
    distinguishes all three negation readings. -/
theorem licenses_injective :
    Function.Injective (fun pos => fun d => licenses pos d) := by
  intro a b h
  have h1 : licenses a .nciLicensed = licenses b .nciLicensed := congr_fun h _
  have h2 : licenses a .nahodou = licenses b .nahodou := congr_fun h _
  have h3 : licenses a .fakt = licenses b .fakt := congr_fun h _
  cases a <;> cases b <;> simp_all [licenses]

/-- Evidential bias strength of a negation position — inner strong,
medial weak, outer none, FALSUM being epistemic-bias-based
([stankova-2026] §3.1). -/
def Position.biasStrength : Position → EvidentialBiasStrength
  | .inner  => .strong
  | .medial => .weak
  | .outer  => .none_

/-- Scope ordering: inner < medial < outer. -/
theorem inner_lt_medial : Position.inner < .medial := by decide
theorem medial_lt_outer : Position.medial < .outer := by decide
theorem inner_lt_outer : Position.inner < .outer := by decide

end Czech.Negation
