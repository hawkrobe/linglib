import Mathlib.Order.Nat
import Mathlib.Data.Fintype.Basic

/-!
# Czech Three-Way Negation: Core Types
@cite{stankova-2025} @cite{zeijlstra-2004}

Pure type definitions for the three-way negation distinction in Czech polar
questions (Staňková 2026). Extracted from `Phenomena.Negation.CzechThreeWayNeg`
so that Fragment files can reference these types without importing empirical data.

-/

namespace Semantics.Negation.CzechNegation

/-- The three LF positions for negation in Czech PQs (Staňková 2026 §3, ex. 16).

  [CP... [PolP ne- [ModP ne- [TP ne-]]]]
              OUTER MEDIAL INNER
-/
inductive NegPosition where
  /-- Inner negation: in TP, propositional ¬p. Narrow scope.
      Licenses NCIs by Agree, licenses NPIs. Standard sentential negation. -/
  | inner
  /-- Medial negation: in ModP, scopes over □_ev. Wide scope but syntactically low.
      Non-propositional: part of evidential bias presupposition. -/
  | medial
  /-- Outer negation: in PolP, FALSUM operator. Widest scope.
      Maps to high negation (VSO word order). Obligatorily focused. -/
  | outer
  deriving DecidableEq, Repr

-- ── NegPosition: LinearOrder, Fintype ──

/-- Numeric embedding: inner ↦ 0, medial ↦ 1, outer ↦ 2 (by scope width). -/
def NegPosition.toNat : NegPosition → Nat
  | .inner  => 0
  | .medial => 1
  | .outer  => 2

instance : LinearOrder NegPosition :=
  LinearOrder.lift' NegPosition.toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [NegPosition.toNat])

/-- NegPosition ≃ Fin 3. -/
def NegPosition.equivFin : NegPosition ≃ Fin 3 where
  toFun | .inner => 0 | .medial => 1 | .outer => 2
  invFun | ⟨0, _⟩ => .inner | ⟨1, _⟩ => .medial | ⟨2, _⟩ => .outer
         | ⟨n + 3, h⟩ => absurd h (by omega)
  left_inv p := by cases p <;> rfl
  right_inv i := by
    match i with
    | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
    | ⟨n + 3, h⟩ => exact absurd h (by omega)

instance : Fintype NegPosition := Fintype.ofEquiv _ NegPosition.equivFin.symm

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
  deriving DecidableEq, Repr

-- ── Diagnostic: Fintype ──

/-- Diagnostic ≃ Fin 5. -/
def Diagnostic.equivFin : Diagnostic ≃ Fin 5 where
  toFun | .ppiOutscoping => 0 | .nciLicensed => 1 | .nahodou => 2
        | .jeste => 3 | .fakt => 4
  invFun | ⟨0, _⟩ => .ppiOutscoping | ⟨1, _⟩ => .nciLicensed
         | ⟨2, _⟩ => .nahodou | ⟨3, _⟩ => .jeste | ⟨4, _⟩ => .fakt
         | ⟨n + 5, h⟩ => absurd h (by omega)
  left_inv d := by cases d <;> rfl
  right_inv i := by
    match i with
    | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl | ⟨4, _⟩ => rfl
    | ⟨n + 5, h⟩ => exact absurd h (by omega)

instance : Fintype Diagnostic := Fintype.ofEquiv _ Diagnostic.equivFin.symm

/-- Table 1 from Staňková (2026 §3): compatibility of each negation reading
with polarity items and particles.

This is the core empirical fingerprint: each negation position has a unique
Boolean signature across the five diagnostics. -/
def licenses : NegPosition → Diagnostic → Bool
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

/-- Each NegPosition has a unique 5-bit diagnostic signature.
    This is the formal statement that the diagnostic table (Table 1)
    distinguishes all three negation readings. -/
theorem licenses_injective :
    Function.Injective (fun pos => fun d => licenses pos d) := by
  intro a b h
  have h1 : licenses a .nciLicensed = licenses b .nciLicensed := congr_fun h _
  have h2 : licenses a .nahodou = licenses b .nahodou := congr_fun h _
  have h3 : licenses a .fakt = licenses b .fakt := congr_fun h _
  cases a <;> cases b <;> simp_all [licenses]

/-- Scope ordering: inner < medial < outer. -/
theorem inner_lt_medial : NegPosition.inner < .medial := by decide
theorem medial_lt_outer : NegPosition.medial < .outer := by decide
theorem inner_lt_outer : NegPosition.inner < .outer := by decide

end Semantics.Negation.CzechNegation
