import Linglib.Semantics.Modification.Basic
import Linglib.Semantics.Intensional.Rigidity
import Mathlib.Order.PropInstances
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Common

/-!
# Modifier-Meaning Classification at the Intensional Carrier
[kamp-1975] [kamp-partee-1995] [parsons-1970]

The standard classification of adnominal modifier meanings, constrained
by meaning postulates. The order-theoretic classes
(`Modifier.isIntersective` / `.isSubsective` / `.isPrivative`) live in
`Modification/Basic.lean`; this file works at the intensional carrier
`Modifier (Property W E)` — functions from properties to properties,
type `⟨⟨s,⟨e,t⟩⟩, ⟨s,⟨e,t⟩⟩⟩` in Montague notation — adding the
pointwise unfolding lemmas, the one genuinely intensional class
(`isExtensional`), the implication structure, and [partee-2010]'s
post-collapse `RevisedClass`.

[parsons-1970] independently introduced the operator approach
(modifiers as functions on predicates, not conjoinable predicates) and
distinguished "predicative" adjectives (analyzable as conjunction =
intersective) from "non-predicative" (= non-intersective), and
"standard" modifiers (A N → N = subsective) from "non-standard"
(= non-subsective). [kamp-1975] refined these binary distinctions
into the full four-class hierarchy below.

## Hierarchy

1. **Intersective**: `⟦A N⟧ = ⟦A⟧ ∩ ⟦N⟧`
2. **Subsective**: `⟦A N⟧ ⊆ ⟦N⟧`
3. **Privative**: `⟦A N⟧ ∩ ⟦N⟧ = ∅`
4. **Extensional**: depends only on N's extension, not intension
5. **Non-subsective** (modal): no entailment (alleged, potential)

## Implication Structure

    intersective → {extensional, subsective}

Extensional and subsective are independent: neither implies the other
(§ 3 provides witnesses for both separations).
Privative is incompatible with subsective (given non-empty extension).

## Design

Single-world (extensional) specializations are the same order-theoretic
classes at the carrier `E → Prop` — see `Studies/Kamp1975.lean` § 1 for
the specialization theorems. Whether *adjectives* uniformly denote
`Modifier (Property W E)` is itself a theoretical claim (see
`Studies/Elbourne2026.lean`); the carrier is named for the denotation
type, not the word class.

[partee-2010] argues the privative class should be eliminated
in favor of subsective + noun coercion; see `Partee2010.lean`. The
post-collapse 3-class hierarchy is captured by `RevisedClass` below;
the licensing mechanism (NVP + HPP) lives in
`Semantics/Modification/Coercion.lean`.
-/

namespace Modification

/-- An intensional property: an `Intensional.Intension` valued in
    characteristic predicates over entities (a function from worlds to
    predicates). -/
abbrev Property (W E : Type*) := Intensional.Intension W (E → Prop)

/-! ### Pointwise forms of the order-theoretic classes -/

section Hierarchy

open Modifier

variable {W E : Type*} {adj : Modifier (Property W E)}

/-- Pointwise form of `Modifier.isIntersective` at the intensional
    carrier: the extension at each world is the intersection of the
    noun's extension with some fixed property Q ([kamp-1975]).

    Examples: "gray", "French", "carnivorous", "four-legged". -/
theorem isIntersective_iff :
    isIntersective adj ↔
      ∃ (Q : Property W E), ∀ (N : Property W E) (w : W) (x : E),
        adj N w x ↔ (Q w x ∧ N w x) := by
  refine ⟨fun ⟨Q, hQ⟩ => ⟨Q, fun N w x => by rw [hQ]; exact Iff.rfl⟩,
          fun ⟨Q, hQ⟩ => ⟨Q, fun N => ?_⟩⟩
  funext w x
  exact propext (hQ N w x)

/-- Pointwise form of `Modifier.isSubsective` at the intensional
    carrier: the extension is always a subset of the noun's extension
    ([kamp-1975]).

    Examples: "skillful", "good", "typical". -/
theorem isSubsective_iff :
    isSubsective adj ↔
      ∀ (N : Property W E) (w : W) (x : E), adj N w x → N w x :=
  Iff.rfl

/-- Pointwise form of `Modifier.isPrivative` at the intensional carrier:
    the extension is always disjoint from the noun's extension
    ([kamp-1975]).

    Examples: "fake", "counterfeit".
    [partee-2010] argues this class should be eliminated. -/
theorem isPrivative_iff :
    isPrivative adj ↔
      ∀ (N : Property W E) (w : W) (x : E), adj N w x → ¬ N w x := by
  simp only [isPrivative, Pi.disjoint_iff, Prop.disjoint_iff, not_and]

/-- A modifier meaning is **extensional** if its extension in world w
    depends only on the noun's extension in w, not on the noun's
    intension ([kamp-1975]). The one class of the hierarchy that is
    genuinely intensional — it has no order-theoretic form.

    "four-legged" and "gray" are extensional; "skillful" is not (being a
    skillful surgeon depends on what counts as a surgeon across contexts,
    not just who the surgeons are in this world). -/
def isExtensional (adj : Modifier (Property W E)) : Prop :=
  ∀ (N₁ N₂ : Property W E) (w : W),
    (∀ x, N₁ w x ↔ N₂ w x) → ∀ x, adj N₁ w x ↔ adj N₂ w x

/-! ### Implication Structure

    Intersective → {extensional, subsective} (the second is
    `Modifier.isIntersective.isSubsective`, at any carrier).
    Extensional and subsective are independent.
    Privative is incompatible with subsective (given non-empty extension;
    the order-theoretic core is `Modifier.isPrivative.eq_bot`). -/

/-- Intersective modifier meanings are extensional: if
    `F(N)(w)(x) ↔ Q(w)(x) ∧ N(w)(x)`, then the result in w depends only
    on N(w). -/
theorem isExtensional_of_isIntersective (h : isIntersective adj) :
    isExtensional adj := by
  obtain ⟨Q, hQ⟩ := isIntersective_iff.mp h
  intro N₁ N₂ w hext x
  simp only [hQ, hext]

/-- Privative modifier meanings are not subsective (when the modifier has
    non-empty extension for some noun). -/
theorem not_isSubsective_of_isPrivative (hp : isPrivative adj)
    (hne : ∃ N w x, adj N w x) : ¬ isSubsective adj := by
  intro hs
  obtain ⟨N, w, x, hadj⟩ := hne
  exact isPrivative_iff.mp hp N w x hadj (hs N w x hadj)

end Hierarchy

/-! ### Independence: Extensional ⊥ Subsective

    Neither extensional → subsective nor subsective → extensional.
    We construct explicit witnesses for both separations. -/

section Independence

open Modifier

/-- Witness: extensional but NOT subsective.
    A modifier that ignores both the noun and intension entirely
    (always returns True) is trivially extensional, but not subsective
    because it holds even when the noun does not. -/
private inductive W1 | w
private inductive E1 | a

private def extNotSubAdj : Modifier (Property W1 E1) := fun _N _w _x => True

theorem extensional_not_implies_subsective :
    ∃ (adj : Modifier (Property W1 E1)), isExtensional adj ∧ ¬ isSubsective adj :=
  ⟨extNotSubAdj,
   fun _ _ _ _ _ => Iff.rfl,
   fun h => (h (fun _ _ => False) .w .a trivial).elim⟩

/-- Witness: subsective but NOT extensional.
    "skillful N" depends on N's intension (whether entity a is N in
    world w₁) to determine the result in world w₂. Subsective because
    the first conjunct is `N w x`. -/
private inductive W2' | w₁ | w₂
private inductive E2 | a | b

private def subNotExtAdj : Modifier (Property W2' E2) := fun N w x =>
  N w x ∧ match x with
    | .a => N .w₁ .a
    | _  => False

theorem subsective_not_implies_extensional :
    ∃ (adj : Modifier (Property W2' E2)), isSubsective adj ∧ ¬ isExtensional adj :=
  ⟨subNotExtAdj,
   fun _ _ _ h => h.1,
   fun hext => by
     let N₁ : Property W2' E2 := fun _ _ => True
     let N₂ : Property W2' E2 := fun w x => match w, x with
       | .w₁, .a => False
       | _, _    => True
     have hagree : ∀ x, N₁ .w₂ x ↔ N₂ .w₂ x := fun x => by
       cases x <;> simp [N₁, N₂]
     have h := hext N₁ N₂ .w₂ hagree .a
     -- LHS: subNotExtAdj N₁ .w₂ .a = True ∧ True; RHS: True ∧ False
     have hLHS : subNotExtAdj N₁ .w₂ .a := ⟨trivial, trivial⟩
     exact (h.mp hLHS).2⟩

end Independence

/-! ### Revised Hierarchy ([partee-2010])

The post-collapse 3-class hierarchy after eliminating "privative" via
noun coercion. Per [partee-2010] footnote 1, the hierarchy is
subset-ordered (intersective ⊂ subsective ⊂ unrestricted), not linear;
the enum picks the *narrowest fit* per adjective. The licensing
mechanism (NVP + HPP) is in
`Semantics/Modification/Coercion.lean`. -/

section Revised

variable {W E : Type*}

/-- Adjective hierarchy after [partee-2010]'s collapse: the
    privative class is eliminated in favor of subsective + noun coercion. -/
inductive RevisedClass where
  /-- `⟦A N⟧ = ⟦Q⟧ ∩ ⟦N⟧` (Kamp's intersective). -/
  | intersective
  /-- `⟦A N⟧ ⊆ ⟦N*⟧` — includes former "privatives" via coercion. -/
  | subsective
  /-- No entailment: alleged, potential, putative (Kamp's non-subsective). -/
  | nonSubsective
  deriving DecidableEq

/-- Predicate-level interpretation of `RevisedClass`. Per the subset
    ordering, `intersective` and `subsective` are not disjoint: every
    intersective modifier meaning satisfies `Modifier.isSubsective`
    (`Modifier.isIntersective.isSubsective`).

    Caveat on `.nonSubsective`: the membership condition `¬ isSubsective
    adj` is necessary but coarse — it also holds of Kamp-privatives,
    which under Partee's reanalysis are not supposed to exist as a
    natural class. Read `.nonSubsective` as Partee's *intended* "modal"
    class (alleged, potential, putative); the bare predicate
    `¬ isSubsective` over-generates. -/
def RevisedClass.satisfies : RevisedClass → Modifier (Property W E) → Prop
  | .intersective  => Modifier.isIntersective
  | .subsective    => Modifier.isSubsective
  | .nonSubsective => fun adj => ¬ Modifier.isSubsective adj

end Revised

end Modification
