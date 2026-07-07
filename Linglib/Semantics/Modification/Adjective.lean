import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Common

/-!
# Adjective Classification Hierarchy
[kamp-1975] [kamp-partee-1995] [parsons-1970]

The standard classification of adjective meanings as functions from
properties to properties, constrained by meaning postulates.

[parsons-1970] independently introduced the operator approach
(modifiers as functions on predicates, not conjoinable predicates) and
distinguished "predicative" adjectives (analyzable as conjunction =
intersective) from "non-predicative" (= non-intersective), and
"standard" modifiers (A N → N = subsective) from "non-standard"
(= non-subsective). [kamp-1975] refined these binary distinctions
into the full four-class hierarchy below; the terminology follows Kamp.

## Hierarchy

1. **Intersective** (Kamp's "predicative", def. 4): `⟦A N⟧ = ⟦A⟧ ∩ ⟦N⟧`
2. **Subsective** (Kamp's "affirmative", def. 6): `⟦A N⟧ ⊆ ⟦N⟧`
3. **Privative** (def. 5): `⟦A N⟧ ∩ ⟦N⟧ = ∅`
4. **Extensional** (def. 7): depends only on N's extension, not intension
5. **Non-subsective** (modal): no entailment (alleged, potential)

## Implication Structure

    intersective → {extensional, subsective}

Extensional and subsective are independent: neither implies the other
(§ 3 provides witnesses for both separations).
Privative is incompatible with subsective (given non-empty extension).

## Design

The hierarchy is defined over *intensional* adjective meanings
(`Property W E → Property W E`) parameterized by a world type `W` and
entity type `E`. This is the most general formulation, from which
single-world (extensional) specializations follow — see
`Montague/Modification.lean` for the Montague-typed extensional versions
and `Kamp1975.lean` § 1 for single-world specialization theorems.

[partee-2010] argues the privative class should be eliminated
in favor of subsective + noun coercion; see `Partee2010.lean`. The
post-collapse 3-class hierarchy is captured by `RevisedClass` below;
the licensing mechanism (NVP + HPP) lives in
`Semantics/Composition/Coercion.lean`.
-/

namespace Degree.Classification

/-- An intensional property: a function from worlds to characteristic
    predicates over entities. -/
abbrev Property (W E : Type*) := W → E → Prop

/-- An adjective meaning: a function from noun properties to modified
    noun-phrase properties (type `⟨⟨s,⟨e,t⟩⟩, ⟨s,⟨e,t⟩⟩⟩` in Montague
    notation). -/
abbrev AdjMeaning (W E : Type*) := Property W E → Property W E

/-! ### Class Definitions -/

section Hierarchy

variable {W E : Type*}

/-- An adjective is **intersective** if its extension at each world is the
    intersection of the noun's extension with some fixed property Q.
    [kamp-1975] definition (4) ("predicative").

    Examples: "gray", "French", "carnivorous", "four-legged". -/
def isIntersective (adj : AdjMeaning W E) : Prop :=
  ∃ (Q : Property W E), ∀ (N : Property W E) (w : W) (x : E),
    adj N w x ↔ (Q w x ∧ N w x)

/-- An adjective is **subsective** if its extension is always a subset
    of the noun's extension.
    [kamp-1975] definition (6) ("affirmative").

    Examples: "skillful", "good", "typical". -/
def isSubsective (adj : AdjMeaning W E) : Prop :=
  ∀ (N : Property W E) (w : W) (x : E), adj N w x → N w x

/-- An adjective is **privative** if its extension is always disjoint
    from the noun's extension.
    [kamp-1975] definition (5).

    Examples: "fake", "counterfeit".
    [partee-2010] argues this class should be eliminated. -/
def isPrivative (adj : AdjMeaning W E) : Prop :=
  ∀ (N : Property W E) (w : W) (x : E), adj N w x → ¬ N w x

/-- An adjective is **extensional** if its extension in world w depends
    only on the noun's extension in w, not on the noun's intension.
    [kamp-1975] definition (7).

    "four-legged" and "gray" are extensional; "skillful" is not (being a
    skillful surgeon depends on what counts as a surgeon across contexts,
    not just who the surgeons are in this world). -/
def isExtensional (adj : AdjMeaning W E) : Prop :=
  ∀ (N₁ N₂ : Property W E) (w : W),
    (∀ x, N₁ w x ↔ N₂ w x) → ∀ x, adj N₁ w x ↔ adj N₂ w x

/-! ### Implication Structure

    Intersective → {extensional, subsective}.
    Extensional and subsective are independent.
    Privative is incompatible with subsective (given non-empty extension). -/

/-- Intersective adjectives are extensional: if `F(N)(w)(x) ↔ Q(w)(x) ∧ N(w)(x)`,
    then the result in w depends only on N(w). -/
theorem intersective_implies_extensional {adj : AdjMeaning W E}
    (h : isIntersective adj) : isExtensional adj := by
  obtain ⟨Q, hQ⟩ := h
  intro N₁ N₂ w hext x
  simp only [hQ, hext]

/-- Intersective adjectives are subsective: if
    `F(N)(w)(x) ↔ Q(w)(x) ∧ N(w)(x)`, then `F(N)(w)(x) → N(w)(x)`. -/
theorem intersective_implies_subsective {adj : AdjMeaning W E}
    (h : isIntersective adj) : isSubsective adj := by
  obtain ⟨Q, hQ⟩ := h
  intro N w x hadj
  exact ((hQ N w x).mp hadj).2

/-- Privative adjectives are not subsective (when the adjective has
    non-empty extension for some noun). -/
theorem privative_not_subsective {adj : AdjMeaning W E}
    (hp : isPrivative adj)
    (hne : ∃ N w x, adj N w x) :
    ¬ isSubsective adj := by
  intro ha
  obtain ⟨N, w, x, hadj⟩ := hne
  exact hp N w x hadj (ha N w x hadj)

end Hierarchy

/-! ### Independence: Extensional ⊥ Subsective

    Neither extensional → subsective nor subsective → extensional.
    We construct explicit witnesses for both separations. -/

section Independence

/-- Witness: extensional but NOT subsective.
    An adjective that ignores both the noun and intension entirely
    (always returns True) is trivially extensional, but not subsective
    because it holds even when the noun does not. -/
private inductive W1 | w
private inductive E1 | a

private def extNotSubAdj : AdjMeaning W1 E1 := fun _N _w _x => True

theorem extensional_not_implies_subsective :
    ∃ (adj : AdjMeaning W1 E1), isExtensional adj ∧ ¬ isSubsective adj :=
  ⟨extNotSubAdj,
   fun _ _ _ _ _ => Iff.rfl,
   fun h => (h (fun _ _ => False) .w .a trivial).elim⟩

/-- Witness: subsective but NOT extensional.
    "skillful N" depends on N's intension (whether entity a is N in
    world w₁) to determine the result in world w₂. Subsective because
    the first conjunct is `N w x`. -/
private inductive W2' | w₁ | w₂
private inductive E2 | a | b

private def subNotExtAdj : AdjMeaning W2' E2 := fun N w x =>
  N w x ∧ match x with
    | .a => N .w₁ .a
    | _  => False

theorem subsective_not_implies_extensional :
    ∃ (adj : AdjMeaning W2' E2), isSubsective adj ∧ ¬ isExtensional adj :=
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
`Semantics/Composition/Coercion.lean`. -/

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
    intersective adjective satisfies `isSubsective` (see
    `intersective_implies_subsective`).

    Caveat on `.nonSubsective`: the membership condition `¬ isSubsective
    adj` is necessary but coarse — it also holds of Kamp-privatives,
    which under Partee's reanalysis are not supposed to exist as a
    natural class. Read `.nonSubsective` as Partee's *intended* "modal"
    class (alleged, potential, putative); the bare predicate
    `¬ isSubsective` over-generates. -/
def RevisedClass.satisfies : RevisedClass → AdjMeaning W E → Prop
  | .intersective  => isIntersective
  | .subsective    => isSubsective
  | .nonSubsective => fun adj => ¬ isSubsective adj

end Revised

end Degree.Classification
