/-
# NP Type-Shifting Principles (Partee 1987)

The type-shifting triangle between three NP semantic types:
- `e` : referential (proper names, pronouns)
- `⟨e,t⟩` : predicative (common nouns, adjectives)
- `⟨⟨e,t⟩,t⟩` : quantificational (generalized quantifiers)

```
         e  ——lift——→  ⟨⟨e,t⟩,t⟩
         ↑  ←—lower——    ↑
       iota              BE
         ↑               ↑
        ⟨e,t⟩  ——A——→  ⟨⟨e,t⟩,t⟩
         ↑
       ident
         ↑
         e
```

## References

- Partee, B. H. (1987). Noun Phrase Interpretation and Type-shifting Principles.
  In Groenendijk et al. (eds.), Studies in Discourse Representation Theory.
-/

import Linglib.Theories.TruthConditional.Basic
import Linglib.Theories.TruthConditional.Conjunction
import Mathlib.Order.Hom.BoundedLattice

namespace TruthConditional.Noun.TypeShifting

open TruthConditional (Model Ty toyModel ToyEntity)
open TruthConditional.Conjunction (typeRaise)

variable {m : Model}

section TotalShifts

/-- Type-raising: `lift(j) = λP. P(j)` -/
def lift (j : m.interpTy .e) : m.interpTy Ty.ett :=
  fun P => P j

/-- Singleton property: `ident(j) = λx. [j = x]`.
Uses `j = x` order for definitional equality with `BE(lift(j))`. -/
def ident (j : m.interpTy .e) : m.interpTy Ty.et :=
  fun x => @decide (j = x) (m.decEq j x)

/-- Predicative content of a GQ: `BE(Q) = λx. Q(λy. y = x)` -/
def BE (Q : m.interpTy Ty.ett) : m.interpTy Ty.et :=
  fun x => Q (fun y => @decide (y = x) (m.decEq y x))

end TotalShifts

section BooleanHomomorphism

instance (m : Model) : BooleanAlgebra (m.interpTy Ty.et) :=
  show BooleanAlgebra (m.Entity → Bool) from inferInstance
instance (m : Model) : BooleanAlgebra (m.interpTy Ty.ett) :=
  show BooleanAlgebra ((m.Entity → Bool) → Bool) from inferInstance

/-- `BE` is a `BoundedLatticeHom` (Partee §3.3, Fact 1). -/
def BE_hom (m : Model) : BoundedLatticeHom (m.interpTy Ty.ett) (m.interpTy Ty.et) where
  toFun := BE
  map_sup' _ _ := by funext; rfl
  map_inf' _ _ := by funext; rfl
  map_top' := by funext x; show BE ⊤ x = true; rfl
  map_bot' := by funext x; show BE ⊥ x = false; rfl

/-- `BE ∘ lift = ident` (Figure 3 commutativity). -/
theorem BE_lift_eq_ident (j : m.interpTy .e) :
    BE (lift j) = ident j := by
  funext x; simp only [BE, lift, ident]

/-- `BE(Q₁ ∧ Q₂) = BE(Q₁) ∧ BE(Q₂)` -/
theorem BE_conj (Q₁ Q₂ : m.interpTy Ty.ett) :
    BE (fun P => Q₁ P && Q₂ P) = (fun x => BE Q₁ x && BE Q₂ x) := by
  funext x; simp only [BE]

/-- `BE(Q₁ ∨ Q₂) = BE(Q₁) ∨ BE(Q₂)` -/
theorem BE_disj (Q₁ Q₂ : m.interpTy Ty.ett) :
    BE (fun P => Q₁ P || Q₂ P) = (fun x => BE Q₁ x || BE Q₂ x) := by
  funext x; simp only [BE]

/-- `BE(¬Q) = ¬BE(Q)` -/
theorem BE_neg (Q : m.interpTy Ty.ett) :
    BE (fun P => !(Q P)) = (fun x => !(BE Q x)) := by
  funext x; simp only [BE]

end BooleanHomomorphism

section PartialShifts

/-- Partial inverse of `lift`. Defined when `Q` is a principal ultrafilter. -/
def lower (domain : List m.Entity) (Q : m.interpTy Ty.ett) : Option (m.interpTy .e) :=
  match domain.filter (fun j => Q (fun x => @decide (x = j) (m.decEq x j))) with
  | [j] => some j
  | _ => none

/-- Partial inverse of `ident`. Returns the unique satisfier of `P`. -/
def iota (domain : List m.Entity) (P : m.interpTy Ty.et) : Option (m.interpTy .e) :=
  match domain.filter (fun x => P x) with
  | [j] => some j
  | _ => none

/-- Existential closure: `A(P) = λQ. ∃x. P(x) ∧ Q(x)` -/
def A (domain : List m.Entity) (P : m.interpTy Ty.et) : m.interpTy Ty.ett :=
  fun Q => domain.any (fun x => P x && Q x)

/-- Helper: for a nodup list, filtering for equality gives a singleton or empty. -/
private theorem filter_decEq_of_mem (domain : List m.Entity) (j : m.Entity)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    domain.filter (fun k => @decide (j = k) (m.decEq j k)) = [j] := by
  induction domain with
  | nil => nomatch hmem
  | cons hd tl ih =>
    have ⟨hd_nmem, tl_nd⟩ := List.nodup_cons.mp hnd
    have filter_tl_nil : ∀ (hj : j ∈ tl → False),
        tl.filter (fun k => @decide (j = k) (m.decEq j k)) = [] := by
      intro hj
      rw [List.filter_eq_nil_iff]
      intro k hk hdec
      have hne : j ≠ k := fun heq => hj (heq ▸ hk)
      have hf : @decide (j = k) (m.decEq j k) = false := by
        cases m.decEq j k with | isTrue h => exact absurd h hne | isFalse _ => rfl
      rw [hf] at hdec; exact Bool.noConfusion hdec
    cases hmem with
    | head =>
      have hdec : @decide (j = j) (m.decEq j j) = true := by
        cases m.decEq j j with | isTrue _ => rfl | isFalse h => exact absurd rfl h
      rw [List.filter_cons, if_pos hdec, filter_tl_nil hd_nmem]
    | tail _ hmem' =>
      have hne : ¬ (j = hd) := fun heq => hd_nmem (heq ▸ hmem')
      have hdec : ¬ (@decide (j = hd) (m.decEq j hd) = true) := by
        cases m.decEq j hd with | isTrue h => exact absurd h hne | isFalse _ => exact Bool.noConfusion
      rw [List.filter_cons, if_neg hdec]
      exact ih hmem' tl_nd

/-- `lower ∘ lift = some` on the domain (Partee's round-trip).

    Requires `j ∈ domain` (j must be in the model) and `domain.Nodup`
    (no duplicates, ensuring unique filter result). -/
theorem lower_lift (domain : List m.Entity) (j : m.interpTy .e)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    lower domain (lift j) = some j := by
  unfold lower lift
  erw [filter_decEq_of_mem domain j hmem hnd]

/-- `iota ∘ ident = some` on the domain (Partee's round-trip).

    The `ident` predicate picks out exactly `j`, so `iota` returns `j`
    when `j` is the unique satisfier (guaranteed by `Nodup`). -/
theorem iota_ident (domain : List m.Entity) (j : m.interpTy .e)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    iota domain (ident j) = some j := by
  unfold iota ident
  erw [filter_decEq_of_mem domain j hmem hnd]

end PartialShifts

section LexicalTypes

/-- Lexical semantic type of an NP: `e` (proper nouns) or `⟨e,t⟩` (common nouns). -/
inductive LexicalNPType where
  | entity
  | pred
  deriving DecidableEq, Repr, BEq

/-- Link's `*` operator applies to type `⟨e,t⟩` only. -/
def pluralAppliesTo : LexicalNPType → Bool
  | .pred => true
  | .entity => false

theorem proper_noun_no_direct_plural :
    pluralAppliesTo .entity = false := rfl

theorem common_noun_pluralizable :
    pluralAppliesTo .pred = true := rfl

/-- Coerced plural via `ident`: `e → ⟨e,t⟩`, enabling `*` to apply. -/
def coercedPlural {m : Model} (j : m.interpTy .e)
    (star : m.interpTy Ty.et → m.interpTy Ty.et) : m.interpTy Ty.et :=
  star (ident j)

end LexicalTypes

/-- `lift = Conjunction.typeRaise` -/
theorem lift_eq_typeRaise {m : Model} (j : m.interpTy .e) :
    lift j = typeRaise j := rfl

/-- Coherence of the three readings of "the king" (Partee §3.2). -/
theorem the_king_coherence (domain : List m.Entity) (P : m.interpTy Ty.et)
    (j : m.interpTy .e) (_h : iota domain P = some j) :
    BE (lift j) = ident j :=
  BE_lift_eq_ident j

-- ============================================================================
-- When do type-shifts change truth conditions?
-- ============================================================================

/-! ## Truth-Conditional Transparency of Type-Shifts

A type-shift is **truth-conditionally transparent** when the shifted meaning
produces the same sentential truth value as the original. The precise condition:

**Theorem**: For a GQ `Q : ⟨⟨α,t⟩,t⟩`, the round-trip `A(BE(Q))` preserves
truth conditions iff `Q` is a **principal ultrafilter** (i.e., `Q = lift(j)`
for some individual `j`).

For non-principal GQs (quantifiers, degree quantifiers like numerals),
`A(BE(Q))` yields a strictly weaker meaning. This is precisely when
the RSA model should include both the original and shifted meanings as
alternative interpretations.

Applications:
- **Proper names**: `Q = lift(john)` → `A(BE(Q)) = Q` → no ambiguity
- **Numerals**: `Q = ⟦three⟧` → `A(BE(Q)) = ∃d[d=3 ∧ D(d)]` ≠ `Q` → ambiguity
- **Universal quantifiers**: `Q = ⟦every student⟧` → `A(BE(Q)) = ⟦some student⟧` ≠ `Q`
-/

/-- A GQ is a principal ultrafilter iff it equals `lift(j)` for some entity. -/
def isPrincipalUltrafilter (domain : List m.Entity) (Q : m.interpTy Ty.ett) : Prop :=
  ∃ j ∈ domain, Q = lift j

/-- Helper: `decide (j = j)` is always `true`. -/
private theorem decide_eq_self (j : m.interpTy .e) :
    @decide (j = j) (m.decEq j j) = true := by simp

/-- Helper: if `j ∈ domain`, then `domain.any (λ x => decide(j=x) && P(x)) = P(j)`. -/
private theorem any_decide_eq_apply (domain : List m.Entity) (j : m.interpTy .e)
    (hj : j ∈ domain) (P : m.interpTy Ty.et) :
    domain.any (fun x => @decide (j = x) (m.decEq j x) && P x) = P j := by
  induction domain with
  | nil => contradiction
  | cons a tl ih =>
    simp only [List.any_cons]
    cases List.mem_cons.mp hj with
    | inl h =>
      subst h; simp
    | inr h =>
      by_cases heq : j = a
      · subst heq; simp
      · have : @decide (j = a) (m.decEq j a) = false := by
          simp [decide_eq_false_iff_not]; exact heq
        simp only [this, Bool.false_and, Bool.false_or]
        exact ih h

/-- **Round-trip preservation for principal ultrafilters.**
    For `Q = lift(j)`, `A(BE(Q))(P) = Q(P)` for all P.
    This means type-shifting is truth-conditionally transparent for
    proper names, pronouns, definites — any expression that denotes
    a principal ultrafilter. -/
theorem roundtrip_preserves_principal (domain : List m.Entity) (j : m.interpTy .e)
    (hj : j ∈ domain) :
    ∀ P : m.interpTy Ty.et, A domain (BE (lift j)) P = lift j P := by
  intro P
  simp only [A, BE, lift]
  exact any_decide_eq_apply domain j hj P

/-- For non-principal GQs, the round-trip can differ.
    Example: `⟦every⟧(P)(Q) = ∀x[P(x) → Q(x)]`, but
    `A(BE(⟦every⟧(P)))(Q) = ∃x[P(x) ∧ Q(x)]` — existential, not universal.
    Verified on the toy model. -/
private def toyDom : List ToyEntity := [.john, .mary, .pizza]
private def toyEvery : toyModel.interpTy Ty.ett := fun P => toyDom.all P

/-- For non-principal GQs, the round-trip changes truth conditions.
    `every(⊤) = true` but `A(BE(every))(⊤) = false` — the round-trip
    collapses universal quantification to `⊥` on multi-element domains.
    (`BE(every)` asks "which entity equals all entities?" — none do.) -/
theorem roundtrip_changes_nonprincipal :
    toyEvery (fun _ => true) = true ∧
    A toyDom (BE toyEvery) (fun _ => true) = false :=
  ⟨rfl, rfl⟩

section ToyExamples

open TruthConditional.ToyLexicon (john_sem)

private def toyDomain : List ToyEntity := [.john, .mary, .pizza, .book]

example : lift (m := toyModel) john_sem TruthConditional.ToyLexicon.sleeps_sem = true := rfl
example : BE (m := toyModel) (lift john_sem) = ident john_sem :=
  BE_lift_eq_ident john_sem
example : iota (m := toyModel) toyDomain (ident john_sem) = some john_sem := rfl
example : lower (m := toyModel) toyDomain (lift john_sem) = some john_sem := rfl

end ToyExamples

-- ============================================================================
-- Snyder (2026) / Partee (1986) Type-Shifters
-- ============================================================================

section SnyderShifts

/-- CARD: number → cardinality predicate (Snyder 2026, (6a)).
    CARD = λn.λx. μ(x) = n. Turns a number into a predicate
    on entities that have exactly n atomic parts. -/
def CARD (μ : m.interpTy .e → Nat) (n : Nat) : m.interpTy Ty.et :=
  fun x => decide (μ x = n)

/-- PM: Predicate Modification (Heim & Kratzer 1998, (7a)).
    PM = λP.λQ.λx. P(x) ∧ Q(x). Intersective modifier. -/
def PM (P Q : m.interpTy Ty.et) : m.interpTy Ty.et :=
  fun x => P x && Q x

/-- NOM: Nominalization (Partee 1986, Chierchia 1984, (10a)).
    Maps a property to its individual property correlate.
    In the finite setting, returns the unique entity satisfying P if singleton. -/
def NOM (domain : List m.Entity) (P : m.interpTy Ty.et) : Option (m.interpTy .e) :=
  iota domain P  -- NOM and iota coincide for singleton predicates

end SnyderShifts

end TruthConditional.Noun.TypeShifting
