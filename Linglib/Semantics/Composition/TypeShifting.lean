import Linglib.Semantics.Intensional.Defs
import Linglib.Semantics.Quantification.Quantifier
import Linglib.Semantics.Intensional.Conjunction
import Linglib.Semantics.Modification.Basic
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Data.Finset.Lattice.Fold

/-!
# NP Type-Shifting Principles
[partee-1987]

Three NP semantic types and six type-shifting operations (three inverse pairs):

    individual / lower : e ↔ ⟨⟨e,t⟩,t⟩    (total / partial)
    ident / iota       : e ↔ ⟨e,t⟩         (formal; total / partial)
    pred  / nom        : e ↔ ⟨e,t⟩         (substantive; Chierchia's ∪ and ∩)
          A / BE       : ⟨e,t⟩ ↔ ⟨⟨e,t⟩,t⟩ (total / total)
        THE            : ⟨e,t⟩ → ⟨⟨e,t⟩,t⟩ (partial; presuppositional)

The two quantifier-side operations `A` and `BE`, and the Montague lift
`Quantification.individual`, are the quantifier API and live in
`Semantics.Quantification.Quantifier`; this file holds the entity-side shifts
and the commuting triangle relating all three types.

In the finite extensional setting, `pred = ident` and `nom = iota`. The
conceptual difference: `ident`/`iota` are *formal* (pure combinatorics),
while `pred`/`nom` are *substantive* (depend on entity-property correspondence).
The `pred`/`nom` pair originates in [chierchia-1984]'s nominalization
operator `^` from HST* (Cocchiarella's property theory), applied to infinitival
and gerundive complements. The intensional generalizations are Chierchia's
∪ (up) and ∩ (down) operators in `Semantics.Kinds.NMP`,
which extend the same type-shift to kinds and bare plurals.

-/

namespace Semantics.Composition.TypeShifting

open Intensional
open Quantification

variable {E W : Type}

section TotalShifts

/-- Singleton property: `ident(j) = λx. [j = x]`.
Uses `j = x` order for definitional equality with `BE(individual j)`. -/
def ident (j : E) : (E → Prop) :=
  fun x => j = x

/-- Propositional analogue of `ident`: `propIdent(p) = λq. [p = q]`,
i.e. the singleton question `{p}` from a proposition `p`.

This is `ID` of [elliott-etal-2017] (their eq. 10), used to coerce a
proposition into a question denotation when an embedding predicate (e.g.
a Predicate of Relevance like `care`) selects only for questions. The shape
mirrors `ident` one type-theoretic level up: entities ↦ singleton properties
becomes propositions ↦ singleton questions. -/
def propIdent (p : (W → Prop)) : Quantifier W :=
  fun q => p = q

/-- Predicativize: extensional counterpart of Chierchia's ∪ (up) operator.

    In the finite extensional setting, `pred` coincides with `ident`:
    both map an entity to its singleton property `λx. [j = x]`.

    Conceptually distinct ([partee-1987] Figure 1):
    - `ident` is *formal* — pure combinatorics, always defined.
    - `pred` is *substantive* — applies to entity-correlates of properties
      and returns the corresponding property.

    The intensional generalization is `Semantics.Kinds.NMP.up`. -/
abbrev pred := @ident E

end TotalShifts

section Uniqueness

-- Boolean structure on the `Prop`/`Pi` denotation types is supplied directly by
-- mathlib (no `Ty`/`Denot` reflection, no bridge instances).

/-- Evaluate `Finset.inf` of function-valued functions at a point. -/
private lemma finset_inf_fun_eval {ι α : Type*}
    (s : Finset ι) (g : ι → α → Prop) (a : α) :
    (s.inf g) a = s.inf (fun i => g i a) := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons x s hx ih => simp only [Finset.inf_cons, Pi.inf_apply, ih]

/-- `BE ∘ individual = ident` (Figure 3 commutativity). -/
theorem BE_individual_eq_ident (j : E) :
    BE (individual j) = ident j := by
  funext x; simp only [BE, individual, ident]

/-- **Fact 2** ([partee-1987] §3.3): `BE` is the **unique**
    `BoundedLatticeHom` from `⟨⟨e,t⟩,t⟩` to `⟨e,t⟩` that makes
    Figure 3 commute (i.e., satisfies `f(individual j) = ident(j)`).

    Proof ([keenan-faltz-1985]): For each entity `x`, construct the
    atom `atom_x = ⨅_j literal(j)` where `literal(j) = individual j` if `j = x`
    and `(individual j)ᶜ` otherwise. This atom is the indicator of `{P_x}` where
    `P_x = λy. [y = x]`. Since `f` preserves `⊓` and complements, `f` maps
    `atom_x` correctly. Then monotonicity determines `f(Q)(x)` for arbitrary
    `Q` by cases on `Q(P_x)`. -/
theorem BE_unique [Fintype E] [DecidableEq E]
    (f : BoundedLatticeHom (Quantifier E) ((E → Prop)))
    (hcomm : ∀ j : E, f (individual j) = ident j) :
    ∀ Q : Quantifier E, f Q = BE Q := by
  intro Q; funext x
  show f Q x = Q (fun j => j = x)
  let lit : E → Quantifier E := fun j =>
    if j = x then (individual j : Quantifier E) else (individual j)ᶜ
  let atom_x : Quantifier E := Finset.inf Finset.univ lit
  let f_lit : E → (E → Prop) := fun j =>
    if j = x then (ident j : (E → Prop)) else (ident j)ᶜ
  -- Step 1: f maps each literal correctly
  have hf_lit : ∀ j, f (lit j) = f_lit j := by
    intro j; simp only [lit, f_lit]; split
    · exact hcomm j
    · rw [map_compl' f, hcomm j]
  -- Step 2: f preserves the atom
  have hf_atom_eq : f atom_x = Finset.inf Finset.univ f_lit := by
    show f (Finset.inf Finset.univ lit) = _
    rw [map_finset_inf f Finset.univ lit]; congr 1; funext j; exact hf_lit j
  -- Step 3: Each f_lit j holds at x
  have hf_lit_x : ∀ j : E, f_lit j x := by
    intro j; show (if j = x then ident j else (ident j)ᶜ) x
    split
    · next h => show ident j x; show j = x; exact h
    · next h => show ¬ident j x; exact h
  -- f(atom_x) at x holds
  have hf_atom_true : f atom_x x := by
    have h1 : f atom_x x = (Finset.univ.inf f_lit) x := congrFun hf_atom_eq x
    have h2 : (Finset.univ.inf f_lit) x = Finset.univ.inf (fun i => f_lit i x) :=
      finset_inf_fun_eval Finset.univ f_lit x
    rw [h1, h2]
    exact (Finset.le_inf (fun j _ => show ⊤ ≤ f_lit j x from fun _ => hf_lit_x j)) trivial
  -- Step 4: atom_x R holds → R = (fun j => j = x)
  have hatom_point : ∀ R : (E → Prop), atom_x R →
      R = fun j => j = x := by
    intro R hR
    have hlit : ∀ j : E, lit j R := by
      intro j
      exact (Finset.inf_le (Finset.mem_univ j) : atom_x ≤ lit j) R hR
    funext j
    have hj := hlit j; simp only [lit] at hj
    split at hj
    · next h =>
      -- hj : individual j R, i.e. R j. Goal: R j = (j = x)
      exact propext ⟨fun _ => h, fun _ => hj⟩
    · next h =>
      -- hj : (individual j)ᶜ R, i.e. ¬R j. Goal: R j = (j = x)
      exact propext ⟨fun hr => absurd hr hj, fun heq => absurd heq h⟩
  -- Step 5: conclude by cases on Q(fun j => j = x)
  have hatom_le : ∀ S : Quantifier E, S (fun j => j = x) → atom_x ≤ S := by
    intro S hS R hR
    have : R = fun j => j = x := hatom_point R hR
    rw [this]; exact hS
  by_cases hQPx : Q (fun j => j = x)
  · -- Q(P_x) holds: f Q x must hold by monotonicity
    exact propext ⟨fun _ => hQPx, fun _ =>
      OrderHomClass.mono f (hatom_le Q hQPx) x hf_atom_true⟩
  · -- ¬Q(P_x): f Q x must be false by complement reasoning
    have hQc : Qᶜ (fun j => j = x) := hQPx
    have hfQc : f Qᶜ x :=
      OrderHomClass.mono f (hatom_le Qᶜ hQc) x hf_atom_true
    have hfQc2 : ¬f Q x := by
      have := congrFun (map_compl' f Q) x
      -- this : f Qᶜ x = (f Q)ᶜ x, i.e. f Qᶜ x = ¬f Q x
      rw [this] at hfQc; exact hfQc
    exact propext ⟨fun h => absurd h hfQc2, fun h => absurd h hQPx⟩

end Uniqueness

section PartialShifts

/-- Partial inverse of `individual`. Defined when `Q` is a principal
ultrafilter. -/
noncomputable def lower (domain : List E) (Q : Quantifier E) : Option E :=
  match domain.filter (fun j => @decide (Q (fun x => x = j)) (Classical.dec _)) with
  | [j] => some j
  | _ => none

/-- Partial inverse of `ident`. Returns the unique satisfier of `P`. -/
noncomputable def iota (domain : List E) (P : (E → Prop)) : Option E :=
  match domain.filter (fun x => @decide (P x) (Classical.dec _)) with
  | [j] => some j
  | _ => none

/-- NOM: Nominalization ([partee-1987] Figure 1, [chierchia-1984]).
    Maps a property to its individual correlate: `⟨e,t⟩ → e` (partial).

    In the finite extensional setting, NOM = iota (returns the unique
    satisfier of P, if singleton). The intensional generalization is
    `Semantics.Kinds.NMP.down` (Chierchia's ∩). -/
noncomputable def NOM (domain : List E) (P : (E → Prop)) : Option E :=
  iota domain P

/-- THE: Presuppositional type-shifter for definites ([partee-1987] Figure 1).
    `THE(P) = individual(iota(P))` when `iota(P)` is defined (P has a unique
    satisfier).

    Maps `⟨e,t⟩ → ⟨⟨e,t⟩,t⟩` (partial). Unlike `A` (which is total), `THE`
    presupposes existence and uniqueness. Connects to the semantics of "the"
    in `Semantics.Definiteness`. -/
noncomputable def THE (domain : List E) (P : (E → Prop)) : Option (Quantifier E) :=
  (iota domain P).map individual

/-- Helper: for a nodup list, filtering for equality gives a singleton or empty. -/
private theorem filter_decEq_of_mem [DecidableEq E]
    (domain : List E) (j : E)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    domain.filter (fun k => @decide (j = k) inferInstance) = [j] := by
  induction domain with
  | nil => nomatch hmem
  | cons hd tl ih =>
    have ⟨hd_nmem, tl_nd⟩ := List.nodup_cons.mp hnd
    have filter_tl_nil : ∀ (hj : j ∈ tl → False),
        tl.filter (fun k => @decide (j = k) inferInstance) = [] := by
      intro hj
      rw [List.filter_eq_nil_iff]
      intro k hk hdec
      have hne : j ≠ k := fun heq => hj (heq ▸ hk)
      exact absurd (@of_decide_eq_true _ inferInstance hdec) hne
    cases hmem with
    | head =>
      have hdec : @decide (j = j) inferInstance = true :=
        @decide_eq_true _ inferInstance rfl
      rw [List.filter_cons, if_pos hdec, filter_tl_nil hd_nmem]
    | tail _ hmem' =>
      have hne : ¬ (j = hd) := fun heq => hd_nmem (heq ▸ hmem')
      have hdec : ¬ (@decide (j = hd) inferInstance = true) :=
        fun h => absurd (@of_decide_eq_true _ inferInstance h) hne
      rw [List.filter_cons, if_neg hdec]
      exact ih hmem' tl_nd

/-- `lower ∘ individual = some` on the domain (Partee's round-trip).

    Requires `j ∈ domain` (j must be in the model) and `domain.Nodup`
    (no duplicates, ensuring unique filter result). -/
theorem lower_individual [DecidableEq E] (domain : List E) (j : E)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    lower domain (individual j) = some j := by
  -- lower uses Classical.dec, filter_decEq_of_mem uses inferInstance
  -- Bridge: show the filter predicates are equal, then compute the result
  have heq : domain.filter
      (fun k => @decide (individual j (fun x => x = k)) (Classical.dec _)) = [j] := by
    rw [show (fun k => @decide (individual j (fun x => x = k)) (Classical.dec _)) =
            (fun k => @decide (j = k) inferInstance) from
      funext fun k => decide_eq_decide.mpr Iff.rfl]
    exact filter_decEq_of_mem domain j hmem hnd
  unfold lower individual; erw [heq]

/-- `iota ∘ ident = some` on the domain (Partee's round-trip).

    The `ident` predicate picks out exactly `j`, so `iota` returns `j`
    when `j` is the unique satisfier (guaranteed by `Nodup`). -/
theorem iota_ident [DecidableEq E] (domain : List E) (j : E)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    iota domain (ident j) = some j := by
  have heq : domain.filter (fun k => @decide (ident j k) (Classical.dec _)) = [j] := by
    rw [show (fun k => @decide (ident j k) (Classical.dec _)) =
            (fun k => @decide (j = k) inferInstance) from
      funext fun k => decide_eq_decide.mpr Iff.rfl]
    exact filter_decEq_of_mem domain j hmem hnd
  unfold iota ident; erw [heq]

/-- `THE ∘ ident = some ∘ individual` on the domain.
    When `ident(j)` has a unique satisfier (always, given Nodup),
    THE shifts it to the corresponding principal ultrafilter. -/
theorem THE_ident [DecidableEq E] (domain : List E) (j : E)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    THE domain (ident j) = some (individual j) := by
  simp only [THE, iota_ident domain j hmem hnd, Option.map]

end PartialShifts

/-- Coherence of the three readings of "the king" ([partee-1987] §3.2).
    When `iota` succeeds, the `e`, `⟨e,t⟩`, and `⟨⟨e,t⟩,t⟩` readings are
    related by `BE(individual j) = ident(j)` (Figure 2 commutativity). -/
theorem the_king_coherence (domain : List E) (P : (E → Prop))
    (j : E) (_h : iota domain P = some j) :
    BE (individual j) = ident j :=
  BE_individual_eq_ident j

/-! ### The type-shifting triangle ([partee-1987] Figure 3)

Partee's type-shifting triangle connects three NP semantic types via
six operations (three inverse pairs). The triangle **commutes**: any
two paths between the same pair of types yield the same result.

```
              e
             ╱ ╲
       ident╱   ╲individual
           ╱     ╲
          ↓       ↓
       ⟨e,t⟩ ⇄ ⟨⟨e,t⟩,t⟩
           A →
          ← BE
```

**Commutativity** (two faces):
- `BE ∘ individual = ident`    (right face, `BE_individual_eq_ident`)
- `A  ∘ ident = individual`    (left face, `A_ident_eq_individual`)

**Retraction**: `A` is a section of `BE` — `BE ∘ A = id` on `⟨e,t⟩`
(`Quantification.BE_A_id`).

**Consequence**: All composite paths agree. The triangle is a commutative
diagram in **Set**, with `A` and `BE` witnessing that the two embeddings
`ident : e → ⟨e,t⟩` and `individual : e → ⟨⟨e,t⟩,t⟩` are "the same map" up to
the A/BE retraction on their codomains.
-/

section TypeShiftingTriangle

/-- **Left face of the triangle**: `A ∘ ident = individual`.

    `A(ident(j))(P) = ∃x∈dom. [j=x] ∧ P(x) = P(j) = individual(j)(P)`.

    Together with `BE_individual_eq_ident` (right face), this establishes
    full commutativity of the type-shifting triangle. -/
theorem A_ident_eq_individual (domain : List E) (j : E)
    (hj : j ∈ domain) :
    A domain (ident j) = individual j := by
  funext P; simp only [A, individual, ident]
  refine propext ⟨?_, fun hPj => ⟨j, hj, rfl, hPj⟩⟩
  rintro ⟨x, _, rfl, hPx⟩; exact hPx

/-- Full cycle e →individual ⟨⟨e,t⟩,t⟩ →BE ⟨e,t⟩ →A ⟨⟨e,t⟩,t⟩ = individual.

    Going around the triangle through GQ-space returns to the same GQ. -/
theorem A_BE_individual (domain : List E) (j : E)
    (hj : j ∈ domain) :
    A domain (BE (individual j)) = individual j := by
  rw [BE_individual_eq_ident]; exact A_ident_eq_individual domain j hj

/-- Full cycle e →ident ⟨e,t⟩ →A ⟨⟨e,t⟩,t⟩ →BE ⟨e,t⟩ = ident.

    Going around the triangle through predicate-space returns to
    the same predicate. -/
theorem BE_A_ident (domain : List E) (j : E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    BE (A domain (ident j)) = ident j :=
  BE_A_id domain (ident j) hcomplete

/-- Partial path e →individual ⟨⟨e,t⟩,t⟩ →BE ⟨e,t⟩ →iota e = some.

    The indirect route through GQ-space recovers the entity. -/
theorem iota_BE_individual [DecidableEq E] (domain : List E) (j : E)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    iota domain (BE (individual j)) = some j := by
  rw [BE_individual_eq_ident]; exact iota_ident domain j hmem hnd

/-- Partial path e →ident ⟨e,t⟩ →A ⟨⟨e,t⟩,t⟩ →lower e = some.

    The indirect route through predicate-space recovers the entity. -/
theorem lower_A_ident [DecidableEq E] (domain : List E) (j : E)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    lower domain (A domain (ident j)) = some j := by
  rw [A_ident_eq_individual domain j hmem]; exact lower_individual domain j hmem hnd

/-- THE respects the triangle: `THE ∘ BE ∘ individual = some ∘ individual`.

    Recovering the definite description from a type-raised proper name
    via BE, then THE, yields the original type-raised individual. -/
theorem THE_BE_individual [DecidableEq E] (domain : List E) (j : E)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    THE domain (BE (individual j)) = some (individual j) := by
  rw [BE_individual_eq_ident]; exact THE_ident domain j hmem hnd

end TypeShiftingTriangle

/-! ### Numeral type-shifters ([snyder-2026]) -/

section NumeralShifts

/-- CARD: number → cardinality predicate ([snyder-2026], (6a)).
    CARD = λn.λx. μ(x) = n. Turns a number into a predicate
    on entities that have exactly n atomic parts. -/
def CARD (μ : E → Nat) (n : Nat) : (E → Prop) :=
  fun x => μ x = n

/-- PM: Predicate Modification ([heim-kratzer-1998], (7a)).
    PM = λP.λQ.λx. P(x) ∧ Q(x): `Modifier.intersective` at `e ⇒ t`. -/
def PM (P Q : (E → Prop)) : (E → Prop) :=
  Modifier.intersective P Q

end NumeralShifts

/-- `NOM(pred(j)) = some j`: nominalizing the predicativization of an entity
    returns that entity. The extensional counterpart of Chierchia's `∩(∪k) = k`
    (`Semantics.Kinds.NMP.down_up_id`). -/
theorem NOM_pred [DecidableEq E] (domain : List E) (j : E)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    NOM domain (pred j) = some j :=
  iota_ident domain j hmem hnd

/-! ### Complement denotation types ([chierchia-1984])

[chierchia-1984] argues that infinitival and gerundive complements
denote **properties** (type ⟨e,t⟩), not propositions (type ⟨s,t⟩). This
is the original linguistic motivation for the `pred`/`nom` operators in
[partee-1987]'s type-shifting triangle.

The key insight: `pred` and `nom` mediate between the **individual
correlate** of a property (an entity of type `e` that "is" the property)
and the property itself (type ⟨e,t⟩). This is exactly what infinitival
complements need: "to run" denotes a property, but it can be nominalized
("running is fun") to denote the individual correlate of that property.

The intensional generalization of this idea appears in [chierchia-1998]
as ∩ (down) and ∪ (up), applied to kinds rather than infinitives.
Both applications share the same underlying type-shift: there is a
systematic correspondence between properties and their individual
correlates in the domain. -/

/-- Complement denotation layer: whether a complement denotes a
    property (⟨e,t⟩, open predicate) or a proposition (t / ⟨s,t⟩, closed).

    [chierchia-1984] Ch I: the infinitive/gerund vs. finite clause
    distinction corresponds to this type distinction. Nominalization
    (`NOM`/`nom`) and control both require the property layer — control
    needs an unsaturated individual argument to bind, and nominalization
    maps ⟨e,t⟩ → e. Propositions must go through existential closure
    (`A`) to reach the GQ layer.

    The extensional `pred`/`nom` pair, their intensional generalization
    as ∩/∪ in [chierchia-1998], and the Control Principle in
    [chierchia-1984] Ch IV all operate on the property layer. -/
inductive ClauseLayer where
  /-- Property layer: ⟨e,t⟩. Domain of `pred`/`nom`/`NOM`.
      Infinitival and gerundive complements. -/
  | property
  /-- Propositional layer: t (or ⟨s,t⟩ intensionally).
      Finite indicative and subjunctive complements. -/
  | proposition
  deriving DecidableEq, Repr

/-- Property-type complements support nominalization (⟨e,t⟩ → e via `NOM`)
    and control (the unsaturated argument position can be bound).

    This unifies [chierchia-1984]'s two central claims: control and
    nominalization are both consequences of the property/proposition
    type distinction. -/
def ClauseLayer.isProperty : ClauseLayer → Bool
  | .property    => true
  | .proposition => false

end Semantics.Composition.TypeShifting
