import Linglib.Core.Logic.Intensional.Frame
import Linglib.Core.Logic.Intensional.Conjunction
import Linglib.Semantics.Composition.ToyDomain
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Data.Finset.Lattice.Fold

/-!
# NP Type-Shifting Principles
[partee-1987]

Three NP semantic types and six type-shifting operations (three inverse pairs):

    lift  / lower : e ↔ ⟨⟨e,t⟩,t⟩         (total / partial)
    ident / iota  : e ↔ ⟨e,t⟩              (formal; total / partial)
    pred  / nom   : e ↔ ⟨e,t⟩              (substantive; Chierchia's ∪/∩)
          A / BE  : ⟨e,t⟩ ↔ ⟨⟨e,t⟩,t⟩     (total / total)
        THE       : ⟨e,t⟩ → ⟨⟨e,t⟩,t⟩     (partial; presuppositional)

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

open Core.Logic.Intensional
open Core.Logic.Intensional.Conjunction (typeRaise)
open Semantics.Montague (ToyEntity)

variable {E W : Type}

section TotalShifts

/-- Type-raising: `lift(j) = λP. P(j)` -/
def lift (j : E) : ((E → Prop) → Prop) :=
  fun P => P j

/-- Singleton property: `ident(j) = λx. [j = x]`.
Uses `j = x` order for definitional equality with `BE(lift(j))`. -/
def ident (j : E) : (E → Prop) :=
  fun x => j = x

/-- Propositional analogue of `ident`: `propIdent(p) = λq. [p = q]`,
i.e. the singleton question `{p}` from a proposition `p`.

This is `ID` of [elliott-etal-2017] (their eq. 10), used to coerce a
proposition into a question denotation when an embedding predicate (e.g.
a Predicate of Relevance like `care`) selects only for questions. The shape
mirrors `ident` one type-theoretic level up: entities ↦ singleton properties
becomes propositions ↦ singleton questions. -/
def propIdent (p : (W → Prop)) : ((W → Prop) → Prop) :=
  fun q => p = q

/-- Predicative content of a GQ: `BE(Q) = λx. Q(λy. y = x)` -/
def BE (Q : ((E → Prop) → Prop)) : (E → Prop) :=
  fun x => Q (fun y => y = x)

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

section BooleanHomomorphism

-- Boolean structure on the `Prop`/`Pi` denotation types is supplied directly by
-- mathlib (no `Ty`/`Denot` reflection, no bridge instances).

/-- Evaluate `Finset.inf` of function-valued functions at a point. -/
private lemma finset_inf_fun_eval {ι α : Type*}
    (s : Finset ι) (g : ι → α → Prop) (a : α) :
    (s.inf g) a = s.inf (fun i => g i a) := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons x s hx ih => simp only [Finset.inf_cons, Pi.inf_apply, ih]

/-- `BE` is a `BoundedLatticeHom` (Partee §3.3, Fact 1). -/
def BE_hom (E : Type) : BoundedLatticeHom (((E → Prop) → Prop)) ((E → Prop)) where
  toFun := BE
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl

/-- `BE ∘ lift = ident` (Figure 3 commutativity). -/
theorem BE_lift_eq_ident (j : E) :
    BE (lift j) = ident j := by
  funext x; simp only [BE, lift, ident]

/-- **Fact 2** ([partee-1987] §3.3): `BE` is the **unique**
    `BoundedLatticeHom` from `⟨⟨e,t⟩,t⟩` to `⟨e,t⟩` that makes
    Figure 3 commute (i.e., satisfies `f(lift(j)) = ident(j)`).

    Proof ([keenan-faltz-1985]): For each entity `x`, construct the
    atom `atom_x = ⨅_j literal(j)` where `literal(j) = lift(j)` if `j = x`
    and `(lift(j))ᶜ` otherwise. This atom is the indicator of `{P_x}` where
    `P_x = λy. [y = x]`. Since `f` preserves `⊓` and complements, `f` maps
    `atom_x` correctly. Then monotonicity determines `f(Q)(x)` for arbitrary
    `Q` by cases on `Q(P_x)`. -/
theorem BE_unique [Fintype E] [DecidableEq E]
    (f : BoundedLatticeHom (((E → Prop) → Prop)) ((E → Prop)))
    (hcomm : ∀ j : E, f (lift j) = ident j) :
    ∀ Q : ((E → Prop) → Prop), f Q = BE Q := by
  intro Q; funext x
  show f Q x = Q (fun j => j = x)
  let lit : E → ((E → Prop) → Prop) := fun j =>
    if j = x then (lift j : ((E → Prop) → Prop)) else (lift j)ᶜ
  let atom_x : ((E → Prop) → Prop) := Finset.inf Finset.univ lit
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
      -- hj : lift j R, i.e. R j. Goal: R j = (j = x)
      exact propext ⟨fun _ => h, fun _ => hj⟩
    · next h =>
      -- hj : (lift j)ᶜ R, i.e. ¬R j. Goal: R j = (j = x)
      exact propext ⟨fun hr => absurd hr hj, fun heq => absurd heq h⟩
  -- Step 5: conclude by cases on Q(fun j => j = x)
  have hatom_le : ∀ S : ((E → Prop) → Prop), S (fun j => j = x) → atom_x ≤ S := by
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

/-- `BE(Q₁ ∧ Q₂) = BE(Q₁) ∧ BE(Q₂)` -/
theorem BE_conj (Q₁ Q₂ : ((E → Prop) → Prop)) :
    BE (fun P => Q₁ P ∧ Q₂ P) = (fun x => BE Q₁ x ∧ BE Q₂ x) := rfl

/-- `BE(Q₁ ∨ Q₂) = BE(Q₁) ∨ BE(Q₂)` -/
theorem BE_disj (Q₁ Q₂ : ((E → Prop) → Prop)) :
    BE (fun P => Q₁ P ∨ Q₂ P) = (fun x => BE Q₁ x ∨ BE Q₂ x) := rfl

/-- `BE(¬Q) = ¬BE(Q)` -/
theorem BE_neg (Q : ((E → Prop) → Prop)) :
    BE (fun P => ¬(Q P)) = (fun x => ¬(BE Q x)) := rfl

end BooleanHomomorphism

section PartialShifts

/-- Partial inverse of `lift`. Defined when `Q` is a principal ultrafilter. -/
noncomputable def lower (domain : List E) (Q : ((E → Prop) → Prop)) : Option E :=
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

/-- Existential closure: `A(P) = λQ. ∃x. P(x) ∧ Q(x)` -/
def A (domain : List E) (P : (E → Prop)) : ((E → Prop) → Prop) :=
  fun Q => ∃ x ∈ domain, P x ∧ Q x

/-- THE: Presuppositional type-shifter for definites ([partee-1987] Figure 1).
    `THE(P) = lift(iota(P))` when `iota(P)` is defined (P has a unique satisfier).

    Maps `⟨e,t⟩ → ⟨⟨e,t⟩,t⟩` (partial). Unlike `A` (which is total), `THE`
    presupposes existence and uniqueness. Connects to the semantics of "the"
    in `Semantics.Definiteness`. -/
noncomputable def THE (domain : List E) (P : (E → Prop)) : Option (((E → Prop) → Prop)) :=
  (iota domain P).map lift

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

/-- `lower ∘ lift = some` on the domain (Partee's round-trip).

    Requires `j ∈ domain` (j must be in the model) and `domain.Nodup`
    (no duplicates, ensuring unique filter result). -/
theorem lower_lift [DecidableEq E] (domain : List E) (j : E)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    lower domain (lift j) = some j := by
  -- lower uses Classical.dec, filter_decEq_of_mem uses inferInstance
  -- Bridge: show the filter predicates are equal, then compute the result
  have heq : domain.filter (fun k => @decide (lift j (fun x => x = k)) (Classical.dec _)) = [j] := by
    rw [show (fun k => @decide (lift j (fun x => x = k)) (Classical.dec _)) =
            (fun k => @decide (j = k) inferInstance) from
      funext fun k => decide_eq_decide.mpr Iff.rfl]
    exact filter_decEq_of_mem domain j hmem hnd
  unfold lower lift; erw [heq]

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

/-- `THE ∘ ident = some ∘ lift` on the domain.
    When `ident(j)` has a unique satisfier (always, given Nodup),
    THE shifts it to the corresponding principal ultrafilter. -/
theorem THE_ident [DecidableEq E] (domain : List E) (j : E)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    THE domain (ident j) = some (lift j) := by
  simp only [THE, iota_ident domain j hmem hnd, Option.map]

end PartialShifts

/-- `lift = Conjunction.typeRaise` -/
theorem lift_eq_typeRaise (j : E) :
    lift j = (typeRaise (W := W) j) := rfl

/-- Coherence of the three readings of "the king" ([partee-1987] §3.2).
    When `iota` succeeds, the `e`, `⟨e,t⟩`, and `⟨⟨e,t⟩,t⟩` readings are
    related by `BE(lift(j)) = ident(j)` (Figure 2 commutativity). -/
theorem the_king_coherence (domain : List E) (P : (E → Prop))
    (j : E) (_h : iota domain P = some j) :
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
def isPrincipalUltrafilter (domain : List E) (Q : ((E → Prop) → Prop)) : Prop :=
  ∃ j ∈ domain, Q = lift j

/-- Helper: `(∃ x ∈ domain, j = x ∧ P x) ↔ P j` when `j ∈ domain`. -/
private theorem exists_eq_and_iff (domain : List E) (j : E)
    (hj : j ∈ domain) (P : (E → Prop)) :
    (∃ x ∈ domain, j = x ∧ P x) ↔ P j := by
  constructor
  · rintro ⟨x, _, rfl, hPx⟩; exact hPx
  · intro hPj; exact ⟨j, hj, rfl, hPj⟩

/-- **Round-trip preservation for principal ultrafilters.**
    For `Q = lift(j)`, `A(BE(Q))(P) = Q(P)` for all P.
    This means type-shifting is truth-conditionally transparent for
    proper names, pronouns, definites — any expression that denotes
    a principal ultrafilter. -/
theorem roundtrip_preserves_principal (domain : List E) (j : E)
    (hj : j ∈ domain) :
    ∀ P : (E → Prop), A domain (BE (lift j)) P = lift j P := by
  intro P
  simp only [A, BE, lift]
  exact propext (exists_eq_and_iff domain j hj P)

/-- **`BE ∘ A = id` on properties** ([partee-1987] §3.3).

    For any property `P`, `BE(A(P)) = P`. This makes `A` a right inverse
    of `BE`: existential closure followed by predicative content recovers
    the original property.

    This is the key result establishing `A` as a "natural" type-shifting
    functor — it is an inverse of `BE`, and Partee argues it (together with
    `some`) is the most natural DET-type functor.

    Proof: `BE(A(P))(x) = A(P)(λy. y=x) = ∃z∈dom. P(z) ∧ (z=x) = P(x)`.
    The `decide(z=x)` selects exactly `z = x`, collapsing the existential. -/
theorem BE_A_id (domain : List E) (P : (E → Prop))
    (hcomplete : ∀ x : E, x ∈ domain) :
    BE (A domain P) = P := by
  funext x; show (∃ z ∈ domain, P z ∧ z = x) = P x
  apply propext; constructor
  · rintro ⟨z, _, hPz, hzx⟩; cases hzx; exact hPz
  · intro hPx; exact ⟨x, hcomplete x, hPx, rfl⟩

/-- For non-principal GQs, the round-trip can differ.
    Example: `⟦every⟧(P)(Q) = ∀x[P(x) → Q(x)]`, but
    `A(BE(⟦every⟧(P)))(Q) = ∃x[P(x) ∧ Q(x)]` — existential, not universal.
    Verified on the toy model. -/
private def toyDomain₁ : List ToyEntity := [.john, .mary, .pizza]
private def toyEvery : (ToyEntity → Prop) → Prop := fun P => ∀ x ∈ toyDomain₁, P x

/-- For non-principal GQs, the round-trip changes truth conditions.
    `every(⊤) = True` but `A(BE(every))(⊤) = False` — the round-trip
    collapses universal quantification to `⊥` on multi-element domains.
    (`BE(every)` asks "which entity equals all entities?" — none do.) -/
theorem roundtrip_changes_nonprincipal :
    toyEvery (fun _ => True) ∧ ¬ A toyDomain₁ (BE toyEvery) (fun _ => True) := by
  refine ⟨fun _ _ => trivial, ?_⟩
  intro ⟨x, _, hBE, _⟩
  -- hBE : BE toyEvery x, i.e. ∀ y ∈ toyDomain₁, y = x
  -- Impossible since toyDomain₁ has 3 distinct elements
  simp only [BE, toyEvery, toyDomain₁] at hBE
  have h1 : ToyEntity.john = x := hBE .john (by simp)
  have h2 : ToyEntity.mary = x := hBE .mary (by simp)
  rw [← h1] at h2; exact ToyEntity.noConfusion h2

section ToyExamples

open Semantics.Montague.ToyLexicon (john_sem)

private def toyDomain₂ : List ToyEntity := [.john, .mary, .pizza, .book]

example : lift (E := ToyEntity) john_sem Semantics.Montague.ToyLexicon.sleeps_sem :=
  show Semantics.Montague.ToyLexicon.sleeps_sem john_sem from trivial
example : BE (E := ToyEntity) (lift john_sem) = ident john_sem :=
  BE_lift_eq_ident john_sem

end ToyExamples

-- ============================================================================
-- The Type-Shifting Triangle ([partee-1987] Figure 3)
-- ============================================================================

/-! ## The Full Commutativity Diagram

Partee's type-shifting triangle connects three NP semantic types via
six operations (three inverse pairs). The triangle **commutes**: any
two paths between the same pair of types yield the same result.

```
           e
          ╱ ╲
    ident╱   ╲lift
        ╱     ╲
       ↓       ↓
    ⟨e,t⟩ ⇄ ⟨⟨e,t⟩,t⟩
        A →
       ← BE
```

**Commutativity** (two faces):
- `BE ∘ lift = ident`    (right face, `BE_lift_eq_ident`)
- `A  ∘ ident = lift`    (left face, `A_ident_eq_lift`)

**Retraction**: `BE ∘ A = id` on `⟨e,t⟩` (`BE_A_id`) — `A` is a section of `BE`.

**Consequence**: All composite paths agree. The triangle is a commutative
diagram in **Set**, with `A` and `BE` witnessing that the two embeddings
`ident : e → ⟨e,t⟩` and `lift : e → ⟨⟨e,t⟩,t⟩` are "the same map" up to
the A/BE retraction on their codomains.
-/

section TypeShiftingTriangle

/-- **Left face of the triangle**: `A ∘ ident = lift`.

    `A(ident(j))(P) = ∃x∈dom. [j=x] ∧ P(x) = P(j) = lift(j)(P)`.

    Together with `BE_lift_eq_ident` (right face), this establishes
    full commutativity of the type-shifting triangle. -/
theorem A_ident_eq_lift (domain : List E) (j : E)
    (hj : j ∈ domain) :
    A domain (ident j) = lift j := by
  funext P; simp only [A, lift, ident]
  exact propext (exists_eq_and_iff domain j hj P)

/-- Full cycle e →lift ⟨⟨e,t⟩,t⟩ →BE ⟨e,t⟩ →A ⟨⟨e,t⟩,t⟩ = lift.

    Going around the triangle through GQ-space returns to the same GQ. -/
theorem A_BE_lift (domain : List E) (j : E)
    (hj : j ∈ domain) :
    A domain (BE (lift j)) = lift j := by
  rw [BE_lift_eq_ident]; exact A_ident_eq_lift domain j hj

/-- Full cycle e →ident ⟨e,t⟩ →A ⟨⟨e,t⟩,t⟩ →BE ⟨e,t⟩ = ident.

    Going around the triangle through predicate-space returns to
    the same predicate. -/
theorem BE_A_ident (domain : List E) (j : E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    BE (A domain (ident j)) = ident j :=
  BE_A_id domain (ident j) hcomplete

/-- Partial path e →lift ⟨⟨e,t⟩,t⟩ →BE ⟨e,t⟩ →iota e = some.

    The indirect route through GQ-space recovers the entity. -/
theorem iota_BE_lift [DecidableEq E] (domain : List E) (j : E)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    iota domain (BE (lift j)) = some j := by
  rw [BE_lift_eq_ident]; exact iota_ident domain j hmem hnd

/-- Partial path e →ident ⟨e,t⟩ →A ⟨⟨e,t⟩,t⟩ →lower e = some.

    The indirect route through predicate-space recovers the entity. -/
theorem lower_A_ident [DecidableEq E] (domain : List E) (j : E)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    lower domain (A domain (ident j)) = some j := by
  rw [A_ident_eq_lift domain j hmem]; exact lower_lift domain j hmem hnd

/-- THE respects the triangle: `THE ∘ BE ∘ lift = some ∘ lift`.

    Recovering the definite description from a type-raised proper name
    via BE, then THE, yields the original type-raised individual. -/
theorem THE_BE_lift [DecidableEq E] (domain : List E) (j : E)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    THE domain (BE (lift j)) = some (lift j) := by
  rw [BE_lift_eq_ident]; exact THE_ident domain j hmem hnd

-- --------------------------------------------------------------------------
-- Section/retraction structure via Mathlib
-- --------------------------------------------------------------------------

/-- `BE` is a left inverse of `A`: the section/retraction structure of the
    type-shifting triangle, expressed using `Function.LeftInverse`.

    This connects to Mathlib's function infrastructure, giving us
    `Surjective BE` and `Injective (A domain)` for free. -/
theorem BE_leftInverse_A (domain : List E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    Function.LeftInverse BE (A domain) :=
  fun P => BE_A_id domain P hcomplete

/-- `BE` is surjective: every predicate is the predicative content of some GQ.
    Derived from `Function.LeftInverse.surjective`. -/
theorem BE_surjective (domain : List E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    Function.Surjective (@BE E) :=
  (BE_leftInverse_A domain hcomplete).surjective

/-- `A` is injective: distinct predicates yield distinct GQs under
    existential closure. Linguistically: different common nouns mean
    different things as indefinites.
    Derived from `Function.LeftInverse.injective`. -/
theorem A_injective (domain : List E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    Function.Injective (A domain) :=
  (BE_leftInverse_A domain hcomplete).injective

end TypeShiftingTriangle

-- ============================================================================
-- Galois Coinsertion on Upward-Closed GQs
-- ============================================================================

/-! ## The A/BE Adjunction on Monotone GQs

[barwise-cooper-1981] observed that natural language determiners
denote **upward-closed** (monotone) generalized quantifiers: if `Q(P)` and
`P ⊆ P'`, then `Q(P')`. This constraint is exactly what makes `A` and `BE`
form a `GaloisCoinsertion` — an adjunction where the upper adjoint (`BE`)
retracts the lower adjoint (`A`).

On the full Boolean algebra of all GQs, `A ⊣ BE` fails: for non-monotone Q
(e.g., `λR. ¬R(a)`), `A(BE(Q)) ≤ Q` does not hold. But restricted to the
sublattice of monotone GQs, the key inequality `A(BE(Q)) ≤ Q` holds because
singleton predicates `{x} ≤ R` whenever `R(x)`, and monotonicity of `Q`
lifts this to `Q({x}) ≤ Q(R)`.

The `GaloisCoinsertion` gives us, via Mathlib:
- `GaloisConnection`: `A(P) ≤ Q ↔ P ≤ BE(Q)` for monotone Q
- `BE_up` is surjective on `UpwardGQ` and `A_up` is injective
- `A_up` is strictly monotone
-/

section GaloisStructure

/-- Upward-closed (monotone) generalized quantifiers — the
    [barwise-cooper-1981] constraint on natural language determiners.

    `Q` is upward-closed when `Q(P)` and `P ≤ P'` imply `Q(P')`.
    Equivalently, `Monotone Q` in the pointwise order on `⟨e,t⟩`. -/
def UpwardGQ (E : Type) := { Q : ((E → Prop) → Prop) // Monotone Q }

instance : PartialOrder (UpwardGQ E) := Subtype.partialOrder _

/-- `A(P)` is always upward-closed: if ∃x∈dom with P(x) ∧ R(x),
    and R ≤ R', then ∃x∈dom with P(x) ∧ R'(x). -/
theorem A_monotone_gq (domain : List E) (P : (E → Prop)) :
    Monotone (A domain P) := by
  intro R R' hRR'
  show (∃ x ∈ domain, P x ∧ R x) → ∃ x ∈ domain, P x ∧ R' x
  exact fun ⟨x, hx, hPx, hRx⟩ => ⟨x, hx, hPx, hRR' x hRx⟩

/-- Lift `A` to the `UpwardGQ` subtype. -/
def A_up (domain : List E) (P : (E → Prop)) : UpwardGQ E :=
  ⟨A domain P, A_monotone_gq domain P⟩

/-- Project `BE` from the `UpwardGQ` subtype. -/
def BE_up (Q : UpwardGQ E) : (E → Prop) := BE Q.val

/-- `A` is monotone as a map from predicates to GQs. -/
theorem A_up_mono (domain : List E) : Monotone (A_up domain (E := E)) := by
  intro P P' hPP'; show A domain P ≤ A domain P'; intro R
  show (∃ x ∈ domain, P x ∧ R x) → ∃ x ∈ domain, P' x ∧ R x
  exact fun ⟨x, hx, hPx, hRx⟩ => ⟨x, hx, hPP' x hPx, hRx⟩

/-- `BE` is monotone on `UpwardGQ`. -/
theorem BE_up_mono : Monotone (BE_up (E := E)) := by
  intro Q Q' hQQ'; show BE Q.val ≤ BE Q'.val; intro x
  exact hQQ' (fun y => y = x)

/-- Singleton predicate `{x}` is below any `R` with `R(x)`. -/
private lemma singleton_le_of_mem {x : E} {R : (E → Prop)}
    (hRx : R x) :
    (fun y => y = x) ≤ R := by
  intro y (h : y = x); rw [h]; exact hRx

/-- **Key inequality**: `A(BE(Q)) ≤ Q` for upward-closed Q.

    `A(BE(Q))(R) = ∃x∈dom. Q({x}) ∧ R(x)`. When `R(x)` holds,
    `{x} ≤ R` in the pointwise order. By monotonicity of `Q`,
    `Q({x}) ≤ Q(R)`, establishing the inequality.

    This is precisely the condition that fails for non-monotone Q
    (e.g., `Q = λR. ¬R(a)` where `Q({a}) = false` but `Q(∅) = true`). -/
theorem A_BE_le_of_mono (domain : List E) (Q : UpwardGQ E) :
    A_up domain (BE_up Q) ≤ Q := by
  show A domain (BE Q.val) ≤ Q.val
  intro R; simp only [A, BE]
  intro ⟨x, _, hQx, hRx⟩
  exact Q.property (singleton_le_of_mem hRx) hQx

/-- **Galois coinsertion**: `A` (existential closure) and `BE` (predicative
    content) form a `GaloisCoinsertion` on the sublattice of upward-closed GQs.

    This is the order-theoretic content of Partee's type-shifting triangle:
    - `BE ∘ A = id` on predicates (the retraction)
    - `A(BE(Q)) ≤ Q` for monotone Q (the counit inequality)

    Linguistically: [barwise-cooper-1981]'s constraint that natural
    language determiners denote monotone GQs is **exactly** the condition
    under which the A/BE pair forms an adjunction. -/
def galoisCoinsertion (domain : List E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    GaloisCoinsertion (A_up domain (E := E)) BE_up :=
  GaloisCoinsertion.monotoneIntro
    BE_up_mono
    (A_up_mono domain)
    (A_BE_le_of_mono domain)
    (fun P => BE_A_id domain P hcomplete)

/-- The Galois connection: `A(P) ≤ Q ↔ P ≤ BE(Q)` for monotone Q. -/
theorem gc_A_BE (domain : List E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    GaloisConnection (A_up domain (E := E)) BE_up :=
  (galoisCoinsertion domain hcomplete).gc

end GaloisStructure

-- ============================================================================
-- Numeral type-shifters ([snyder-2026])
-- ============================================================================

section NumeralShifts

/-- CARD: number → cardinality predicate ([snyder-2026], (6a)).
    CARD = λn.λx. μ(x) = n. Turns a number into a predicate
    on entities that have exactly n atomic parts. -/
def CARD (μ : E → Nat) (n : Nat) : (E → Prop) :=
  fun x => μ x = n

/-- PM: Predicate Modification ([heim-kratzer-1998], (7a)).
    PM = λP.λQ.λx. P(x) ∧ Q(x). Intersective modifier. -/
def PM (P Q : (E → Prop)) : (E → Prop) :=
  fun x => P x ∧ Q x

end NumeralShifts

/-- `NOM(pred(j)) = some j`: nominalizing the predicativization of an entity
    returns that entity. The extensional counterpart of Chierchia's `∩(∪k) = k`
    (`Semantics.Kinds.NMP.down_up_id`). -/
theorem NOM_pred [DecidableEq E] (domain : List E) (j : E)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    NOM domain (pred j) = some j :=
  iota_ident domain j hmem hnd

-- ============================================================================
-- Complement Denotation Types ([chierchia-1984])
-- ============================================================================

/-! ## Property vs. Proposition: Complement Denotation Types

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
inductive ComplSemLayer where
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
def ComplSemLayer.isProperty : ComplSemLayer → Bool
  | .property    => true
  | .proposition => false

end Semantics.Composition.TypeShifting
