import Linglib.Theories.Semantics.Montague.Types
import Linglib.Theories.Semantics.Montague.Conjunction
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Data.Finset.Lattice.Fold

/-!
# NP Type-Shifting Principles
@cite{partee-1987}

Three NP semantic types and six type-shifting operations (three inverse pairs):

    lift  / lower : e ↔ ⟨⟨e,t⟩,t⟩         (total / partial)
    ident / iota  : e ↔ ⟨e,t⟩              (formal; total / partial)
    pred  / nom   : e ↔ ⟨e,t⟩              (substantive; Chierchia's ∪/∩)
          A / BE  : ⟨e,t⟩ ↔ ⟨⟨e,t⟩,t⟩     (total / total)
        THE       : ⟨e,t⟩ → ⟨⟨e,t⟩,t⟩     (partial; presuppositional)

In the finite extensional setting, `pred = ident` and `nom = iota`. The
conceptual difference: `ident`/`iota` are *formal* (pure combinatorics),
while `pred`/`nom` are *substantive* (depend on entity-property correspondence).
The intensional generalizations are Chierchia's ∪ (up) and ∩ (down) operators
in `Semantics.Lexical.Noun.Kind.Chierchia1998`.

-/

namespace Semantics.Composition.TypeShifting

open Semantics.Montague (Model Ty toyModel ToyEntity)
open Semantics.Montague.Conjunction (typeRaise)

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

/-- Predicativize: extensional counterpart of Chierchia's ∪ (up) operator.

    In the finite extensional setting, `pred` coincides with `ident`:
    both map an entity to its singleton property `λx. [j = x]`.

    Conceptually distinct (@cite{partee-1987} Figure 1):
    - `ident` is *formal* — pure combinatorics, always defined.
    - `pred` is *substantive* — applies to entity-correlates of properties
      and returns the corresponding property.

    The intensional generalization is `Semantics.Lexical.Noun.Kind.Chierchia1998.up`. -/
abbrev pred := @ident m

end TotalShifts

section BooleanHomomorphism

instance (m : Model) : BooleanAlgebra (m.interpTy Ty.t) :=
  show BooleanAlgebra Bool from inferInstance
instance (m : Model) : BooleanAlgebra (m.interpTy Ty.et) :=
  show BooleanAlgebra (m.Entity → Bool) from inferInstance
instance (m : Model) : BooleanAlgebra (m.interpTy Ty.ett) :=
  show BooleanAlgebra ((m.Entity → Bool) → Bool) from inferInstance

/-- Evaluate `Finset.inf` of function-valued functions at a point. -/
private lemma finset_inf_fun_eval {ι α : Type*}
    (s : Finset ι) (g : ι → α → Bool) (a : α) :
    (s.inf g) a = s.inf (fun i => g i a) := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons x s hx ih => simp only [Finset.inf_cons, Pi.inf_apply, ih]

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

/-- **Fact 2** (@cite{partee-1987} §3.3): `BE` is the **unique**
    `BoundedLatticeHom` from `⟨⟨e,t⟩,t⟩` to `⟨e,t⟩` that makes
    Figure 3 commute (i.e., satisfies `f(lift(j)) = ident(j)`).

    Proof (@cite{keenan-faltz-1985}): For each entity `x`, construct the
    atom `atom_x = ⨅_j literal(j)` where `literal(j) = lift(j)` if `j = x`
    and `(lift(j))ᶜ` otherwise. This atom is the indicator of `{P_x}` where
    `P_x = λy. [y = x]`. Since `f` preserves `⊓` and complements, `f` maps
    `atom_x` correctly. Then monotonicity determines `f(Q)(x)` for arbitrary
    `Q` by cases on `Q(P_x)`. -/
theorem BE_unique [Fintype m.Entity]
    (f : BoundedLatticeHom (m.interpTy Ty.ett) (m.interpTy Ty.et))
    (hcomm : ∀ j : m.Entity, f (lift j) = ident j) :
    ∀ Q : m.interpTy Ty.ett, f Q = BE Q := by
  letI : DecidableEq m.Entity := m.decEq
  intro Q; funext x
  show f Q x = Q (fun j => decide (j = x))
  let lit : m.Entity → m.interpTy Ty.ett := fun j =>
    if j = x then (lift j : m.interpTy Ty.ett) else (lift j)ᶜ
  let atom_x : m.interpTy Ty.ett := Finset.inf Finset.univ lit
  let f_lit : m.Entity → m.interpTy Ty.et := fun j =>
    if j = x then (ident j : m.interpTy Ty.et) else (ident j)ᶜ
  -- Step 1: f maps each literal correctly
  have hf_lit : ∀ j, f (lit j) = f_lit j := by
    intro j; simp only [lit, f_lit]; split
    · exact hcomm j
    · rw [map_compl' f, hcomm j]
  -- Step 2: f preserves the atom
  have hf_atom_eq : f atom_x = Finset.inf Finset.univ f_lit := by
    show f (Finset.inf Finset.univ lit) = _
    rw [map_finset_inf f Finset.univ lit]; congr 1; funext j; exact hf_lit j
  -- Step 3: Each f_lit j evaluates to true at x
  have hf_lit_x : ∀ j : m.Entity, f_lit j x = true := by
    intro j; simp only [f_lit]; split
    · next h => rw [h]; simp [ident]
    · next h =>
      have hid : ident j x = false := by simp [ident, h]
      have := Pi.compl_apply (ident j) x
      rw [this, hid]; rfl
  -- f(atom_x) at x is true
  have hf_atom_true : f atom_x x = true := by
    rw [congrFun hf_atom_eq x, finset_inf_fun_eval Finset.univ f_lit x]
    have h := Finset.le_inf (fun j (_ : j ∈ Finset.univ) => ge_of_eq (hf_lit_x j))
    exact top_le_iff.mp h
  -- Step 4: atom_x R = true → R = P_x
  have hatom_point : ∀ R : m.interpTy Ty.et, atom_x R = true →
      R = fun j => decide (j = x) := by
    intro R hR
    have hlit_true : ∀ j : m.Entity, lit j R = true := by
      intro j
      have h1 : atom_x ≤ lit j := Finset.inf_le (Finset.mem_univ j)
      have h2 := h1 R
      rw [hR] at h2
      exact top_le_iff.mp h2
    funext j
    have hj := hlit_true j; simp only [lit] at hj
    split at hj
    · next h =>
      simp only [lift] at hj; rw [hj]; symm
      exact @decide_eq_true _ (m.decEq j x) h
    · next h =>
      have hcompl := Pi.compl_apply (lift j) R
      rw [hcompl] at hj; simp only [lift] at hj
      have hRj : R j = false := by
        cases hv : R j with
        | false => rfl
        | true => rw [hv] at hj; exact Bool.noConfusion hj
      rw [hRj]; symm
      exact @decide_eq_false _ (m.decEq j x) h
  -- Step 5: conclude by cases on Q(P_x)
  set P_x := fun j => decide (j = x)
  have hatom_le : ∀ S : m.interpTy Ty.ett, S P_x = true → atom_x ≤ S := by
    intro S hS R
    cases hR : atom_x R with
    | false => exact Bool.false_le _
    | true =>
      have : R = P_x := hatom_point R hR
      rw [this]; exact le_of_eq hS.symm
  cases hQPx : Q P_x with
  | false =>
    have hQc : Qᶜ P_x = true := by
      change (Q P_x)ᶜ = true; rw [hQPx]; rfl
    have hfQc : f Qᶜ x = true := by
      have h := (hatom_le Qᶜ hQc : atom_x ≤ Qᶜ)
      have h2 := OrderHomClass.mono f h x
      rw [hf_atom_true] at h2
      exact top_le_iff.mp h2
    have hfQc2 : (f Q x)ᶜ = true := by
      rw [← Pi.compl_apply, ← map_compl' f]; exact hfQc
    cases hv : f Q x with
    | false => rfl
    | true => rw [hv] at hfQc2; exact Bool.noConfusion hfQc2
  | true =>
    have h := OrderHomClass.mono f (hatom_le Q hQPx) x
    rw [hf_atom_true] at h
    exact top_le_iff.mp h

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

/-- NOM: Nominalization (@cite{partee-1987} Figure 1, @cite{chierchia-1984}).
    Maps a property to its individual correlate: `⟨e,t⟩ → e` (partial).

    In the finite extensional setting, NOM = iota (returns the unique
    satisfier of P, if singleton). The intensional generalization is
    `Semantics.Lexical.Noun.Kind.Chierchia1998.down` (Chierchia's ∩). -/
def NOM (domain : List m.Entity) (P : m.interpTy Ty.et) : Option (m.interpTy .e) :=
  iota domain P

/-- Existential closure: `A(P) = λQ. ∃x. P(x) ∧ Q(x)` -/
def A (domain : List m.Entity) (P : m.interpTy Ty.et) : m.interpTy Ty.ett :=
  fun Q => domain.any (fun x => P x && Q x)

/-- THE: Presuppositional type-shifter for definites (@cite{partee-1987} Figure 1).
    `THE(P) = lift(iota(P))` when `iota(P)` is defined (P has a unique satisfier).

    Maps `⟨e,t⟩ → ⟨⟨e,t⟩,t⟩` (partial). Unlike `A` (which is total), `THE`
    presupposes existence and uniqueness. Connects to the semantics of "the"
    in `Semantics.Lexical.Determiner.Definite`. -/
def THE (domain : List m.Entity) (P : m.interpTy Ty.et) : Option (m.interpTy Ty.ett) :=
  (iota domain P).map lift

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

/-- `THE ∘ ident = some ∘ lift` on the domain.
    When `ident(j)` has a unique satisfier (always, given Nodup),
    THE shifts it to the corresponding principal ultrafilter. -/
theorem THE_ident (domain : List m.Entity) (j : m.interpTy .e)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    THE domain (ident j) = some (lift j) := by
  simp only [THE, iota_ident domain j hmem hnd, Option.map]

end PartialShifts

/-- `lift = Conjunction.typeRaise` -/
theorem lift_eq_typeRaise {m : Model} (j : m.interpTy .e) :
    lift j = typeRaise j := rfl

/-- Coherence of the three readings of "the king" (@cite{partee-1987} §3.2).
    When `iota` succeeds, the `e`, `⟨e,t⟩`, and `⟨⟨e,t⟩,t⟩` readings are
    related by `BE(lift(j)) = ident(j)` (Figure 2 commutativity). -/
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

/-- **`BE ∘ A = id` on properties** (@cite{partee-1987} §3.3).

    For any property `P`, `BE(A(P)) = P`. This makes `A` a right inverse
    of `BE`: existential closure followed by predicative content recovers
    the original property.

    This is the key result establishing `A` as a "natural" type-shifting
    functor — it is an inverse of `BE`, and Partee argues it (together with
    `some`) is the most natural DET-type functor.

    Proof: `BE(A(P))(x) = A(P)(λy. y=x) = ∃z∈dom. P(z) ∧ (z=x) = P(x)`.
    The `decide(z=x)` selects exactly `z = x`, collapsing the existential. -/
theorem BE_A_id (domain : List m.Entity) (P : m.interpTy Ty.et)
    (hcomplete : ∀ x : m.Entity, x ∈ domain) :
    BE (A domain P) = P := by
  funext x; simp only [BE, A]
  -- Goal: domain.any (fun z => P z && decide(z=x)) = P x
  -- Reduce to any_decide_eq_apply by swapping conjunction and equality direction
  have h := any_decide_eq_apply domain x (hcomplete x) P
  rw [← h]; congr 1; funext z
  rw [Bool.and_comm]
  congr 1
  cases m.decEq z x with
  | isTrue hz => cases m.decEq x z with
    | isTrue _ => rfl
    | isFalse h' => exact absurd hz.symm h'
  | isFalse hz => cases m.decEq x z with
    | isTrue h' => exact absurd h'.symm hz
    | isFalse _ => rfl

/-- For non-principal GQs, the round-trip can differ.
    Example: `⟦every⟧(P)(Q) = ∀x[P(x) → Q(x)]`, but
    `A(BE(⟦every⟧(P)))(Q) = ∃x[P(x) ∧ Q(x)]` — existential, not universal.
    Verified on the toy model. -/
private def toyDomain₁ : List ToyEntity := [.john, .mary, .pizza]
private def toyEvery : toyModel.interpTy Ty.ett := fun P => toyDomain₁.all P

/-- For non-principal GQs, the round-trip changes truth conditions.
    `every(⊤) = true` but `A(BE(every))(⊤) = false` — the round-trip
    collapses universal quantification to `⊥` on multi-element domains.
    (`BE(every)` asks "which entity equals all entities?" — none do.) -/
theorem roundtrip_changes_nonprincipal :
    toyEvery (fun _ => true) = true ∧
    A toyDomain₁ (BE toyEvery) (fun _ => true) = false :=
  ⟨rfl, rfl⟩

section ToyExamples

open Semantics.Montague.ToyLexicon (john_sem)

private def toyDomain₂ : List ToyEntity := [.john, .mary, .pizza, .book]

example : lift (m := toyModel) john_sem Semantics.Montague.ToyLexicon.sleeps_sem = true := rfl
example : BE (m := toyModel) (lift john_sem) = ident john_sem :=
  BE_lift_eq_ident john_sem
example : iota (m := toyModel) toyDomain₂ (ident john_sem) = some john_sem := rfl
example : lower (m := toyModel) toyDomain₂ (lift john_sem) = some john_sem := rfl

end ToyExamples

-- ============================================================================
-- The Type-Shifting Triangle (@cite{partee-1987} Figure 3)
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
theorem A_ident_eq_lift (domain : List m.Entity) (j : m.interpTy .e)
    (hj : j ∈ domain) :
    A domain (ident j) = lift j := by
  funext P; simp only [A, lift, ident]
  exact any_decide_eq_apply domain j hj P

/-- Full cycle e →lift ⟨⟨e,t⟩,t⟩ →BE ⟨e,t⟩ →A ⟨⟨e,t⟩,t⟩ = lift.

    Going around the triangle through GQ-space returns to the same GQ. -/
theorem A_BE_lift (domain : List m.Entity) (j : m.interpTy .e)
    (hj : j ∈ domain) :
    A domain (BE (lift j)) = lift j := by
  rw [BE_lift_eq_ident]; exact A_ident_eq_lift domain j hj

/-- Full cycle e →ident ⟨e,t⟩ →A ⟨⟨e,t⟩,t⟩ →BE ⟨e,t⟩ = ident.

    Going around the triangle through predicate-space returns to
    the same predicate. -/
theorem BE_A_ident (domain : List m.Entity) (j : m.interpTy .e)
    (hcomplete : ∀ x : m.Entity, x ∈ domain) :
    BE (A domain (ident j)) = ident j :=
  BE_A_id domain (ident j) hcomplete

/-- Partial path e →lift ⟨⟨e,t⟩,t⟩ →BE ⟨e,t⟩ →iota e = some.

    The indirect route through GQ-space recovers the entity. -/
theorem iota_BE_lift (domain : List m.Entity) (j : m.interpTy .e)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    iota domain (BE (lift j)) = some j := by
  rw [BE_lift_eq_ident]; exact iota_ident domain j hmem hnd

/-- Partial path e →ident ⟨e,t⟩ →A ⟨⟨e,t⟩,t⟩ →lower e = some.

    The indirect route through predicate-space recovers the entity. -/
theorem lower_A_ident (domain : List m.Entity) (j : m.interpTy .e)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    lower domain (A domain (ident j)) = some j := by
  rw [A_ident_eq_lift domain j hmem]; exact lower_lift domain j hmem hnd

/-- THE respects the triangle: `THE ∘ BE ∘ lift = some ∘ lift`.

    Recovering the definite description from a type-raised proper name
    via BE, then THE, yields the original type-raised individual. -/
theorem THE_BE_lift (domain : List m.Entity) (j : m.interpTy .e)
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
theorem BE_leftInverse_A (domain : List m.Entity)
    (hcomplete : ∀ x : m.Entity, x ∈ domain) :
    Function.LeftInverse BE (A domain) :=
  fun P => BE_A_id domain P hcomplete

/-- `BE` is surjective: every predicate is the predicative content of some GQ.
    Derived from `Function.LeftInverse.surjective`. -/
theorem BE_surjective (domain : List m.Entity)
    (hcomplete : ∀ x : m.Entity, x ∈ domain) :
    Function.Surjective (@BE m) :=
  (BE_leftInverse_A domain hcomplete).surjective

/-- `A` is injective: distinct predicates yield distinct GQs under
    existential closure. Linguistically: different common nouns mean
    different things as indefinites.
    Derived from `Function.LeftInverse.injective`. -/
theorem A_injective (domain : List m.Entity)
    (hcomplete : ∀ x : m.Entity, x ∈ domain) :
    Function.Injective (A domain) :=
  (BE_leftInverse_A domain hcomplete).injective

end TypeShiftingTriangle

-- ============================================================================
-- Galois Coinsertion on Upward-Closed GQs
-- ============================================================================

/-! ## The A/BE Adjunction on Monotone GQs

@cite{barwise-cooper-1981} observed that natural language determiners
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

-- Bridge instance: Ty.et is a `def` for (.e ⇒ .t), so interpTy (.e ⇒ .t)
-- doesn't match interpTy Ty.et for type class synthesis.
private instance (m : Model) : BooleanAlgebra (m.interpTy (.e ⇒ .t)) :=
  show BooleanAlgebra (m.Entity → Bool) from inferInstance

/-- Monotonicity of `List.any` with respect to pointwise `≤`. -/
private lemma list_any_mono {α : Type*} {domain : List α} {f g : α → Bool}
    (h : ∀ x, f x ≤ g x) : domain.any f ≤ domain.any g := by
  induction domain with
  | nil => exact le_refl _
  | cons a tl ih => simp only [List.any_cons]; exact sup_le_sup (h a) ih

/-- Upward-closed (monotone) generalized quantifiers — the
    @cite{barwise-cooper-1981} constraint on natural language determiners.

    `Q` is upward-closed when `Q(P)` and `P ≤ P'` imply `Q(P')`.
    Equivalently, `Monotone Q` in the pointwise order on `⟨e,t⟩`. -/
def UpwardGQ (m : Model) := { Q : m.interpTy Ty.ett // Monotone Q }

instance : PartialOrder (UpwardGQ m) := Subtype.partialOrder _

/-- `A(P)` is always upward-closed: if ∃x∈dom with P(x) ∧ R(x),
    and R ≤ R', then ∃x∈dom with P(x) ∧ R'(x). -/
theorem A_monotone_gq (domain : List m.Entity) (P : m.interpTy Ty.et) :
    Monotone (A domain P) := by
  intro R R' hRR'
  show domain.any (fun x => P x && R x) ≤ domain.any (fun x => P x && R' x)
  exact list_any_mono (fun x => inf_le_inf_left (P x) (hRR' x))

/-- Lift `A` to the `UpwardGQ` subtype. -/
def A_up (domain : List m.Entity) (P : m.interpTy Ty.et) : UpwardGQ m :=
  ⟨A domain P, A_monotone_gq domain P⟩

/-- Project `BE` from the `UpwardGQ` subtype. -/
def BE_up (Q : UpwardGQ m) : m.interpTy Ty.et := BE Q.val

/-- `A` is monotone as a map from predicates to GQs. -/
theorem A_up_mono (domain : List m.Entity) : Monotone (A_up domain (m := m)) := by
  intro P P' hPP'; show A domain P ≤ A domain P'; intro R
  exact list_any_mono (fun x => inf_le_inf_right (R x) (hPP' x))

/-- `BE` is monotone on `UpwardGQ`. -/
theorem BE_up_mono : Monotone (BE_up (m := m)) := by
  intro Q Q' hQQ'; show BE Q.val ≤ BE Q'.val; intro x
  exact hQQ' (fun y => @decide (y = x) (m.decEq y x))

/-- Singleton predicate `{x}` is below any `R` with `R(x) = true`. -/
private lemma singleton_le_of_mem {x : m.Entity} {R : m.interpTy Ty.et}
    (hRx : R x = true) :
    (fun y => @decide (y = x) (m.decEq y x)) ≤ R := by
  intro y
  show @decide (y = x) (m.decEq y x) ≤ R y
  by_cases h : y = x
  · subst h; simp [hRx]
  · have : @decide (y = x) (m.decEq y x) = false := by simp [h]
    rw [this]; exact Bool.false_le _

/-- **Key inequality**: `A(BE(Q)) ≤ Q` for upward-closed Q.

    `A(BE(Q))(R) = ∃x∈dom. Q({x}) ∧ R(x)`. When `R(x)` holds,
    `{x} ≤ R` in the pointwise order. By monotonicity of `Q`,
    `Q({x}) ≤ Q(R)`, establishing the inequality.

    This is precisely the condition that fails for non-monotone Q
    (e.g., `Q = λR. ¬R(a)` where `Q({a}) = false` but `Q(∅) = true`). -/
theorem A_BE_le_of_mono (domain : List m.Entity) (Q : UpwardGQ m) :
    A_up domain (BE_up Q) ≤ Q := by
  show A domain (BE Q.val) ≤ Q.val
  intro R; simp only [A, BE]
  cases h : domain.any (fun x =>
    Q.val (fun y => @decide (y = x) (m.decEq y x)) && R x)
  · exact Bool.false_le _
  · rw [List.any_eq_true] at h
    obtain ⟨x, _, hx⟩ := h
    have hQx : Q.val (fun y => @decide (y = x) (m.decEq y x)) = true := by
      revert hx; cases Q.val (fun y => @decide (y = x) (m.decEq y x)) <;> simp
    have hRx : R x = true := by revert hx; cases R x <;> simp
    exact le_trans (le_of_eq hQx.symm) (Q.property (singleton_le_of_mem hRx))

/-- **Galois coinsertion**: `A` (existential closure) and `BE` (predicative
    content) form a `GaloisCoinsertion` on the sublattice of upward-closed GQs.

    This is the order-theoretic content of Partee's type-shifting triangle:
    - `BE ∘ A = id` on predicates (the retraction)
    - `A(BE(Q)) ≤ Q` for monotone Q (the counit inequality)

    Linguistically: @cite{barwise-cooper-1981}'s constraint that natural
    language determiners denote monotone GQs is **exactly** the condition
    under which the A/BE pair forms an adjunction. -/
def galoisCoinsertion (domain : List m.Entity)
    (hcomplete : ∀ x : m.Entity, x ∈ domain) :
    GaloisCoinsertion (A_up domain (m := m)) BE_up :=
  GaloisCoinsertion.monotoneIntro
    BE_up_mono
    (A_up_mono domain)
    (A_BE_le_of_mono domain)
    (fun P => BE_A_id domain P hcomplete)

/-- The Galois connection: `A(P) ≤ Q ↔ P ≤ BE(Q)` for monotone Q. -/
theorem gc_A_BE (domain : List m.Entity)
    (hcomplete : ∀ x : m.Entity, x ∈ domain) :
    GaloisConnection (A_up domain (m := m)) BE_up :=
  (galoisCoinsertion domain hcomplete).gc

end GaloisStructure

-- ============================================================================
-- Numeral type-shifters (@cite{snyder-2026})
-- ============================================================================

section NumeralShifts

/-- CARD: number → cardinality predicate (@cite{snyder-2026}, (6a)).
    CARD = λn.λx. μ(x) = n. Turns a number into a predicate
    on entities that have exactly n atomic parts. -/
def CARD (μ : m.interpTy .e → Nat) (n : Nat) : m.interpTy Ty.et :=
  fun x => decide (μ x = n)

/-- PM: Predicate Modification (@cite{heim-kratzer-1998}, (7a)).
    PM = λP.λQ.λx. P(x) ∧ Q(x). Intersective modifier. -/
def PM (P Q : m.interpTy Ty.et) : m.interpTy Ty.et :=
  fun x => P x && Q x

end NumeralShifts

/-- `NOM(pred(j)) = some j`: nominalizing the predicativization of an entity
    returns that entity. The extensional counterpart of Chierchia's `∩(∪k) = k`
    (`Semantics.Lexical.Noun.Kind.Chierchia1998.down_up_id`). -/
theorem NOM_pred (domain : List m.Entity) (j : m.interpTy .e)
    (hmem : j ∈ domain) (hnd : domain.Nodup) :
    NOM domain (pred j) = some j :=
  iota_ident domain j hmem hnd

end Semantics.Composition.TypeShifting
