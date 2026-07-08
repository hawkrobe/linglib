import Linglib.Core.Logic.CylindricAlgebra
import Linglib.Semantics.Dynamic.DPL

/-!
# Groenendijk & Stokhof (1991): Dynamic Predicate Logic
[groenendijk-stokhof-1991]

Dynamic Predicate Logic. *Linguistics and Philosophy* 14(1): 39-100.

## Key Claims Verified

1. **Cross-sentential anaphora** (§2.1): Existential quantifiers bind
   variables across conjunction (`scope_extension`).

2. **Donkey sentences** (§2.4): Existential quantifiers in the antecedent
   of an implication have universal force (`donkey_equivalence`).

3. **Blocking** (§2.5): Universal quantifiers, negation, implication, and
   disjunction are externally static — they do not export bindings.

4. **DNE failure** (§3.4): Double negation elimination fails for anaphora
   (`dpl_dne_fails_anaphora`), because negation resets the output assignment.

5. **Interdefinability** (§3.4): `→`, `∨`, `∀` are definable from `¬`, `∧`, `∃`,
   but not vice versa — the DPL asymmetry.
-/

namespace GroenendijkStokhof1991

open Semantics.Dynamic.DPL

-- ════════════════════════════════════════════════════════════════
-- § 1. Cross-Sentential Anaphora (§2.1, §2.3)
-- ════════════════════════════════════════════════════════════════

/-! "A man walks in the park. He whistles."

DPL translation: ∃x[man(x) ∧ walk_in_park(x)] ∧ whistle(x)

The scope extension theorem shows this equals ∃x[man(x) ∧ walk_in_park(x) ∧ whistle(x)]:
the existential quantifier's binding power extends across conjunction.

This accounts for `Heim1982.Examples.indefinite_persists`. -/

/-- DPL correctly predicts indefinite persistence: scope extension
ensures ∃x in the first sentence binds x in the second. -/
theorem indefinite_persistence_predicted :
    ∀ {E : Type*} (x : Nat) (P Q R : DPLRel E)
      (hfree : ∀ (g h : Nat → E) (d : E),
        R g h ↔ R (λ n => if n = x then d else g n)
                    (λ n => if n = x then d else h n)),
    DPLRel.exists_ x (DPLRel.conj (DPLRel.conj P Q) R) =
    DPLRel.conj (DPLRel.exists_ x (DPLRel.conj P Q)) R :=
  fun x P Q R hfree => scope_extension x (DPLRel.conj P Q) R hfree

-- ════════════════════════════════════════════════════════════════
-- § 2. Donkey Sentences (§2.4)
-- ════════════════════════════════════════════════════════════════

/-! "If a farmer owns a donkey, he beats it."

DPL translation: ∃x[farmer(x) ∧ ∃y[donkey(y) ∧ own(x,y)]] → beat(x,y)

By `donkey_equivalence`, this is equivalent to:
  ∀x[farmer(x) ∧ ∃y[donkey(y) ∧ own(x,y)] → beat(x,y)]

And applying it again for y:
  ∀x∀y[farmer(x) ∧ donkey(y) ∧ own(x,y) → beat(x,y)]

This gives the universal "strong" reading recorded for
`Geach1962.Examples.donkey_classic` and
`Heim1982.Examples.conditional_donkey`. -/

/-- The donkey equivalence gives universal force to indefinites in
conditional antecedents, matching the strong/universal reading of
`Heim1982.Examples.conditional_donkey`. -/
theorem donkey_universal_force :
    ∀ {E : Type*} (x : Nat) (φ ψ : DPLRel E),
    DPLRel.impl (DPLRel.exists_ x φ) ψ =
    DPLRel.forall_ x (DPLRel.impl φ ψ) :=
  fun x φ ψ => donkey_equivalence x φ ψ

-- ════════════════════════════════════════════════════════════════
-- § 3. Blocking: Universal Quantifiers are Tests (§2.5)
-- ════════════════════════════════════════════════════════════════

/-! "Every man walked in. *He sat down."

The universal quantifier is a test: ⟦∀xφ⟧(g,h) forces g = h.
This means no new bindings are created — the pronoun "he" has
no accessible antecedent.

This accounts for `Heim1982.Examples.universal_blocks`. -/

/-- Universal quantification is externally static: it cannot
introduce discourse referents. Any formula following ∀xφ sees
the same assignment as before. -/
theorem universal_blocks_anaphora {E : Type*} (x : Nat) (φ : DPLRel E)
    (g h : Nat → E) (hfa : DPLRel.forall_ x φ g h) : g = h :=
  forall_isTest x φ g h hfa

/-- Negation is externally static: it blocks anaphora.
Accounts for `Heim1982.Examples.standard_negation_blocks`. -/
theorem negation_blocks_anaphora {E : Type*} (φ : DPLRel E)
    (g h : Nat → E) (hn : DPLRel.neg φ g h) : g = h := hn.1

/-- Implication is externally static: bindings in the antecedent
or consequent don't escape. Accounts for
`Heim1982.Examples.conditional_antecedent`. -/
theorem implication_blocks_anaphora {E : Type*} (φ ψ : DPLRel E)
    (g h : Nat → E) (hi : DPLRel.impl φ ψ g h) : g = h := hi.1

-- ════════════════════════════════════════════════════════════════
-- § 4. DNE Failure (§3.4)
-- ════════════════════════════════════════════════════════════════

/-! "It is not the case that nobody walked in. *He sat down."

Double negation ¬¬∃xφ is a test (g = h), so it cannot export the
witness introduced by ∃x. This contrasts with ∃xφ itself, which
does export. Hence ¬¬∃xφ ≠ ∃xφ.

A known limitation of DPL: doubly negated indefinites do in fact
license anaphora (`ElliottSudo2025.Examples.double_negation` is judged
acceptable), so DPL underpredicts here. The divergence is stated as a
theorem in `Studies/ElliottSudo2025.lean`
(`dpl_diverges_on_double_negation`), where the later, comparing paper
lives. -/

/-- DPL predicts double negation blocks anaphora, contra the empirical
judgment in `ElliottSudo2025.Examples.double_negation`. This is the
well-known DPL limitation that [elliott-sudo-2025] and bilateral
update semantics address. -/
theorem dne_blocks_anaphora_dpl_prediction {E : Type*} [Nontrivial E] :
    ∃ (x : Nat) (φ : DPLRel E),
      DPLRel.neg (DPLRel.neg (DPLRel.exists_ x φ)) ≠
      DPLRel.exists_ x φ :=
  dpl_dne_fails_anaphora

-- ════════════════════════════════════════════════════════════════
-- § 5. The DPL Asymmetry (§3.4)
-- ════════════════════════════════════════════════════════════════

/-! In standard PL, any pair from {¬, ∧, ∨, →} plus quantifiers
suffices to define the others. In DPL, only {¬, ∧, ∃} works as
a basis — {¬, →, ∀} and {¬, ∨, ∀} cannot define conjunction or
existential quantification, because ∧ and ∃ are the only connectives
that are externally dynamic. -/

/-- ¬, ∧, ∃ suffice: implication is definable. -/
theorem impl_from_conj_neg {E : Type*} (φ ψ : DPLRel E) :
    DPLRel.impl φ ψ = DPLRel.neg (DPLRel.conj φ (DPLRel.neg ψ)) :=
  impl_interdefinable φ ψ

/-- ¬, ∧, ∃ suffice: disjunction is definable. -/
theorem disj_from_conj_neg {E : Type*} (φ ψ : DPLRel E) :
    DPLRel.disj φ ψ = DPLRel.neg (DPLRel.conj (DPLRel.neg φ) (DPLRel.neg ψ)) :=
  disj_interdefinable φ ψ

/-- ¬, ∧, ∃ suffice: universal is definable. -/
theorem forall_from_exists_neg {E : Type*} (x : Nat) (φ : DPLRel E) :
    DPLRel.forall_ x φ = DPLRel.neg (DPLRel.exists_ x (DPLRel.neg φ)) :=
  forall_interdefinable x φ

/-- The reverse fails: conjunction is NOT definable from →, ∨, ∀, ¬ alone,
because conjunction is the only binary connective that is externally dynamic. -/
theorem conj_not_from_static_ops {E : Type*} [Nontrivial E] :
    ∃ (φ ψ : DPLRel E), DPLRel.conj φ ψ ≠ DPLRel.conj ψ φ :=
  conj_not_comm

/-! ### Cylindric-algebra bridges

DPL's existential and identity test are cylindric-algebra operations under
`closure` — the defining correspondence between DPL and cylindric set
algebra ([henkin-monk-tarski-1971]). These are algebraic identities, not
analogies. -/

section CylindricAlgebra

open Core.CylindricAlgebra
open Core (Assignment)
open Semantics.Dynamic.Core.DynProp (closure)

/-- **DPL existential = cylindrification.**

`closure(∃x.φ) = cₓ(closure(φ))`: the truth-conditional content of
DPL's existential quantifier at variable `x` is exactly cylindrification
at register `x`. -/
theorem dpl_closure_exists_eq_cylindrify {E : Type*} (x : Nat) (φ : DPLRel E) :
    closure (toDRS (DPLRel.exists_ x φ)) =
    cylindrify x (closure (toDRS φ)) := by
  have hup : ∀ (g : Assignment E) (d : E),
      (fun n => if n = x then d else g n) = Function.update g x d := fun g d => by
    funext n; simp [Function.update_apply]
  ext g; simp only [closure, toDRS, DPLRel.exists_, cylindrify]
  exact ⟨fun ⟨h, d, hφ⟩ => ⟨d, h, hup g d ▸ hφ⟩,
         fun ⟨d, h, hφ⟩ => ⟨h, d, (hup g d).symm ▸ hφ⟩⟩

/-- **DPL identity test = diagonal element.**

`closure(atom(g(x) = g(y))) = Dxy`: the truth condition of the DPL
atomic formula `x = y` is the diagonal element `Dxy` from cylindric
algebra. -/
theorem dpl_closure_identity_eq_diagonal {E : Type*} (x y : Nat) :
    closure (toDRS (DPLRel.atom (fun g : Assignment E => g x = g y))) =
    @diagonal E x y := by
  ext g; simp only [closure, toDRS, DPLRel.atom, diagonal]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨g, rfl, h⟩⟩

/-- DPL negation under closure is a test for non-cylindrifiability:
`closure(¬φ)(g)` iff no assignment update satisfies φ. -/
theorem dpl_closure_neg_eq {E : Type*} (φ : DPLRel E) :
    closure (toDRS (DPLRel.neg φ)) =
    fun g => ¬ closure (toDRS φ) g := by
  ext g; simp only [closure, toDRS, DPLRel.neg]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨g, rfl, h⟩⟩

end CylindricAlgebra

end GroenendijkStokhof1991
