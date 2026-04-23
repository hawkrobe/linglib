import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! # Alonso-Ovalle & Moghiseh 2025: Generic split exhaustification
@cite{alonso-ovalle-moghiseh-2025}

General theorems grounding the split exhaustification analysis of
Existential Free Choice Items (EFCIs). These results hold for arbitrary
domains — not specific world types — capturing the logical core of
the analysis at full generality.

The companion file `AlonsoOvalleMoghiseh2025.lean` (same directory)
verifies each result computationally via `native_decide` on 2-book worlds;
this file proves them structurally, without `native_decide`.

## Architecture

Split exhaustification factors the exhaustivity operator into two
independent components:

- **O_σ** (scalar): exhaustifies w.r.t. numeral-scale alternatives
  (e.g., "at least 2" for "one"), clause-bounded below modals
- **O_EXH-D** (domain): exhaustifies w.r.t. pre-exhaustified subdomain
  alternatives, scoping above modals

The split is necessary because single-operator exhaustification with all
alternatives yields ⊥ (`exhAll`) or vacuity (`exhB`) for 2-element
domains (`root_full_exh_contradiction`).

## Results

1. **Scalar uniqueness**: O_σ yields "exactly one" (`scalar_exh_uniqueness`)
2. **Exclusive-alt negation**: O_EXH-D yields "at least two"
   (`neg_all_exclusive_alts`)
3. **Two-element FC**: for |D| = 2, "at least two" = "all"
   (`fc_two_element`)
4. **Root contradiction**: full exh on |D| = 2 → ⊥
   (`root_full_exh_contradiction`)
5. **DE weakening**: antecedent strengthening weakens conditionals
   (`strict_antecedent_weakening`)
6. **DE domain vacuousness**: domain alts entailed in DE
   (`de_domain_alt_entailed`)
7. **Split necessity — scalar preserved**: domain-exh never negates the
   scalar (`exclusive_false_of_universal`,
   `domain_exh_result_compatible_with_scalar`)
8. **Split necessity — |D|≥3 contrast**: full exh consistent for larger
   domains (`full_exh_consistent_three`)

### Modal Level (§6)

All root-level results lift to arbitrary Kripke frames via instantiation
at `Q d := ∃ w, Acc w ∧ P d w`. The modal theorems add:

9. **◇ preserves existence** (`diamond_preserves_exist`,
   `diamond_uniqueness_implies_exist`)
10. **Modal FC** (`modal_split_exh_fc`): domain-exh above ◇ gives
    ∀d, ◇(P d) for |D|=2
11. **Full composition** (`modal_split_exh_full`): FC + embedded uniqueness
12. **Below-only too weak** (`modal_uniqueness_not_fc`): countermodel
13. **Full exh too strong** (`modal_full_exh_contradiction`): ⊥ for |D|=2
14. **Split preserves scalar** (`modal_split_compatible_with_joint`,
    `modal_split_full_compatible_with_joint`): FC consistent with ◇(∀d P d)
15. **General plurality** (`modal_domain_exh_plurality`): ∃≥2 for any D
-/

namespace AlonsoOvalleMoghiseh2025.Generic


-- ============================================================
-- § 1. Scalar Exhaustification → Uniqueness
-- ============================================================

/-!
## Scalar Uniqueness

O_σ exhaustifies "at least one" w.r.t. the scalar alternative "at least
two," yielding "exactly one." This is yek-i's root reading: the partial
exhaustification rescue mechanism prunes domain alternatives and applies
only O_σ, producing uniqueness without modal insertion.
-/

/-- **Scalar uniqueness**: "at least one and not at least two" is
equivalent to "exactly one."

This is the semantic content of O_σ: with a single scalar alternative
(the next numeral on the Horn scale), innocent exclusion trivially
returns that alternative (singleton MCE), and its negation gives
uniqueness. General over any domain D — no finiteness needed. -/
theorem scalar_exh_uniqueness {D : Type*} (P : D → Prop) :
    ((∃ d, P d) ∧ ¬∃ d₁ d₂, d₁ ≠ d₂ ∧ P d₁ ∧ P d₂) ↔
    ∃ d, P d ∧ ∀ e, P e → e = d := by
  constructor
  · rintro ⟨⟨d, hd⟩, hNotTwo⟩
    exact ⟨d, hd, fun e he => by_contra fun hne =>
      hNotTwo ⟨e, d, hne, he, hd⟩⟩
  · rintro ⟨d, hd, huniq⟩
    exact ⟨⟨d, hd⟩, fun ⟨d₁, d₂, hne, h1, h2⟩ =>
      hne ((huniq d₁ h1).trans (huniq d₂ h2).symm)⟩


-- ============================================================
-- § 2. Domain Exhaustification → Free Choice
-- ============================================================

/-!
## Free Choice from Exclusive-Alt Negation

O_EXH-D negates pre-exhaustified domain alternatives. Each says "d is
the EXCLUSIVE satisfier" (P d ∧ ∀e≠d, ¬P e). Negating all of these,
combined with existence, yields a cardinality lower bound:

- **General**: at least 2 satisfy P
- **|D| = 2**: both satisfy P (full free choice)

The general-to-specific factoring explains why FC emerges specifically
from the 2-element structure: "at least 2 out of 2" = "all."
-/

/-- **Exclusive-alt negation → plurality**: if at least one element
satisfies P, and no element is the exclusive satisfier, then at least
two distinct elements satisfy P.

This is the content of O_EXH-D: each pre-exhaustified domain alternative
is innocently excludable (they form a single MCE since they can all be
simultaneously negated), and negating all of them forces multiple
satisfiers. General over any domain D. -/
theorem neg_all_exclusive_alts {D : Type*} (P : D → Prop)
    (hExist : ∃ d, P d)
    (hNegExcl : ∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e)) :
    ∃ d₁ d₂, d₁ ≠ d₂ ∧ P d₁ ∧ P d₂ := by
  obtain ⟨d, hd⟩ := hExist
  by_contra hNoTwo
  exact hNegExcl d ⟨hd, fun e hne hPe => hNoTwo ⟨e, d, hne, hPe, hd⟩⟩

/-- **Two-element free choice**: for a two-element domain, existence plus
negation of all exclusive alternatives forces every element to satisfy P.

This completes the FC derivation for yek-i under deontic modals:
O_EXH-D negates the two exclusive modal alternatives, and since |D| = 2,
"at least 2 satisfy ◇P" becomes "both satisfy ◇P" — free choice. -/
theorem fc_two_element (P : Fin 2 → Prop)
    (hExist : ∃ d, P d)
    (hNegExcl : ∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e)) :
    ∀ d, P d := by
  obtain ⟨d₁, d₂, hne, h1, h2⟩ := neg_all_exclusive_alts P hExist hNegExcl
  intro d; fin_cases d <;> fin_cases d₁ <;> fin_cases d₂ <;> simp_all


-- ============================================================
-- § 3. Root Contradiction
-- ============================================================

/-!
## Root Contradiction: Why Rescue Mechanisms Are Needed

For a 2-element domain, full exhaustification (negating both the scalar
alternative and both exclusive domain alternatives) is contradictory.
This motivates the EFCI rescue typology (Table 2):

- *vreun* (−,−): no rescue → ungrammatical in root
- *irgendein* (+,−): modal insertion → covert □ → epistemic ignorance
- *yek-i* (−,+): partial exhaustification → O_σ only → uniqueness
-/

/-- **Root contradiction**: asserting "at least one," negating "all"
(scalar), and negating both exclusive domain alternatives yields ⊥
for a two-element domain.

Proof: negating both exclusives gives FC (both hold), contradicting
"not all." This is a STRUCTURAL impossibility, not an artifact of
the specific world type used for computational verification. -/
theorem root_full_exh_contradiction (P : Fin 2 → Prop)
    (hExist : ∃ d, P d)
    (hNotAll : ¬∀ d, P d)
    (hNegExcl : ∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e)) :
    False :=
  hNotAll (fc_two_element P hExist hNegExcl)

/-- Uniqueness (from scalar-only exhaustification) is satisfiable:
unlike full exhaustification, O_σ alone yields a consistent result.
This witnesses that partial exhaustification is a genuine rescue. -/
theorem uniqueness_satisfiable :
    ∃ P : Fin 2 → Prop, ∃ d, P d ∧ ∀ e, P e → e = d :=
  ⟨(· = 0), 0, rfl, fun _ h => h⟩

/-- Uniqueness precludes universality: "exactly one" entails "not all"
for any domain with at least two elements. This shows O_σ's result is
strictly between the assertion and the full-exh contradiction. -/
theorem uniqueness_precludes_universality {D : Type*} {a b : D}
    (hab : a ≠ b) (P : D → Prop)
    (hUniq : ∃ d, P d ∧ ∀ e, P e → e = d) :
    ¬∀ d, P d := by
  obtain ⟨d, _, huniq⟩ := hUniq
  intro hall
  exact hab ((huniq a (hall a)).trans (huniq b (hall b)).symm)


-- ============================================================
-- § 4. DE Contexts: Maximize Strength & Domain Vacuousness
-- ============================================================

/-!
## DE Contexts: Plain Existential Force

Two independent mechanisms ensure EFCIs contribute plain existential
force in downward-entailing contexts:

1. **Maximize Strength blocks O_σ**: scalar exhaustification strengthens
   the conditional's antecedent, which WEAKENS the overall conditional.
   Since this loses information, Maximize Strength prevents it.

2. **O_EXH-D is vacuous**: the full-domain conditional entails each
   subdomain conditional (since P d → ∃x P x), so domain alternatives
   are weaker than the assertion and not in NW — nothing to exclude.
-/

/-- **Antecedent monotonicity**: strengthening a conditional's antecedent
weakens the conditional. If Q → P (Q is stronger), then (P → R) entails
(Q → R) (but not vice versa in general).

In EFCI terms: ∃!x P(x) → ∃x P(x), so (∃x → R) entails (∃!x → R).
Scalar exhaustification replaces ∃x with ∃!x in the antecedent,
weakening the matrix. Maximize Strength blocks this. -/
theorem antecedent_weakening {P Q R : Prop} (hQP : Q → P) :
    (P → R) → (Q → R) :=
  fun hPR hQ => hPR (hQP hQ)

/-- **Strict weakening witness**: when Q ⊂ P strictly (Q → P but
∃w with P w, ¬Q w, ¬R w), there is a world where the weaker conditional
P → R fails but the stronger conditional Q → R holds.

This witnesses the information loss: the world where P holds and Q doesn't
(e.g., "bought both books") makes (P → R) false but (Q → R) vacuously
true, demonstrating strict weakening. -/
theorem strict_antecedent_weakening {W : Type*} (P Q R : W → Prop)
    (hWitness : ∃ w, P w ∧ ¬Q w ∧ ¬R w) :
    ∃ w, ¬(P w → R w) ∧ (Q w → R w) := by
  obtain ⟨w, hPw, hNQw, hNRw⟩ := hWitness
  exact ⟨w, fun hPR => hNRw (hPR hPw), fun hQw => absurd hQw hNQw⟩

/-- **Domain alternatives entailed in DE**: the full-domain conditional
(∃x P(x)) → R entails each subdomain conditional P(d) → R, since
P d → ∃x P(x) for any d.

Consequence: domain alternatives are weakened by the DE operator (they
are entailed by the assertion), so they are not in NW(assertion) and
IE is empty — O_EXH-D contributes nothing. -/
theorem de_domain_alt_entailed {D : Type*} (P : D → Prop) (R : Prop) (d : D) :
    ((∃ x, P x) → R) → (P d → R) :=
  fun h hPd => h ⟨d, hPd⟩



-- ============================================================
-- § 5. Why Split Exhaustification Is Necessary
-- ============================================================

/-!
## Split Exhaustification Necessity

@cite{alonso-ovalle-moghiseh-2025} argue (§5, eqs. 143–146) that only split
exhaustification derives the correct FC + embedded uniqueness for EFCIs
under modals. Three alternative architectures — single operator below ◇,
single operator above ◇, two operators above+below — all produce wrong
results.

The structural core of the argument:

1. **Domain-exh preserves scalar compatibility** (`exclusive_false_of_universal`,
   `domain_exh_result_compatible_with_scalar`): when all elements satisfy P,
   every exclusive alternative is false. O_EXH-D's result never conflicts
   with the scalar (∀d P d) — the scalar "survives" domain-only
   exhaustification.

2. **Full exh contradicts for |D|=2** (`root_full_exh_contradiction`,
   `fc_two_element`): domain-exh on a 2-element domain forces universality,
   so adding scalar negation yields ⊥. Any operator targeting both
   alternative classes at the modal level produces the unwanted
   ¬◇(∀d P d).

3. **Full exh is consistent for |D|≥3** (`full_exh_consistent_three`):
   the 2-element contradiction is special — for larger domains, ∃≥2
   doesn't imply ∀d, so assertion + ¬scalar + ¬exclusives can all hold
   simultaneously.
-/

/-- **Exclusive alternatives false under universality**: if all elements
satisfy P, then no element is the exclusive satisfier.

Consequence for split exh: O_EXH-D's negations are entailed by ∀d P d,
so the scalar alternative cannot be innocently excluded by domain-only
exhaustification. A fortiori, the scalar is never negated by O_EXH-D.
General over any domain D with at least two elements. -/
theorem exclusive_false_of_universal {D : Type*} {a b : D}
    (hab : a ≠ b) (P : D → Prop) (hAll : ∀ d, P d) :
    ∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e) := by
  intro d ⟨_, hexcl⟩
  have : Nontrivial D := ⟨⟨a, b, hab⟩⟩
  obtain ⟨e, hne⟩ := exists_ne d
  exact hexcl e hne (hAll e)

/-- **Domain-exh result compatible with scalar**: there exists a model
satisfying all three conditions simultaneously — the assertion (∃d P d),
the domain-exh negations (∀d ¬exclusive(d)), AND the scalar (∀d P d).

This witnesses that domain-only exhaustification does not exclude the
scalar. Contrast with `root_full_exh_contradiction`: adding ¬(∀d P d)
makes this inconsistent for |D|=2. -/
theorem domain_exh_result_compatible_with_scalar {D : Type*} {a b : D}
    (hab : a ≠ b) :
    ∃ P : D → Prop,
      (∃ d, P d) ∧
      (∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e)) ∧
      (∀ d, P d) := by
  refine ⟨fun _ => True, ⟨a, trivial⟩, ?_, fun _ => trivial⟩
  exact exclusive_false_of_universal hab _ (fun _ => trivial)

/-- **Full exh consistent for 3-element domain**: unlike the 2-element
case (`root_full_exh_contradiction`), for |D|=3 we can simultaneously
have: (1) ∃d P d, (2) ¬∀d P d, and (3) ∀d ¬exclusive(d).

Witness: P = {0, 1}, ¬P 2. Two elements satisfy P (enough to block
all exclusives) but not all three do (¬∀d P d).

This shows the root contradiction is specific to 2-element domains.
For larger domains, full exhaustification is consistent (though it
still produces unwanted scalar negation at the modal level). -/
theorem full_exh_consistent_three :
    ∃ P : Fin 3 → Prop,
      (∃ d, P d) ∧
      ¬(∀ d, P d) ∧
      (∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e)) := by
  refine ⟨(· ≠ (2 : Fin 3)), ⟨0, by decide⟩, fun h => h 2 rfl, ?_⟩
  intro d ⟨hPd, hexcl⟩
  fin_cases d
  · exact hexcl 1 (by decide) (by decide)
  · exact hexcl 0 (by decide) (by decide)
  · exact hPd rfl


-- ============================================================
-- § 6. Modal Split Exhaustification
-- ============================================================

/-!
## Modal Split Exhaustification

All root-level results lift to arbitrary Kripke frames by instantiating
`P : D → Prop` with `fun d => ∃ w, Acc w ∧ Q d w` where `Acc : W → Prop`
is the accessibility predicate and `Q : D → W → Prop` is the base property.

Modal operators:
- **◇φ** ≡ `∃ w, Acc w ∧ φ w`
- **□φ** ≡ `∀ w, Acc w → φ w`

The split architecture: O_σ below ◇ yields uniqueness within each world;
O_EXH-D above ◇ targets modal alternatives ◇(Q d), yielding FC.
-/

/-- **◇ preserves existential**: if some accessible world satisfies
∃x, Q x, then ∃d, ◇(Q d). Bridges below-modal content to above-modal
exhaustification premises. -/
theorem diamond_preserves_exist {W D : Type*}
    (Acc : W → Prop) (Q : D → W → Prop)
    (h : ∃ w, Acc w ∧ ∃ d, Q d w) :
    ∃ d, ∃ w, Acc w ∧ Q d w := by
  obtain ⟨w, hw, d, hd⟩ := h
  exact ⟨d, w, hw, hd⟩

/-- **◇ preserves existence from uniqueness**: ◇(∃!d, Q d) entails
∃d, ◇(Q d). Uniqueness is stronger than existence, so this is a
corollary. -/
theorem diamond_uniqueness_implies_exist {W D : Type*}
    (Acc : W → Prop) (Q : D → W → Prop)
    (h : ∃ w, Acc w ∧ ∃ d, Q d w ∧ ∀ e, Q e w → e = d) :
    ∃ d, ∃ w, Acc w ∧ Q d w := by
  obtain ⟨w, hw, d, hd, _⟩ := h
  exact ⟨d, w, hw, hd⟩

/-- **Modal domain-exh gives plurality (general)**: for any domain D,
if ◇(∃x, Q x) and domain-exh negates all exclusive modal alternatives,
then at least two domain elements are possible.

This is `neg_all_exclusive_alts` composed through ◇. -/
theorem modal_domain_exh_plurality {W D : Type*}
    (Acc : W → Prop) (Q : D → W → Prop)
    (hExist : ∃ d, ∃ w, Acc w ∧ Q d w)
    (hNegExcl : ∀ d, ¬((∃ w, Acc w ∧ Q d w) ∧
                        ∀ e, e ≠ d → ¬∃ w, Acc w ∧ Q e w)) :
    ∃ d₁ d₂, d₁ ≠ d₂ ∧ (∃ w, Acc w ∧ Q d₁ w) ∧ (∃ w, Acc w ∧ Q d₂ w) :=
  neg_all_exclusive_alts (fun d => ∃ w, Acc w ∧ Q d w) hExist hNegExcl

/-- **Modal split exh gives FC (|D|=2)**: for a 2-element domain,
domain-exh above ◇ gives full free choice: every element is permitted.

Instantiates `fc_two_element` with `P d := ◇(Q d)`. -/
theorem modal_split_exh_fc {W : Type*}
    (Acc : W → Prop) (Q : Fin 2 → W → Prop)
    (hExist : ∃ d, ∃ w, Acc w ∧ Q d w)
    (hNegExcl : ∀ d, ¬((∃ w, Acc w ∧ Q d w) ∧
                        ∀ e, e ≠ d → ¬∃ w, Acc w ∧ Q e w)) :
    ∀ d, ∃ w, Acc w ∧ Q d w :=
  fc_two_element (fun d => ∃ w, Acc w ∧ Q d w) hExist hNegExcl

/-- **Full split exh composition**: O_σ below ◇ gives uniqueness;
domain-exh above ◇ gives FC. Together: FC + embedded uniqueness. -/
theorem modal_split_exh_full {W : Type*}
    (Acc : W → Prop) (Q : Fin 2 → W → Prop)
    (hUniq : ∃ w, Acc w ∧ ∃ d, Q d w ∧ ∀ e, Q e w → e = d)
    (hNegExcl : ∀ d, ¬((∃ w, Acc w ∧ Q d w) ∧
                        ∀ e, e ≠ d → ¬∃ w, Acc w ∧ Q e w)) :
    (∀ d, ∃ w, Acc w ∧ Q d w) ∧
    (∃ w, Acc w ∧ ∃ d, Q d w ∧ ∀ e, Q e w → e = d) :=
  ⟨modal_split_exh_fc Acc Q
    (diamond_uniqueness_implies_exist Acc Q hUniq) hNegExcl,
   hUniq⟩

/-- **◇(uniqueness) doesn't entail FC**: countermodel where only d=0
satisfies Q in the unique accessible world. Single operator below ◇
is insufficient. -/
theorem modal_uniqueness_not_fc :
    ∃ (W : Type) (Acc : W → Prop) (Q : Fin 2 → W → Prop),
      (∃ w, Acc w ∧ ∃ d, Q d w ∧ ∀ e, Q e w → e = d) ∧
      ¬(∀ d, ∃ w, Acc w ∧ Q d w) :=
  ⟨Unit, fun _ => True, fun d _ => d = 0,
   ⟨(), trivial, 0, rfl, fun _ h => h⟩,
   fun h => by obtain ⟨_, _, h1⟩ := h 1; exact absurd h1 (by decide)⟩

/-- **Full exh above ◇ contradicts FC (|D|=2)**: adding scalar
negation ¬(∀d, ◇(Q d)) to domain-exh yields ⊥.

Instantiates `root_full_exh_contradiction` through ◇. -/
theorem modal_full_exh_contradiction {W : Type*}
    (Acc : W → Prop) (Q : Fin 2 → W → Prop)
    (hExist : ∃ d, ∃ w, Acc w ∧ Q d w)
    (hNotAll : ¬∀ d, ∃ w, Acc w ∧ Q d w)
    (hNegExcl : ∀ d, ¬((∃ w, Acc w ∧ Q d w) ∧
                        ∀ e, e ≠ d → ¬∃ w, Acc w ∧ Q e w)) :
    False :=
  root_full_exh_contradiction (fun d => ∃ w, Acc w ∧ Q d w)
    hExist hNotAll hNegExcl

/-- **∀d ◇(Q d) negates all exclusives**: if every element is possible,
then no element is exclusively possible. Instantiates
`exclusive_false_of_universal` at the modal level. -/
theorem modal_exclusive_false_of_universal {W D : Type*} {a b : D}
    (hab : a ≠ b) (Acc : W → Prop) (Q : D → W → Prop)
    (hAll : ∀ d, ∃ w, Acc w ∧ Q d w) :
    ∀ d, ¬((∃ w, Acc w ∧ Q d w) ∧ ∀ e, e ≠ d → ¬∃ w, Acc w ∧ Q e w) :=
  exclusive_false_of_universal hab _ hAll

/-- **Split exh compatible with ◇(∀d Q d)**: domain-exh premises, FC,
and the modal scalar ◇(∀d Q d) hold simultaneously. The scalar is
never in O_EXH-D's target set. -/
theorem modal_split_compatible_with_joint :
    ∃ (W : Type) (Acc : W → Prop) (Q : Fin 2 → W → Prop),
      (∃ d, ∃ w, Acc w ∧ Q d w) ∧
      (∀ d, ¬((∃ w, Acc w ∧ Q d w) ∧ ∀ e, e ≠ d → ¬∃ w, Acc w ∧ Q e w)) ∧
      (∀ d, ∃ w, Acc w ∧ Q d w) ∧
      (∃ w, Acc w ∧ ∀ d, Q d w) := by
  refine ⟨Unit, fun _ => True, fun _ _ => True,
    ⟨0, (), trivial, trivial⟩, ?_, fun _ => ⟨(), trivial, trivial⟩,
    ⟨(), trivial, fun _ => trivial⟩⟩
  intro d ⟨_, hall⟩
  obtain ⟨e, hne⟩ := exists_ne d
  exact hall e hne ⟨(), trivial, trivial⟩

/-- **Full split exh with joint compatibility**: FC + embedded uniqueness
+ ◇(∀d Q d) all hold simultaneously.

Witness: 3-world model — w0 has only Q 0, w1 has only Q 1, w2 has both.
Uniqueness in singleton worlds, universality in the joint world, FC
because both elements have a witness world. -/
theorem modal_split_full_compatible_with_joint :
    ∃ (W : Type) (Acc : W → Prop) (Q : Fin 2 → W → Prop),
      (∃ w, Acc w ∧ ∃ d, Q d w ∧ ∀ e, Q e w → e = d) ∧
      (∀ d, ¬((∃ w, Acc w ∧ Q d w) ∧ ∀ e, e ≠ d → ¬∃ w, Acc w ∧ Q e w)) ∧
      (∀ d, ∃ w, Acc w ∧ Q d w) ∧
      (∃ w, Acc w ∧ ∀ d, Q d w) := by
  refine ⟨Fin 3, fun _ => True,
    fun d w => (d = 0 ∧ w ≠ 1) ∨ (d = 1 ∧ w ≠ 0),
    ?_, ?_, ?_, ?_⟩
  · exact ⟨0, trivial, 0, Or.inl ⟨rfl, by decide⟩,
      fun e he => by rcases he with ⟨rfl, _⟩ | ⟨rfl, h⟩ <;> [rfl; exact absurd rfl h]⟩
  · intro d ⟨_, hall⟩
    fin_cases d
    · exact hall 1 (by decide) ⟨1, trivial, Or.inr ⟨rfl, by decide⟩⟩
    · exact hall 0 (by decide) ⟨0, trivial, Or.inl ⟨rfl, by decide⟩⟩
  · intro d; fin_cases d
    · exact ⟨0, trivial, Or.inl ⟨rfl, by decide⟩⟩
    · exact ⟨1, trivial, Or.inr ⟨rfl, by decide⟩⟩
  · refine ⟨2, trivial, fun d => ?_⟩
    fin_cases d
    · exact Or.inl ⟨rfl, by decide⟩
    · exact Or.inr ⟨rfl, by decide⟩


end AlonsoOvalleMoghiseh2025.Generic
