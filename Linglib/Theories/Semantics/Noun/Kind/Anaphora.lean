import Linglib.Theories.Semantics.Noun.Kind.Chierchia1998
import Linglib.Theories.Semantics.Dynamic.DiscourseRef
import Linglib.Theories.Semantics.Dynamic.Connectives.Defs
import Linglib.Core.Assignment

/-!
# Kind Anaphora: Static-Dynamic Bridge
@cite{krifka-2026}

Bridges the static kind semantics in @cite{chierchia-1998} (∩, ⊔, `IsMass`,
`kindAnaphorMass`, `kindAnaphorCount`) with the dynamic concept discourse
referent types in `DiscourseRef` (`ConceptDRef`, `DRefVal`).

Both modules share `MassCount` from `Core.Lexical.Word`, which models the
morphosyntactic mass/count feature that determines kind-anaphor pronoun
selection (*it* for [MASS], *they* for [COUNT]).

## Core insight

@cite{krifka-2026} proposes that head nouns introduce **concept discourse
referents** — properties annotated with a [MASS]/[COUNT] feature. Kind anaphors
pick up these concept drefs and derive kind individuals via Chierchia's ∩
operator:

- *it* picks up [MASS] concepts: ⟦it⟧ = λP[MASS]. ∩P
- *they* picks up [COUNT] concepts: ⟦they⟧ = λP[COUNT]. ∩(⊔P)

Concept drefs **project past anaphoric islands** (negation, modals,
conditionals) because they are presupposed in the input assignment,
not existentially introduced. This is what licenses:

  *John doesn't own a dog. He is afraid of them.*

while blocking:

  *John doesn't own a dog. \*It is friendly.*

## Sections

1. Kind anaphor selection by mass/count feature
2. Concept dref projection past anaphoric islands
-/

namespace Semantics.Noun.Kind.Anaphora

open Semantics.Noun.Kind.Chierchia1998 (Kind Property IsMass
  kindAnaphorMass kindAnaphorCount kindAnaphorCount_mass)
open Semantics.Dynamic.Core (ConceptDRef DRefVal)

-- ════════════════════════════════════════════════════
-- § 1. Kind Anaphor Selection
-- ════════════════════════════════════════════════════

/-- Select the kind-anaphor operator based on the morphosyntactic mass/count feature.

    @cite{krifka-2026} (17a,b):
    - ⟦it⟧  = λP[MASS].  λi. ∩P(i)           → `kindAnaphorMass`
    - ⟦they⟧ = λP[COUNT]. λi. ∩(⊔P)(i)        → `kindAnaphorCount`

    The [MASS]/[COUNT] feature determines the pronoun form and whether
    plural closure (⊔) applies before nominalization (∩). -/
def selectKindAnaphor (World Atom : Type) (feature : MassCount)
    (P : Property World Atom) : Kind World Atom :=
  match feature with
  | .mass => kindAnaphorMass World Atom P
  | .count => kindAnaphorCount World Atom P

/-- For mass properties, both anaphor paths yield the same kind.

    @cite{krifka-2026} (16): ⊔⊔S = ⊔S for cumulative S (absorption rule).
    Since mass nouns are cumulative, plural closure is a no-op, so
    `kindAnaphorCount P = kindAnaphorMass P` when P is mass.

    This means the [MASS]/[COUNT] feature's only role is selecting
    pronoun morphology — the semantic content of the kind anaphor
    is identical for mass properties. -/
theorem selectKindAnaphor_mass_absorb {World Atom : Type}
    (P : Property World Atom) (hMass : IsMass World Atom P) :
    selectKindAnaphor World Atom .count P =
    selectKindAnaphor World Atom .mass P :=
  kindAnaphorCount_mass World Atom P hMass


-- ════════════════════════════════════════════════════
-- § 2. Concept DRef Projection past Anaphoric Islands
-- ════════════════════════════════════════════════════

section Projection

variable {W E : Type*}

/-- Heterogeneous assignment: maps indices to discourse referent values.

    Following @cite{krifka-2026} §4: assignments are partial functions
    from ℕ to a heterogeneous universe including entities, concepts
    (properties with mass/count features), and world-time indices. Partiality
    is modeled by `DRefVal.undef`. -/
abbrev HAssign (W E : Type*) := Nat → DRefVal W E

/-- Dynamic sentence meaning: relation between input and output assignments.

    @cite{krifka-2026} §4: meanings of type **aast** map input assignment g
    to output assignment h relative to a world-time index i. We omit the
    index parameter for the projection theorems since it is orthogonal
    to the island-escaping behavior. -/
def DSent (W E : Type*) := HAssign W E → HAssign W E → Prop

/-- DPL-style negation: test (output = input) plus denial of body.

    @cite{krifka-2026} (34): ⟦NEG⟧ = λp.λghi[g=h, ¬∃k[g≤k, p(gki)]]

    Negation is a *test*: it preserves the input assignment (g = h) and
    checks that no extension of g satisfies the body. This is why
    entity drefs introduced under negation are inaccessible — they
    exist only in the existentially bound extension k. -/
def dNeg (φ : DSent W E) : DSent W E :=
  λ g h => g = h ∧ ¬∃ k, φ g k

/-- Existential introduction of an entity dref at index n.

    Models the indexed determiner *a*₃ in @cite{krifka-2026} (40c,e):
    the determiner introduces a new entity dref (index 3) that falls
    under the concept property (index 2). -/
def entityIntro (n : Nat) (body : DSent W E) : DSent W E :=
  λ g h => ∃ e : E, body (λ m => if m = n then .entity e else g m) h

/-- Concept presupposition: the input assignment must already contain
    a concept dref at index n.

    Models how head nouns introduce concept drefs *presuppositionally*
    in @cite{krifka-2026} §4 — they behave like names. The indexed
    head noun *dog*₂ in (40d) is interpreted as a dynamic predicate
    of type **eaast** that *presupposes* dref 2 is anchored to the
    property 'dog'. Unlike entity drefs (existentially introduced by
    the determiner), concept drefs are conditions on the INPUT
    assignment, making them globally accessible. -/
def conceptPresup (n : Nat) (c : ConceptDRef W E) (body : DSent W E) :
    DSent W E :=
  λ g h => g n = .concept c ∧ body g h

/-- After negation, every index in the output has the same value as
    in the input. This is the fundamental property of negation-as-test. -/
theorem dNeg_preserves (φ : DSent W E) {g h : HAssign W E}
    (hNeg : dNeg φ g h) (n : Nat) :
    h n = g n :=
  congr_fun hNeg.1.symm n

/-- **Concept drefs survive negation.**

    If a concept dref was presupposed in the input, it remains accessible
    in the output of a negated sentence.

    @cite{krifka-2026} §3, §4:
    *John doesn't own a dog.* introduces concept dref x₂ for 'dog'
    in the main box / input assignment. After negation, x₂ persists,
    licensing continuations like *He is afraid of them₂.*

    Proof: negation forces h = g (test), so h(n) = g(n) = .concept c. -/
theorem concept_survives_negation {n : Nat} {c : ConceptDRef W E}
    {body : DSent W E} {g h : HAssign W E}
    (hPresup : g n = .concept c)
    (hNeg : dNeg body g h) :
    h n = .concept c :=
  (dNeg_preserves body hNeg n).trans hPresup

/-- **Entity drefs die under negation.**

    Entity drefs introduced by indefinites under negation are inaccessible
    in the output: the existentially introduced entity exists only in the
    local extension k, which is bound under ¬∃.

    @cite{krifka-2026} §4: after *John doesn't own [a₃ dog₂]*,
    index 3 (the entity dref for the dog John might own) is NOT in the
    output assignment, because it was introduced by ∃k (the determiner)
    under ¬ (the negation operator).

    Formally: negation forces h = g, and since the entity was NEWLY
    introduced at n (novelty: g(n) = .undef), the output h(n) = .undef. -/
theorem entity_trapped_by_negation {n : Nat}
    {body : DSent W E} {g h : HAssign W E}
    (hNeg : dNeg (entityIntro n body) g h)
    (hNovel : g n = .undef) :
    h n = .undef :=
  (dNeg_preserves (entityIntro n body) hNeg n).trans hNovel

/-- The asymmetry between concept and entity drefs under negation.

    In the same sentence *John₁ doesn't own [a₃ dog₂]*, the concept
    dref at index 2 survives while the entity dref at index 3 does not.

    This theorem combines the two projection results. -/
theorem concept_entity_asymmetry
    {nConcept nEntity : Nat}
    {c : ConceptDRef W E}
    {φ : DSent W E} {g h : HAssign W E}
    (hPresup : g nConcept = .concept c)
    (hNovel : g nEntity = .undef)
    (hNeg : dNeg φ g h) :
    h nConcept = .concept c ∧ h nEntity = .undef :=
  ⟨concept_survives_negation hPresup hNeg,
   (dNeg_preserves φ hNeg nEntity).trans hNovel⟩

end Projection


-- ════════════════════════════════════════════════════
-- § 3. DPL Bridge
-- ════════════════════════════════════════════════════

section DPLBridge

open Semantics.Dynamic.Core.DynProp (DRS dneg test)
open _root_.Core (Assignment)

variable {W E : Type*}

/-- Embed a homogeneous DPL-style assignment (`Assignment E = Nat → E`,
    @cite{groenendijk-stokhof-1991}) into a heterogeneous Krifka-style
    assignment (`Nat → DRefVal W E`) by wrapping every value in `.entity`. -/
def embedAssign (g : Assignment E) : HAssign W E :=
  λ n => .entity (g n)

/-- Lift a DPL-style relation (`DRS (Assignment E)`) to operate on
    heterogeneous assignments via the entity embedding. -/
def liftDPL (φ : DRS (Assignment E)) : DSent W E :=
  λ g h => ∃ g' h' : Assignment E, embedAssign g' = g ∧ embedAssign h' = h ∧ φ g' h'

/-- `dNeg` and `test (dneg φ)` (the substrate form of @cite{groenendijk-stokhof-1991}'s
    DPL negation) have identical structure.

    Both are: `λ g h => g = h ∧ ¬∃ k, φ g k`.
    @cite{krifka-2026}'s negation (34) generalizes DPL negation from homogeneous
    (`Nat → E`) to heterogeneous (`Nat → DRefVal W E`) assignments. The structure
    is preserved because the projection mechanism depends only on `g = h`. -/
theorem dNeg_structure (φ : DSent W E) (g h : HAssign W E) :
    dNeg φ g h ↔ (g = h ∧ ¬∃ k, φ g k) :=
  Iff.rfl

theorem dplNeg_structure (φ : DRS (Assignment E)) (g h : Assignment E) :
    test (dneg φ) g h ↔ (g = h ∧ ¬∃ k, φ g k) := by
  simp only [test, dneg]
  exact ⟨fun ⟨heq, hneg⟩ => ⟨heq, heq ▸ hneg⟩,
         fun ⟨heq, hneg⟩ => ⟨heq, heq ▸ hneg⟩⟩

/-- Negation commutes with the DPL→heterogeneous embedding.

    Lifting a DPL-style negation produces the same result as negating the
    lifted relation, modulo the entity-only constraint on assignments. -/
theorem liftDPL_neg (φ : DRS (Assignment E)) (g h : HAssign W E) :
    liftDPL (W := W) (test (dneg φ)) g h →
    dNeg (liftDPL (W := W) φ) g h := by
  intro ⟨g', h', hg, hh, hEq, hNex⟩
  -- hEq : g' = h'  (test's first conjunct)
  -- hNex : ¬∃ k, φ h' k  (test (dneg φ) puts the dneg-condition at the second arg)
  refine ⟨?_, ?_⟩
  · rw [← hg, ← hh]; exact congrArg embedAssign hEq
  · intro ⟨k, g'', h'', hg'', hk, hφ⟩
    rw [← hg] at hg''
    have hgeq : g' = g'' := by
      have := congrFun hg''.symm
      funext n; have := this n; simp [embedAssign] at this; exact this
    -- h' = g' (hEq.symm) = g'' (hgeq), so hφ : φ g'' h'' ↦ φ h' h''
    have hh'eq : h' = g'' := hEq.symm.trans hgeq
    exact hNex ⟨h'', hh'eq ▸ hφ⟩

end DPLBridge

end Semantics.Noun.Kind.Anaphora
