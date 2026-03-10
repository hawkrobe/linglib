import Linglib.Theories.Syntax.Minimalism.Core.Derivation

/-!
# Derivational Economy
@cite{chomsky-1995} @cite{chomsky-2000}

Economy principles constrain syntactic derivations by comparing
competing derivations that converge on the same PF string and LF
interpretation, selecting the one with fewest operations.

## Key Principles

- **Least Effort**: Among derivations yielding the same PF string and
  LF interpretation, prefer the one with fewest operations and fewest
  lexical resources drawn from the numeration.
- **Pronunciation Economy**: PF-reducing operations (ellipsis) may apply
  only if they have an effect on pronunciation. This bans vacuous
  deletion — eliding material that is already unpronounced.

## Design

Economy is formalized as a COMPARISON between derivation costs, not as
a constraint on individual derivations. This captures the global,
transderivational character of economy: the grammar evaluates the full
set of convergent derivations and selects the cheapest.

`DerivationCost` is abstract — it counts operations by type without
committing to a particular derivation model. Both the core `Derivation`
(step-based) and `FullDerivation` (workspace-based) models can project
onto `DerivationCost`.
-/

namespace Minimalism

-- ============================================================================
-- § 1: Derivation Cost
-- ============================================================================

/-- Cost of a syntactic derivation, measured by operation and resource counts.

    The four dimensions capture the resources consumed:
    - `lexicalItems`: items drawn from the numeration (lexical resources)
    - `mergeOps`: External + Internal Merge (structure building)
    - `agreeOps`: Agree operations (feature checking)
    - `ellipsisOps`: E-feature triggered deletions at PF -/
structure DerivationCost where
  lexicalItems : Nat
  mergeOps : Nat
  agreeOps : Nat
  ellipsisOps : Nat
  deriving Repr, DecidableEq

/-- Total number of syntactic operations (excluding lexical selection). -/
def DerivationCost.totalOps (c : DerivationCost) : Nat :=
  c.mergeOps + c.agreeOps + c.ellipsisOps

/-- Extract cost from a core `Derivation` (step-based model).

    Counts `emL`/`emR` as External Merge and `im` as Internal Merge.
    Agree and ellipsis are not tracked in the core model. -/
def Derivation.cost (d : Derivation) : DerivationCost where
  lexicalItems := d.steps.filter (match · with | .emL _ | .emR _ => true | _ => false) |>.length
  mergeOps := d.steps.length
  agreeOps := 0
  ellipsisOps := 0

-- ============================================================================
-- § 2: Economy Comparison
-- ============================================================================

/-- Derivation c1 is at least as economical as c2: no more operations
    and no more lexical resources on any dimension. -/
def atLeastAsEconomical (c1 c2 : DerivationCost) : Prop :=
  c1.totalOps ≤ c2.totalOps ∧ c1.lexicalItems ≤ c2.lexicalItems

/-- Derivation c1 is strictly more economical than c2: at least as
    economical, and strictly better on at least one dimension. -/
def strictlyMoreEconomical (c1 c2 : DerivationCost) : Prop :=
  atLeastAsEconomical c1 c2 ∧
  (c1.totalOps < c2.totalOps ∨ c1.lexicalItems < c2.lexicalItems)

/-- Economy comparison is reflexive. -/
theorem atLeastAsEconomical_refl (c : DerivationCost) :
    atLeastAsEconomical c c :=
  ⟨le_refl _, le_refl _⟩

/-- Economy comparison is transitive. -/
theorem atLeastAsEconomical_trans {c1 c2 c3 : DerivationCost}
    (h12 : atLeastAsEconomical c1 c2)
    (h23 : atLeastAsEconomical c2 c3) :
    atLeastAsEconomical c1 c3 :=
  ⟨le_trans h12.1 h23.1, le_trans h12.2 h23.2⟩

/-- Strict economy is irreflexive. -/
theorem strictlyMoreEconomical_irrefl (c : DerivationCost) :
    ¬strictlyMoreEconomical c c := by
  intro ⟨_, h⟩
  exact h.elim (lt_irrefl _) (lt_irrefl _)

/-- Strict economy is transitive. -/
theorem strictlyMoreEconomical_trans {c1 c2 c3 : DerivationCost}
    (h12 : strictlyMoreEconomical c1 c2)
    (h23 : strictlyMoreEconomical c2 c3) :
    strictlyMoreEconomical c1 c3 := by
  obtain ⟨⟨hops12, hlex12⟩, _⟩ := h12
  obtain ⟨⟨hops23, hlex23⟩, hstrict23⟩ := h23
  exact ⟨⟨le_trans hops12 hops23, le_trans hlex12 hlex23⟩,
    hstrict23.elim
      (fun h => .inl (lt_of_le_of_lt hops12 h))
      (fun h => .inr (lt_of_le_of_lt hlex12 h))⟩

/-- Strict economy is asymmetric. -/
theorem strictlyMoreEconomical_asymm {c1 c2 : DerivationCost}
    (h : strictlyMoreEconomical c1 c2) :
    ¬strictlyMoreEconomical c2 c1 := by
  intro h2
  exact strictlyMoreEconomical_irrefl c1
    (strictlyMoreEconomical_trans h h2)

-- ============================================================================
-- § 3: Pronunciation Economy
-- ============================================================================

/-- Pronunciation Economy: ellipsis may apply only if it changes the
    PF output.

    An ellipsis operation that targets material already unpronounced
    (e.g., because a prior deletion already removed it) is vacuous
    and therefore banned.

    `pfBefore`: the PF string before ellipsis applies.
    `pfAfter`: the PF string after ellipsis applies. -/
def pronunciationEconomy (pfBefore pfAfter : List String) : Prop :=
  pfBefore ≠ pfAfter

/-- Vacuous ellipsis: the PF output is unchanged by the deletion. -/
def vacuousEllipsis (pfBefore pfAfter : List String) : Prop :=
  pfBefore = pfAfter

/-- Pronunciation Economy holds iff ellipsis is not vacuous. -/
theorem pronEcon_iff_not_vacuous (pf1 pf2 : List String) :
    pronunciationEconomy pf1 pf2 ↔ ¬vacuousEllipsis pf1 pf2 :=
  Iff.rfl

-- ============================================================================
-- § 4: PF Equivalence
-- ============================================================================

/-- Two syntactic objects are PF-equivalent if they produce the same
    phonological string (left-to-right leaf yield). -/
def pfEquivalent (so1 so2 : SyntacticObject) : Prop :=
  so1.phonYield = so2.phonYield

/-- PF equivalence is reflexive. -/
theorem pfEquivalent_refl (so : SyntacticObject) : pfEquivalent so so :=
  rfl

/-- PF equivalence is symmetric. -/
theorem pfEquivalent_symm {so1 so2 : SyntacticObject}
    (h : pfEquivalent so1 so2) : pfEquivalent so2 so1 :=
  h.symm

/-- PF equivalence is transitive. -/
theorem pfEquivalent_trans {so1 so2 so3 : SyntacticObject}
    (h12 : pfEquivalent so1 so2) (h23 : pfEquivalent so2 so3) :
    pfEquivalent so1 so3 :=
  h12.trans h23

end Minimalism
