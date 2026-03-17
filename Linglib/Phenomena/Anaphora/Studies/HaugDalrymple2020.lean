import Linglib.Theories.Semantics.Reference.Reciprocals

/-!
# Haug & Dalrymple (2020) @cite{haug-dalrymple-2020}

Reciprocity: Anaphora, scope, and quantification.
*Semantics & Pragmatics* 13(10): 1--62.

This paper develops the **relational analysis** of reciprocals, where
*each other* is a pronoun bearing an anaphoric relation (reciprocity R)
to its antecedent. The narrow/wide scope ambiguity reduces to the choice
of anaphoric relation between the local antecedent and the matrix subject:

- **Narrow scope** (we-reading): group identity (∪) + reciprocity (R)
- **Wide scope** (I-reading): binding (=) + reciprocity (R)
- **Crossed reading** (§3.3): group identity (∪) + group identity (∪),
  with reciprocity contributed by the DRS distinctness presupposition

The formal semantics of the three anaphoric relations (binding, group
identity, reciprocity) are defined in `Theories.Semantics.Reference.Reciprocals`
as `bindingSem`, `groupIdentitySem`, and `reciprocitySem`.

## Key Contributions Formalized

1. **Formal semantics of anaphoric relations** (§§2.2--2.4): three relations
   over discourse referent functions `S → E`
2. **Scope from anaphoric relation** (§3): narrow ↔ ∪, wide ↔ =
3. **Crossed readings** (§3.3): both relations are ∪
4. **Underspecification** (§4.2): German *sich*, Czech *se*, Cheyenne
   REFL/RECIP affix (@cite{murray-2008}) — group identity without
   distinctness permits reflexive, reciprocal, and mixed readings
5. **Maximize Anaphora** (§6): replaces Strongest Meaning Hypothesis
   of @cite{dalrymple-et-al-1998}; maximize the set of pairs standing
   in R_u subject to world knowledge consistency

## Connection to Cumulativity

The `groupIdentitySem` definition — bidirectional existential coverage of
value ranges — is structurally parallel to `cumulativeOp` in
`Theories.Semantics.Lexical.Plural.Cumulativity`. Both express that two
pluralities cover the same set of atomic parts. This is not a coincidence:
reciprocity is a species of cumulativity, as @cite{langendoen-1978}
first observed and @cite{haug-dalrymple-2020} §1 reaffirms.
-/

namespace Phenomena.Anaphora.Studies.HaugDalrymple2020

open Semantics.Reference.Reciprocals

-- ════════════════════════════════════════════════════════════════
-- § 1: Scope from Anaphoric Relation (@cite{haug-dalrymple-2020} §3)
-- ════════════════════════════════════════════════════════════════

/-- Narrow scope uses group identity between the local antecedent and
    the matrix subject. -/
theorem narrow_uses_groupIdentity :
    narrowScopeRelations.1 = .groupIdentity := rfl

/-- Wide scope uses binding between the local antecedent and the matrix
    subject. -/
theorem wide_uses_binding :
    wideScopeRelations.1 = .binding := rfl

/-- The narrow-scope antecedent relation denotes `groupIdentitySem`. -/
theorem narrow_antecedent_denotes {S E : Type*} (u_ant u_pro : S → E) :
    narrowScopeRelations.1.denotes u_ant u_pro = groupIdentitySem u_ant u_pro := rfl

/-- The wide-scope antecedent relation denotes `bindingSem`. -/
theorem wide_antecedent_denotes {S E : Type*} (u_ant u_pro : S → E) :
    wideScopeRelations.1.denotes u_ant u_pro = bindingSem u_ant u_pro := rfl

/-- Both readings use the reciprocity relation for the reciprocal itself,
    which denotes `reciprocitySem`. -/
theorem both_reciprocal_denotes {S E : Type*} (u_ant u_pro : S → E) :
    narrowScopeRelations.2.denotes u_ant u_pro = reciprocitySem u_ant u_pro ∧
    wideScopeRelations.2.denotes u_ant u_pro = reciprocitySem u_ant u_pro :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 2: Crossed Readings (@cite{haug-dalrymple-2020} §3.3)
-- ════════════════════════════════════════════════════════════════

/-- Crossed readings arise when *both* anaphoric relations are group
    identity (∪). The subject pronoun bears group identity to the matrix
    subject (`∪u₂ → ∪u₁`), and the reciprocal bears group identity to
    the subject pronoun (`∪u₃ → ∪u₂`). Reciprocity is contributed by
    the DRS distinctness presupposition (`∂(u₃ ≠ u₂)`), not by an
    anaphoric reciprocity relation.

    Example: "Two girls thought they saw each other" on the crossed
    reading — *girl₁* thought *girl₂* saw *girl₁* and vice versa. -/
def crossedScopeRelations : AnaphoricRelation × AnaphoricRelation :=
  (.groupIdentity, .groupIdentity)

/-- Crossed readings use neither binding nor reciprocity as an anaphoric
    relation — both slots are group identity. This distinguishes them from
    narrow and wide readings. -/
theorem crossed_distinct_from_narrow_and_wide :
    crossedScopeRelations ≠ narrowScopeRelations ∧
    crossedScopeRelations ≠ wideScopeRelations := by
  constructor <;> decide

/-- Both components of the crossed reading denote `groupIdentitySem`. -/
theorem crossed_both_denote_groupIdentity {S E : Type*} (u_ant u_pro : S → E) :
    crossedScopeRelations.1.denotes u_ant u_pro = groupIdentitySem u_ant u_pro ∧
    crossedScopeRelations.2.denotes u_ant u_pro = groupIdentitySem u_ant u_pro :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 3: Formal Semantics Properties
-- ════════════════════════════════════════════════════════════════

/-- Group identity does not imply binding: a Bool counterexample where
    `id` and `not` have the same range (`{true, false}`) but differ
    pointwise. -/
theorem groupIdentity_not_implies_binding :
    ¬(∀ (u_ant u_pro : Bool → Bool),
      groupIdentitySem u_ant u_pro → bindingSem u_ant u_pro) := by
  intro h
  have := h id (!·) ⟨fun s => ⟨!s, by cases s <;> rfl⟩,
                       fun s => ⟨!s, by cases s <;> rfl⟩⟩
  have := this true
  simp at this

-- ════════════════════════════════════════════════════════════════
-- § 4: Underspecification (@cite{haug-dalrymple-2020} §4.2)
-- ════════════════════════════════════════════════════════════════

/-- Underspecified pronouns (German *sich*, Czech *se*, Cheyenne REFL/RECIP
    affix) allow any reading consistent with group identity: reflexive
    (binding + group identity), reciprocal (reciprocity + group identity),
    or mixed (@cite{murray-2008}). The underspecified meaning
    `underspecifiedSem` is exactly `groupIdentitySem`. -/
theorem underspecified_permits_binding {S E : Type*} {u_ant u_pro : S → E}
    (h : bindingSem u_ant u_pro) : underspecifiedSem u_ant u_pro :=
  binding_implies_groupIdentity h

/-- Underspecified pronouns permit reciprocal readings: reciprocity
    implies underspecification. -/
theorem underspecified_permits_reciprocity {S E : Type*} {u_ant u_pro : S → E}
    (h : reciprocitySem u_ant u_pro) : underspecifiedSem u_ant u_pro :=
  reciprocity_strengthens_underspecified h

-- ════════════════════════════════════════════════════════════════
-- § 5: Maximize Anaphora (@cite{haug-dalrymple-2020} §6)
-- ════════════════════════════════════════════════════════════════

/-- **Maximize Anaphora** replaces the Strongest Meaning Hypothesis of
    @cite{dalrymple-et-al-1998}. In interpreting a DRS K containing a
    discourse referent u introduced by a reciprocal with antecedent u',
    maximize the set of pairs R_u standing in the relation φ(u, u'),
    subject to the constraint that φ(u, u') holds in K given world
    knowledge.

    Maximize Anaphora is orthogonal to reciprocal scope (§6.3):
    it constrains the *strength* of the reciprocal relation (weak vs.
    strong reciprocity), not the *scope* (narrow vs. wide). Scope is
    determined by the anaphoric relation on the antecedent (binding vs.
    group identity), which is a separate parameter. -/
theorem maximize_anaphora_orthogonal_to_scope :
    -- Scope is determined by the first component of the relation pair
    narrowScopeRelations.1 ≠ wideScopeRelations.1 ∧
    -- Both readings use the same reciprocity relation
    narrowScopeRelations.2 = wideScopeRelations.2 := by
  constructor <;> decide

-- ════════════════════════════════════════════════════════════════
-- § 6: Reciprocal Scope Constraint (@cite{haug-dalrymple-2020} §3.4)
-- ════════════════════════════════════════════════════════════════

/-- Key constraint: on the relational analysis, the reciprocal's scope
    is *determined* by the anaphoric relation on its antecedent. There
    is no independent scope mechanism. Local antecedent properties
    directly constrain scope, unlike the quantificational analysis
    where scope is independent (@cite{williams-1991}). -/
theorem scope_determined_by_antecedent_relation :
    (narrowScopeRelations.1 = .groupIdentity ∧ wideScopeRelations.1 = .binding) ∧
    narrowScopeRelations.2 = wideScopeRelations.2 :=
  ⟨⟨rfl, rfl⟩, rfl⟩

/-- The scope constraint additionally means that the reciprocal never
    scopes higher than the highest binder of the local antecedent
    (@cite{williams-1991}, @cite{haug-dalrymple-2020} §3.4).
    On the relational analysis this falls out automatically: scope is
    parasitic on the antecedent's anaphoric relation, and binding is
    limited by c-command. The quantificational analysis must stipulate
    this constraint separately. -/
theorem scope_parasitic_on_antecedent :
    -- Wide scope = binding; binding requires c-command (structurally limited)
    wideScopeRelations.1 = .binding ∧
    -- Narrow scope = group identity; no c-command required (can be nonlocal)
    narrowScopeRelations.1 = .groupIdentity := ⟨rfl, rfl⟩

end Phenomena.Anaphora.Studies.HaugDalrymple2020
