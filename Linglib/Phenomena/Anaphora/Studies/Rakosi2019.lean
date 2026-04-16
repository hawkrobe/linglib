import Linglib.Theories.Semantics.Reference.Reciprocals
import Linglib.Fragments.Hungarian.Reciprocals

/-!
# Rákosi (2019): Reciprocal anaphors in singular constructions in Hungarian
@cite{rakosi-2019}

Workshop on Cross-Linguistic Semantics of Reciprocals, Utrecht University,
7–8 October 2019. Proceedings edited by Palmieri, Winter & Zwarts (2020).

## Core Empirical Generalization

Hungarian reciprocals (*egymás*) tolerate morphosyntactically singular
antecedents in four construction types (§§3–6), while reflexives
(*maga/maguk*) require morphosyntactic plurality (plural noun head +
plural verb agreement + plural anaphor form).

| §  | Construction            | Syn# | Sem# | Refl(PL) | Recip |
|----|-------------------------|------|------|----------|-------|
| 3  | Quantified NP           | SG   | PL   | ✗        | ✓     |
| 4  | Singular coordinate DP  | SG   | PL   | ✗        | ✓     |
| 5  | Collective noun         | SG   | PL   | ✗        | ✓     |
| 6  | Bound variable (pro)    | SG   | PL   | —        | ✓     |
| —  | Plural NP (baseline)    | PL   | PL   | ✓        | ✓     |

## Theoretical Claim

The plurality requirement on reciprocal antecedents is **semantic**, not
morphosyntactic. This follows from the formal semantics of the
anaphoric relations: reciprocity (R) requires per-situation distinctness
(`u_ant s ≠ u_pro s`), presupposing multiple individuals in the
denotation. Reflexive binding (=) operates via φ-feature agreement,
a morphosyntactic mechanism.

## Connections

- `Theories/Semantics/Reference/Reciprocals.lean` §§9–10 — the
  `PluralityRequirement` type and semantic justification theorems
- `Fragments/Hungarian/Reciprocals.lean` — `AntecedentConfig`,
  `reciprocalLicensed`, `pluralReflexiveLicensed`, verification
- `Phenomena/Anaphora/Studies/DalrympleHaug2024.lean` §2 — the
  bound-variable case (§6 here) is also discussed there as evidence
  for the relational analysis of reciprocal scope
- `Phenomena/Anaphora/Coreference.lean` — the `reciprocalPattern`
  notes that syntactically singular antecedents are possible
-/

namespace Rakosi2019

open Semantics.Reference.Reciprocals
open Fragments.Hungarian.Reciprocals

-- ════════════════════════════════════════════════════════════════
-- § 1: The Asymmetry — Derived from PluralityRequirement
-- ════════════════════════════════════════════════════════════════

/-- The paper's core generalization: reciprocals need semantic plurality,
    reflexives need morphosyntactic plurality.

    This is not stipulated — it is derived from `anaphorPluralityReq`
    in the theory layer, which in turn follows from the formal semantics
    of binding (=) vs. reciprocity (R). -/
theorem core_generalization :
    anaphorPluralityReq (isReciprocal := true) = .semantic ∧
    anaphorPluralityReq (isReciprocal := false) = .morphosyntactic := ⟨rfl, rfl⟩

/-- All four singular constructions license reciprocals. -/
theorem all_singular_constructions_license_recip :
    singularConstructions.map reciprocalLicensed = [true, true, true, true] :=
  (singular_asymmetry).1

/-- No singular construction licenses the plural reflexive. -/
theorem no_singular_construction_licenses_pl_refl :
    singularConstructions.map pluralReflexiveLicensed = [false, false, false, false] :=
  (singular_asymmetry).2

-- ════════════════════════════════════════════════════════════════
-- § 2: Inclusive Reference Reflexives Are Not True Anaphors
-- ════════════════════════════════════════════════════════════════

/-- §2 rules out a potential confound: Hungarian "inclusive reference"
    reflexives (1SG subject + "ourselves") look like singular antecedent
    + plural reflexive, but these are NOT bound variables.

    Evidence: under *csak* ('only'), the inclusive reflexive gets a
    referential reading ("for us"), not a bound-variable reading
    ("for themselves"). True anaphors (matching-φ reflexives and
    reciprocals) DO get bound readings under *csak*.

    The reciprocal is NEVER licensed in inclusive reference:
    "*Sokszor sajnálom egymás-t" is ungrammatical — the 1SG
    antecedent is not semantically plural. -/
structure InclusiveRefData where
  /-- Can the inclusive reflexive be bound under "only"? -/
  boundUnderOnly : Bool
  /-- Can the reciprocal appear in the inclusive construction? -/
  reciprocalPossible : Bool
  deriving Repr

def inclusiveReflexive : InclusiveRefData :=
  { boundUnderOnly := false   -- referential only (ex. 4a)
    reciprocalPossible := false }  -- *Sokszor sajnálom egymást (ex. 6)

/-- Inclusive reflexives are not true anaphors: they don't bind under
    *only*, and the reciprocal is categorically excluded. -/
theorem inclusive_not_anaphor :
    inclusiveReflexive.boundUnderOnly = false ∧
    inclusiveReflexive.reciprocalPossible = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 3: Per-Construction Verification
-- ════════════════════════════════════════════════════════════════

/-- §3: Quantified antecedents. Hungarian quantified NPs are
    morphologically singular and take 3SG verbs.

    (8a) A két gyerek jól érezte magá-t/\*maguk-at.
    'The two children felt well.' (SG reflexive only)

    (9a) A szobában három kisgyerek kergeti egymás-t.
    'Three little children are chasing each other.' (reciprocal OK) -/
theorem quantified_np_asymmetry :
    reciprocalLicensed quantifiedNP = true ∧
    pluralReflexiveLicensed quantifiedNP = false ∧
    quantifiedNP.verbAgr = .sg := ⟨rfl, rfl, rfl⟩

/-- §4: Singular coordinate DPs.

    (11a) Kati és Éva kihúzta magát/\*magukat.
    'Kati and Éva drew themselves up.' (3SG verb → SG reflexive only)

    (12) Kati és Éva látta/látták egymás-t a tükörben.
    'Kati and Éva saw each other.' (reciprocal OK with SG or PL verb) -/
theorem coordinate_dp_asymmetry :
    reciprocalLicensed singularCoordinate = true ∧
    pluralReflexiveLicensed singularCoordinate = false ∧
    singularCoordinate.verbAgr = .sg := ⟨rfl, rfl, rfl⟩

/-- §5: Collective noun antecedents.

    (14) A személyzet fáradt volt/\*voltak.
    'The staff was tired.' (collective nouns: 3SG agreement only)

    (15a) A személyzet riadtan nézte egymás-t.
    'The staff were watching each other frightened.' (reciprocal OK)

    (16) Az egész család jól érezte magá-t/\*maguk-at.
    'The whole family enjoyed themselves.' (SG reflexive only) -/
theorem collective_noun_asymmetry :
    reciprocalLicensed collectiveNoun = true ∧
    pluralReflexiveLicensed collectiveNoun = false ∧
    collectiveNoun.verbAgr = .sg := ⟨rfl, rfl, rfl⟩

/-- §6: Bound variable antecedent.

    (17) Péter és Éva az-t gondolja, hogy (\*ő) szereti egymás-t.
    'Péter and Éva think that they love each other.'
    (pro-dropped 3SG embedded subject, reciprocal OK, wide scope only)

    This case is also discussed in @cite{dalrymple-haug-2024} §2 as
    evidence for the relational analysis: the singular bound pronoun
    forces binding (=), yielding the I-reading. -/
theorem bound_variable_asymmetry :
    reciprocalLicensed boundVariable = true ∧
    pluralReflexiveLicensed boundVariable = false ∧
    boundVariable.verbAgr = .sg := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 4: Connection to Formal Semantics
-- ════════════════════════════════════════════════════════════════

/-- The semantic justification: reciprocity requires distinct individuals,
    which is a denotation-level property. A semantically-plural but
    syntactically-singular antecedent provides the needed distinct
    individuals. A truly singular (atomic) antecedent does not —
    which is why "*A gyerek kergeti egymás-t" (the child chases
    each other) is ungrammatical even though the verb is 3SG. -/
theorem semantic_justification :
    -- Semantic plurality suffices for reciprocals
    satisfiesPluralityReq .semantic false true = true ∧
    -- Syntactic singularity blocks plural reflexives
    satisfiesPluralityReq .morphosyntactic false true = false ∧
    -- True singularity (no semantic plurality) blocks both
    satisfiesPluralityReq .semantic false false = false ∧
    satisfiesPluralityReq .morphosyntactic false false = false := ⟨rfl, rfl, rfl, rfl⟩

/-- The formal semantics connection: reciprocity (R) presupposes
    multiple individuals in the range of the discourse referent function.
    This is derived in `Reciprocals.lean` §10:
    `reciprocity_implies_multiple_individuals`. -/
theorem recip_needs_multiple_individuals :
    reciprocitySem (fun (_ : Unit) => (0 : Nat)) (fun (_ : Unit) => (0 : Nat)) →
    False :=
  fun h => h.2 () rfl

/-- Binding (=) is compatible with a single individual —
    explaining why reflexives don't impose a semantic plurality
    requirement. -/
theorem binding_ok_with_singleton :
    bindingSem (fun (_ : Unit) => (42 : Nat)) (fun (_ : Unit) => 42) :=
  binding_compatible_with_singleton 42

-- ════════════════════════════════════════════════════════════════
-- § 5: Cross-References to Existing Formalization
-- ════════════════════════════════════════════════════════════════

/-- *egymás* is morphologically invariable — it bears no number feature.
    This is consistent with the claim that its plurality requirement is
    semantic, not morphosyntactic: it doesn't participate in φ-agreement. -/
theorem egymas_no_number_feature :
    egymas.number = none := rfl

/-- The reflexive DOES participate in φ-agreement: *maga* (SG) vs.
    *maguk* (PL). The anaphor's number must match the verb's agreement,
    confirming that reflexive licensing is morphosyntactic. -/
theorem reflexive_number_paradigm :
    maga.number = some .sg ∧ maguk.number = some .pl := ⟨rfl, rfl⟩

/-- The morphological invariance of *egymás* predicts it should be
    insensitive to verb agreement number — and it is: reciprocals are
    grammatical with both SG and PL verbs when the antecedent is a
    coordinate DP (ex. 12: "Kati és Éva látta/látták egymás-t"). -/
theorem recip_indifferent_to_verb_agreement :
    reciprocalLicensed singularCoordinate = true ∧
    reciprocalLicensed pluralAntecedent = true := ⟨rfl, rfl⟩

end Rakosi2019
