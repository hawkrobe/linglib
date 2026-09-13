import Linglib.Semantics.Dynamic.PPCDRT.Anaphora
import Linglib.Fragments.Hungarian.Reciprocals

/-!
# Rákosi (2019): Reciprocal anaphors in singular constructions in Hungarian
[rakosi-2019]

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

- `Semantics/Dynamic/PPCDRT/Anaphora.lean` — the formal-semantic
  reciprocity / binding conditions over plural assignments.
- `Fragments/Hungarian/Reciprocals.lean` — the lexical entries and the
  antecedent constructions `AntecedentConfig`.
- `Studies/Chomsky1981.lean` — the English reciprocal minimal pairs
  notes that syntactically singular antecedents are possible.
-/

namespace Rakosi2019

open PPCDRT
open Core
open Hungarian.Reciprocals

-- ════════════════════════════════════════════════════════════════
-- § 1: The Asymmetry
-- ════════════════════════════════════════════════════════════════

/-- The reciprocal is licensed by a semantically plural antecedent: reciprocity requires
    distinct individuals in the denotation (`recip_needs_multiple_individuals`), whatever
    the antecedent's morphology. -/
def reciprocalLicensed (cfg : AntecedentConfig) : Bool := cfg.semanticPl

/-- The plural reflexive is licensed by a morphosyntactically plural antecedent: reflexive
    binding is φ-agreement, and binding imposes no distinctness
    (`binding_ok_with_singleton`). -/
def pluralReflexiveLicensed (cfg : AntecedentConfig) : Bool := cfg.syntacticPl

/-- All four singular constructions license reciprocals. -/
theorem all_singular_constructions_license_recip :
    singularConstructions.map reciprocalLicensed = [true, true, true, true] := rfl

/-- No singular construction licenses the plural reflexive. -/
theorem no_singular_construction_licenses_pl_refl :
    singularConstructions.map pluralReflexiveLicensed = [false, false, false, false] := rfl

/-- With a standard plural antecedent, both are licensed. -/
theorem plural_licenses_both :
    reciprocalLicensed pluralAntecedent = true ∧
    pluralReflexiveLicensed pluralAntecedent = true := ⟨rfl, rfl⟩

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
    quantifiedNP.verbAgr = .Sing := ⟨rfl, rfl, rfl⟩

/-- §4: Singular coordinate DPs.

    (11a) Kati és Éva kihúzta magát/\*magukat.
    'Kati and Éva drew themselves up.' (3SG verb → SG reflexive only)

    (12) Kati és Éva látta/látták egymás-t a tükörben.
    'Kati and Éva saw each other.' (reciprocal OK with SG or PL verb) -/
theorem coordinate_dp_asymmetry :
    reciprocalLicensed singularCoordinate = true ∧
    pluralReflexiveLicensed singularCoordinate = false ∧
    singularCoordinate.verbAgr = .Sing := ⟨rfl, rfl, rfl⟩

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
    collectiveNoun.verbAgr = .Sing := ⟨rfl, rfl, rfl⟩

/-- §6: Bound variable antecedent.

    (17) Péter és Éva az-t gondolja, hogy (\*ő) szereti egymás-t.
    'Péter and Éva think that they love each other.'
    (pro-dropped 3SG embedded subject, reciprocal OK, wide scope only) -/
theorem bound_variable_asymmetry :
    reciprocalLicensed boundVariable = true ∧
    pluralReflexiveLicensed boundVariable = false ∧
    boundVariable.verbAgr = .Sing := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 4: Connection to Formal Semantics
-- ════════════════════════════════════════════════════════════════

/-- Reciprocity restricted to states where both discourse referents are defined forces two
    distinct individuals: the distinctness clause of `reciprocityCond` gives a distinct pair
    from any jointly defined state, which is the semantic plurality requirement on the
    antecedent of a reciprocal. -/
theorem reciprocity_implies_multiple_individuals {E : Type*} (uAnaph uAnt : Nat)
    (S : PluralAssign ℕ E) (Δ : Set Nat)
    (hdef : ∃ s ∈ S, (s uAnaph).isSome ∧ (s uAnt).isSome)
    (h : reciprocityCond uAnaph uAnt S Δ) :
    ∃ (a b : E), a ≠ b := by
  obtain ⟨g, hgS, hAnaph, hAnt⟩ := hdef
  obtain ⟨da, hda⟩ := Option.isSome_iff_exists.mp hAnaph
  obtain ⟨db, hdb⟩ := Option.isSome_iff_exists.mp hAnt
  exact ⟨da, db, h.2 g hgS da db hda hdb⟩

/-- Binding is compatible with a singleton state mapping both discourse referents to one
    value: reflexive binding imposes no semantic plurality. -/
theorem binding_compatible_with_singleton {E : Type*} (e : E) (uAnaph uAnt : Nat) :
    bindingCond uAnaph uAnt
      {PartialAssign.update (PartialAssign.update PartialAssign.empty uAnaph e) uAnt e} ∅ := by
  intro g hg
  obtain rfl : g = _ := hg
  by_cases h : uAnaph = uAnt
  · subst h; rfl
  · simp [PartialAssign.update_at, h]

/-- The contrapositive on a concrete state: with both anaphor and antecedent mapped to the
    same value in a singleton state, the distinctness clause of `reciprocityCond` fails. -/
theorem recip_needs_multiple_individuals :
    ¬ reciprocityCond (E := Nat) 0 1
        {PartialAssign.update
          (PartialAssign.update PartialAssign.empty 0 0) 1 0} ∅ := by
  intro h
  have hg : (PartialAssign.update (PartialAssign.update PartialAssign.empty 0 0) 1 0) ∈
            ({PartialAssign.update (PartialAssign.update PartialAssign.empty 0 0) 1 0} :
              PluralAssign ℕ Nat) :=
    rfl
  have h0 :
      (PartialAssign.update (PartialAssign.update PartialAssign.empty 0 0) 1 0) 0 = some 0 := by
    simp [PartialAssign.update]
  have h1 :
      (PartialAssign.update (PartialAssign.update PartialAssign.empty 0 0) 1 0) 1 = some 0 := by
    simp [PartialAssign.update]
  exact h.2 _ hg 0 0 h0 h1 rfl

/-- Binding (=) is compatible with a singleton state where both drefs
    point to the same value — explaining why reflexives don't impose a
    semantic plurality requirement. -/
theorem binding_ok_with_singleton :
    bindingCond (E := Nat) 0 1
      {PartialAssign.update
        (PartialAssign.update PartialAssign.empty 0 42) 1 42} ∅ :=
  binding_compatible_with_singleton 42 0 1

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
    maga.number = some .singular ∧ maguk.number = some .plural := ⟨rfl, rfl⟩

/-- The morphological invariance of *egymás* predicts it should be
    insensitive to verb agreement number — and it is: reciprocals are
    grammatical with both SG and PL verbs when the antecedent is a
    coordinate DP (ex. 12: "Kati és Éva látta/látták egymás-t"). -/
theorem recip_indifferent_to_verb_agreement :
    reciprocalLicensed singularCoordinate = true ∧
    reciprocalLicensed pluralAntecedent = true := ⟨rfl, rfl⟩

end Rakosi2019
