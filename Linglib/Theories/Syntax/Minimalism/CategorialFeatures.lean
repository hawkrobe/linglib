import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic

/-!
# Categorial Feature Theories: @cite{chomsky-1970} vs. @cite{panagiotidis-2015}

@cite{panagiotidis-2015} @cite{grimshaw-2005} @cite{chomsky-1970}

Two theories of what makes a noun a noun and a verb a verb:

1. **@cite{chomsky-1970}**: [±V, ±N] as arbitrary binary diacritics that cross-classify
   the four lexical categories. Adopted by @cite{grimshaw-2005} for Extended Projections.
   Implemented in `CatFeatures`.

2. **@cite{panagiotidis-2015}**: [N] and [V] as substantive, LF-interpretable features:
   - [N] = sortal perspective / referentiality
   - [V] = temporal perspective / eventivity (§4.3)
   On categorizers (v, n, a), these are *interpretable*; on functional heads
   (T, C, D, etc.), they are *uninterpretable* copies (§5.8).
   Implemented in `CategorialFeatures`.

## Key Agreement

The two systems produce the same four equivalence classes — {verbal}, {nominal},
{adjectival}, {adpositional} — and therefore agree on all EP-consistency judgments
(`chomsky_panagiotidis_agree`).

## Key Disagreement

The status of **P** (prepositions/adpositions):

- Chomsky: P *actively bears* [-V, -N] — two negative feature values
- Panagiotidis: P is the **default** categorizer, lacking both [N] and [V]

This matters for the theory of features: in Chomsky's system, [-V] and [-N] are
just as "real" as [+V] and [+N]. In Panagiotidis's system, the absence of [N] and
[V] is genuinely the absence of categorial content — P is the elsewhere case. This
predicts that P should be the most promiscuous category (appearing in the most
diverse syntactic environments), which Panagiotidis argues is borne out.

## Adjectives

Both systems agree that A shares properties with both N and V:
- Chomsky: A = [+V, +N], the only category with both positive values
- Panagiotidis: A = [N, V], bearing both substantive features

The difference: for Panagiotidis, this is *explanatory* — adjectives have temporal
anchoring (because [V]) and sortal perspective (because [N]). For Chomsky,
the co-presence of [+V] and [+N] is a notational fact without semantic content.
-/

namespace Comparisons.CategorialFeatures

open Minimalism

-- ═══════════════════════════════════════════════════════════════
-- § 1: Extensional Equivalence
-- ═══════════════════════════════════════════════════════════════

/-- The two theories agree on every pairwise consistency judgment.
    Re-export of the theorem from Basic.lean for visibility. -/
theorem extensional_equivalence (c1 c2 : Cat) :
    categoryConsistent c1 c2 = categorialConsistent c1 c2 :=
  chomsky_panagiotidis_agree c1 c2

-- ═══════════════════════════════════════════════════════════════
-- § 2: Internal Structure of Each System
-- ═══════════════════════════════════════════════════════════════

/-- In Chomsky's system, every category has at least one positive feature
    except P (which has [-V, -N] = ⟨false, false⟩). -/
theorem chomsky_p_has_no_positive_feature :
    (catFeatures .P).plusV = false ∧ (catFeatures .P).plusN = false := by decide

/-- In Panagiotidis's system, P is the default: no categorial features. -/
theorem panagiotidis_p_is_default :
    (categorialFeatures .P).hasN = false ∧ (categorialFeatures .P).hasV = false := by decide

/-- These are extensionally identical — but the theories *interpret* ⟨false, false⟩
    differently: Chomsky reads it as "actively [-V, -N]"; Panagiotidis reads it
    as "absence of both [N] and [V]" (the elsewhere case). -/
theorem p_same_values :
    catFeatures .P = ⟨false, false⟩ ∧ categorialFeatures .P = ⟨false, false⟩ := by decide

/-- Adjectives bear both features in both systems. -/
theorem adjective_both_features :
    catFeatures .A = ⟨true, true⟩ ∧ categorialFeatures .A = ⟨true, true⟩ := by decide

-- ═══════════════════════════════════════════════════════════════
-- § 3: Feature Semantics (Panagiotidis only)
-- ═══════════════════════════════════════════════════════════════

/-- [N] = sortal perspective / referentiality. Every category in the nominal
    EP bears [N] (interpretable on n, uninterpretable on Num/Q/D; §5.8). -/
theorem nominal_ep_has_n :
    (categorialFeatures .N).hasN ∧ (categorialFeatures .n).hasN ∧
    (categorialFeatures .Num).hasN ∧ (categorialFeatures .Q).hasN ∧
    (categorialFeatures .D).hasN := by decide

/-- [V] = temporal perspective / eventivity. Every category in the verbal
    EP bears [V] (interpretable on v, uninterpretable on T/C; §5.8). -/
theorem verbal_ep_has_v :
    (categorialFeatures .V).hasV ∧ (categorialFeatures .v).hasV ∧
    (categorialFeatures .T).hasV ∧ (categorialFeatures .C).hasV := by decide

/-- Adjectives bear both [N] (sortal perspective) and [V] (temporal perspective).
    This explains why adjectives can be nominalized (via [N]) and
    have temporal anchoring (via [V]). -/
theorem adjective_referential_and_predicative :
    (categorialFeatures .A).hasN ∧ (categorialFeatures .A).hasV := by decide

/-- The adjectival categorizer *a* inherits [N, V] from A. -/
theorem a_categorizer_referential_and_predicative :
    (categorialFeatures .a).hasN ∧ (categorialFeatures .a).hasV := by decide

/-- P bears neither [N] nor [V] — the default/elsewhere categorizer.
    This predicts P is the most syntactically promiscuous category. -/
theorem p_neither_referential_nor_predicative :
    ¬(categorialFeatures .P).hasN ∧ ¬(categorialFeatures .P).hasV := by decide

-- ═══════════════════════════════════════════════════════════════
-- § 4: Categorizers as a Natural Class
-- ═══════════════════════════════════════════════════════════════

/-- The three categorizers (v, n, a) form a natural class at F1
    (Grimshaw's system). Each bears the interpretable categorial features
    of its EP family. Note: Panagiotidis (§4.5) argues categorizers are
    lexical, not functional, despite being placed at F1 in the EP. -/
theorem categorizers_are_f1 :
    isCategorizer .v ∧ isCategorizer .n ∧ isCategorizer .a ∧
    fValue .v = 1 ∧ fValue .n = 1 ∧ fValue .a = 1 := by decide

/-- Lexical heads (V, N, A, P) are not categorizers. In Panagiotidis's
    system, these represent *categorized* items (√+categorizer), not
    the categorizers themselves. -/
theorem lexical_heads_not_categorizers :
    isCategorizer .V = false ∧ isCategorizer .N = false ∧
    isCategorizer .A = false ∧ isCategorizer .P = false := by decide

/-- Each categorizer bears the *interpretable* features of its family:
    v bears [V] (temporal), n bears [N] (sortal), a bears [N, V] (both). -/
theorem categorizer_features :
    categorialFeatures .v = ⟨false, true⟩ ∧
    categorialFeatures .n = ⟨true, false⟩ ∧
    categorialFeatures .a = ⟨true, true⟩ := by decide

-- ═══════════════════════════════════════════════════════════════
-- § 5: CatFamily as Theory-Neutral Ground
-- ═══════════════════════════════════════════════════════════════

/-- CatFamily is the theory-neutral representation: it records which
    categories group together without committing to the mechanism.
    Both Chomsky and Panagiotidis produce the same CatFamily partition. -/
theorem catFamily_from_chomsky (c1 c2 : Cat) :
    (catFeatures c1 == catFeatures c2) = (catFamily c1 == catFamily c2) := by
  cases c1 <;> cases c2 <;> decide

theorem catFamily_from_panagiotidis (c1 c2 : Cat) :
    (categorialFeatures c1 == categorialFeatures c2) = (catFamily c1 == catFamily c2) := by
  cases c1 <;> cases c2 <;> decide

end Comparisons.CategorialFeatures
