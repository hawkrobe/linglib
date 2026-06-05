import Linglib.Features.Person.Decomposition

/-!
# Clusivity systems — typology of inclusive/exclusive distinctions
[cysouw-2009]

System-level typology of how a language encodes the inclusive/exclusive
distinction in 1pl pronouns. Per-referent person *categories*
(`s1`, `minIncl`, `augIncl`, `excl`, ...) live in
`Features/Person.lean::Category`; this file classifies *systems* by which
of those categories they grammatically distinguish.

The substrate cut is intentionally finer than WALS Ch 39 (which collapses
plain inclExcl with minimal-augmented into a single "inclusive/exclusive"
value). The minimal-augmented type — which licenses a 1-dual-inclusive
form in addition to a 1pl-inclusive — is the typologically distinctive
property of Tagalog (*kata* / *tayo*), several other Philippine languages,
and many Australian languages.

Scope: pronominal clusivity (independent personal pronouns). Verbal
clusivity (WALS Ch 40, `Pronoun.InclusiveExclusiveVerbal`) is a
separately-marked phenomenon that may dissociate from pronominal clusivity
(e.g. some Athabaskan languages). The five-value enum here is a first-cut
typology; [cysouw-2009] discusses additional minor types
(degenerate-minimal-augmented, composite-unit-augmented) that this
substrate does not currently distinguish.
-/

set_option autoImplicit false

namespace Features.Clusivity

/-- The five common marking types of the first person complex
    ([cysouw-2009] Table 3.2; the attested-and-common five of the
    fifteen possible patterns, his Fig 3.1–3.2). Classified by which of
    the categories 1+2, 1+2+3, 1+3 receive specialized morphemes. The
    five rare attested patterns ((Pf)–(Pj), his §3.6.6) are not
    represented. -/
inductive System where
  /-- (Pb) No-we: none of 1+2, 1+2+3, 1+3 marked by a specialized
      morpheme (English verbal inflection; Pirahã, which lacks group
      marking altogether). -/
  | noWe
  /-- (Pa) Unified-we: all three categories marked by the same
      specialized morpheme (English *we*, German *wir*). -/
  | unifiedWe
  /-- (Pc) Only-inclusive: 1+2 and 1+2+3 share a specialized inclusive
      morpheme; 1+3 is marked by the first-person singular morpheme,
      not a specialized one (Maká). -/
  | onlyInclusive
  /-- (Pd) Inclusive/exclusive: inclusive (1+2, 1+2+3) and exclusive
      (1+3) each get a specialized morpheme (Apalai; Indonesian
      *kita*/*kami*). -/
  | inclusiveExclusive
  /-- (Pe) Minimal/augmented: all three categories get separate
      specialized morphemes (Tagalog *kata*/*tayo*/*kami* per
      [schachter-otanes-1972] Chart 7; Ilocano *ta*/*tayo*/*mi*, his
      Fig 3.5–3.6). -/
  | minimalAugmented
  deriving DecidableEq, Repr, Fintype

namespace System

/-! Fig 3.10's nested questions: each type answers one more question
positively than its predecessor, which is exactly why the types form
the First Person Hierarchy (3.26). -/

/-- Some specialized 'we' morpheme exists. -/
def specializedWe : System → Bool
  | .noWe => false
  | _ => true

/-- The inclusive (1+2, 1+2+3) has marking distinct from the
    exclusive. -/
def specializedInclusive : System → Bool
  | .noWe | .unifiedWe => false
  | _ => true

/-- The exclusive (1+3) has its own specialized morpheme. -/
def specializedExclusive : System → Bool
  | .inclusiveExclusive | .minimalAugmented => true
  | _ => false

/-- The inclusive is split: separate morphemes for 1+2 and 1+2+3. -/
def splitInclusive : System → Bool
  | .minimalAugmented => true
  | _ => false

/-- A system grammatically distinguishes inclusive from exclusive. -/
abbrev hasInclExcl (s : System) : Bool := s.specializedExclusive

/-- A system distinguishes minimal from augmented inclusive. -/
abbrev hasMinimalAugmented (s : System) : Bool := s.splitInclusive

/-- **Addressee inclusion implication I** ([cysouw-2009] (3.23),
    Fig 3.8): a specialized exclusive requires a specialized inclusive.
    The converse fails — only-inclusive systems are the witness. (Over
    the common types; the rare Binandere pattern, his (3.22)/(Pj), is
    the noted incidental exception.) -/
theorem exclusive_implies_inclusive :
    ∀ s : System, s.specializedExclusive → s.specializedInclusive := by
  decide

theorem not_inclusive_implies_exclusive :
    ¬ ∀ s : System, s.specializedInclusive → s.specializedExclusive := by
  decide

/-- **Addressee inclusion implication II** ([cysouw-2009] (3.24),
    Fig 3.9): a split inclusive requires a specialized exclusive
    (disregarding the rare (Pf)/(Pg) patterns, his §3.6.6). -/
theorem splitInclusive_implies_exclusive :
    ∀ s : System, s.splitInclusive → s.specializedExclusive := by
  decide

/-- Position in the **First Person Hierarchy** ([cysouw-2009] (3.26)):
    no-we > unified-we > only-inclusive > inclusive/exclusive >
    minimal/augmented (rank counts the Fig 3.10 questions answered
    positively). -/
def hierarchyRank : System → Nat
  | .noWe => 0
  | .unifiedWe => 1
  | .onlyInclusive => 2
  | .inclusiveExclusive => 3
  | .minimalAugmented => 4

/-- The hierarchy is exactly the nesting of Fig 3.10's questions: each
    of the four predicates is monotone in hierarchy rank, so each type's
    profile extends its predecessor's by one positive answer. -/
theorem hierarchy_is_question_nesting :
    ∀ s t : System, s.hierarchyRank ≤ t.hierarchyRank →
      (s.specializedWe → t.specializedWe = true) ∧
      (s.specializedInclusive → t.specializedInclusive = true) ∧
      (s.specializedExclusive → t.specializedExclusive = true) ∧
      (s.splitInclusive → t.splitInclusive = true) := by
  decide

end System

/-! The per-referent clusivity `Value` (inclusive/exclusive) and the
`categoryOf` bridge were dissolved into the canonical person inventory:
clusivity is a person-value distinction (`Person.firstInclusive` /
`Person.firstExclusive`, `Features/Person/Basic.lean`), and the category
bridge is `Person.Category.ofPersonNumber`
(`Features/Person/Decomposition.lean`). This file keeps the
paradigm-level `System` typology, which classifies how a language's
pronoun paradigm carves the person–number space. -/

end Features.Clusivity
