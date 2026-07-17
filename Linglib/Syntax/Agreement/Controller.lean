/-!
# Agreement Controller — Grammatical Role of the Controlling NP
[corbett-2006] ch 2 §2.1, ch 6 §6.6

While `Syntax/Agreement/Basic.lean` enumerates WHERE agreement morphology
surfaces (Corbett 1991 Agreement Hierarchy), this file enumerates WHICH
GRAMMATICAL ROLE the controlling NP plays. The two axes are orthogonal:
a language can have subject-controlled verb agreement
(`Controller.subj` × `Target.verb`) and possessor-controlled
attributive agreement (`Controller.poss` × `Target.attributive`).

## Typological labels

The labels here are typological metalanguage — Comrie/Dixon S/A/P
+ grammatical-relation labels used across frameworks. Different theories
operationalize them differently (LFG SUBJ ≠ Minimalist external argument
≠ RG 1), but at the level of CROSS-LINGUISTIC DESCRIPTION (which is what
`Morphology.MorphCategory.agreement` records), the labels are
reasonably consensual. Framework-specific projections
(LFG analysis → Controller, Minimalist analysis → Controller) live in
framework-specific subdirs like `Syntax/Minimalist/Agreement/`.

## Cases derived from Corbett 2006

[corbett-2006] §2.1 surveys controller TYPES (canonical NPs,
defective clauses §2.1.2, weather-verb absent controllers §2.1.3,
possessive adjectives §2.1.4, qualitative adjectives §2.1.5). Within
canonical NP controllers, the orthogonal GRAMMATICAL-ROLE dimension
is treated in §6.6 — Hindi/Urdu (p. 195): "if the subject is in
the nominative, the verb agrees with it; otherwise, if the object
is in the nominative, the verb agrees with that; otherwise the verb
shows default agreement". This 3-way subj/obj/default rule is the
canonical Indo-Aryan pattern; other languages fold in indirect
objects (recipients), possessors (Upper Sorbian §2.1.4), and rarely
obliques.

## Anderson 2006 Ch 5 §5.2 motivation

The substrate gap that prompted this enum: Anderson's split/doubled
AVC typology turns on "subjects on both AUX and LV; objects only on
LV" — a generalization unstateable when `MorphCategory.agreement`
collapses subj/obj. Parameterizing `agreement` on `Controller`
makes the Anderson Ch 5 typology directly Lean-checkable:
`dist.onLex.contains (.agreement .obj) ∧ ¬ dist.onAux.contains (.agreement .obj)`.

## Bybee 1985 motivation

`Studies/Bybee1985.lean:255-257` already encodes
Bybee's source distinction `personAgr / personAgrObj / genderAgr` but
collapses all three onto flat `.agreement` in the substrate projection.
With the parametric form, the projection round-trips:
`personAgr → .agreement .subj`, `personAgrObj → .agreement .obj`.

## What's NOT here

- **Case** — case-marking (nom/erg/abs/dat/...) is orthogonal to
  grammatical role. Quirky-case subjects in Icelandic, ergative-case
  agents in Tsakhur, etc. are case phenomena, not controller-role
  phenomena. Case lives in `Features/Case/` and `Syntax/Case/`.
- **φ-features** (person, number, gender) — these are properties of
  the CONTROLLER NP that determine agreement values. Not encoded in
  the controller-role enum itself.
- **Animacy / topicality / focus** — agreement *conditions* per
  [corbett-2006] ch 6, not controller-role labels.
-/

namespace Agreement

/-- Grammatical role of the agreement controller. Cross-linguistically
    motivated typological labels per [corbett-2006] §6.6. -/
inductive Controller where
  /-- Subject (S in intransitive, A in transitive). The unmarked case
      cross-linguistically. Russian *kniga* controlling verb agreement;
      English *he* controlling *-s*. -/
  | subj
  /-- Direct object (P in transitive). In ergative-absolutive systems,
      the absolutive argument; cf. Dargwa gender-prefix agreement
      controlled by absolutive ([corbett-2006] §6.5 ex. 21-26). -/
  | obj
  /-- Indirect object / recipient (G in ditransitive). Some Bantu and
      Romance dialects show recipient agreement on the verb. -/
  | iobj
  /-- Possessor. Hungarian possessive suffix; Upper Sorbian
      *moj-eho muž-ow-a sotr-a* where the possessive adjective
      controls the attributive ([corbett-2006] §2.1.4). -/
  | poss
  /-- Oblique (rare; some Bantu locative agreement). Provided for
      typological completeness. -/
  | obl
  /-- No canonical controller. Weather verbs (Italian *piove*
      [corbett-2006] §2.1.3), defective clausal/infinitival
      controllers (§2.1.2): the target shows default agreement
      (typically 3sg.M in IE languages). -/
  | defaultAgr
  deriving DecidableEq, Repr, Inhabited

end Agreement
