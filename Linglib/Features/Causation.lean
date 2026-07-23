/-!
# Features.Causation
[talmy-1988] [wolff-2003] [karttunen-1971] [nadathur-2023-implicatives]

Per-verb-entry feature taxonomies for causal verb classifications:
the `Causative` enum (force-dynamic mechanism) and the `Implicative`
enum (Karttunen complement-entailment polarity).

## Provenance

Bundled together (rather than 2 separate single-enum files) per the
mathlib idiom of co-locating peer concepts. Moved from
`Core/Lexical/VerbClass.lean` in the cleanup that dissolved `Core/Lexical/`.

## Framework commitment

Both enums here encode specific theoretical commitments rather than
neutral substrate:

- **Causative** (`Causative`): the 5-way `cause/make/force/enable/prevent`
  split is **linglib's extension** of the 3-way force-dynamic taxonomy
  of [wolff-2003] (CAUSE / ENABLE / PREVENT). The substrate
  subdivides Wolff's CAUSE category into `{cause, make, force}` to
  carry the counterfactual-dependence (`cause`) vs direct-sufficient-
  guarantee (`make`) vs coercive-sufficiency (`force`) distinctions
  that [talmy-1988] discusses but does not crystallize as named
  primitives. The `assertsSufficiency`/`assertsNecessity`/`isCoercive`/
  `isPermissive` derivations match the [nadathur-lauer-2020]
  sufficiency/necessity decomposition.

  Major non-force-dynamic frameworks for causation:
  - [comrie-1989] typological scale (lexical / morphological /
    syntactic causatives, with implications for productivity).
  - Shibatani 1976 / Shibatani & Pardeshi 2002 directness typology
    (direct vs indirect causation correlating with morphological vs
    analytic encoding); not currently in `references.bib`.
  - [pylkkanen-2008] Voice/Cause-head theory (where the cause
    head is a separately licensed functional element).
  None of these carve verbs into exactly the 5 cases here.

  See `Semantics/Causation/Interpretation.lean` for the
  force-dynamic mapping to truth conditions; alternative analyses live
  in sibling Theories files.

- **Implicative** (`Implicative`): the binary positive/negative split
  is the [karttunen-1971] bipartition. Finer-grained alternatives:
  Karttunen 2012 / Nairn et al. 2006 9-way matrix (`++`/`+-`/`-+`/
  `--`/`+o`/`o+`/`-o`/`o-`/`oo`) capturing both one-direction and
  two-direction implications, and update-semantics revisions that
  treat implicativity as projection through context rather than direct
  entailment. The substrate fixes 2 cases; richer frameworks need their
  own enum (planned slot:
  `Semantics/Implicative/NairnCondoravdiKarttunen.lean`).

UNVERIFIED: Shibatani 1976 / Shibatani & Pardeshi 2002 publication
details and Karttunen 2012 / Nairn-Condoravdi-Karttunen 2006 9-way
matrix details cited from memory; verify before adding to
`references.bib`.
-/

namespace Features

-- ════════════════════════════════════════════════════
-- § 1. Causative (force-dynamic mechanism)
-- ════════════════════════════════════════════════════

/-- How a causative verb's semantics is built from causal model infrastructure.

    Names a **force-dynamic mechanism**, not a causal-model property.
    `toSemantics` (in `Semantics/Causation/Interpretation.lean`)
    maps each variant to its truth-condition function; properties like
    sufficiency/necessity are derived via theorems.

    - `cause`: Counterfactual dependence — removing cause blocks effect.
    - `make`: Direct sufficient guarantee — adding cause ensures effect.
    - `force`: Coercive sufficiency — overcome resistance, no alternatives.
    - `enable`: Permissive — remove barrier so effect can occur.
    - `prevent`: Blocking — add barrier so effect cannot occur. -/
inductive Causative where
  /-- Counterfactual dependence: removing cause → no effect.
      Semantic function: `causeSem`. -/
  | cause
  /-- Direct sufficient guarantee: adding cause → effect.
      Semantic function: `causallySufficient`. -/
  | make
  /-- Coercive sufficiency: overcome resistance, no alternatives.
      Same truth conditions as `make`; distinguished by `isCoercive`. -/
  | force
  /-- Permissive: remove barrier so effect can occur.
      Same truth conditions as `make`; distinguished by `isPermissive`. -/
  | enable
  /-- Blocking: add barrier so effect cannot occur.
      Semantic function: `preventSem` (dual of `causeSem`). -/
  | prevent
  deriving DecidableEq, Repr

namespace Causative

/-- Does this variant assert causal sufficiency ([nadathur-lauer-2020]'s
    definition (23))?

    DERIVED: true for variants whose `toSemantics` maps to `causallySufficient`. -/
def assertsSufficiency : Causative → Bool
  | .make | .force | .enable => true
  | .cause | .prevent => false

/-- Does this variant assert causal necessity ([nadathur-lauer-2020]'s
    definition (24))?

    DERIVED: true only for `.cause`, whose `toSemantics` maps to `causeSem`. -/
def assertsNecessity : Causative → Bool
  | .cause => true
  | _ => false

/-- Does this variant encode coercion (overcoming resistance)?

    Force-dynamic property: `.force` encodes that the causer overcame
    the causee's resistance. -/
def isCoercive : Causative → Bool
  | .force => true
  | _ => false

/-- Does this variant encode permissivity (barrier removal)?

    Force-dynamic property: `.enable` encodes that the causer removed
    a barrier, allowing the effect to occur naturally. -/
def isPermissive : Causative → Bool
  | .enable => true
  | _ => false

end Causative

-- ════════════════════════════════════════════════════
-- § 2. Implicative (Karttunen 1971 polarity)
-- ════════════════════════════════════════════════════

/-- Polarity for implicative verbs.

    Positive implicatives (*manage*, *remember*) entail the complement on success.
    Negative implicatives (*fail*, *forget*) entail the complement does NOT hold
    on success.

    Note: `Implicative` and `Causative` are structurally different
    ([nadathur-2023-implicatives]): causatives directly predicate causation (make/cause →
    sufficiency/necessity), while implicatives predicate a prerequisite whose
    causal relationship to the complement is only presupposed. -/
inductive Implicative where
  | positive   -- manage, remember: success → complement true
  | negative   -- fail, forget: success → complement NOT true
  deriving DecidableEq, Repr

namespace Implicative

/-- Whether the verb entails the complement (positive) or its negation (negative). -/
def entailsComplement : Implicative → Bool
  | .positive => true
  | .negative => false

end Implicative

end Features
