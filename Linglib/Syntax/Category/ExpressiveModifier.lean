/-!
# Expressive wh-modifiers: ANDL typology

[pesetsky-1987] [chou-2012] [merchant-2002]
[hoeksema-napoli-2008] [jackendoff-audring-2020]
[chan-shen-2026]

Per-language typological substrate for **aggressively non-D-linked**
(ANDL) wh-modifiers — *the-hell*, *the heck*, *the fuck*, *the devil*,
*the dickens*, *in the world*, *in God's name* (English; [hoeksema-napoli-2008],
[jackendoff-audring-2020]); *daodi* 到底 (Mandarin; [chou-2012]);
*ittai* (Japanese); *ttaeyche* (Korean); *zum-Teufel* (German); etc.

The shared empirical generalization ([pesetsky-1987]): ANDL modifiers
have a distributional restriction that bare wh-words do not. Different
languages and different ANDL items vary along a small set of typological
parameters, formalized here.

## Provenance

Moved from `Core/Lexical/ExpressiveModifier.lean` in the cleanup that
dissolved `Core/Lexical/`. The file's per-language entry-schema +
abstract-licensing-predicate shape (Fragment-importable, syntax-framework-
neutral) matches `Typology/PolarityMarking.lean` and `Typology/Negation.lean`,
not the framework-agnostic substrate shape `Core/` is for.

**Framework commitment.** The parasitic/independent dichotomy
(`ANDLMovementType`) is the single typological parameter
[chan-shen-2026] isolate as distinguishing English/Singlish *the-hell*
from Mandarin *daodi*. This is one carve-up among several in the ANDL
literature — alternatives exist that classify these items by
syntactic category (DP-modifier vs. adverb), by intervention profile,
or by perspectival semantics rather than by movement source. The schema
is intentionally thin: only the Chan-Shen 2026 dimension is encoded;
competing classifications attach as separate predicates in
`Theories/`.

## Out of scope (lives in Theories)

This file does **not** commit to a syntactic framework. It carries no
features, no Spec-CP, no Agree, no AttP. A Minimalist analysis (POV
features [*ud*]/[+d], Spec-head Agree, parasitic adjunction) would live
in `Syntax/Minimalist/ANDL.lean` (planned; not yet present).
The semantic analysis (negative attitude, conventional implicature,
possible-ignorance presupposition) lives in `Pragmatics/Expressives/`
(currently `Basic.lean` + `OutlookMarker.lean`) and
`Syntax/Minimalist/LeftPeriphery.lean`. Fragment
lexemes import only this file.
-/

namespace ExpressiveModifier

/-- How an ANDL modifier reaches its scope-taking position.

    - `parasitic`: must adjoin to the wh-phrase; rides along with
      wh-movement; cannot move on its own. English/Singlish *the-hell*
      ([merchant-2002], [chan-shen-2026]).
    - `independent`: can undergo movement on its own (typically covert)
      to the scope position. Mandarin *daodi* ([chou-2012]).

    This is the single typological parameter [chan-shen-2026]
    isolate as distinguishing English/Singlish *the-hell* from Mandarin
    *daodi*. -/
inductive ANDLMovementType where
  /-- Modifier must adjoin to wh-host; moves only as a passenger. -/
  | parasitic
  /-- Modifier moves on its own to the scope position. -/
  | independent
  deriving DecidableEq, Repr

/-- Where an ANDL modifier scopes — its required host position at
    the end of the derivation. For all currently-attested cases this is
    matrix scope; the abstraction leaves room for future findings of
    e.g. embedded-scope ANDLs. -/
inductive ANDLHostPosition where
  /-- Modifier must reach matrix scope (English, Mandarin, Singlish). -/
  | matrixScope
  /-- Modifier permits embedded scope. (Currently unattested; placeholder.) -/
  | embeddedScopeOk
  deriving DecidableEq, Repr

/-- A theory-neutral lexical entry for an ANDL (aggressively non-D-linked)
    wh-modifier. Carries phonological form, gloss, and the typological
    parameters that determine licensing.

    Theory-specific analyses (POV features, conventional implicature,
    perspectival semantics) attach as separate predicates in
    `Theories/`. -/
structure ExpressiveWhModifier where
  /-- Written form. -/
  form : String
  /-- Gloss (English description). -/
  gloss : String
  /-- Whether the modifier moves parasitically on the wh-phrase or
      independently. -/
  movementType : ANDLMovementType
  /-- Required scope position. -/
  hostPosition : ANDLHostPosition := .matrixScope
  deriving Repr, DecidableEq

/-- Theory-neutral licensing: an ANDL modifier with required scope at
    matrix is licensed iff *some* element (the modifier itself, or its
    wh-host) reaches the scope position.

    Parameters:
    - `m` — the ANDL lexeme
    - `whHostReachesScope` — does the wh-phrase reach matrix scope under
      the strategy in question? (e.g., `WhInterpMechanism.ReachesSpecCP`)

    The predicate is the disjunction: licensed iff host reaches scope
    OR (modifier moves independently to matrix scope on its own).
    Specific theories instantiate `whHostReachesScope` with their own
    structural primitives. -/
def Licensed (m : ExpressiveWhModifier) (whHostReachesScope : Prop) : Prop :=
  whHostReachesScope ∨
  (m.movementType = .independent ∧ m.hostPosition = .matrixScope)

instance (m : ExpressiveWhModifier) (P : Prop) [Decidable P] :
    Decidable (Licensed m P) := by
  unfold Licensed; infer_instance

/-- For a parasitic modifier (`the-hell`-type), licensing reduces to the
    wh-host reaching scope. -/
theorem parasitic_licensed_iff_host_reaches
    {m : ExpressiveWhModifier} (h : m.movementType = .parasitic)
    (P : Prop) :
    Licensed m P ↔ P := by
  simp [Licensed, h]

/-- For an independent modifier (`daodi`-type) with matrix scope, licensing
    holds regardless of whether the host reaches scope. -/
theorem independent_matrix_always_licensed
    {m : ExpressiveWhModifier}
    (hMov : m.movementType = .independent)
    (hHost : m.hostPosition = .matrixScope)
    (P : Prop) :
    Licensed m P :=
  Or.inr ⟨hMov, hHost⟩

end ExpressiveModifier
