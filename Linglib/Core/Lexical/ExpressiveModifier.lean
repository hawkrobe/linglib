/-!
# Expressive Wh-Modifiers: Aggressively Non-D-Linked (ANDL) Items

@cite{pesetsky-1987} @cite{chou-2012} @cite{merchant-2002}
@cite{hoeksema-napoli-2008} @cite{jackendoff-audring-2020}
@cite{chan-shen-2026}

Theory-neutral lexical infrastructure for **aggressively non-D-linked**
(ANDL) wh-modifiers — *the-hell*, *the heck*, *the fuck*, *the devil*,
*the dickens*, *in the world*, *in God's name* (English; @cite{hoeksema-napoli-2008},
@cite{jackendoff-audring-2020}); *daodi* 到底 (Mandarin; @cite{chou-2012});
*ittai* (Japanese); *ttaeyche* (Korean); *zum-Teufel* (German); etc.

The shared empirical generalization (@cite{pesetsky-1987}): ANDL modifiers
have a distributional restriction that bare wh-words do not. Different
languages and different ANDL items vary along a small set of typological
parameters, formalized here.

## Out of scope (lives in Theories)

This file does **not** commit to a syntactic framework. It carries no
features, no Spec-CP, no Agree, no AttP. The Minimalist analysis (POV
features [*ud*]/[+d], Spec-head Agree, parasitic adjunction) lives in
`Theories/Syntax/Minimalism/ANDL.lean`. The semantic analysis
(negative attitude, conventional implicature, possible-ignorance
presupposition) lives in `Theories/Pragmatics/Expressives/` and
`Theories/Interfaces/SyntaxSemantics/LeftPeriphery.lean`. Fragment
lexemes import only this file.
-/

namespace Core.Lexical.ExpressiveModifier

/-- How an ANDL modifier reaches its scope-taking position.

    - `parasitic`: must adjoin to the wh-phrase; rides along with
      wh-movement; cannot move on its own. English/Singlish *the-hell*
      (@cite{merchant-2002}, @cite{chan-shen-2026}).
    - `independent`: can undergo movement on its own (typically covert)
      to the scope position. Mandarin *daodi* (@cite{chou-2012}).

    This is the single typological parameter @cite{chan-shen-2026}
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

end Core.Lexical.ExpressiveModifier
