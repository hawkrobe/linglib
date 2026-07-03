import Linglib.Discourse.Gameboard.Defs

/-!
# KOS: LocProp Grounding & CRification
[ginzburg-2012] Ch. 6 §6.5–6.7

The Pending → Facts vs Pending → CR-on-QUD branching for utterance
integration. When a `LocProp` enters the Pending field, the addressee
either *grounds* it (cparams instantiable from addressee beliefs →
content enters FACTS) or *CRifies* it (some cparam not instantiable →
a clarification request question is pushed onto QUD via a CCUR).

## Two integration APIs

This file provides two integration interfaces:

- `integrateLocProp` — the **one-shot stub** (legacy): branches purely on
  whether `lp.cparams` is empty. Sufficient for the binary
  grounding/CRification contrast that downstream studies test, but
  collapses Ginzburg's contextual-instantiation step.
- `integrateLocPropCCUR` — the **multi-stage CCURs pipeline** (faithful):
  Pending Update → Contextual Instantiation → (Grounding | CCUR
  application). Models the §6.6–6.7 protocol where the addressee's
  belief base may witness dgb-params even when `lp.cparams` is non-empty.

Both produce an `IntegrationResult`. The CCUR variant is the one the
Ginzburg2012 §9 grounding-protocol section consumes.

## CCURs (Clarification Context Update Rules)

[ginzburg-2012] Ch. 6 footnote 30 p. 167 introduces "CCURs" as
the renamed and reformulated successors to the 2004 *coercion operations*.
The book posits TWO canonical CCURs (p. 167; full treatments at
ex. 73-79 pp. 192-195 and ex. 80-86 pp. 196-198):

- **Parameter Identification** (constituent CR — "What is the intended
  reference of u_i?", ex. 31 p. 167)
- **Parameter Focussing** (clausal CR — "Was Ariadne asking if JO SREDOVIC
  left?", p. 167)

A third construct, **Repetition CR** (Ginzburg §6.8), is included for
completeness with the caveat that its CCUR-vs-RequestRepeat status is
contested in the book.

## Belief Base

The addressee's `BeliefBase` is modeled as a partial assignment from
cparam indices to string witnesses. In a fuller TTR-typed substrate,
witnesses would be typed values (records); the string version suffices
for paper-replication studies.

## Replaces

The 2004 coercion-operations apparatus (`parameterFocussing`,
`parameterIdentification`, `existentialGeneralization`) is the
predecessor to this protocol; it lives in
`Studies/GinzburgCooper2004.lean` (paper-anchored,
single-consumer demotion).
-/

namespace Discourse.Gameboard

-- ════════════════════════════════════════════════════
-- § 1. LocProp Resolution Predicates
-- ════════════════════════════════════════════════════

/-- Whether a LocProp has all contextual parameters resolved.
A fully resolved LocProp can be grounded directly. -/
def LocProp.isFullyResolved {Cont : Type} (lp : LocProp Cont) : Prop :=
  lp.cparams.length = 0

instance {Cont : Type} (lp : LocProp Cont) : Decidable (lp.isFullyResolved) :=
  inferInstanceAs (Decidable (_ = _))


-- ════════════════════════════════════════════════════
-- § 2. Integration Result
-- ════════════════════════════════════════════════════

/-- The result of integrating a LocProp into a DGB.
Either grounded (content → FACTS) or CRified (CR question → QUD). -/
inductive IntegrationResult (Cont : Type) (QContent : Type*) where
  /-- All cparams resolved: content enters FACTS. -/
  | grounded (content : Cont)
  /-- Some cparam unresolved: CR question pushed onto QUD. -/
  | crification (crQuestion : QContent) (unresolvedParam : CParam)
  deriving Repr

/-- Is this integration result a grounding? -/
def IntegrationResult.isGrounded {Cont : Type} {QContent : Type*} :
    IntegrationResult Cont QContent → Bool
  | .grounded _ => true
  | .crification _ _ => false

-- ════════════════════════════════════════════════════
-- § 3. One-shot Integration (legacy stub)
-- ════════════════════════════════════════════════════

/-- Integrate a LocProp: ground if resolved, CRify otherwise.

The `toCR` function converts an unresolved parameter to a clarification
question — this is domain-specific (e.g., "Who do you mean by 'Bo'?").

**Stub caveat**: this is a one-shot branching version. Ginzburg's actual
integration is a multi-stage pipeline (Pending Update → Contextual
Instantiation → CCURs); use `integrateLocPropCCUR` for the faithful
version that consults addressee beliefs. -/
def integrateLocProp {Cont : Type} {QContent : Type*}
    (lp : LocProp Cont) (toCR : CParam → QContent) :
    IntegrationResult Cont QContent :=
  match lp.cparams with
  | [] => .grounded lp.cont
  | p :: _ => .crification (toCR p) p

/-- A fully resolved LocProp always grounds. -/
theorem resolved_always_grounds {Cont : Type} {QContent : Type*}
    (lp : LocProp Cont) (toCR : CParam → QContent)
    (h : lp.isFullyResolved) :
    (integrateLocProp lp toCR).isGrounded = true := by
  simp only [LocProp.isFullyResolved, List.length_eq_zero_iff] at h
  simp only [integrateLocProp, h, IntegrationResult.isGrounded]

/-- If there are no coercion options and the LocProp has unresolved params,
integration produces a CRification — there is no silent fallback. -/
theorem no_coercion_fallback {Cont : Type} {QContent : Type*}
    (lp : LocProp Cont) (toCR : CParam → QContent) (p : CParam) (ps : CParamSet)
    (h : lp.cparams = p :: ps) :
    (integrateLocProp lp toCR).isGrounded = false := by
  simp only [integrateLocProp, h, IntegrationResult.isGrounded]

-- ════════════════════════════════════════════════════
-- § 4. Belief Base + Contextual Instantiation
-- ════════════════════════════════════════════════════

/-- The addressee's belief base: a partial assignment from cparam indices
to string witnesses.

[ginzburg-2012] eq. 48 (p. 178): contextual instantiation tries to
discharge dgb-params by binding each index to a witness from the
addressee's beliefs. -/
abbrev BeliefBase := List (String × String)

/-- Try to find a witness for a cparam in the belief base. -/
def CParam.instantiate (cp : CParam) (beliefs : BeliefBase) : Option String :=
  (beliefs.find? (·.1 == cp.index)).map (·.2)

/-- The result of contextual instantiation: either every cparam was
witnessed, or some remained unresolved.

[ginzburg-2012] eq. 48 (p. 178). -/
inductive ContextualInstantiationResult where
  /-- All cparams instantiated; the resolved bindings carry the witnesses. -/
  | fullyInstantiated (witnesses : List (String × String))
  /-- Some cparams remain unresolved after consulting beliefs. -/
  | partiallyResolved (resolved : List (String × String)) (unresolved : CParamSet)
  deriving Repr

/-- Attempt to instantiate every cparam of a LocProp from a belief base.
[ginzburg-2012] eq. 48 (p. 178). -/
def contextualInstantiate {Cont : Type} (lp : LocProp Cont) (beliefs : BeliefBase) :
    ContextualInstantiationResult :=
  let resolved : List (String × String) :=
    lp.cparams.filterMap (fun cp =>
      (cp.instantiate beliefs).map (fun w => (cp.index, w)))
  let resolvedIdx : List String := resolved.map (·.1)
  let unresolved : CParamSet :=
    lp.cparams.filter (fun cp => !resolvedIdx.contains cp.index)
  if unresolved.isEmpty then
    .fullyInstantiated resolved
  else
    .partiallyResolved resolved unresolved

/-- Contextual instantiation on an empty cparam list always fully succeeds. -/
theorem contextualInstantiate_empty {Cont : Type} (lp : LocProp Cont)
    (h : lp.cparams = []) (beliefs : BeliefBase) :
    ∃ ws, contextualInstantiate lp beliefs = .fullyInstantiated ws := by
  refine ⟨[], ?_⟩
  unfold contextualInstantiate
  simp [h]

-- ════════════════════════════════════════════════════
-- § 5. CCURs — Clarification Context Update Rules
-- ════════════════════════════════════════════════════

/-- The Clarification Context Update Rules of [ginzburg-2012]
§6.6 (canonical pair) and §6.8 (debated third).

Each CCUR fires when contextual instantiation fails and produces a
specific kind of CR question:

- `parameterIdentification` (Ginzburg ex. 31 p. 167, §6.6 ex. 73-79
  pp. 192-195): target one unresolved cparam, ask "What is the intended
  reference of u_i?" — the constituent CR
- `parameterFocussing` (Ginzburg p. 167, §6.6 ex. 80-86 pp. 196-198):
  abstract over the target's content while instantiating all other
  parameters, ask a confirmation question about the antecedent
  proposition — the clausal CR
- `repetitionCR` (Ginzburg §6.8): a debated CCUR-analog handling
  phonetic repetition requests; included for completeness

These replace the three coercion operations of [ginzburg-cooper-2004]
(`parameterFocussing`, `parameterIdentification`, `existentialGeneralization`),
which now live as paper-specific apparatus in
`Studies/GinzburgCooper2004.lean §0`. The 2004→2012
correspondence: `parameterFocussing` (2004) ↔ `parameterFocussing` (2012);
`parameterIdentification` (both); `existentialGeneralization` (2004) has
no 2012 CCUR analog (the 2012 framework handles it via contextual
instantiation succeeding without a CR being needed). -/
inductive CCUR (Cont : Type) (QContent : Type*) where
  /-- Parameter Identification (Ginzburg ex. 31 p. 167): target one
      unresolved cparam, ask "What is the intended reference of u_i?"
      (constituent CR). -/
  | parameterIdentification (paramIdx : String) (crQuestion : QContent)
  /-- Parameter Focussing (Ginzburg p. 167): abstract over the target's
      content while instantiating all other parameters, ask a
      confirmation question (clausal CR — polar confirmation). -/
  | parameterFocussing (lp : LocProp Cont) (crQuestion : QContent)
  /-- Repetition CR (Ginzburg §6.8): a debated CCUR-analog for phonetic
      repetition requests ("Pardon?"). -/
  | repetitionCR (lp : LocProp Cont) (crQuestion : QContent)
  deriving Repr

/-- Project a CCUR back to its CR question content. -/
def CCUR.crQuestion {Cont : Type} {QContent : Type*} :
    CCUR Cont QContent → QContent
  | .parameterIdentification _ q => q
  | .parameterFocussing _ q => q
  | .repetitionCR _ q => q

-- ════════════════════════════════════════════════════
-- § 6. Multi-stage Integration with CCURs
-- ════════════════════════════════════════════════════

/-- The faithful [ginzburg-2012] §6.6 integration pipeline.

Stages:
1. The LocProp `lp` enters Pending (caller's responsibility).
2. **Contextual Instantiation** (Ginzburg §6.5): consult addressee
   beliefs to instantiate cparams.
3. **Branching**:
   - If fully instantiated → grounding (content enters FACTS)
   - If partial → apply a **CCUR**: this implementation defaults to
     Parameter Identification on the first unresolved cparam (the most
     common case per Ginzburg's worked examples in §6.6, and the form
     instantiated by the running "Did Jo leave?"/"Jo?" example, ex. 31
     p. 167). Choice between `parameterIdentification` and
     `parameterFocussing` depends on whether the target is a
     sub-utterance (former) or the whole utterance (latter).

The `toCR` function constructs the CR question for an unresolved param.

This replaces `integrateLocProp` for substrate uses requiring the
contextual-instantiation step. -/
def integrateLocPropCCUR {Cont : Type} {QContent : Type*}
    (lp : LocProp Cont) (beliefs : BeliefBase) (toCR : CParam → QContent) :
    IntegrationResult Cont QContent :=
  match contextualInstantiate lp beliefs with
  | .fullyInstantiated _ => .grounded lp.cont
  | .partiallyResolved _ unresolved =>
    match unresolved with
    | [] => .grounded lp.cont  -- unreachable: partiallyResolved with empty unresolved
    | p :: _ => .crification (toCR p) p

/-- A fully-resolved LocProp grounds via the CCUR pipeline regardless of
beliefs (since contextual instantiation trivially succeeds with empty
cparams). -/
theorem resolved_grounds_via_ccur {Cont : Type} {QContent : Type*}
    (lp : LocProp Cont) (beliefs : BeliefBase) (toCR : CParam → QContent)
    (h : lp.isFullyResolved) :
    (integrateLocPropCCUR lp beliefs toCR).isGrounded = true := by
  simp only [LocProp.isFullyResolved, List.length_eq_zero_iff] at h
  unfold integrateLocPropCCUR contextualInstantiate
  simp [h, IntegrationResult.isGrounded]

/-- Helper: when every cparam in a LocProp has a witness in the belief
base, contextual instantiation returns `fullyInstantiated`.

Pulls out the `unresolved.isEmpty = true` derivation that
`belief_resolution_grounds_via_ccur` consumes. -/
private theorem contextualInstantiate_fullyInstantiated_of_all_witnessed
    {Cont : Type} (lp : LocProp Cont) (beliefs : BeliefBase)
    (h : ∀ cp ∈ lp.cparams, (cp.instantiate beliefs).isSome) :
    ∃ ws, contextualInstantiate lp beliefs =
      ContextualInstantiationResult.fullyInstantiated ws := by
  unfold contextualInstantiate
  have hempty :
      (lp.cparams.filter (fun cp => !((lp.cparams.filterMap (fun cp' =>
        (cp'.instantiate beliefs).map (fun w => (cp'.index, w)))).map
          (·.1)).contains cp.index)).isEmpty = true := by
    rw [List.isEmpty_iff, List.filter_eq_nil_iff]
    intro cp hcp h_pos
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (h cp hcp)
    have hcontains :
        ((lp.cparams.filterMap (fun cp' =>
          (cp'.instantiate beliefs).map (fun w => (cp'.index, w)))).map
            (·.1)).contains cp.index = true := by
      rw [List.contains_iff_mem, List.mem_map]
      refine ⟨(cp.index, w), ?_, rfl⟩
      rw [List.mem_filterMap]
      exact ⟨cp, hcp, by rw [hw]; rfl⟩
    rw [hcontains] at h_pos
    exact Bool.false_ne_true h_pos
  simp only [hempty, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- A LocProp with cparams but full belief coverage grounds via the CCUR
pipeline. This is the substantive difference from the one-shot stub:
unresolved cparams aren't an automatic CRification trigger when
addressee beliefs witness them. -/
theorem belief_resolution_grounds_via_ccur {Cont : Type} {QContent : Type*}
    (lp : LocProp Cont) (beliefs : BeliefBase) (toCR : CParam → QContent)
    (h : ∀ cp ∈ lp.cparams, (cp.instantiate beliefs).isSome) :
    (integrateLocPropCCUR lp beliefs toCR).isGrounded = true := by
  obtain ⟨_, hws⟩ :=
    contextualInstantiate_fullyInstantiated_of_all_witnessed lp beliefs h
  unfold integrateLocPropCCUR
  rw [hws]
  rfl

end Discourse.Gameboard
