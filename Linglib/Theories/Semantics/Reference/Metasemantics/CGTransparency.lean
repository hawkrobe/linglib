import Linglib.Theories.Semantics.Reference.Metasemantics.Coordination

/-!
# CG transparency: Ney 2026 §3 prima facie challenge
@cite{ney-2026} @cite{king-2013}

@cite{ney-2026} §3 argues that @cite{king-2013}'s coordination account
has a prima facie incompatibility with the observed deniability of
insinuative reference. The argument (Ney's `<ONE>`-`<FOUR>` chain,
pp. 18–19) relies on a closure principle on the common ground:

> `<ONE>` A competent, reasonable and attentive hearer would recognise
> that the speaker intends for the unavowed referent to be a semantic
> value of the insinuatively-used supplementive (i.e. (B) is satisfied).
>
> `<TWO>` It is available from the common ground that the hearer is
> competent, reasonable and attentive (assumption).
>
> `<THREE>` It is available from the common ground that the hearer
> recognises that the speaker intends for the unavowed referent to be
> a semantic value of the insinuatively-used supplementive (from
> `<ONE>` and `<TWO>`).
>
> `<FOUR>` It is available from the common ground that the unavowed
> referent is the semantic value of the insinuatively-used supplementive
> (from `<ONE>` and `<THREE>`).

`<THREE>` contradicts (iib): "it is not in the common ground that the
speaker had the unavowed referential intention". `<FOUR>` contradicts
(iia): "it is not in the common ground that the unavowed referent is
the semantic value".

This file formalizes the closure principle as an abstract
`CGModalOperator` and proves:

- `prima_facie_challenge_kingNeyReconstruction`: under King's binary
  reconstruction (`coordination.kingNeyReconstruction`), if both
  conceptions' coverage of an intention is individually CG-transparent,
  then the success is in CG. The formal core of `<ONE>`+`<TWO>` ⊢
  `<THREE>`.

- `ney_revision_succeeds_without_cgTransparency`: under Ney's revision
  (`coordination.neyRevision`), success can hold without either
  conception being in CG, so the chain breaks. Ney's resolution.

- `king_neyRevision_cg_asymmetry`: the two facts above bundled into a
  single asymmetry statement.

## Why an abstract `CGModalOperator` rather than `commonBelief`

`Theories/Semantics/Modality/EpistemicLogic.lean` already provides
`commonBelief` (line 183). In principle a `CGModalOperator` instance
can be built from `commonBelief` once a `CG.toAgentAccess :
CG W → AgentAccessRel W E` bridge is constructed (the bridge is
independently useful — it would unblock common-ground-conditioned
reasoning across `Phenomena/Anaphora/`, `Phenomena/Presupposition/`,
etc.). For the prima facie challenge we don't need the full S5
machinery — only K-axiom MP and conjunction-introduction — so the
abstract operator gives a tighter formalization. Building the bridge
is a separate task.
-/

namespace Semantics.Reference.Metasemantics

open Core.CommonGround

universe u v w

namespace Account

/-- A common-ground modal operator: `inCG P` says "P is available from
the common ground". Bundles the closure principles
@cite{ney-2026}'s `<ONE>`-`<FOUR>` argument relies on:

- `inCG_K` — modus ponens (K-axiom): `CG (P → Q) → CG P → CG Q`.
- `inCG_and_intro` — conjunction-introduction. Standard for K-systems
  with necessitation; declared directly to avoid importing the full
  necessitation infrastructure.

A concrete instance can be built from `commonBelief` in
`Theories/Semantics/Modality/EpistemicLogic.lean` once a
`CG.toAgentAccess` bridge exists. -/
structure CGModalOperator where
  inCG : Prop → Prop
  inCG_K : ∀ {P Q : Prop}, inCG (P → Q) → inCG P → inCG Q
  inCG_and_intro : ∀ {P Q : Prop}, inCG P → inCG Q → inCG (P ∧ Q)

namespace CGModalOperator

/-- The empty CG operator: nothing is in the common ground. Useful as a
witness for non-transparency claims. K-axiom and and-introduction hold
vacuously since the premises are unsatisfiable. -/
def empty : CGModalOperator where
  inCG := fun _ => False
  inCG_K := fun _ h => h.elim
  inCG_and_intro := fun h _ => h.elim

end CGModalOperator

variable {C : Type u} {W : Type v} {E : Type w}

/-! ## CG transparency of conception coverage -/

/-- `R` is *CG-transparent for s* if, when `R` covers the intention `s`,
this fact is in the common ground. This is the assumption Ney's
`<ONE>`-`<FOUR>` argument relies on (specifically, on the universal
`(B)` clause being CG when satisfied). -/
def CGTransparent (cgOp : CGModalOperator)
    (R : ConceptionOfReasonableness C W E) (s : SpeakerIntention C W E) :
    Prop :=
  R s → cgOp.inCG (R s)

/-! ## The prima facie challenge -/

/-- @cite{ney-2026} §3 prima facie challenge: under @cite{king-2013}'s
binary reconstruction (`kingNeyReconstruction`), if both conceptions
are CG-transparent for the intention, then the account's success is
in CG.

This is the formal version of Ney's `<ONE>`+`<TWO>` ⊢ `<THREE>`:
clause (B) being satisfied is the conjunction `RS s ∧ RH s` (the
"shared" reading of "every reasonable hearer would recognize"); CG-
transparency lifts each conjunct into CG; conjunction-introduction
(K-axiom standard) lifts the whole conjunction into CG; this is
definitionally the success of the account.

The contradiction with @cite{ney-2026}'s observed deniability ((iia),
(iib)) follows: successful insinuative reference requires the success
NOT to be in CG. Hence King's binary reconstruction + standard CG
closure + transparency forces an inconsistency on insinuative cases. -/
theorem prima_facie_challenge_kingNeyReconstruction
    (cgOp : CGModalOperator)
    (RS RH : ConceptionOfReasonableness C W E)
    (s : SpeakerIntention C W E) (cg : CG W)
    (transparentRS : CGTransparent cgOp RS s)
    (transparentRH : CGTransparent cgOp RH s)
    (h_succeeds : coordination.kingNeyReconstruction RS RH s cg) :
    cgOp.inCG (coordination.kingNeyReconstruction RS RH s cg) :=
  cgOp.inCG_and_intro
    (transparentRS h_succeeds.left)
    (transparentRH h_succeeds.right)

/-! ## Ney's resolution -/

/-- A minimal speaker-intention witness over `Bool`: speaker `false`,
intends `true`, with a constant character. Used as the carrier for the
non-transparency existence theorem below. -/
private def witnessIntention : SpeakerIntention Unit Unit Bool where
  speaker     := false
  expression  := { character := fun _ _ => true
                 , profile := ⟨true, true, false⟩ }
  context     := ()
  intendedRef := true

/-- @cite{ney-2026} (end of §4) resolution: under Ney's revision
(`neyRevision`), success can hold without either individual conception
being in CG. The disjunction in `joint₂` requires only one conception
to actually cover the intention; CG-transparency of that conception is
not implied by success, and OR-introduction in CG would require either
conception to be already in CG (which Ney argues isn't the case for
private conceptions).

We exhibit a concrete witness: speaker's conception covers everything,
hearer's covers nothing relevant, neither is in CG. Ney's revision
succeeds (via the speaker's coverage) but no individual transparency
condition holds. -/
theorem ney_revision_succeeds_without_cgTransparency :
    ∃ (RS RH : ConceptionOfReasonableness Unit Unit Bool)
      (s : SpeakerIntention Unit Unit Bool) (cg : CG Unit),
      coordination.neyRevision RS RH s cg ∧
      ¬ CGModalOperator.empty.inCG (RS s) ∧
      ¬ CGModalOperator.empty.inCG (RH s) :=
  ⟨fun _ => True, fun _ => False, witnessIntention, CG.empty,
   Or.inl trivial, id, id⟩

/-! ## The asymmetry -/

/-- Combining the two preceding theorems: King's binary reconstruction
propagates success into CG under individual conception-transparency;
Ney's revision does not. This is the formal counterpart of @cite{ney-2026}'s
claim that the revision dissolves the prima facie challenge. -/
theorem king_neyRevision_cg_asymmetry :
    -- King under transparency forces success into CG
    (∀ (cgOp : CGModalOperator)
       (RS RH : ConceptionOfReasonableness C W E)
       (s : SpeakerIntention C W E) (cg : CG W),
       CGTransparent cgOp RS s → CGTransparent cgOp RH s →
       coordination.kingNeyReconstruction RS RH s cg →
       cgOp.inCG (coordination.kingNeyReconstruction RS RH s cg)) ∧
    -- Ney can succeed without CG-transparency of either conception
    (∃ (RS RH : ConceptionOfReasonableness Unit Unit Bool)
       (s : SpeakerIntention Unit Unit Bool) (cg : CG Unit),
       coordination.neyRevision RS RH s cg ∧
       ¬ CGModalOperator.empty.inCG (RS s) ∧
       ¬ CGModalOperator.empty.inCG (RH s)) :=
  ⟨fun cgOp RS RH s cg trS trH h =>
     prima_facie_challenge_kingNeyReconstruction cgOp RS RH s cg trS trH h,
   ney_revision_succeeds_without_cgTransparency⟩

end Account
end Semantics.Reference.Metasemantics
