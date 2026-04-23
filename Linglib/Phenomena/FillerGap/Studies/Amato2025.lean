import Linglib.Theories.Syntax.Minimalism.NestedAgree

/-!
# @cite{amato-2025} — Filler-gap case studies via Nested Agree

@cite{amato-2025} (NLLT) §4.2.3 extends Nested Agree from Agree
features to **Merge features**, deriving order-preserving multiple
wh-fronting in Bulgarian (and Romanian) from a probe stack on C
where the Merge probe `[•wh•]` is restricted by Nested Agree to the
last goal of the prior Agree probe `[*wh*]`. This file collects the
Amato-2025 case studies whose primary phenomenon is filler-gap
dependency formation.

Currently only the Bulgarian case (§4.2.3) lands here. Other
filler-gap-adjacent Amato-2025 material (none in the published §4)
would land in this file as additional sub-namespaces.

## Cross-domain validation thesis

`NestedAgreeConfig` was originally designed against an Agree-feature
case (Italian aux selection). Bulgarian uses *Merge* features —
formally identical at the abstract layer (a probe is a probe), but
linguistically distinct (movement vs valuation). That the same
`NestedAgreeConfig` shape models Bulgarian without API changes
validates the abstraction's neutrality between Agree and Merge.

## Out of scope

The Bulgarian formalization captures the **structural Nested-Agree
restriction** on the Merge probe — the central §4.2.3 claim that
post-Agree Merge is constrained to the prior Agree's last goal. It
does *not* capture:

- **Multiple Agree** on the prior probe (`[*wh*]` actually hits both
  wh-sbj and wh-obj sequentially; we abstract by setting the goal
  to wh-obj, the last hit). Multiple Agree as a primitive would
  require `runStack` to return `List Token` rather than
  `Option Token` — a substantive API extension deferred until a
  case study genuinely needs it.
- **Probe restart**: in Amato's full derivation, after wh-obj raises
  to inner Spec,C, the Merge probe re-discharges to raise wh-sbj to
  outer Spec,C. We model only the *first* movement step.
- **Movement itself**: `SyntacticObject` is static. The post-movement
  tree (with wh-obj in Spec,C and a trace below) is not constructed
  here. The structural claim about the *pre-movement* configuration
  is what the Nested-Agree theorem captures.

Honest scope: we prove that Nested Agree's matryoshka excludes
wh-sbj from the Merge probe's truncated domain at the relevant
derivational step. The full multi-step Bulgarian fronting derivation
is future work.
-/

namespace Phenomena.FillerGap.Studies.Amato2025

open Minimalism
open Minimalism.NestedAgree

-- ════════════════════════════════════════════════════════════════════════════
-- Part A: §4.2.3 — Bulgarian multiple wh-fronting
-- ════════════════════════════════════════════════════════════════════════════

/-! ## Part A: Bulgarian multiple wh-fronting (Amato §4.2.3)

Bulgarian permits (and requires) multiple wh-phrases to front to the
left periphery, in **order-preserving** fashion: when a sentence has
both a wh-subject and a wh-object, the surface order is wh-sbj > wh-obj
matching base-merge order, *not* the order standard minimality would
predict (which would require wh-sbj first regardless of base order).

@cite{amato-2025} §4.2.3 derives order-preservation from Nested Agree
applied to Merge features:

1. C bears `[*wh*] ≻ [•wh•]` — Agree feature first, Merge feature
   second.
2. `[*wh*]` undergoes Multiple Agree: hits wh-sbj first (closest),
   then extends to wh-obj. Last goal: wh-obj.
3. `[•wh•]` by Nested Agree must target the same goal as the prior
   probe → wh-obj. wh-obj raises to inner Spec,C.
4. (Out of scope) `[•wh•]` re-discharges; finds wh-sbj; raises it to
   outer Spec,C. Surface: outer Spec,C > inner Spec,C → wh-sbj > wh-obj.

This file formalizes step (3): the structural Nested-Agree restriction
on the Merge probe. The wh-sbj is in C's c-command (probe 0's domain)
but excluded from wh-obj's daughters (probe 1's truncated domain).
This is the same `apparent_intervener_excluded` structure that
applied to Italian DPsubj, Icelandic DPdat, and Lak Erg — modulo
the Agree-vs-Merge distinction at the consumer level. -/

namespace Bulgarian

/-- The C head bearing the wh-features. -/
private def aC : LIToken := ⟨LexicalItem.simple .C [], 0⟩
/-- The wh-subject in Spec,T. Apparent intervener for the Merge
    probe at the relevant derivational step. -/
private def aWhSbj : LIToken := ⟨LexicalItem.simple .D [], 1⟩
/-- The lexical V (irrelevant for the Nested Agree derivation but
    present structurally between wh-sbj and wh-obj). -/
private def aV : LIToken := ⟨LexicalItem.simple .V [], 2⟩
/-- The wh-object in Spec,v. Last goal of `[*wh*]` Multiple Agree;
    chosen goal of `[•wh•]` by Nested Agree. -/
private def aWhObj : LIToken := ⟨LexicalItem.simple .D [], 3⟩

/-- C's probe with C-area horizon. Both `[*wh*]` and `[•wh•]` use
    this profile; the Agree-vs-Merge distinction is at the consumer
    interpretive layer, not at the abstract `NestedAgreeConfig` level. -/
private def cProbe : ProbeProfile := ⟨.C, none⟩

/-- Bulgarian multi-wh configuration at the relevant derivational
    step (post-Multiple-Agree, pre-movement). Pre-movement tree:
    `C [wh-sbj [V wh-obj]]`, goal = wh-obj (the last token Multiple
    Agree reached, what Nested Agree forces the Merge probe to also
    target). The Agree-vs-Merge distinction between probes 0 and 1
    is implicit in the linguistic interpretation, not in the
    abstract config. -/
def bulgarianMultiWh : NestedAgreeConfig :=
  standardConfig cProbe aC aWhSbj aV aWhObj aWhObj (fun _ => true)

theorem bulgarianMultiWh_is_nested :
    IsNestedAgreeConfig bulgarianMultiWh := by decide

theorem bulgarianMultiWh_runStack_0 :
    runStack bulgarianMultiWh 0 = some (.leaf aWhObj) := by decide

theorem bulgarianMultiWh_runStack_1 :
    runStack bulgarianMultiWh 1 = some (.leaf aWhObj) := by decide

/-- **Apparent wh-subject intervention is not actual.** The
    wh-subject is in C's c-command (probe 0's full domain) but is
    *not* in wh-obj's daughters (wh-obj doesn't c-command wh-sbj —
    wh-sbj is structurally above wh-obj). So wh-sbj is excluded from
    probe 1's truncated domain by Nested Agree.

    This is the central §4.2.3 derivational claim: the Merge probe
    `[•wh•]`, restricted by Nested Agree to the last Agree goal
    (= wh-obj), cannot target wh-sbj even though wh-sbj is the
    structurally closer wh-phrase. wh-obj raises first; wh-sbj is
    raised in the (out-of-scope) restart phase. -/
theorem bulgarianMultiWh_excludes_wh_subject :
    SyntacticObject.leaf aWhSbj ∈ bulgarianMultiWh.searchDomain 0 ∧
    SyntacticObject.leaf aWhSbj ∉ bulgarianMultiWh.searchDomain 1 :=
  apparent_intervener_excluded bulgarianMultiWh 0 (.leaf aWhSbj)
    (by decide) (by decide)

end Bulgarian

end Phenomena.FillerGap.Studies.Amato2025
