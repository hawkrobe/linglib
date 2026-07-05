import Linglib.Features.QParticleLayer
import Linglib.Fragments.German.QuestionParticles
import Linglib.Fragments.Mandarin.QuestionParticles
import Linglib.Semantics.Questions.Bias.Defs

/-!
# Theiler (2021): *Denn* as a Highlighting-Sensitive Particle
[theiler-2021] [zheng-2025] [dayal-2025]

[theiler-2021] analyzes German *denn* as a flavoring particle that
signals the question is prompted by a salient/highlighted proposition
in the discourse context: using *denn* signals that learning the clause's
highlighted content is a necessary precondition for the speaker to proceed
from a salient prior move. The polar/wh asymmetry (denn is freer in
*wh*-questions) follows from highlighting-sensitivity, not from any
contextual-evidence bias.

This study file records *denn*'s left-peripheral layer assignment
within the [dayal-2025] cartography `[SAP [PerspP [CP ...]]]`:
*denn* sits at PerspP, alongside its Mandarin parallel *nandao*
([zheng-2025]). The PerspP analysis predicts that *denn* — like
*nandao* — should be incompatible with subordinated interrogatives.
The point of contrast with *nandao* is the *wh*-question compatibility
of *denn*: *denn* is at the (matrix) PerspP layer but is not restricted
to polar questions.
-/

namespace Theiler2021

open Features (QParticleLayer)

/-- Theiler's layer assignment for *denn*. The `_` argument is unused
    because the layer is a theoretical overlay, not a computed property
    of the fragment entry. -/
def denn_layer (_ : Particle) : QParticleLayer := .perspP

/-- *denn* sits at PerspP, the same layer as Mandarin *nandao*. -/
theorem denn_is_PerspP :
    denn_layer German.QuestionParticles.denn = .perspP := rfl

/-- Theiler's bias classification of *denn*: no contextual-evidence and no
    speaker-bias requirement — the felicity condition is a
    highlighting/precondition relation instead. This is the point on which
    *denn* differs from its evidence-requiring Mandarin parallel *nandao*
    (whose classification lives in `Zheng2025`), and the point on which
    Bayer/Obenauer-style evidence-sensitive analyses of *denn* would
    disagree. -/
def dennBias : Option Semantics.Questions.Bias.ContextualEvidence := none

/-- Unlike Mandarin *nandao*, *denn* is licensed in constituent
    questions. Both are PerspP-layer particles, but *denn* lacks
    *nandao*'s polar-only restriction. Derived from the fragments'
    distribution facets. -/
theorem denn_wh_unlike_nandao :
    German.QuestionParticles.denn.LicensedIn .constituentInterrogative ∧
    ¬ Mandarin.QuestionParticles.nandao.LicensedIn .constituentInterrogative := by
  decide

end Theiler2021
