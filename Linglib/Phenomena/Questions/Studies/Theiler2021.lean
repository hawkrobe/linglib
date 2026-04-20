import Linglib.Theories.Semantics.Questions.QParticleLayer
import Linglib.Fragments.German.QuestionParticles
import Linglib.Fragments.Mandarin.QuestionParticles

/-!
# Theiler (2021): *Denn* as a Highlighting-Sensitive Particle
@cite{theiler-2021} @cite{zheng-2025} @cite{dayal-2025}

@cite{theiler-2021} analyzes German *denn* as a flavoring particle that
signals the question is prompted by a salient/highlighted proposition
in the discourse context. In polar questions this manifests as an
evidential-bias requirement; in *wh*-questions it merely signals
informational need.

This study file records *denn*'s left-peripheral layer assignment
within the @cite{dayal-2025} cartography `[SAP [PerspP [CP ...]]]`:
*denn* sits at PerspP, alongside its Mandarin parallel *nandao*
(@cite{zheng-2025}). The PerspP analysis predicts that *denn* — like
*nandao* — should be incompatible with subordinated interrogatives.
The point of contrast with *nandao* is the *wh*-question compatibility
of *denn*: *denn* is at the (matrix) PerspP layer but is not restricted
to polar questions.
-/

namespace Phenomena.Questions.Studies.Theiler2021

open Semantics.Questions (QParticleLayer)

/-- Theiler's layer assignment for *denn*. The `_` argument is unused
    because the layer is a theoretical overlay, not a computed property
    of the fragment entry. -/
def denn_layer (_ : Fragments.German.QuestionParticles.QParticleEntry) : QParticleLayer := .perspP

/-- *denn* sits at PerspP, the same layer as Mandarin *nandao*. -/
theorem denn_is_PerspP :
    denn_layer Fragments.German.QuestionParticles.denn = .perspP := rfl

/-- *denn* requires evidential bias — the highlighting/salience condition
    is what surfaces as a positive-evidential requirement in polar
    questions. This connects the PerspP assignment to the bias profile
    in the fragment. -/
theorem denn_evidential :
    Fragments.German.QuestionParticles.denn.requiresEvidentialBias = true := rfl

/-- Unlike Mandarin *nandao*, *denn* is compatible with *wh*-questions.
    Both are PerspP-layer particles requiring evidential bias, but
    *denn* lacks the polar-only restriction. -/
theorem denn_wh_unlike_nandao :
    Fragments.German.QuestionParticles.denn.whOk = true ∧
    Fragments.Mandarin.QuestionParticles.nandao.whOk = false := ⟨rfl, rfl⟩

end Phenomena.Questions.Studies.Theiler2021
