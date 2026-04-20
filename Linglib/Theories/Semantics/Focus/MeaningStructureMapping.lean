/-!
# The Meaning-Structure Mapping Hypothesis (MSMH)
@cite{kiss-1998} @cite{hartmann-zimmermann-2007}

The MSMH — proposed in different forms by @cite{kiss-1998} (eq. 9) and
sharpened by @cite{hartmann-zimmermann-2007} (eq. 21) — is the
typological claim that focus *position* determines focus
*interpretation*: utterances whose focused constituent occupies the same
structural position must receive the same focus interpretation.

The empirical content varies by language:
- **Hungarian** @cite{kiss-1998}: preverbal Spec,FP ↔ identificational
  (exhaustive); postverbal in-situ ↔ information (non-exhaustive). Same
  position forces same focus type. *Validated.*
- **Hausa** @cite{hartmann-zimmermann-2007}: both ex-situ and in-situ
  host all four pragmatic uses of focus (new-info, corrective,
  selective, contrastive). Same strategy admits different
  interpretations. *Refuted.*

The polymorphic predicate `MeaningStructureMapping` here makes the
shape of the hypothesis explicit, so per-language study files can
instantiate it with their concrete utterance type, structural
projection, and interpretation projection. A `licensed` filter
restricts the universal to grammatical configurations — necessary for
Hungarian (where the 2×2 product of `Position × FocusType` includes
ungrammatical cells) and harmless for Hausa (whose refutation already
uses licensed witnesses).
-/

namespace Theories.Semantics.Focus.MSMH

/-- **Meaning-Structure Mapping Hypothesis** in fully polymorphic form.
    Reads: among admissible utterances, having the same structural
    property forces having the same interpretation.

    Type parameters:
    - `U` — the utterance type (e.g., `FocusUtterance`, `FocusConfig`)
    - `S` — the structural property type (e.g., `Strategy`, `Position`)
    - `I` — the interpretation type (e.g., `PragType`, `FocusType`)

    Function arguments:
    - `licensed` — admissibility filter (e.g., grammatical/well-formed)
    - `struct`   — projection from utterance to structural property
    - `interp`   — projection from utterance to interpretation -/
def MeaningStructureMapping {U S I : Type}
    (licensed : U → Prop) (struct : U → S) (interp : U → I) : Prop :=
  ∀ u₁ u₂ : U, licensed u₁ → licensed u₂ →
    struct u₁ = struct u₂ → interp u₁ = interp u₂

/-- Standard refutation pattern: any pair of licensed utterances that
    agree on `struct` but disagree on `interp` falsifies MSMH. Used by
    the Hausa study file to refute the hypothesis from the matrix of
    eight licensed cells. -/
theorem refute_by_witness {U S I : Type}
    {licensed : U → Prop} {struct : U → S} {interp : U → I}
    (u₁ u₂ : U) (h₁ : licensed u₁) (h₂ : licensed u₂)
    (hstruct : struct u₁ = struct u₂) (hinterp : interp u₁ ≠ interp u₂) :
    ¬ MeaningStructureMapping licensed struct interp := by
  intro h
  exact hinterp (h u₁ u₂ h₁ h₂ hstruct)

end Theories.Semantics.Focus.MSMH
