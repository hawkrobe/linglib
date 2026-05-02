import Mathlib.Init

set_option autoImplicit false

/-!
# Silence as a low-prior alternative
@cite{bergen-levy-goodman-2016}

`WithSilence U := Option U` is the standard wrapper that adds a "silence"
element to any utterance type. `none` represents silence; `some u` represents
a paper-utterance.

Following @cite{bergen-levy-goodman-2016}, silence has universal extension
(`liftMeaning` makes it true at every world), giving it the smallest lex
value (`1/card W`) under the standard `extensionOf`-based literal listener.
This disfavors silence at the softmax when stronger utterances are honest.
At observations where no non-silent utterance is honest, silence absorbs
all probability — dissolving the "no `qOk` witness" defect that would
otherwise make `(access, word) ∉ {sensible}` cases vacuous in PMF
formalizations of @cite{goodman-stuhlmuller-2013}-style models.

## Main definitions

- `WithSilence U` — `Option U`, where `none` = silence.
- `liftMeaning m` — extends `m : U → W → Bool` to `WithSilence U → W → Bool`,
  with silence true at every world.

## Per-paper specialisations

The "cover hypothesis is universally satisfied because silence is always
`qOk`" theorem is paper-specific (because `qOk` depends on the paper's
observation type and compatibility predicate). Each consumer paper proves
its own `cover_silent` as a 1-line application of `liftMeaning_none`.
-/

namespace RSA

/-- Silence-extended utterance type. `some u` is a paper-utterance;
`none` is the "say nothing" alternative.

Definitionally `Option U` so it inherits all standard instances
(`DecidableEq`, `Fintype`, `Repr`, `Inhabited`) without manual derivation. -/
abbrev WithSilence (U : Type*) := Option U

/-- Lift a meaning function to handle silence. Silence is "vacuously honest"
— true at every world (commits to nothing).

This is the canonical lifting that makes silence the universally-qOk
fallback: at any observation, the only worlds the speaker considers are
those compatible with the obs, and silence is true at all of them
trivially. -/
def liftMeaning {U W : Type*} (m : U → W → Bool) : WithSilence U → W → Bool
  | some u, w => m u w
  | none,   _ => true

@[simp] theorem liftMeaning_some {U W : Type*} (m : U → W → Bool) (u : U) (w : W) :
    liftMeaning m (some u) w = m u w := rfl

@[simp] theorem liftMeaning_none {U W : Type*} (m : U → W → Bool) (w : W) :
    liftMeaning m none w = true := rfl

end RSA
