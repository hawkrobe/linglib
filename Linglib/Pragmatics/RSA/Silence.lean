import Linglib.Pragmatics.RSA.Operators

/-!
# Silence as a null alternative
[bergen-levy-goodman-2016]

`WithSilence U := Option U` is the standard wrapper that adds a "silence"
element to any utterance type: `none` is silence, `some u` a paper-utterance.
`liftMeaning` gives silence universal extension — true at every world —
following the null utterance of [bergen-levy-goodman-2016], which is true in
every world so that the speaker always has an honest option.

**Deviation from the source**: [bergen-levy-goodman-2016] disfavor their null
utterance by *cost* (it is the most expensive alternative), and observe that a
sufficiently cheap null utterance *is* used in the fully ignorant knowledge
state. This costless rendering disfavors silence by informativity alone:
universal extension gives it the smallest literal-listener value (`1/card W`
under the `extensionOf`-based literal listener), so the softmax speaker
prefers any honest informative utterance, and silence absorbs all probability
exactly where none exists. That dissolves the "no `qOk` witness" defect that
would otherwise make some observation cells vacuous in PMF formalizations of
[goodman-stuhlmuller-2013]-style models (whose own utterance sets have no
null utterance).

## Main definitions

- `WithSilence U` — `Option U`, where `none` = silence.
- `liftMeaning m` — extends `m : U → W → Bool` to `WithSilence U → W → Bool`,
  with silence true at every world.
- `extensionOf_liftMeaning_none` — silence's extension is the whole world
  space.

## Per-paper specialisations

The "cover hypothesis is universally satisfied because silence is always
`qOk`" theorem is paper-specific (because `qOk` depends on the paper's
observation type and compatibility predicate). Each consumer paper proves
its own `cover_silent` as a 1-line application of `liftMeaning_none`.
-/

namespace RSA

variable {U W : Type*}

/-- Silence-extended utterance type. `some u` is a paper-utterance;
`none` is the "say nothing" alternative.

Definitionally `Option U` so it inherits all standard instances
(`DecidableEq`, `Fintype`, `Repr`, `Inhabited`) without manual derivation. -/
abbrev WithSilence (U : Type*) := Option U

/-- Lift a meaning function to handle silence. Silence is "vacuously honest"
— true at every world (commits to nothing). -/
def liftMeaning (m : U → W → Bool) : WithSilence U → W → Bool
  | some u, w => m u w
  | none,   _ => true

@[simp] theorem liftMeaning_some (m : U → W → Bool) (u : U) (w : W) :
    liftMeaning m (some u) w = m u w := rfl

@[simp] theorem liftMeaning_none (m : U → W → Bool) (w : W) :
    liftMeaning m none w = true := rfl

/-! ### The extension of silence

Universal truth makes silence's extension the whole world space — the
largest possible, hence the smallest uniform literal-listener value. -/

variable [Fintype W]

@[simp] theorem extensionOf_liftMeaning_none (m : U → W → Bool) :
    extensionOf (liftMeaning m) (none : WithSilence U) = Finset.univ := by
  ext w; simp

theorem card_extensionOf_liftMeaning_none (m : U → W → Bool) :
    (extensionOf (liftMeaning m) (none : WithSilence U)).card = Fintype.card W := by
  simp

/-- Every paper-utterance's extension is contained in silence's. -/
theorem extensionOf_liftMeaning_some_subset (m : U → W → Bool) (u : U) :
    extensionOf (liftMeaning m) (some u) ⊆ extensionOf (liftMeaning m) none := by
  simp

end RSA
