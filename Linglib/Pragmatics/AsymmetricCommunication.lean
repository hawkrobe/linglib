import Linglib.Pragmatics.InformationTheory.Channel

/-!
# Asymmetric Communication Models
@cite{xu-etal-2024} @cite{milroy-milroy-1985} @cite{labov-2011}

A communicative interaction in which **speaker and listener operate on
different lexicons / different channels**. The canonical case is
variation/innovation diffusion: a speaker has acquired a novel encoding
`E*`, the listener has not yet, so the speaker's production policy is
conditioned on `L'` while the listener's interpretation is conditioned
on `L` (@cite{xu-etal-2024} §2.1).

This generalizes the standard symmetric Shannon setup
(@cite{kemp-regier-2012}, @cite{zaslavsky-kemp-regier-tishby-2018}, where
speaker and listener share one channel) and serves as substrate for any
linguistic-modeling case in which the two ends of a communication act
have different generative models. Concrete uses:

- Lexicalization spread (@cite{xu-etal-2024})
- Iterated learning (parent / child generation mismatch;
  @cite{kirby-tamariz-cornish-smith-2015})
- L1 / L2 communicative accommodation
- Native / non-native listener mismatch in adaptation studies

## Two layers

`ChannelAccess` is a bare-bones non-finite, non-normalized score function
`C → W → ℝ` — the most general view of "what a participant returns when
asked about (concept, form)". `CommChannel` (in `InformationTheory/Channel.lean`)
is the Shannon-strength version (finite alphabets + row-stochastic).
`CommChannel.toAccess` projects the latter onto the former. `AsymmetricCommModel`
holds two `ChannelAccess`es so it can be instantiated either by lifting two
`CommChannel`s (`ofCommChannels`) or by stipulating two arbitrary score
functions over a non-finite type (e.g., `String`-valued lexicons).
-/

set_option autoImplicit false

namespace Pragmatics.Communication

/-- Bare-bones channel access: a score function `C → W → ℝ` with no
    finiteness or normalization constraints. The minimal interface
    needed to compute per-pair surprisals. -/
abbrev ChannelAccess (C W : Type*) : Type _ := C → W → ℝ

end Pragmatics.Communication

/-- Project a Shannon `CommChannel` onto its bare access function.
    Lives in `Pragmatics.InformationTheory` so dot notation
    `ch.toAccess` resolves. -/
def Pragmatics.InformationTheory.CommChannel.toAccess
    {C W : Type} [Fintype C] [Fintype W]
    (ch : Pragmatics.InformationTheory.CommChannel C W) :
    Pragmatics.Communication.ChannelAccess C W := ch.encode

namespace Pragmatics.Communication

open Pragmatics.InformationTheory

/-- A two-channel communication model: speaker uses `produce`, listener
    uses `comprehend`. The asymmetry is structural — `produce` and
    `comprehend` are independent fields and may disagree.

    @cite{xu-etal-2024}'s headline conceptual move over @cite{kemp-regier-2012}
    and @cite{zaslavsky-kemp-regier-tishby-2018}: the speaker's production
    policy is conditioned on the expanded lexicon `L'` while the listener's
    interpretation is conditioned on the existing lexicon `L`. This
    structural distinction lives in the variation-theory tradition of
    @cite{labov-2011} and @cite{milroy-milroy-1985}. -/
structure AsymmetricCommModel (C W : Type*) where
  /-- Speaker channel `p(w | c, L')`. -/
  produce : ChannelAccess C W
  /-- Listener channel `p(w | c, L)` (or, equivalently, the listener's
      score function for inferring `c` from `w` under their lexicon). -/
  comprehend : ChannelAccess C W

namespace AsymmetricCommModel

variable {C W : Type*}

/-- Symmetric special case: speaker and listener share one channel.
    Recovers the Kemp-Regier / Zaslavsky setup as
    `AsymmetricCommModel.symmetric ch`. -/
def symmetric (ch : ChannelAccess C W) : AsymmetricCommModel C W :=
  ⟨ch, ch⟩

/-- Construct an asymmetric model from two finite-alphabet
    `CommChannel`s — one for the speaker on `L'`, one for the listener
    on `L`. -/
def ofCommChannels {C W : Type} [Fintype C] [Fintype W]
    (speakerCh listenerCh : CommChannel C W) :
    AsymmetricCommModel C W :=
  ⟨speakerCh.toAccess, listenerCh.toAccess⟩

/-- An asymmetric model is symmetric iff its two channels coincide as
    functions. -/
def IsSymmetric (m : AsymmetricCommModel C W) : Prop :=
  m.produce = m.comprehend

@[simp] theorem symmetric_isSymmetric (ch : ChannelAccess C W) :
    (symmetric ch).IsSymmetric := rfl

@[simp] theorem symmetric_produce (ch : ChannelAccess C W) :
    (symmetric ch).produce = ch := rfl

@[simp] theorem symmetric_comprehend (ch : ChannelAccess C W) :
    (symmetric ch).comprehend = ch := rfl

end AsymmetricCommModel

end Pragmatics.Communication
