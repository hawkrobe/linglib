import Linglib.Theories.Syntax.Minimalism.Core.VerbalDecomposition

/-!
# Applicative Heads
@cite{cuervo-2003} @cite{pylkknen-2008}

Applicative heads introduce applied arguments (benefactives, goals,
sources) into the verbal structure. The high/low distinction determines
whether the applied argument relates to the event as a whole (high)
or to the theme (low).

Low applicatives further split into **recipient** (transfer *to*) and
**source** (transfer *from*), following @cite{pylkknen-2008} Table 1.1.

-/

namespace Minimalism

/-- High vs low applicatives (@cite{pylkknen-2008}, Table 1.1).

    - **High**: Above VP, relates applied argument to the event
      (benefactive: Chaga "he ate food for wife")
    - **Low recipient**: Below VP, transfer-of-possession *to* the
      applied argument (English DOC: "I sent him a letter")
    - **Low source**: Below VP, transfer-of-possession *from* the
      applied argument (Korean, Hebrew possessor datives, Japanese
      adversity passives) -/
inductive ApplType where
  | high          -- Above VP: individual-event relation (@cite{pylkknen-2008})
  | lowRecipient  -- Below VP: transfer TO applied arg (@cite{pylkknen-2008})
  | lowSource     -- Below VP: transfer FROM applied arg (@cite{pylkknen-2008} §2.2, §2.3)
  deriving DecidableEq, BEq, Repr

/-- Is this a low applicative (either recipient or source)? -/
def ApplType.isLow : ApplType → Bool
  | .lowRecipient => true
  | .lowSource    => true
  | .high         => false

end Minimalism
