/-!
# V2

Theory-neutral V2 data: for each clause form, whether verb movement to
second position is observed. Used by `Fragments/{Lang}/V2.lean` files
for descriptive encoding of cross-Germanic V2 variation
(@cite{westergaard-2009}).
-/

namespace Features

structure V2Data where
  name : String
  /-- V2 in root declaratives. -/
  declarativeV2 : Bool
  /-- V2 in wh-questions. -/
  whQuestionV2 : Bool
  /-- V2 in yes/no-questions. -/
  yesNoQuestionV2 : Bool
  /-- V2 in exclamatives. -/
  exclamativeV2 : Bool
  /-- V2 in imperatives. -/
  imperativeV2 : Bool
  /-- V-to-I in embedded finite clauses. (Strictly speaking V-to-I, not
      V-to-C, but kept under the V2Data umbrella for Westergaard's
      micro-parameter table.) -/
  embeddedFinV2 : Bool
  /-- V2 in embedded questions. -/
  embeddedQuestionV2 : Bool
  deriving Repr, DecidableEq

end Features
