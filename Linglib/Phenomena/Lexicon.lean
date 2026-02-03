/-
# Phenomena Lexicon (Re-export)

This module re-exports from `Linglib.Phenomena.Core.Lexicon` for backwards compatibility.
New code should import `Linglib.Phenomena.Core.Lexicon` directly.
-/

import Linglib.Phenomena.Core.Lexicon

-- Re-export everything from Core.Lexicon
export Lexicon (
  a an the this that these some_ every many few
  john mary
  boy girl man dog cat_ book ball table pizza
  boys girls dogs cats books balls
  i you he she we they
  me him her us them
  himself herself themselves
  who what
  sleep sleeps laugh laughs arrives leave
  see sees saw eat eats eaten reads buy bought sell met kicks kicked chased devours
  gives gives_dat sends puts
  think wonder
  do_ does did can was
  to on by_ before
  that_c if_ because
  and_ or_
  happy smart old wise
)
