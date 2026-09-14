import Linglib.Semantics.Evidential.Defs

/-!
# Mandarin Chinese evidentiality

Mandarin Chinese has no grammatical evidentials: information source is conveyed lexically, by
*tīngshuō* 听说 'hear say', *juéde* 觉得 'feel' and the sentence-final particle *ba* 吧.

## References

* [aikhenvald-2004]
* [de-haan-2013]
-/

namespace Mandarin.Evidentiality

/-- No evidentials; lexical strategies only. -/
def evidentials : List Evidential := []

end Mandarin.Evidentiality
