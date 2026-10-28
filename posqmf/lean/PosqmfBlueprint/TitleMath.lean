import Verso

/-!
# Inline math in titles

Verso derives a plain-text form of every title, used for instance for the browser tab and the
search index. It has no plain-text form for inline math, which it renders as `<missing>`. This
module gives it one: the source of the math, as written. The navigation buttons likewise show the
source of the math in the titles they link to.

Math in titles is therefore written with Unicode symbols rather than TeX commands where possible,
as in `$`G̃``: KaTeX typesets the combining tilde as an accent, while the plain-text forms show `G̃`.
Chapters with inline math in a title import this module.
-/

open Lean Verso.Doc.Elab

namespace PosqmfBlueprint

/-- The plain-text form of inline math: its source, as written. -/
@[inline_to_string Lean.Doc.Syntax.inline_math]
def inlineMathToString : InlineToString
  | env, .node _ _ #[_, code] => some (inlineToString env code)
  | _, _ => none

end PosqmfBlueprint
