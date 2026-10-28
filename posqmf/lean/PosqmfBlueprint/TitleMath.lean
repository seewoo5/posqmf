import Verso

/-!
# Inline math in titles

Verso derives a plain-text form of every title, used for instance for the browser tab and the
search index. It has no plain-text form for inline math, which it renders as `<missing>`. This
module gives it one: the TeX source, with `\widetilde{x}` written as `x̃`. Chapters with inline
math in a title import it.

The previous/next buttons do not use this plain-text form: they show the TeX source of the math in
the titles they link to.
-/

open Lean Verso.Doc.Elab

namespace PosqmfBlueprint

/-- Writes `\widetilde{x}` as `x` followed by a combining tilde, and keeps any other TeX as is. -/
def untilde (tex : String) : String :=
  match tex.splitOn "\\widetilde{" with
  | [] => tex
  | first :: rest =>
    first ++ String.join (rest.map fun part =>
      match part.splitOn "}" with
      | arg :: after => arg ++ "̃" ++ "}".intercalate after
      | [] => part)

/-- The plain-text form of inline math: its TeX source, with tildes written as in `untilde`. -/
@[inline_to_string Lean.Doc.Syntax.inline_math]
def inlineMathToString : InlineToString
  | env, .node _ _ #[_, code] => some (untilde (inlineToString env code))
  | _, _ => none

end PosqmfBlueprint
