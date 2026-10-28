import VersoManual
import VersoBlueprint.PreviewManifest
import PosqmfBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

/-- Generator entry point of the blueprint site (`lake exe vbp build`). -/
def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc PosqmfBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
