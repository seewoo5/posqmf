import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import PosqmfBlueprint.Chapters.Introduction
import PosqmfBlueprint.Chapters.QExpansions
import PosqmfBlueprint.Chapters.KanekoZagier
import PosqmfBlueprint.Chapters.PolynomialModel
import PosqmfBlueprint.Chapters.FFamily
import PosqmfBlueprint.Chapters.GFamily
import PosqmfBlueprint.Chapters.LogInequalities
import PosqmfBlueprint.Chapters.PolymodInequalities
import PosqmfBlueprint.Chapters.ExtremalForms

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.graph.defaultPack true

#doc (Manual) "Positive quasimodular forms in Lean" =>

This is the blueprint of the Lean code in [posqmf](https://github.com/seewoo5/posqmf): the
informal statements and proofs, taken from the papers they come from, linked to the Lean
declarations that formalize them. The main results are also stated in self-contained form in
`posqmf/lean/PosqmfChallenge`, where [Comparator](https://github.com/leanprover/comparator) checks
them against the library.

{include 0 PosqmfBlueprint.Chapters.Introduction}
{include 0 PosqmfBlueprint.Chapters.QExpansions}
{include 0 PosqmfBlueprint.Chapters.KanekoZagier}
{include 0 PosqmfBlueprint.Chapters.PolynomialModel}
{include 0 PosqmfBlueprint.Chapters.FFamily}
{include 0 PosqmfBlueprint.Chapters.GFamily}
{include 0 PosqmfBlueprint.Chapters.LogInequalities}
{include 0 PosqmfBlueprint.Chapters.PolymodInequalities}
{include 0 PosqmfBlueprint.Chapters.ExtremalForms}

{blueprint_graph (direction := LR)}
{blueprint_summary}
{blueprint_bibliography}
