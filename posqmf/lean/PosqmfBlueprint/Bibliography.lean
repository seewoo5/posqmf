import VersoManual
import VersoBlueprint

/-!
# Bibliography of the blueprint

Each entry is registered with `@[bib]` and cited from the chapters with `Informal.citep` and
`Informal.citet`.
-/

open Verso.Genre.Manual

namespace PosqmfBlueprint.Bibliography

@[bib "lee2026sign"]
def lee2026sign : Bibliography.Citable := .arXiv
  { title := inlines!"Positive quasimodular forms and the sign uncertainty principle"
    authors := #[inlines!"Seewoo Lee"]
    year := 2026
    id := "2608.15415" }

@[bib "lee2026polymod"]
def lee2026polymod : Bibliography.Citable := .arXiv
  { title := inlines!"Inequalities involving polynomials and quasimodular forms"
    authors := #[inlines!"Seewoo Lee"]
    year := 2026
    id := "2602.10536" }

@[bib "lee2026thesis"]
def lee2026thesis : Bibliography.Citable := .thesis
  { title := inlines!"Positive quasimodular forms and linear programming bounds"
    author := inlines!"Seewoo Lee"
    year := 2026
    university := inlines!"University of California, Berkeley"
    degree := inlines!"PhD"
    url := some "https://escholarship.org/uc/item/2j65b950" }

@[bib "lee2024algebraic"]
def lee2024algebraic : Bibliography.Citable := .arXiv
  { title := inlines!"Algebraic proof of modular form inequalities for optimal sphere packings"
    authors := #[inlines!"Seewoo Lee"]
    year := 2024
    id := "2406.14659" }

@[bib "bourgain2010principe"]
def bourgain2010principe : Bibliography.Citable := .article
  { title := inlines!"Principe d'Heisenberg et fonctions positives"
    authors := #[inlines!"Jean Bourgain", inlines!"Laurent Clozel", inlines!"Jean-Pierre Kahane"]
    journal := inlines!"Annales de l'Institut Fourier"
    year := 2010
    month := none
    volume := inlines!"60"
    number := inlines!"4"
    pages := some (1215, 1232) }

@[bib "cohn2019optimal"]
def cohn2019optimal : Bibliography.Citable := .article
  { title := inlines!"An optimal uncertainty principle in twelve dimensions via modular forms"
    authors := #[inlines!"Henry Cohn", inlines!"Felipe Gonçalves"]
    journal := inlines!"Inventiones mathematicae"
    year := 2019
    month := none
    volume := inlines!"217"
    number := inlines!"3"
    pages := some (799, 831) }

@[bib "feigenbaum2021eigenfunctions"]
def feigenbaum2021eigenfunctions : Bibliography.Citable := .article
  { title := inlines!"Eigenfunctions of the Fourier transform with specified zeros"
    authors := #[inlines!"Ahram S. Feigenbaum", inlines!"Peter J. Grabner",
      inlines!"Douglas P. Hardin"]
    journal := inlines!"Mathematical Proceedings of the Cambridge Philosophical Society"
    year := 2021
    month := none
    volume := inlines!"171"
    number := inlines!"2"
    pages := some (329, 367) }

@[bib "kaneko2006extremal"]
def kaneko2006extremal : Bibliography.Citable := .article
  { title := inlines!"On extremal quasimodular forms"
    authors := #[inlines!"Masanobu Kaneko", inlines!"Masao Koike"]
    journal := inlines!"Kyushu Journal of Mathematics"
    year := 2006
    month := none
    volume := inlines!"60"
    number := inlines!"2"
    pages := some (457, 470) }

@[bib "kaneko1998supersingular"]
def kaneko1998supersingular : Bibliography.Citable := .article
  { title := inlines!"Supersingular j-invariants, hypergeometric series, and Atkin's orthogonal polynomials"
    authors := #[inlines!"Masanobu Kaneko", inlines!"Don Zagier"]
    journal := inlines!"AMS/IP Studies in Advanced Mathematics"
    year := 1998
    month := none
    volume := inlines!"7"
    number := inlines!""
    pages := some (97, 126) }

@[bib "kaneko2017third"]
def kaneko2017third : Bibliography.Citable := .article
  { title := inlines!"The third order modular linear differential equations"
    authors := #[inlines!"Masanobu Kaneko", inlines!"Kiyokazu Nagatomo", inlines!"Yuichi Sakai"]
    journal := inlines!"Journal of Algebra"
    year := 2017
    month := none
    volume := inlines!"485"
    number := inlines!""
    pages := some (332, 352) }

@[bib "cohn2022universal"]
def cohn2022universal : Bibliography.Citable := .article
  { title := inlines!"Universal optimality of the E8 and Leech lattices and interpolation formulas"
    authors := #[inlines!"Henry Cohn", inlines!"Abhinav Kumar", inlines!"Stephen D. Miller",
      inlines!"Danylo Radchenko", inlines!"Maryna Viazovska"]
    journal := inlines!"Annals of Mathematics"
    year := 2022
    month := none
    volume := inlines!"196"
    number := inlines!"3"
    pages := some (983, 1082) }

@[bib "pellarin2020extremal"]
def pellarin2020extremal : Bibliography.Citable := .article
  { title := inlines!"On extremal quasi-modular forms after Kaneko and Koike"
    authors := #[inlines!"Federico Pellarin"]
    journal := inlines!"Kyushu Journal of Mathematics"
    year := 2020
    month := none
    volume := inlines!"74"
    number := inlines!"2"
    pages := some (401, 413) }

@[bib "deligne1974weil"]
def deligne1974weil : Bibliography.Citable := .article
  { title := inlines!"La conjecture de Weil. I"
    authors := #[inlines!"Pierre Deligne"]
    journal := inlines!"Publications Mathématiques de l'IHÉS"
    year := 1974
    month := none
    volume := inlines!"43"
    number := inlines!""
    pages := some (273, 307) }

end PosqmfBlueprint.Bibliography
