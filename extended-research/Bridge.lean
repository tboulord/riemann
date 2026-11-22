/-
Bridge to the base project's proof: discharges the last hypothesis of the ℚ(i) result.

`HorizonERH` proves `dedekindERH_QI_of_statement : DirichletLNonvanishingRightOfHalf →
∀ D, DedekindERH QI D`, where `DirichletLNonvanishingRightOfHalf` is the base project's own
statement (`src/Statements.lean`). `src/Main.lean` proves that statement as
`LFunction_ne_zero_of_half_lt_re`. This file plugs one into the other.

It is NOT checked by CI: importing `Main` needs a full build of the base tree
(175,177 modules in the import closure of `Main`; several CPU-days). To check it:
  lake build Main            -- full base build
  lake build Bridge          -- or: lake env lean extended-research/Bridge.lean
and confirm the `#print axioms` line shows only `propext`, `Classical.choice`, `Quot.sound`.
-/
import HorizonERH
import Main

/-- **ERH for `ℚ(i)`**, with no remaining hypothesis beyond the base project's proof:
every zero of the continued Dedekind zeta of `ℚ(i) = CyclotomicField 4 ℚ` with
`Re s > 1/2` is the pole `s = 1`, for every continuation datum. -/
theorem dedekindERH_QI_unconditional (D : DedekindZetaDatum GaussianERH.QI) :
    DedekindERH GaussianERH.QI D :=
  dedekindERH_QI_of_statement LFunction_ne_zero_of_half_lt_re D

/-- Critical-line form of the same result. -/
theorem dedekindZeta_QI_zeros_on_line_unconditional (D : DedekindZetaDatum GaussianERH.QI) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → D.ζ s = 0 → s.re = 1 / 2 :=
  dedekindZeta_QI_zeros_on_line LFunction_ne_zero_of_half_lt_re D

#print axioms dedekindERH_QI_unconditional
#print axioms dedekindZeta_QI_zeros_on_line_unconditional
