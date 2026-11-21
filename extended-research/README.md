# Extended research: toward the Extended Riemann Hypothesis (ERH)

This folder contains **independent follow-up research** building on the Lean-formalized
proof of GRH for Dirichlet L-functions announced by Levent Alpöge (Anthropic) on
2026-11-20 (`https://alpo.ge/remark.pdf`) and machine-verified on 2026-11-21
(all 175,187 modules compiled; independent kernel replays by A. Sutherland, MIT —
`https://math.mit.edu/~drew/grh`).

**Nothing in this folder is part of that proof.** It is forward-looking work:
formal foundations for the extension the author announced as *expected* but did
not include — the Extended Riemann Hypothesis for Hecke/Artin L-functions
(Dedekind zeta functions of number fields) — and for studying the reach of the
theta-lift "manufactured multiplicity" engine beyond the Dirichlet family.

## Contents

* `HorizonERH.lean` — machine-checked foundations, compiled against the *same*
  toolchain and Mathlib revision as the original archive
  (Lean `v4.33.1`, mathlib `0df444a360ea`):

  - `mirror_lemma` — the abstract functional-equation adapter: no zeros strictly
    right of the critical line + completed functional equation (nonzero root
    number, zero-free gamma factor) ⇒ every critical-strip zero lies exactly on
    `Re = 1/2`. This generalizes the role of `Formalism.VW.critLine` in the
    original project to *any* L-function (Dirichlet, Hecke, Artin, automorphic).
  - `DedekindZetaDatum K` — interface packaging the meromorphic continuation of
    `ζ_K`, its completed form, gamma factor and functional equation as data
    (Mathlib defines `NumberField.dedekindZeta` only where the L-series converges).
  - `DedekindERH` — the target statement of the ERH extension for `ζ_K`.
  - `dedekindZetaCriticalLine` — instantiation of the adapter for `ζ_K`.
  - `nonvanishing_right_of_product` / `abelianDedekindERH` — the abelian-case
    reduction: given a factorization of `ζ_K` into finitely many Dirichlet
    L-functions (Kronecker–Weber), GRH-Dirichlet — already proved in the parent
    project — immediately yields ERH for `K`.
  - `gammaR_ne_zero_of_re_pos`, `completedRiemannZeta_eq_gammaR_mul_riemannZeta`,
    `riemannZetaCriticalLine` — the interface instantiated on Mathlib's *own*
    Riemann zeta (`K = ℚ`): the completed factor `Gammaℝ` is zero-free on the
    right half-plane, `Λ(s) = Gammaℝ(s) · ζ(s)`, and Mathlib's zeta passes
    through the mirror adapter. Built from genuine Mathlib theorems only
    (`riemannZeta_def_of_ne_zero`, `completedRiemannZeta_one_sub`,
    `Complex.Gamma_ne_zero_of_re_pos`).

  Axiom footprint (verified by `#print axioms` for all seven theorems):
  `propext`, `Classical.choice`, `Quot.sound` only — no `sorryAx`.

## How to compile

From the repository root (the Lake workspace of the parent project), with the
Lean toolchain `leanprover/lean4:v4.33.1` installed (elan reads `lean-toolchain`):

```bash
lake exe cache get                               # fetch pinned deps + Mathlib binary cache
lake env lean extended-research/HorizonERH.lean  # elaborates; prints axiom footprints
```

A **manual CI pipeline** is provided at `.github/workflows/lean-manual.yml`
(GitHub Actions, `workflow_dispatch`): it fetches the Mathlib cache, elaborates
`extended-research/HorizonERH.lean` (or any files given as input), and fails if
compilation fails or if any `#print axioms` output contains `sorryAx`. It can
also be given an optional lake build target (e.g. `Statements`). Building all
175,187 modules of the parent project is out of reach for CI runners
(~1–2 weeks of CPU).

## Roadmap (research directions, in increasing order of difficulty)

1. **Glue `ζ_ℚ = riemannZeta` in Mathlib** — prove that Mathlib's
   `NumberField.dedekindZeta ℚ` L-series equals `riemannZeta` where both are
   defined (classification of ideals of `ℤ`); together with
   `riemannZetaCriticalLine` this connects `DedekindERH` for `K = ℚ` to the
   already-proven Riemann Hypothesis. Small effort.
2. **Abelian case end-to-end**: formalize Kronecker–Weber + the conductor
   factorization `ζ_K = ∏ L(χ)`; then `abelianDedekindERH` closes ERH for all
   abelian `K` from the parent project's GRH. Cyclotomic ingredients already
   exist in the parent archive (`ReciprocityTheory/Chebotarev/`).
3. **Hecke characters and Hecke L-functions** (idele-class characters, algebraic
   Hecke characters; analytic continuation and functional equation via Mathlib's
   `WeakFEPair` framework). Definitional work; months.
4. **The engine extension**: run the parent project's theta-lift chains
   (`ThetaCorrespondence/`, `ThetaParseval/`) over the idele class group of a
   number field. This is the open research step the author flagged as
   "expected with more time".
5. **Artin L-functions**: Brauer induction (a `GroundTheory/Brauer` tower exists
   in the parent archive) + Artin formalism reduce the Artin case to the Hecke
   case. Consequences: Artin's primitive root conjecture (Hooley), effective
   Chebotarev.

## Status disclaimer

These are research foundations, not results about the Riemann Hypothesis itself.
Any statement *proved* here is conditional on hypotheses explicitly packaged as
data (e.g. `DedekindZetaDatum`); discharging those hypotheses for general number
fields is precisely the open work described in the roadmap.
