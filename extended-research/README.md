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
  - `DirichletGRH` + `nonvanishing_of_dirichlet_factorization` — the abelian
    rung, concretely plugged: `DirichletGRH` is the exact shape of the parent
    project's proven theorem (`Main.lean: LFunction_ne_zero_of_half_lt_re`);
    given a Kronecker-Weber factorization `ζ_K = ∏ L(χ)` into Dirichlet
    L-functions, the proven GRH immediately yields nonvanishing of `ζ_K`
    right of the critical line (pole `s = 1` handled). What remains for the
    abelian case is the factorization itself (hypothesis in Lean;
    DirichletGRH is the parent-proven shape, not imported).
  - **The ℚ(i) / two-squares rung (abelian gate, reduced)**:
    `nonvanishing_of_dirichlet_family` (mixed-conductor Dirichlet products),
    `dedekindZeta_eq_riemannZeta_mul_LFunction_of_convolution` (coefficient
    identity ⟹ `ζ_K = ζ · L(ψ)` via `LSeries_convolution`), and
    `dedekindERH_quadratic_of_twoSquares` (rung assembled via the datum
    construction; remaining input: the two-squares count — note
    DirichletGRH is a hypothesis, not imported).
  - **Hecke rung, interface**: `ERHFamily` + `dedekindERH_of_heckeERH` — ζ_K
    is the Hecke L of the trivial Grössencharakter, so ERH for any family
    containing ζ_K gives `DedekindERH K`. The analytic supply (idele-class
    Hecke characters, continuation, FE) is the rung's remaining content.
  - **Artin rung, reduction step**: `ArtinBrauerDatum` + 
    `nonvanishing_of_artin_brauer` — an Artin L-function with Brauer
    decomposition data (finite product of Hecke-type factors with integer
    exponents, as supplied by Brauer induction over cyclic subgroups) is
    nonvanishing right of the critical line as soon as its factors are.
    Together with `dedekindERH_of_heckeERH` and the mirror adapter this is
    the complete logical bridge **"Hecke ERH + Brauer ⟹ Artin ERH"**.
  - **The `ζ_ℚ` glue (new lemma, not previously in Mathlib)**:
    `card_ideal_rat_absNorm` — exactly one ideal of `𝓞 ℚ` per absolute norm,
    via `Rat.ringOfIntegersEquiv`, `Algebra.norm_eq_of_algEquiv`, and the PID
    structure of `ℤ` transported through `RingEquiv.idealComapOrderIso` —
    culminating in
    `dedekindZeta_rat_eq_riemannZeta : NumberField.dedekindZeta ℚ s = riemannZeta s`
    on the half-plane `1 < Re s`.
  - **The full loop for `K = ℚ`**: `riemannZetaDatum`, a `DedekindZetaDatum ℚ`
    whose anchor field (`agrees`) is *proved* from the glue theorem rather
    than assumed; `dedekindERH_rat_of_RH : RiemannHypothesis →
    DedekindERH ℚ riemannZetaDatum` and the converse bridge
    `riemannHypothesis_of_dedekindERH_rat` (the parent project's mirror step
    `Formalism.VW.rh_of_right` replayed on the datum), giving
    `riemannHypothesis_iff_dedekindERH_rat` — the machine-verified Riemann
    Hypothesis and the ERH statement for `ℚ` are *equivalent*.

  Axiom footprint (verified by `#print axioms` for all theorems above):
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

1. **DONE** — glue `ζ_ℚ = riemannZeta`: `card_ideal_rat_absNorm` (exactly one
   ideal of `𝓞 ℚ` per absolute norm) and `dedekindZeta_rat_eq_riemannZeta`
   connect Mathlib's Dedekind zeta of `ℚ` to `riemannZeta`; the anchored
   datum `riemannZetaDatum` and `dedekindERH_rat_of_RH` then turn the
   machine-verified Riemann Hypothesis into the ERH statement for `ℚ`.
   The `K = ℚ` rung of the ladder is closed, in both directions
   (`riemannHypothesis_iff_dedekindERH_rat`).
2. **Abelian case end-to-end**: formalize Kronecker–Weber + the conductor
   factorization `ζ_K = ∏ L(χ)`; then `abelianDedekindERH` closes ERH for all
   abelian `K` from the parent project's GRH. Cyclotomic ingredients already
   exist in the parent archive (`ReciprocityTheory/Chebotarev/`).
3. **Hecke characters and Hecke L-functions** (the *interfaces* are done:
   `ERHFamily`, `dedekindERH_of_heckeERH`, `nonvanishing_of_artin_brauer`;
   what remains is the analytic construction) (idele-class characters, algebraic
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
