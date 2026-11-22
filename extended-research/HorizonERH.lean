/-
Horizon ERH — blueprint for extending the (now verified) GRH-Dirichlet project
to Dedekind zeta functions of number fields, i.e. the Extended Riemann
Hypothesis in the sense of the author's remark ("the method easily extends").

This file is machine-checked against Mathlib (leanprover/lean4:v4.33.1,
mathlib @ 0df444a360ea) — the same toolchain and Mathlib revision as the
alpo.ge RH/GRH archive.

Contents:
* `mirror_lemma`     — the abstract functional-equation adapter: no zeros right
                       of the critical line + completed FE with nonzero root
                       number and zero-free gamma factor  ⇒  all critical-strip
                       zeros lie exactly on Re = 1/2. This is the piece that
                       `Formalism.VW.critLine` plays in the GRH-Dirichlet proof,
                       isolated here so ANY future L-function (Hecke, Artin,
                       automorphic) can reuse it verbatim.
* `DedekindZetaDatum` — an interface for a Dedekind zeta with its analytic
                       continuation and functional equation (Mathlib defines
                       `NumberField.dedekindZeta` only as an L-series where it
                       converges, so the continuation is packaged as data).
* `dedekindZetaCriticalLine` — instantiation of the adapter for ζ_K.
* `DedekindERH`       — the target statement of the ERH extension.

Everything below compiles with `lake env lean HorizonERH.lean`.
-/

import Mathlib

set_option linter.style.haveILetI false
-- `lake env lean` does not apply the lakefile's `leanOptions`; without this, an unknown
-- identifier in a statement is silently auto-bound as an extra hypothesis.
set_option autoImplicit false

open Complex NumberField

/-! ## The abstract mirror adapter -/

/-- Abstract "completed L-function" adapter. If an L-function `L` has:
* a completed form `Λ = γ · L` on the open critical strip,
* a functional equation `Λ s = ε · Λ (1 - s)` with root number `ε ≠ 0`,
* a factor `γ` that is zero-free on the open critical strip, and
* no zeros of `L` strictly right of the critical line,
then every zero of `L` inside the critical strip lies exactly on the line. -/
theorem mirror_lemma {L Λ γ : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hγ : ∀ s : ℂ, 0 < s.re → s.re < 1 → γ s ≠ 0)
    (hΛ : ∀ s : ℂ, 0 < s.re → s.re < 1 → Λ s = γ s * L s)
    (hfe : ∀ s : ℂ, Λ s = ε * Λ (1 - s))
    (hz : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → L s ≠ 0) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → L s = 0 → s.re = 1 / 2 := by
  intro s hs0 hs1 hL
  rcases lt_trichotomy s.re (1 / 2 : ℝ) with h | h | h
  · exfalso
    -- completion vanishes at s
    have hΛs : Λ s = 0 := by rw [hΛ s hs0 hs1, hL, mul_zero]
    -- so it vanishes at the mirror point 1 - s
    have hΛm : Λ (1 - s) = 0 := by
      have h1 : Λ (1 - s) = ε⁻¹ * Λ s := by
        have h2 := hfe s
        rw [h2, ← mul_assoc, inv_mul_cancel₀ hε, one_mul]
      rw [h1, hΛs, mul_zero]
    -- the mirror point lies strictly right of the line, inside the strip
    have hm0 : 0 < (1 - s).re := by
      rw [sub_re, one_re]; linarith
    have hm1 : (1 - s).re < 1 := by
      rw [sub_re, one_re]; linarith
    have hmhalf : 1 / 2 < (1 - s).re := by
      rw [sub_re, one_re]; linarith
    -- there, Λ = γ * L with γ ≠ 0 and L ≠ 0 : Λ cannot vanish
    have hγm : γ (1 - s) ≠ 0 := hγ (1 - s) hm0 hm1
    have hLm : L (1 - s) ≠ 0 := hz (1 - s) hmhalf hm1
    rw [hΛ (1 - s) hm0 hm1] at hΛm
    rcases mul_eq_zero.1 hΛm with h | h
    · exact hγm h
    · exact hLm h
  · exact h
  · exact absurd hL (hz s h hs1)

/-! ## ERH for Dedekind zeta functions -/

variable (K : Type*) [Field K] [NumberField K]

/-- Interface for the Dedekind zeta function of a number field together with
the analytic ingredients needed to state its Riemann Hypothesis. Mathlib's
`NumberField.dedekindZeta` is (so far) only the L-series in its convergence
half-plane; the meromorphic continuation `ζ`, the completed form `Λ`, the
gamma-type factor `γ` (zero-free on the strip) and the functional equation are
packaged here as data, since establishing them is part of the ERH project. -/
structure DedekindZetaDatum where
  /-- Meromorphic continuation of ζ_K. -/
  ζ : ℂ → ℂ
  /-- Completed zeta Λ(s) = γ(s) · ζ_K(s) on the critical strip. -/
  Λ : ℂ → ℂ
  /-- Archimedean (gamma-type) factor of the completion. -/
  γ : ℂ → ℂ
  /-- Root number of the functional equation. -/
  ε : ℂ
  /-- The continuation agrees with Mathlib's L-series where the latter
  converges (some half-plane Re(s) > bound > 1). -/
  agrees :
    ∃ bound : ℝ, 1 < bound ∧
      Set.EqOn ζ (NumberField.dedekindZeta K) {s : ℂ | bound < s.re}
  hε : ε ≠ 0
  /-- The gamma factor is zero-free on the open critical strip. -/
  hγ : ∀ s : ℂ, 0 < s.re → s.re < 1 → γ s ≠ 0
  /-- Completion identity on the open critical strip. -/
  hΛζ : ∀ s : ℂ, 0 < s.re → s.re < 1 → Λ s = γ s * ζ s
  /-- Functional equation of the completed zeta. -/
  hfe : ∀ s : ℂ, Λ s = ε * Λ (1 - s)
  /-- The continuation is holomorphic away from the pole `s = 1`. Together with
  `agrees`, this pins `ζ` down uniquely (identity theorem, see
  `DedekindZetaDatum.ζ_eqOn`): `ζ` is *the* meromorphic continuation of `ζ_K`,
  not an arbitrary function agreeing with the L-series. -/
  holo : DifferentiableOn ℂ ζ {s : ℂ | s ≠ 1}

/-- The ERH statement for ζ_K, relative to a continuation datum:
every zero with `Re(s) > 1/2` is the pole `s = 1`. -/
def DedekindERH (D : DedekindZetaDatum K) : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → D.ζ s ≠ 0

/-- Instantiation of the mirror adapter: for the Dedekind zeta of any number
field, "no zeros right of the critical line" forces all critical-strip zeros
onto the line — the exact shape of `Formalism.VW.critLine`, now available for
every number field, ready for the Hecke/Artin extension. -/
theorem dedekindZetaCriticalLine (D : DedekindZetaDatum K)
    (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → D.ζ s ≠ 0) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → D.ζ s = 0 → s.re = 1 / 2 :=
  mirror_lemma D.hε D.hγ D.hΛζ D.hfe
    (fun s hs0 hs1 =>
      hz s hs0 (fun hs => by rw [hs, Complex.one_re] at hs1; norm_num at hs1))

/-- **Uniqueness of the continuation.** Two data for the same number field have
the same `ζ` away from `s = 1`: both are holomorphic on the connected open set
`ℂ \ {1}` and agree with Mathlib's L-series on a right half-plane, so the identity
theorem forces them to coincide. -/
theorem DedekindZetaDatum.ζ_eqOn {K : Type*} [Field K] [NumberField K]
    (D₁ D₂ : DedekindZetaDatum K) : Set.EqOn D₁.ζ D₂.ζ {s : ℂ | s ≠ 1} := by
  obtain ⟨b₁, hb₁, h₁⟩ := D₁.agrees
  obtain ⟨b₂, hb₂, h₂⟩ := D₂.agrees
  have hU : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hconn : IsPreconnected {s : ℂ | s ≠ 1} := by
    have h := (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) (1 : ℂ)).isPreconnected
    rwa [Set.compl_singleton_eq] at h
  let z₀ : ℂ := ((max b₁ b₂ + 1 : ℝ) : ℂ)
  have hz₀re : z₀.re = max b₁ b₂ + 1 := Complex.ofReal_re _
  have hz₀ : z₀ ∈ {s : ℂ | s ≠ 1} := by
    intro h
    have h' := congrArg Complex.re h
    rw [hz₀re, Complex.one_re] at h'
    have := le_max_left b₁ b₂
    linarith
  have hev : D₁.ζ =ᶠ[nhds z₀] D₂.ζ := by
    have hopen : IsOpen {s : ℂ | max b₁ b₂ < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hmem : z₀ ∈ {s : ℂ | max b₁ b₂ < s.re} := by
      show max b₁ b₂ < z₀.re
      rw [hz₀re]; linarith
    filter_upwards [hopen.mem_nhds hmem] with s hs
    have hs₁ : b₁ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₂ : b₂ < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    rw [h₁ hs₁, h₂ hs₂]
  exact (D₁.holo.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    (D₂.holo.analyticOnNhd hU) hconn hz₀ hev

/-- Consequently `DedekindERH K D` does not depend on the datum `D`: it is a
property of the number field `K` alone. -/
theorem dedekindERH_iff {K : Type*} [Field K] [NumberField K]
    (D₁ D₂ : DedekindZetaDatum K) : DedekindERH K D₁ ↔ DedekindERH K D₂ := by
  constructor
  · intro h s hs hs1
    rw [← D₁.ζ_eqOn D₂ hs1]
    exact h s hs hs1
  · intro h s hs hs1
    rw [D₁.ζ_eqOn D₂ hs1]
    exact h s hs hs1

#print axioms DedekindZetaDatum.ζ_eqOn
#print axioms dedekindERH_iff

/-! ## The abelian case: reduction to Dirichlet GRH (Kronecker-Weber) -/

/-- Arithmetic glue for the abelian case: if a function factors on a right
half-plane as a finite product of L-functions, each of which is nonvanishing
for `Re(s) > 1/2` away from the point `s = 1` (where a principal-character
factor may have its pole), then the product is nonvanishing for `Re(s) > 1/2`
away from `s = 1`. -/
theorem nonvanishing_right_of_product {ι : Type*} (t : Finset ι)
    (L : ι → ℂ → ℂ) (f : ℂ → ℂ) {bound : ℝ} (hb : bound ≤ 1 / 2)
    (hmul : ∀ z : ℂ, bound < z.re → f z = ∏ i ∈ t, L i z)
    (hnz : ∀ i ∈ t, ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → L i z ≠ 0) :
    ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → f z ≠ 0 := by
  intro z hz hz1
  have hbound : bound < z.re := by linarith
  rw [hmul z hbound, Finset.prod_ne_zero_iff]
  exact fun i hi => hnz i hi z hz hz1

/-- **The abelian case of ERH follows from Dirichlet GRH.** For an abelian
extension, Kronecker-Weber identifies `ζ_K` with a finite product of Dirichlet
L-functions; since the parent project proved that every Dirichlet L-function is
nonvanishing for `Re(s) > 1/2` (`UpperTheory.EveryCharacter`), this theorem
turns such a factorization into the ERH statement for `K`. -/
theorem abelianDedekindERH {K : Type*} [Field K] [NumberField K] (D : DedekindZetaDatum K)
    {ι : Type*} (t : Finset ι) (L : ι → ℂ → ℂ) {bound : ℝ} (hb : bound ≤ 1 / 2)
    (hmul : ∀ z : ℂ, bound < z.re → D.ζ z = ∏ i ∈ t, L i z)
    (hnz : ∀ i ∈ t, ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → L i z ≠ 0) :
    DedekindERH K D :=
  fun z hz hz1 => nonvanishing_right_of_product t L D.ζ hb hmul hnz z hz hz1

/-! ## The interface instantiated on Mathlib's own Riemann zeta -/

/-- Mathlib's completed zeta factor `Gammaℝ s = π ^ (-s/2) * Γ(s/2)` is
zero-free whenever `0 < Re s`: the exponential factor never vanishes and
`Γ` is zero-free on the right half-plane (`Complex.Gamma_ne_zero_of_re_pos`). -/
theorem gammaR_ne_zero_of_re_pos {s : ℂ} (hs0 : 0 < s.re) : Gammaℝ s ≠ 0 := by
  rw [Gammaℝ]
  refine mul_ne_zero ?_ ?_
  · refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
    exact_mod_cast Real.pi_ne_zero
  · refine Complex.Gamma_ne_zero_of_re_pos ?_
    rw [Complex.div_re]
    simp
    linarith

/-- On the right half-plane, Mathlib's completed zeta factors as
`Λ(s) = Gammaℝ(s) · ζ(s)`. -/
theorem completedRiemannZeta_eq_gammaR_mul_riemannZeta {s : ℂ} (hs0 : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have h0 : s ≠ 0 := by
    intro e; rw [e] at hs0; simp at hs0
  have hΓ : Gammaℝ s ≠ 0 := gammaR_ne_zero_of_re_pos hs0
  rw [riemannZeta_def_of_ne_zero h0]
  field_simp

/-- Mathlib's functional equation in the shape consumed by `mirror_lemma`. -/
theorem completedRiemannZeta_one_sub_mul (s : ℂ) :
    completedRiemannZeta s = 1 * completedRiemannZeta (1 - s) := by
  rw [one_mul]
  exact (completedRiemannZeta_one_sub s).symm

/-- Mathlib's own Riemann zeta passes through the mirror adapter: if it has no
zeros strictly right of the critical line, all its critical-strip zeros lie on
the line. Built from genuine Mathlib objects — no hypotheses beyond Mathlib's
own theorems. This is the `K = ℚ` seed of the ERH interface, and the exact
shape the parent project realized as `Formalism.VW.rh_of_right`. -/
theorem riemannZetaCriticalLine
    (hz : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 :=
  mirror_lemma one_ne_zero (fun _ hs0 _ => gammaR_ne_zero_of_re_pos hs0)
    (fun _ hs0 _ => completedRiemannZeta_eq_gammaR_mul_riemannZeta hs0)
    completedRiemannZeta_one_sub_mul
    hz

#print axioms mirror_lemma
#print axioms dedekindZetaCriticalLine
#print axioms nonvanishing_right_of_product
#print axioms abelianDedekindERH

/-- The exact shape of the parent project's proven theorem
(`Main.lean`: `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi`):
every Dirichlet L-function is nonvanishing right of the critical line, apart
from the principal character at its pole `s = 1`. -/
def DirichletGRH : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- **The abelian rung, concretely plugged**: if `ζ_K` factors as a finite
product of Dirichlet L-functions on a half-plane (Kronecker-Weber), then the
parent project's proven Dirichlet GRH immediately yields nonvanishing of
`ζ_K` right of the critical line. Combined with `dedekindZetaCriticalLine`,
a single such factorization gives ERH for `K`. -/
theorem nonvanishing_of_dirichlet_factorization (hgrh : DirichletGRH)
    (ζ : ℂ → ℂ) {N : ℕ} [NeZero N]
    (χs : Finset (DirichletCharacter ℂ N)) {bound : ℝ} (hb : bound ≤ 1 / 2)
    (hmul : ∀ z : ℂ, bound < z.re →
      ζ z = ∏ χ ∈ χs, DirichletCharacter.LFunction χ z) :
    ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → ζ z ≠ 0 :=
  nonvanishing_right_of_product χs DirichletCharacter.LFunction ζ hb hmul
    (fun χ _ z' hz' hz'1 => hgrh N χ z' hz' (Or.inr hz'1))

#print axioms nonvanishing_of_dirichlet_factorization

/-! ## No Siegel zeros -/

/-- The exact shape of the parent project's proven theorem (`Statements.lean`:
`DirichletLZerosOnLine`, proven in `Main.lean` as `LFunction_eq_zero_re :=
claimAll.2.1`): every zero of every Dirichlet L-function in the open critical
strip lies on the critical line. -/
def DirichletCriticalLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- **No Siegel zeros.** Under the (parent-proven) critical-line statement,
there is no real `β ∈ (1/2, 1)` with `L(χ, β) = 0` — for any Dirichlet
character of any level. A "Siegel zero" — a real zero of a real character
dangerously close to `1`, the obstruction responsible for a century of
ineffective constants in analytic number theory (Landau–Siegel) — cannot
exist once the zeros are pinned on the line. -/
theorem no_siegel_zeros (h : DirichletCriticalLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {β : ℝ} (hβ1 : 1 / 2 < β) (hβ2 : β < 1) :
    DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  intro hz
  have hline := h N χ (β : ℂ) (by rw [Complex.ofReal_re]; linarith)
    (by rw [Complex.ofReal_re]; linarith) hz
  rw [Complex.ofReal_re] at hline
  linarith

/-- Dirichlet's nonvanishing at the edge, from the parent-proven GRH shape:
for every non-principal Dirichlet character, `L(χ, 1) ≠ 0`. (This was the
historical input to Dirichlet's theorem on primes in arithmetic progressions;
here it is a corollary of the proven GRH.) -/
theorem LFunction_one_ne_zero (hgrh : DirichletGRH) {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ 1 ≠ 0 :=
  hgrh N χ 1 (by norm_num) (Or.inl hχ)

#print axioms no_siegel_zeros
#print axioms LFunction_one_ne_zero

/-! ## The Hecke and Artin rungs (interfaces and the Brauer reduction) -/

/-- ERH for an arbitrary family of L-functions: every member is nonvanishing
right of the critical line (away from the possible pole at `s = 1`). -/
def ERHFamily (S : Set (ℂ → ℂ)) : Prop :=
  ∀ L ∈ S, ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → L z ≠ 0

/-- **The Hecke rung, interface**: the Dedekind zeta of `K` *is* the Hecke
L-function of the trivial Grössencharakter of `K`; consequently, ERH for a
family of L-functions containing `ζ_K` gives ERH for `K`. Supplying the family
of Hecke L-functions of `K` (idele-class characters, analytic continuation,
functional equation) is the analytic content of the Hecke rung. -/
theorem dedekindERH_of_heckeERH {K : Type*} [Field K] [NumberField K]
    (D : DedekindZetaDatum K) {S : Set (ℂ → ℂ)}
    (hS : ERHFamily S) (hζ : D.ζ ∈ S) :
    DedekindERH K D :=
  fun z hz hz1 => hS D.ζ hζ z hz hz1

/-- **Brauer decomposition data for an Artin L-function**: the L-function
factors, on a half-plane, as a finite product of Hecke-type L-functions with
integer exponents. This is the shape supplied by Brauer's induction theorem
(an Artin character is a virtual combination of characters induced from
1-dimensional characters of subgroups — cyclic by class field theory); the
parent archive contains a `GroundTheory/Brauer` tower in this direction. -/
structure ArtinBrauerDatum (f : ℂ → ℂ) where
  /-- Index type for the Hecke-type factors. -/
  ι : Type*
  /-- Finite support of the decomposition. -/
  t : Finset ι
  /-- The Hecke-type L-functions. -/
  L : ι → ℂ → ℂ
  /-- Integer exponents (Brauer: virtual characters, so signs occur). -/
  e : ι → ℤ
  /-- Where the product identity holds. -/
  bound : ℝ
  /-- The product identity. -/
  hmul : ∀ z : ℂ, bound < z.re → f z = ∏ i ∈ t, (L i z) ^ ((e i : ℂ))

/-- **The Artin rung, reduction step**: an Artin L-function with Brauer
decomposition data is nonvanishing right of the critical line as soon as all
the Hecke-type factors in the decomposition are. Combined with
`dedekindERH_of_heckeERH` and the mirror adapter, this is the complete logical
bridge "Hecke ERH + Brauer induction ⟹ Artin ERH"; what remains is the
analytic supply of the two hypotheses (Hecke L-theory; Brauer induction). -/
theorem nonvanishing_of_artin_brauer {f : ℂ → ℂ} (d : ArtinBrauerDatum f) (hb : d.bound ≤ 1 / 2)
    (hnz : ∀ i ∈ d.t, ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → d.L i z ≠ 0) :
    ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → f z ≠ 0 := by
  intro z hz hz1
  have hbound : d.bound < z.re := by linarith
  rw [d.hmul z hbound, Finset.prod_ne_zero_iff]
  intro i hi
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (hnz i hi z hz hz1))

#print axioms dedekindERH_of_heckeERH
#print axioms nonvanishing_of_artin_brauer

/-! ## The ℚ(i) rung: mixed-level Dirichlet products and the two-squares reduction -/

/-- **Mixed-level Dirichlet products**: unlike
`nonvanishing_of_dirichlet_factorization` (single level `N`), the factor
family may combine Dirichlet L-functions of *different* conductors — e.g.
`ζ · L(χ₄) = L(mod 1) · L(mod 4)`. -/
theorem nonvanishing_of_dirichlet_family (hgrh : DirichletGRH)
    (ζ : ℂ → ℂ) {ι : Type*} (t : Finset ι)
    (L : ι → ℂ → ℂ) {bound : ℝ} (hb : bound ≤ 1 / 2)
    (hmul : ∀ z : ℂ, bound < z.re → ζ z = ∏ i ∈ t, L i z)
    (hfam : ∀ i ∈ t, ∃ (N : ℕ) (_ : NeZero N) (ψ : DirichletCharacter ℂ N),
      ∀ z : ℂ, L i z = DirichletCharacter.LFunction ψ z) :
    ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → ζ z ≠ 0 := by
  refine nonvanishing_right_of_product t L ζ hb hmul ?_
  intro i hi
  obtain ⟨N, hN, ψ, hψ⟩ := hfam i hi
  haveI := hN
  intro z hz hz1
  rw [hψ z]
  exact hgrh N ψ z hz (Or.inr hz1)

/-- **Coefficient identity ⟹ L-series factorization**: if the ideal counts of
`K` equal the Dirichlet convolution `1 ⍟ ψ` (for a Dirichlet character `ψ`),
then the Dedekind zeta of `K` factors as `ζ · L(ψ)` on the convergence
half-plane. For `K = ℚ(i)` and `ψ = χ₄` this is the classical factorization,
and the coefficient identity is the two-squares count
`#{ideals of norm n} = ∑_{d ∣ n} χ₄(d)` — the unique remaining analytic
input of that rung. -/
theorem dedekindZeta_eq_riemannZeta_mul_LFunction_of_convolution
    {K : Type*} [Field K] [NumberField K] {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)
        = (LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => ψ n)) n)
    {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s
      = riemannZeta s * DirichletCharacter.LFunction ψ s := by
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hψ : LSeriesSummable (fun n : ℕ => ψ n) s := DirichletCharacter.LSeriesSummable_of_one_lt_re ψ hs
  unfold NumberField.dedekindZeta
  rw [DirichletCharacter.LFunction_eq_LSeries ψ hs, ← LSeries_one_eq_riemannZeta hs,
    ← LSeries_convolution' h1 hψ]
  exact LSeries_congr (fun {n} hn => hcoeff n hn) s

/-- **The rung assembled**: if the continued zeta of K agrees with
`riemannZeta * L(chi_4)` on the right half-plane (supplied, for the Gaussian
field, by the coefficient identity above together with the identity theorem),
the proven Dirichlet GRH yields the full Dedekind ERH statement for K. -/
theorem dedekindERH_quadratic_of_twoSquares (hgrh : DirichletGRH)
    {K : Type*} [Field K] [NumberField K] (D : DedekindZetaDatum K)
    (χ : DirichletCharacter ℂ 4) {bound : ℝ} (hb : bound ≤ 1 / 2)
    (hcont : ∀ z : ℂ, bound < z.re →
      D.ζ z = riemannZeta z * DirichletCharacter.LFunction χ z) :
    DedekindERH K D := by
  intro z hz hz1 hz0
  rw [hcont z (by linarith), mul_eq_zero] at hz0
  rcases hz0 with h | h
  · exact hgrh 1 (1 : DirichletCharacter ℂ 1) z hz (Or.inr hz1) (by simpa using h)
  · exact hgrh 4 χ z hz (Or.inr hz1) h

#print axioms nonvanishing_of_dirichlet_family
#print axioms dedekindZeta_eq_riemannZeta_mul_LFunction_of_convolution
#print axioms dedekindERH_quadratic_of_twoSquares

/-! ## The quadratic datum: ERH modulo exactly the two-squares count -/

/-- The Dirichlet gamma-factor of any character is zero-free on the open
right half-plane (both the even factor `Γ_ℝ s` and the odd factor
`Γ_ℝ (s+1)` are products of a nonzero exponential with a Gamma value of
positive real part). -/
theorem gammaFactor_ne_zero_of_re_pos {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) :
    DirichletCharacter.gammaFactor ψ s ≠ 0 := by
  rcases ψ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs0
  · rw [h.gammaFactor_def]
    refine Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.add_re, Complex.one_re]; linarith

/-- Functional equation of the twisted product `N ^ (s²/2) · Λ_ζ · Λ_ψ`
for a primitive *quadratic* character `ψ`: it is symmetric up to the
*constant* `rootNumber ψ` inverted. The key exponent identity is
`(1-s)²/2 + (s - 1/2) = s²/2`. -/
private theorem quadraticTwist_fe {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N) (hprim : DirichletCharacter.IsPrimitive ψ)
    (hquad : ψ * ψ = 1) (hroot : DirichletCharacter.rootNumber ψ ≠ 0) (s : ℂ) :
    (N : ℂ) ^ (s ^ 2 / 2) * completedRiemannZeta s
      * DirichletCharacter.completedLFunction ψ s
      = (DirichletCharacter.rootNumber ψ)⁻¹ *
        ((N : ℂ) ^ ((1 - s) ^ 2 / 2) * completedRiemannZeta (1 - s)
          * DirichletCharacter.completedLFunction ψ (1 - s)) := by
  have hNc : ((N:ℂ)) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hd : DirichletCharacter.completedLFunction ψ (1 - s)
      = (N : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber ψ
        * DirichletCharacter.completedLFunction ψ s := by
    rw [DirichletCharacter.IsPrimitive.completedLFunction_one_sub hprim s]
    rw [show ψ⁻¹ = ψ from inv_eq_of_mul_eq_one_left hquad]
  have hpow : ∀ a b : ℂ, ((N:ℂ)) ^ (a + b) = ((N:ℂ)) ^ a * ((N:ℂ)) ^ b :=
    fun a b => Complex.cpow_add a b hNc
  rw [hd, completedRiemannZeta_one_sub s]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [← mul_assoc ψ.rootNumber ψ.rootNumber⁻¹ _, mul_inv_cancel₀ hroot, one_mul, ← hpow]
  congr 1
  ring_nf

/-- **The quadratic Dedekind-zeta datum.** For a number field `K` whose
Dedekind zeta factors as `ζ · L(ψ)` with `ψ` a primitive quadratic character
(`ψ * ψ = 1`), this *constructs* the full `DedekindZetaDatum K`:
the continuation is the product `ζ · L(ψ)` (so the strip-level identity holds
by definition — no identity-theorem step needed), the anchor field `agrees`
is supplied by the coefficient identity (`hcoeff`), and the completed form
`N ^ (s²/2) · Λ_ζ · Λ_ψ` satisfies a functional equation with the *constant*
root number `rootNumber ψ` (the non-constant factor `N ^ (s - 1/2)` in
Dirichlet's functional equation is absorbed by the `N ^ (s²/2)` twist, since
`(1-s)²/2 + (s - 1/2) = s²/2`). -/
noncomputable def quadraticDatum {K : Type*} [Field K] [NumberField K]
    {N : ℕ} [NeZero N] (hN1 : N ≠ 1)
    (ψ : DirichletCharacter ℂ N) (hprim : DirichletCharacter.IsPrimitive ψ)
    (hquad : ψ * ψ = 1) (hroot : DirichletCharacter.rootNumber ψ ≠ 0)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)
        = (LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => ψ n)) n) :
    DedekindZetaDatum K where
  ζ := fun z => riemannZeta z * DirichletCharacter.LFunction ψ z
  Λ := fun z => (N : ℂ) ^ (z ^ 2 / 2) * completedRiemannZeta z
    * DirichletCharacter.completedLFunction ψ z
  γ := fun z => (N : ℂ) ^ (z ^ 2 / 2) * (Gammaℝ z * DirichletCharacter.gammaFactor ψ z)
  ε := (DirichletCharacter.rootNumber ψ)⁻¹
  agrees := ⟨2, by norm_num, fun z hz =>
    (dedekindZeta_eq_riemannZeta_mul_LFunction_of_convolution ψ hcoeff
      (by simp only [Set.mem_ofPred] at hz; linarith)).symm⟩
  hε := inv_ne_zero hroot
  hγ := fun s hs0 _ => mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (NeZero.ne N))))
    (mul_ne_zero (gammaR_ne_zero_of_re_pos hs0) (gammaFactor_ne_zero_of_re_pos ψ hs0))
  hΛζ := by
    intro s hs0 _
    have h1 : completedRiemannZeta s = Gammaℝ s * riemannZeta s :=
      completedRiemannZeta_eq_gammaR_mul_riemannZeta hs0
    have hg : DirichletCharacter.gammaFactor ψ s ≠ 0 :=
      gammaFactor_ne_zero_of_re_pos ψ hs0
    have h2 : DirichletCharacter.completedLFunction ψ s
        = DirichletCharacter.gammaFactor ψ s * DirichletCharacter.LFunction ψ s := by
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ s (Or.inr hN1)]
      field_simp
    rw [h1, h2]; ring
  hfe := fun s => quadraticTwist_fe ψ hprim hquad hroot s
  holo := fun s hs => ((differentiableAt_riemannZeta hs).mul
    (DirichletCharacter.differentiableAt_LFunction ψ s (Or.inl hs))).differentiableWithinAt

/-- **The quadratic ERH rung, closed modulo exactly two classical inputs.**
Given the two-squares coefficient identity (`hcoeff`) and the classical
nonvanishing of the root number (`hroot`; |rootNumber| = 1 via Gauss sums),
the proven Dirichlet GRH yields the full `DedekindERH` for any `K` whose
zeta factors as `ζ · L(ψ)` with `ψ` primitive quadratic — e.g. `K = ℚ(i)`
with `ψ = χ₄` (conductor 4) or `K = ℚ(√d)` with the Kronecker character of
`d`. -/
theorem dedekindERH_quadratic_modulo_twoSquares (hgrh : DirichletGRH)
    {K : Type*} [Field K] [NumberField K] {N : ℕ} [NeZero N] (hN1 : N ≠ 1)
    (ψ : DirichletCharacter ℂ N) (hprim : DirichletCharacter.IsPrimitive ψ)
    (hquad : ψ * ψ = 1) (hroot : DirichletCharacter.rootNumber ψ ≠ 0)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)
        = (LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => ψ n)) n) :
    DedekindERH K (quadraticDatum hN1 ψ hprim hquad hroot hcoeff) := by
  intro z hz hz1 hz0
  have h0 : riemannZeta z * DirichletCharacter.LFunction ψ z = 0 := hz0
  rcases mul_eq_zero.1 h0 with h | h
  · exact hgrh 1 (1 : DirichletCharacter ℂ 1) z hz (Or.inr hz1) (by simpa using h)
  · exact hgrh N ψ z hz (Or.inr hz1) h

#print axioms dedekindERH_quadratic_modulo_twoSquares
#print axioms gammaFactor_ne_zero_of_re_pos
#print axioms quadraticDatum

/-! ## The concrete quadratic character chi_4 (mod 4) -/

/-- The primitive quadratic Dirichlet character mod 4, defined
computationally by residue: `chi_4(1) = 1`, `chi_4(3) = -1`, zero elsewhere. -/
private def chiFourFun (a : ZMod 4) : ℂ :=
  match (a : ZMod 4).val with
  | 1 => 1
  | 3 => -1
  | _ => 0

private theorem chiFourFun_mul (a b : ZMod 4) :
    chiFourFun (a * b) = chiFourFun a * chiFourFun b := by
  have hmul : (a * b : ZMod 4).val = ((a : ZMod 4).val * (b : ZMod 4).val) % 4 :=
    ZMod.val_mul a b
  have ha : (a : ZMod 4).val < 4 := ZMod.val_lt a
  have hb : (b : ZMod 4).val < 4 := ZMod.val_lt b
  rcases (by omega : (a : ZMod 4).val = 0 ∨ (a : ZMod 4).val = 1
    ∨ (a : ZMod 4).val = 2 ∨ (a : ZMod 4).val = 3) with hva | hva | hva | hva <;>
    rcases (by omega : (b : ZMod 4).val = 0 ∨ (b : ZMod 4).val = 1
    ∨ (b : ZMod 4).val = 2 ∨ (b : ZMod 4).val = 3) with hvb | hvb | hvb | hvb <;>
    simp [chiFourFun, hmul, hva, hvb]

/-- The primitive quadratic Dirichlet character chi_4 modulo 4.

Note: Mathlib at the pinned revision already defines `ZMod.χ₄ : MulChar (ZMod 4) ℤ`
(with value lemmas and quadraticity, in `LegendreSymbol/ZModChar.lean`); the
construction below is the ℂ-valued `DirichletCharacter ℂ 4` consumed directly
by the GRH/datum statements. It is equivalent to `ZMod.χ₄` composed with the
integer-to-complex cast. -/

noncomputable def chiFour : DirichletCharacter ℂ 4 :=
  MulChar.mk
    (MonoidHom.mk (OneHom.mk chiFourFun (by
        have hv : ((1 : ℕ) : ZMod 4).val = 1 := ZMod.val_cast_of_lt (by norm_num)
        show chiFourFun ((1 : ℕ) : ZMod 4) = 1
        simp only [chiFourFun, hv]))
      (fun _ _ => chiFourFun_mul _ _)) (by
    intro a ha
    have hc : ¬ (a : ZMod 4).val.Coprime 4 := by
      intro h
      apply ha
      have hI : IsUnit ((a : ZMod 4).val : ZMod 4) := (ZMod.isUnit_iff_coprime _ 4).mpr h
      rwa [ZMod.natCast_zmod_val a] at hI
    have hv : (a : ZMod 4).val < 4 := ZMod.val_lt a
    rcases (by omega : (a : ZMod 4).val = 0 ∨ (a : ZMod 4).val = 1
      ∨ (a : ZMod 4).val = 2 ∨ (a : ZMod 4).val = 3) with h | h | h | h
    · show chiFourFun a = 0
      simp [chiFourFun, h]
    · exact absurd (by rw [h]; norm_num) hc
    · show chiFourFun a = 0
      simp [chiFourFun, h]
    · exact absurd (by rw [h]; norm_num) hc)

@[simp] theorem chiFour_one : chiFour (1 : ZMod 4) = 1 := by
  have hv : ((1 : ℕ) : ZMod 4).val = 1 := ZMod.val_cast_of_lt (by norm_num)
  show chiFourFun ((1 : ℕ) : ZMod 4) = 1
  simp only [chiFourFun, hv]

@[simp] theorem chiFour_zero : chiFour (0 : ZMod 4) = 0 := by
  show chiFourFun ((0 : ℕ) : ZMod 4) = 0
  have hvv : ((0 : ℕ) : ZMod 4).val = 0 := ZMod.val_cast_of_lt (by norm_num)
  simp only [chiFourFun, hvv]

@[simp] theorem chiFour_two : chiFour (2 : ZMod 4) = 0 := by
  have hv : ((2 : ℕ) : ZMod 4).val = 2 := ZMod.val_cast_of_lt (by norm_num)
  show chiFourFun ((2 : ℕ) : ZMod 4) = 0
  simp only [chiFourFun, hv]

@[simp] theorem chiFour_three : chiFour (3 : ZMod 4) = -1 := by
  have hv : ((3 : ℕ) : ZMod 4).val = 3 := ZMod.val_cast_of_lt (by norm_num)
  show chiFourFun ((3 : ℕ) : ZMod 4) = -1
  simp only [chiFourFun, hv]

/-- chi_4 is quadratic: `chi_4 * chi_4 = 1`. -/
theorem chiFour_sq : chiFour * chiFour = 1 := by
  apply MulChar.ext'
  intro a
  have hv : (a : ZMod 4).val < 4 := ZMod.val_lt a
  rcases (by omega : (a : ZMod 4).val = 0 ∨ (a : ZMod 4).val = 1
    ∨ (a : ZMod 4).val = 2 ∨ (a : ZMod 4).val = 3) with h | h | h | h
  · have ha0 : a = ((0 : ℕ) : ZMod 4) := by
      rw [← ZMod.natCast_zmod_val a, h, Nat.cast_zero]
    subst ha0
    have h0 : chiFour ((0 : ℕ) : ZMod 4) = 0 := by
      show chiFourFun ((0 : ℕ) : ZMod 4) = 0
      have hvv : ((0 : ℕ) : ZMod 4).val = 0 := ZMod.val_cast_of_lt (by norm_num)
      simp only [chiFourFun, hvv]
    rw [MulChar.mul_apply, h0, mul_zero]
    exact (MulChar.map_nonunit (1 : DirichletCharacter ℂ 4)
      (show ¬ IsUnit ((0 : ℕ) : ZMod 4) by decide)).symm
  · have ha1 : a = ((1 : ℕ) : ZMod 4) := by
      rw [← ZMod.natCast_zmod_val a, h, Nat.cast_one]
    subst ha1
    have h1v : chiFour ((1 : ℕ) : ZMod 4) = 1 := by
      show chiFourFun ((1 : ℕ) : ZMod 4) = 1
      have hvv : ((1 : ℕ) : ZMod 4).val = 1 := ZMod.val_cast_of_lt (by norm_num)
      simp only [chiFourFun, hvv]
    rw [MulChar.mul_apply, h1v, mul_one]
    exact (map_one (1 : DirichletCharacter ℂ 4)).symm
  · have ha2 : a = ((2 : ℕ) : ZMod 4) := by
      rw [← ZMod.natCast_zmod_val a, h, Nat.cast_two]
    subst ha2
    have h2v : chiFour ((2 : ℕ) : ZMod 4) = 0 := by
      show chiFourFun ((2 : ℕ) : ZMod 4) = 0
      have hvv : ((2 : ℕ) : ZMod 4).val = 2 := ZMod.val_cast_of_lt (by norm_num)
      simp only [chiFourFun, hvv]
    rw [MulChar.mul_apply, h2v, mul_zero]
    exact (MulChar.map_nonunit (1 : DirichletCharacter ℂ 4)
      (show ¬ IsUnit ((2 : ℕ) : ZMod 4) by decide)).symm
  · have ha3 : a = ((3 : ℕ) : ZMod 4) := by
      rw [← ZMod.natCast_zmod_val a, h]
    subst ha3
    have hu : IsUnit ((3 : ℕ) : ZMod 4) := by
      rw [ZMod.isUnit_iff_coprime]
      norm_num
    obtain ⟨u, hu⟩ := hu
    have hvu : ((u : ZMod 4) : ZMod 4).val = 3 := by
      rw [hu, ZMod.val_cast_of_lt (by norm_num)]
    rw [← hu]
    have hc : chiFour (u : ZMod 4) = -1 := by
      show chiFourFun (u : ZMod 4) = -1
      simp only [chiFourFun, hvu]
    rw [MulChar.mul_apply, hc, MulChar.one_apply_coe]
    ring

/-- Every Dirichlet character of level 1 or 2 takes the value `1` at `3`
(when pulled back to level 4): the value only depends on the residue of `3`
modulo the level, and at `1` every character is `1`. -/
private theorem changeLevel_three_of_level_one_or_two {d : ℕ} (hd : d = 1 ∨ d = 2)
    (chi0 : DirichletCharacter ℂ d) {hdvd : d ∣ 4} :
    (DirichletCharacter.changeLevel hdvd chi0) (3 : ZMod 4) = 1 := by
  have hcast : ((3 : ℕ) : ZMod 4) = ((3 : ℤ) : ZMod 4) := by norm_num
  show (DirichletCharacter.changeLevel hdvd chi0) ((3 : ℕ) : ZMod 4) = 1
  rw [hcast, DirichletCharacter.changeLevel_eq_cast_of_dvd' chi0 hdvd
    (show IsCoprime (3 : ℤ) 4 by norm_num)]
  rcases hd with rfl | rfl
  · rw [show ((3 : ℤ) : ZMod 1) = 1 by decide]
    exact map_one chi0
  · rw [show ((3 : ℤ) : ZMod 2) = 1 by decide]
    exact map_one chi0

/-- chi_4 is primitive: its conductor is 4, since it does not factor through
level 1 or 2 (chi_4(3) = -1 while every level-1/2 character takes value 1
there), and the conductor divides 4. -/
theorem chiFour_isPrimitive : DirichletCharacter.IsPrimitive chiFour := by
  have hdvd := DirichletCharacter.conductor_dvd_level chiFour
  have h0 : DirichletCharacter.conductor chiFour ≠ 0 :=
    DirichletCharacter.conductor_ne_zero chiFour
  have hfac := DirichletCharacter.factorsThrough_conductor chiFour
  have hne12 : DirichletCharacter.conductor chiFour ≠ 1
      ∧ DirichletCharacter.conductor chiFour ≠ 2 := by
    constructor
    · intro e
      rw [e] at hfac
      have h3 := congrArg (fun (chi : DirichletCharacter ℂ 4) => chi (3 : ZMod 4))
        hfac.eq_changeLevel
      rw [changeLevel_three_of_level_one_or_two (Or.inl rfl) _, chiFour_three] at h3
      exact absurd h3 (by norm_num)
    · intro e
      rw [e] at hfac
      have h3 := congrArg (fun (chi : DirichletCharacter ℂ 4) => chi (3 : ZMod 4))
        hfac.eq_changeLevel
      rw [changeLevel_three_of_level_one_or_two (Or.inr rfl) _, chiFour_three] at h3
      exact absurd h3 (by norm_num)
  have hle : DirichletCharacter.conductor chiFour ≤ 4 := Nat.le_of_dvd four_pos hdvd
  show DirichletCharacter.conductor chiFour = 4
  rcases (by omega : DirichletCharacter.conductor chiFour = 0
    ∨ DirichletCharacter.conductor chiFour = 1 ∨ DirichletCharacter.conductor chiFour = 2
    ∨ DirichletCharacter.conductor chiFour = 3 ∨ DirichletCharacter.conductor chiFour = 4) with
    h | h | h | h | h
  · exact absurd h h0
  · exact absurd h hne12.1
  · exact absurd h hne12.2
  · rw [h] at hdvd
    exact absurd hdvd (by norm_num)
  · exact h

#print axioms chiFour_sq
#print axioms chiFour_isPrimitive

/-- Bridge: `chiFour` agrees with Mathlib's `ZMod.χ₄` (values in ℤ) cast to
ℂ at every point. This identifies our hand-constructed character with the
canonical one from `LegendreSymbol/ZModChar.lean`. -/
theorem chiFour_agrees_ZMod_chiFour (a : ZMod 4) :
    chiFour a = ((ZMod.χ₄ a : Int) : ℂ) := by
  have hv : a.val < 4 := ZMod.val_lt a
  rcases (by omega : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ a.val = 3) with h | h | h | h
  · have ha : a = ((0 : ℕ) : ZMod 4) := by
      rw [← ZMod.natCast_zmod_val a, h, Nat.cast_zero]
    subst ha
    show chiFourFun ((0 : ℕ) : ZMod 4) = ((ZMod.χ₄ ((0 : ℕ) : ZMod 4) : Int) : ℂ)
    have hvv : ((0 : ℕ) : ZMod 4).val = 0 := ZMod.val_cast_of_lt (by norm_num)
    simp only [chiFourFun, hvv]
    show (0 : ℂ) = ((ZMod.χ₄ ((0 : ℕ) : ZMod 4) : Int) : ℂ)
    norm_num [ZMod.χ₄]
  · have ha : a = ((1 : ℕ) : ZMod 4) := by
      rw [← ZMod.natCast_zmod_val a, h, Nat.cast_one]
    subst ha
    show chiFourFun ((1 : ℕ) : ZMod 4) = ((ZMod.χ₄ ((1 : ℕ) : ZMod 4) : Int) : ℂ)
    have hvv : ((1 : ℕ) : ZMod 4).val = 1 := ZMod.val_cast_of_lt (by norm_num)
    simp only [chiFourFun, hvv]
    show (1 : ℂ) = ((ZMod.χ₄ ((1 : ℕ) : ZMod 4) : Int) : ℂ)
    norm_num [ZMod.χ₄]
  · have ha : a = ((2 : ℕ) : ZMod 4) := by
      rw [← ZMod.natCast_zmod_val a, h, Nat.cast_two]
    subst ha
    show chiFourFun ((2 : ℕ) : ZMod 4) = ((ZMod.χ₄ ((2 : ℕ) : ZMod 4) : Int) : ℂ)
    have hvv : ((2 : ℕ) : ZMod 4).val = 2 := ZMod.val_cast_of_lt (by norm_num)
    simp only [chiFourFun, hvv]
    show (0 : ℂ) = ((ZMod.χ₄ ((2 : ℕ) : ZMod 4) : Int) : ℂ)
    norm_num [ZMod.χ₄]
  · have ha : a = ((3 : ℕ) : ZMod 4) := by
      rw [← ZMod.natCast_zmod_val a, h]
    subst ha
    show chiFourFun ((3 : ℕ) : ZMod 4) = ((ZMod.χ₄ ((3 : ℕ) : ZMod 4) : Int) : ℂ)
    have hvv : ((3 : ℕ) : ZMod 4).val = 3 := ZMod.val_cast_of_lt (by norm_num)
    simp only [chiFourFun, hvv]
    show (-1 : ℂ) = ((ZMod.χ₄ ((3 : ℕ) : ZMod 4) : Int) : ℂ)
    norm_num [ZMod.χ₄]

#print axioms chiFour_agrees_ZMod_chiFour

/-! ## The Gauss sum of chi_4 and the nonvanishing of its root number -/

private theorem stdAddChar_one : ZMod.stdAddChar (1 : ZMod 4) = I := by
  show ZMod.stdAddChar ((1 : ℤ) : ZMod 4) = I
  rw [ZMod.stdAddChar_coe]
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * I * ((1 : ℤ) : ℂ) / ((4 : ℕ) : ℂ))
      = Complex.exp ((Real.pi : ℂ) / 2 * I) := by
    congr 2
    push_cast
    field_simp
    norm_num
  rw [h1, Complex.exp_mul_I]
  have hc : Complex.cos ((Real.pi : ℂ) / 2) = 0 := by
    exact_mod_cast Real.cos_pi_div_two
  have hs : Complex.sin ((Real.pi : ℂ) / 2) = 1 := by
    exact_mod_cast Real.sin_pi_div_two
  rw [hc, hs]
  simp

private theorem stdAddChar_three : ZMod.stdAddChar (3 : ZMod 4) = -I := by
  show ZMod.stdAddChar ((3 : ℤ) : ZMod 4) = -I
  rw [ZMod.stdAddChar_coe]
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * I * ((3 : ℤ) : ℂ) / ((4 : ℕ) : ℂ))
      = Complex.exp ((3 * (Real.pi : ℂ) / 2) * I) := by
    congr 2
    push_cast
    field_simp
    norm_num
  rw [h1, Complex.exp_mul_I]
  have hcp : Complex.cos ((Real.pi : ℂ)) = -1 := by exact_mod_cast Real.cos_pi
  have hsp : Complex.sin ((Real.pi : ℂ)) = 0 := by exact_mod_cast Real.sin_pi
  have hc2 : Complex.cos ((Real.pi : ℂ) / 2) = 0 := by
    exact_mod_cast Real.cos_pi_div_two
  have hs2 : Complex.sin ((Real.pi : ℂ) / 2) = 1 := by
    exact_mod_cast Real.sin_pi_div_two
  have hc : Complex.cos (3 * (Real.pi : ℂ) / 2) = 0 := by
    have h : Complex.cos (3 * (Real.pi : ℂ) / 2)
        = Complex.cos ((Real.pi : ℂ) + (Real.pi : ℂ) / 2) := by
      congr 1
      ring_nf
    rw [h, Complex.cos_add, hcp, hc2, hsp, hs2]
    simp
  have hs : Complex.sin (3 * (Real.pi : ℂ) / 2) = -1 := by
    have h : Complex.sin (3 * (Real.pi : ℂ) / 2)
        = Complex.sin ((Real.pi : ℂ) + (Real.pi : ℂ) / 2) := by
      congr 1
      ring_nf
    rw [h, Complex.sin_add, hcp, hc2, hsp, hs2]
    simp
  rw [hc, hs]
  simp

set_option maxHeartbeats 1000000 in
/-- The classical Gauss sum: `gaussSum chiFour stdAddChar = 2 * I`
(only the units 1 and 3 contribute: `1 * I + (-1) * (-I) = 2 * I`). -/
theorem gaussSum_chiFour : gaussSum chiFour ZMod.stdAddChar = 2 * I := by
  rw [gaussSum]
  have huniv : (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  -- Goal: right-associative sum of four terms
  rw [show
    chiFour (0 : ZMod 4) * ZMod.stdAddChar (0 : ZMod 4)
      + (chiFour (1 : ZMod 4) * ZMod.stdAddChar (1 : ZMod 4)
        + (chiFour (2 : ZMod 4) * ZMod.stdAddChar (2 : ZMod 4)
          + chiFour (3 : ZMod 4) * ZMod.stdAddChar (3 : ZMod 4))) = 2 * I from by
    have hz : chiFour (0 : ZMod 4) * ZMod.stdAddChar (0 : ZMod 4) = 0 := by
      rw [chiFour_zero, zero_mul]
    have hz2 : chiFour (2 : ZMod 4) * ZMod.stdAddChar (2 : ZMod 4) = 0 := by
      rw [chiFour_two, zero_mul]
    have h1 : chiFour (1 : ZMod 4) * ZMod.stdAddChar (1 : ZMod 4) = I := by
      rw [chiFour_one, stdAddChar_one]
      simp
    have h3 : chiFour (3 : ZMod 4) * ZMod.stdAddChar (3 : ZMod 4) = I := by
      rw [chiFour_three, stdAddChar_three]
      simp
    rw [hz, hz2, h1, h3]
    ring]

/-- **The root number of chi_4 is nonzero.** -/
theorem chiFour_rootNumber_ne_zero : DirichletCharacter.rootNumber chiFour ≠ 0 := by
  rw [DirichletCharacter.rootNumber, gaussSum_chiFour]
  refine div_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) ?_) ?_
  · exact pow_ne_zero _ Complex.I_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

#print axioms gaussSum_chiFour
#print axioms chiFour_rootNumber_ne_zero

/-- The level `4` is not `1`. (Previously written as an unbound `four_ne_one`, which
`autoImplicit` silently turned into an extra implicit hypothesis `4 ≠ 1`.) -/
theorem four_ne_one_nat : (4 : ℕ) ≠ 1 := by norm_num

/-- **ERH for any `K` with the ideal counts of ℚ(i), assembled.** For any number field
`K` whose ideal counts satisfy the identity `#{I : N I = n} = ∑_{d ∣ n} χ₄(d)`,
`DirichletGRH` (a hypothesis) yields `DedekindERH K` through the quadratic datum
instantiated at `chi_4` (primitive, quadratic, nonzero root number). The identity is
proved for `ℚ(i) = CyclotomicField 4 ℚ` below (`hcoeff_QI`). -/
theorem dedekindERH_quadratic_i_assembled (hgrh : DirichletGRH)
    {K : Type*} [Field K] [NumberField K]
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)
        = (LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => chiFour n)) n) :
    DedekindERH K (quadraticDatum (N := 4) four_ne_one_nat chiFour
      chiFour_isPrimitive chiFour_sq chiFour_rootNumber_ne_zero hcoeff) :=
  dedekindERH_quadratic_modulo_twoSquares hgrh four_ne_one_nat chiFour
    chiFour_isPrimitive chiFour_sq chiFour_rootNumber_ne_zero hcoeff

#print axioms dedekindERH_quadratic_i_assembled

/-- **Holomorphy of the quadratic datum's continuation.** The function
`riemannZeta · L(χ₄)` is holomorphic away from `s = 1` (product of two
holomorphic functions, each holomorphic except at their respective poles;
`L(χ₄, ·)` is entire since `χ₄ ≠ 1`). This closes the holomorphy gap:
the datum's `ζ` is a *bona fide* analytic function, not just any function
agreeing with the L-series. -/
theorem quadraticDatum_holomorphic {N : ℕ} [NeZero N] (hN1 : N ≠ 1)
    {K : Type*} [Field K] [NumberField K]
    (ψ : DirichletCharacter ℂ N) (hprim : DirichletCharacter.IsPrimitive ψ)
    (hquad : ψ * ψ = 1) (hroot : DirichletCharacter.rootNumber ψ ≠ 0)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)
        = (LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => ψ n)) n) :
    DifferentiableOn ℂ
      (quadraticDatum hN1 ψ hprim hquad hroot hcoeff).ζ {s : ℂ | s ≠ 1} :=
  -- now a field of every `DedekindZetaDatum` (proved in `quadraticDatum` from
  -- `differentiableAt_riemannZeta` and `DirichletCharacter.differentiableAt_LFunction`)
  (quadraticDatum hN1 ψ hprim hquad hroot hcoeff).holo

#print axioms quadraticDatum_holomorphic

/-! ## Counting ideals by norm, and `ℚ(i)` concretely (`hcoeff` proved)

Generic facts for any number field `K` (`idealCount K n` = number of ideals of norm `n`):
multiplicativity in coprime arguments, and the count at `p ^ k` from the primes above
`p` (one prime of inertia degree `f`, or two of degree `1`). Then `ℚ(i)` as
`CyclotomicField 4 ℚ`: splitting of `2`, `p ≡ 1`, `p ≡ 3 (mod 4)` from Mathlib's
cyclotomic ramification theory, and `#{I : N I = n} = ∑_{d ∣ n} χ₄(d)`. No two-squares
(Jacobi) formula is needed: the count is done on ideals, not on elements. -/

namespace GaussianERH

section W1

/-- Number of ideals of `𝓞 K` of absolute norm `n`. -/
noncomputable def idealCount (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

theorem idealCount_one (K : Type*) [Field K] [NumberField K] : idealCount K 1 = 1 := by
  simp [idealCount]

/-- If `A ⊔ B = ⊤`, `A ≤ J` and `B ≤ J'`, then `J * J' ⊔ A = J`. -/
theorem w1_mul_sup_eq {R : Type*} [CommRing R] {A B J J' : Ideal R} (hAB : A ⊔ B = ⊤)
    (hA : A ≤ J) (hB : B ≤ J') : J * J' ⊔ A = J := by
  have h : A ⊔ J' = ⊤ := eq_top_iff.mpr (hAB ▸ sup_le_sup_left hB A)
  rw [sup_comm, mul_comm, Ideal.sup_mul_eq_of_coprime_left h, sup_eq_right.mpr hA]

/-- If `A ⊔ B = ⊤` and `A * B ≤ I`, then `(I ⊔ A) * (I ⊔ B) = I`. -/
theorem w1_sup_mul_sup_eq {R : Type*} [CommRing R] {A B I : Ideal R} (hAB : A ⊔ B = ⊤)
    (h : A * B ≤ I) : (I ⊔ A) * (I ⊔ B) = I := by
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right h)
  · have hc : (I ⊔ A) ⊔ (I ⊔ B) = ⊤ :=
      eq_top_iff.mpr (hAB ▸ sup_le_sup le_sup_right le_sup_right)
    rw [Ideal.mul_eq_inf_of_coprime hc]
    exact le_inf le_sup_left le_sup_left

/-- Arithmetic: divisors `a ∣ m ^ d`, `b ∣ n ^ d` of coprime `m, n` with `a * b = m * n`. -/
theorem w1_norms {a b m n d : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n)
    (ha : a ∣ m ^ d) (hb : b ∣ n ^ d) (hab : a * b = m * n) : a = m ∧ b = n := by
  have ha' : a ∣ m :=
    (Nat.Coprime.coprime_dvd_left ha (hmn.pow_left d)).dvd_of_dvd_mul_right
      (hab ▸ dvd_mul_right a b)
  have hb' : b ∣ n :=
    (Nat.Coprime.coprime_dvd_left hb (hmn.symm.pow_left d)).dvd_of_dvd_mul_left
      (hab ▸ dvd_mul_left b a)
  obtain ⟨k, rfl⟩ := ha'
  obtain ⟨l, rfl⟩ := hb'
  have hpos : 0 < a * b := by
    rcases Nat.eq_zero_or_pos (a * b) with h | h
    · rw [h] at hab
      exact absurd hab.symm (mul_ne_zero hm hn)
    · exact h
  have h1 : a * b * (k * l) = a * b * 1 :=
    calc a * b * (k * l) = a * k * (b * l) := by ring
      _ = a * b * 1 := by rw [mul_one, hab]
  have h2 := mul_eq_one.mp (Nat.eq_of_mul_eq_mul_left hpos h1)
  simp [h2.1, h2.2]

/-- The number of ideals of norm `m * n` is multiplicative in coprime `m, n`. -/
theorem idealCount_mul (K : Type*) [Field K] [NumberField K] {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) :
    idealCount K (m * n) = idealCount K m * idealCount K n := by
  set A : Ideal (𝓞 K) := Ideal.span {(m : 𝓞 K)} with hAdef
  set B : Ideal (𝓞 K) := Ideal.span {(n : 𝓞 K)} with hBdef
  have hAB : A ⊔ B = ⊤ :=
    Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_span_singleton_iff _ _).mpr hmn.cast)
  have hBA : B ⊔ A = ⊤ := by rw [sup_comm]; exact hAB
  have hAn : Ideal.absNorm A = m ^ Module.finrank ℤ (𝓞 K) := Ideal.absNorm_span_natCast m
  have hBn : Ideal.absNorm B = n ^ Module.finrank ℤ (𝓞 K) := Ideal.absNorm_span_natCast n
  have hle : ∀ (J : Ideal (𝓞 K)) (k : ℕ), Ideal.absNorm J = k →
      Ideal.span {(k : 𝓞 K)} ≤ J := by
    intro J k hJ
    have := Ideal.span_singleton_absNorm_le J
    rwa [hJ] at this
  have hABI : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = m * n → A * B ≤ I := by
    intro I hI
    rw [hAdef, hBdef, Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul]
    exact hle I _ hI
  have key : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = m * n →
      Ideal.absNorm (I ⊔ A) = m ∧ Ideal.absNorm (I ⊔ B) = n := by
    intro I hI
    refine w1_norms hm hn hmn (d := Module.finrank ℤ (𝓞 K)) ?_ ?_ ?_
    · rw [← hAn]; exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
    · rw [← hBn]; exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
    · rw [← map_mul, w1_sup_mul_sup_eq hAB (hABI I hI), hI]
  let e : {I : Ideal (𝓞 K) // Ideal.absNorm I = m * n} ≃
      {J : Ideal (𝓞 K) // Ideal.absNorm J = m} × {J : Ideal (𝓞 K) // Ideal.absNorm J = n} :=
    { toFun := fun I => (⟨I.1 ⊔ A, (key I.1 I.2).1⟩, ⟨I.1 ⊔ B, (key I.1 I.2).2⟩)
      invFun := fun p => ⟨p.1.1 * p.2.1, by rw [map_mul, p.1.2, p.2.2]⟩
      left_inv := fun I => Subtype.ext (w1_sup_mul_sup_eq hAB (hABI I.1 I.2))
      right_inv := fun p => by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · exact w1_mul_sup_eq hAB (hle _ _ p.1.2) (hle _ _ p.2.2)
        · show p.1.1 * p.2.1 ⊔ B = p.2.1
          rw [mul_comm]
          exact w1_mul_sup_eq hBA (hle _ _ p.2.2) (hle _ _ p.1.2) }
  unfold idealCount
  rw [← Nat.card_prod]
  exact Nat.card_congr e

end W1

section W2

open Ideal

open UniqueFactorizationMonoid

section helpers

variable {K : Type*} [Field K] [NumberField K]

lemma w2_span_max (p : ℕ) [hp : Fact p.Prime] : (span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
  Int.ideal_span_isMaximal_of_prime p

lemma w2_span_ne_bot (p : ℕ) [hp : Fact p.Prime] : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
  simp [hp.out.ne_zero]

lemma w2_ne_bot (p : ℕ) [Fact p.Prime] {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) : P ≠ ⊥ :=
  ne_bot_of_mem_primesOver (w2_span_ne_bot p) hP

lemma w2_absNorm (p : ℕ) [hp : Fact p.Prime] {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) :
    absNorm P = p ^ inertiaDeg P ℤ := by
  have := hP.1
  have := hP.2
  have := w2_span_max p
  have : P.IsMaximal := hP.1.isMaximal (w2_ne_bot p hP)
  rw [absNorm_eq_pow_inertiaDeg' P hp.out, inertiaDeg'_eq_inertiaDeg]

lemma w2_prime (p : ℕ) [Fact p.Prime] {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) : Prime P :=
  prime_of_isPrime (w2_ne_bot p hP) hP.1

lemma w2_normalizedFactors (p : ℕ) [Fact p.Prime] {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) (n : ℕ) :
    normalizedFactors (P ^ n) = Multiset.replicate n P := by
  rw [normalizedFactors_pow, normalizedFactors_irreducible (w2_prime p hP).irreducible,
    normalize_eq, Multiset.nsmul_singleton]

lemma w2_mem_primesOver (p : ℕ) [hp : Fact p.Prime] {I : Ideal (𝓞 K)} {k : ℕ}
    (hI : absNorm I = p ^ k) {Q : Ideal (𝓞 K)} (hQ : Q ∈ normalizedFactors I) :
    Q ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by
  have hQp : Q.IsPrime := isPrime_of_prime (prime_of_normalized_factor Q hQ)
  have hIQ : I ≤ Q := le_of_dvd (dvd_of_mem_normalizedFactors hQ)
  have h1 : ((p : 𝓞 K)) ^ k ∈ Q := by
    have := hIQ (absNorm_mem I)
    rw [hI] at this
    simpa using this
  have h2 : (p : 𝓞 K) ∈ Q := hQp.mem_of_pow_mem k h1
  refine ⟨hQp, ⟨?_⟩⟩
  refine IsMaximal.eq_of_le (w2_span_max p) IsPrime.ne_top' ?_
  rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_under]
  simpa using h2

lemma w2_ne_bot_of_absNorm (p : ℕ) [hp : Fact p.Prime] {I : Ideal (𝓞 K)} {k : ℕ}
    (hI : absNorm I = p ^ k) : I ≠ ⊥ := by
  intro h
  rw [h, absNorm_bot] at hI
  exact pow_ne_zero k hp.out.ne_zero hI.symm

end helpers

/-- A unique prime above `p` (inert or totally ramified), of inertia degree `f`:
the ideals of norm `p ^ k` are the powers `P ^ (k / f)`, which exist iff `f ∣ k`. -/
theorem idealCount_prime_pow_of_unique {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (f : ℕ) (hf : 0 < f)
    (hS : (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1)
    (hfP : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), inertiaDeg P ℤ = f) (k : ℕ) :
    idealCount K (p ^ k) = if f ∣ k then 1 else 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨P, hSP⟩ := Set.ncard_eq_one.mp hS
  have hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by rw [hSP]; rfl
  have hnorm : ∀ e : ℕ, absNorm (P ^ e) = p ^ (f * e) := by
    intro e
    rw [map_pow, w2_absNorm p hP, hfP P hP, pow_mul]
  have hdec : ∀ I : Ideal (𝓞 K), absNorm I = p ^ k → I = P ^ (normalizedFactors I).card := by
    intro I hI
    have hrep : normalizedFactors I = Multiset.replicate (normalizedFactors I).card P := by
      rw [Multiset.eq_replicate_card]
      intro Q hQ
      have := w2_mem_primesOver p hI hQ
      rw [hSP] at this
      exact this
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self (w2_ne_bot_of_absNorm p hI), hrep]
    rw [Multiset.prod_replicate]
  have hinj : Function.Injective (fun n : ℕ => p ^ n) := Nat.pow_right_injective hp.two_le
  unfold idealCount
  split_ifs with hdvd
  · obtain ⟨e, rfl⟩ := hdvd
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨P ^ e, hnorm e⟩, ?_⟩
    rintro ⟨I, hI⟩
    apply Subtype.ext
    show I = P ^ e
    have h1 := hdec I hI
    rw [h1]
    rw [h1, hnorm] at hI
    have := hinj hI
    rw [Nat.eq_of_mul_eq_mul_left hf this]
  · rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨I, hI⟩
    apply hdvd
    have h1 := hdec I hI
    rw [h1, hnorm] at hI
    exact ⟨_, (hinj hI).symm⟩

/-- Exactly two primes above `p`, both of inertia degree `1`:
the ideals of norm `p ^ k` are the `P₁ ^ a * P₂ ^ b` with `a + b = k`. -/
theorem idealCount_prime_pow_of_split {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (hS : (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2)
    (hfP : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), inertiaDeg P ℤ = 1) (k : ℕ) :
    idealCount K (p ^ k) = k + 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨P₁, P₂, hne, hSP⟩ := Set.ncard_eq_two.mp hS
  have hP₁ : P₁ ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by rw [hSP]; simp
  have hP₂ : P₂ ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by rw [hSP]; simp
  have hnorm : ∀ a b : ℕ, absNorm (P₁ ^ a * P₂ ^ b) = p ^ (a + b) := by
    intro a b
    rw [map_mul, map_pow, map_pow, w2_absNorm p hP₁, w2_absNorm p hP₂, hfP P₁ hP₁, hfP P₂ hP₂,
      pow_one, pow_add]
  have hnf : ∀ a b : ℕ, normalizedFactors (P₁ ^ a * P₂ ^ b) =
      Multiset.replicate a P₁ + Multiset.replicate b P₂ := by
    intro a b
    rw [normalizedFactors_mul (pow_ne_zero _ (w2_prime p hP₁).ne_zero)
      (pow_ne_zero _ (w2_prime p hP₂).ne_zero), w2_normalizedFactors p hP₁,
      w2_normalizedFactors p hP₂]
  have hcount : ∀ a b : ℕ, (normalizedFactors (P₁ ^ a * P₂ ^ b)).count P₁ = a := by
    intro a b
    rw [hnf, Multiset.count_add, Multiset.count_replicate_self,
      Multiset.count_replicate, if_neg (Ne.symm hne), add_zero]
  have hdec : ∀ I : Ideal (𝓞 K), absNorm I = p ^ k →
      I = P₁ ^ (normalizedFactors I).count P₁ * P₂ ^ (normalizedFactors I).count P₂ := by
    intro I hI
    have hsplit : normalizedFactors I = Multiset.replicate ((normalizedFactors I).count P₁) P₁ +
        Multiset.replicate ((normalizedFactors I).count P₂) P₂ := by
      rw [← Multiset.filter_eq', ← Multiset.filter_eq']
      conv_lhs => rw [← Multiset.filter_add_not (· = P₁) (normalizedFactors I)]
      congr 1
      apply Multiset.filter_congr
      intro Q hQ
      have := w2_mem_primesOver p hI hQ
      rw [hSP] at this
      rcases this with h | h
      · simp [h, hne]
      · simp only [Set.mem_singleton_iff] at h
        simp [h, Ne.symm hne]
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self (w2_ne_bot_of_absNorm p hI), hsplit]
    rw [Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_replicate]
  have hinj : Function.Injective (fun n : ℕ => p ^ n) := Nat.pow_right_injective hp.two_le
  let g : Fin (k + 1) → {I : Ideal (𝓞 K) // absNorm I = p ^ k} := fun a =>
    ⟨P₁ ^ (a : ℕ) * P₂ ^ (k - a), by rw [hnorm]; congr 1; have := a.isLt; omega⟩
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      have := congrArg (fun I : {I : Ideal (𝓞 K) // absNorm I = p ^ k} =>
        (normalizedFactors I.1).count P₁) hab
      simp only [g, hcount] at this
      exact Fin.ext this
    · rintro ⟨I, hI⟩
      have h1 := hdec I hI
      have h2 := hI
      rw [h1, hnorm] at h2
      have h3 := hinj h2
      refine ⟨⟨(normalizedFactors I).count P₁, by omega⟩, ?_⟩
      apply Subtype.ext
      simp only [g]
      conv_rhs => rw [h1]
      congr 2
      omega
  unfold idealCount
  rw [← Nat.card_eq_of_bijective g hg, Nat.card_eq_fintype_card, Fintype.card_fin]

end W2

section W3

open Ideal

/-- The Gaussian number field `ℚ(i)`, as the 4th cyclotomic field. -/
abbrev QI : Type := CyclotomicField 4 ℚ

instance w3_neZero_four : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩

instance w3_isCyclotomic : IsCyclotomicExtension {4} ℚ QI :=
  CyclotomicField.isCyclotomicExtension 4 ℚ

/-- For an odd prime `p`, the number of primes above `p` in `ℚ(i)` times their inertia degree
is `2`. -/
theorem w3_ncard_mul_orderOf (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ 4) :
    (primesOver (span {(p : ℤ)}) (𝓞 QI)).ncard * orderOf (p : ZMod 4) = 2 := by
  have : IsGalois ℚ QI := IsCyclotomicExtension.isGalois {4} ℚ QI
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (span {(p : ℤ)}) (𝓞 QI) Gal(QI/ℚ)
  rwa [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p QI hp,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p QI hp, one_mul,
    IsGaloisGroup.card_eq_finrank Gal(QI/ℚ) ℚ QI, IsCyclotomicExtension.Rat.finrank 4 QI,
    show Nat.totient 4 = 2 by decide] at h_main

theorem w3_not_dvd_four (p : ℕ) (hpp : p.Prime) (hp : p % 4 = 1 ∨ p % 4 = 3) : ¬ p ∣ 4 := by
  intro h
  have : p ≤ 4 := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> simp_all [Nat.not_prime_one]

/-- `2` is totally ramified in `ℚ(i)`: one prime above it, of inertia degree `1`. -/
theorem QI_two :
    (primesOver (span {((2 : ℕ) : ℤ)}) (𝓞 QI)).ncard = 1 ∧
      ∀ P ∈ primesOver (span {((2 : ℕ) : ℤ)}) (𝓞 QI), inertiaDeg P ℤ = 1 := by
  have : IsCyclotomicExtension {2 ^ (1 + 1)} ℚ QI := by
    norm_num
    infer_instance
  refine ⟨IsCyclotomicExtension.Rat.ncard_primesOver_of_prime_pow 2 1 QI, ?_⟩
  rintro P ⟨hP1, hP2⟩
  exact IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime_pow 2 1 QI P

/-- A prime `p ≡ 1 (mod 4)` splits in `ℚ(i)`: two primes, of inertia degree `1`. -/
theorem QI_one_mod_four (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    (primesOver (span {(p : ℤ)}) (𝓞 QI)).ncard = 2 ∧
      ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 QI), inertiaDeg P ℤ = 1 := by
  have hnd := w3_not_dvd_four p Fact.out (Or.inl hp)
  have hord : orderOf (p : ZMod 4) = 1 := by
    rw [← ZMod.natCast_mod, hp, Nat.cast_one, orderOf_one]
  refine ⟨by simpa [hord] using w3_ncard_mul_orderOf p hnd, ?_⟩
  rintro P ⟨hP1, hP2⟩
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p QI P hnd, hord]

/-- A prime `p ≡ 3 (mod 4)` is inert in `ℚ(i)`: one prime, of inertia degree `2`. -/
theorem QI_three_mod_four (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    (primesOver (span {(p : ℤ)}) (𝓞 QI)).ncard = 1 ∧
      ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 QI), inertiaDeg P ℤ = 2 := by
  have hnd := w3_not_dvd_four p Fact.out (Or.inr hp)
  have hord : orderOf (p : ZMod 4) = 2 := by
    rw [← ZMod.natCast_mod, hp]
    exact orderOf_eq_prime (by decide) (by decide)
  refine ⟨by simpa [hord] using w3_ncard_mul_orderOf p hnd, ?_⟩
  rintro P ⟨hP1, hP2⟩
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p QI P hnd, hord]

/-- The arithmetic function of `χ₄` is multiplicative. -/
theorem w3_chi_mult :
    (toArithmeticFunction (fun d : ℕ => ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ))).IsMultiplicative := by
  refine ⟨by simp [toArithmeticFunction], fun {m n} _ => ?_⟩
  simp only [toArithmeticFunction, ArithmeticFunction.coe_mk]
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp [hm, hn, Nat.cast_mul, map_mul]

/-- A function `c` with `c 1 = 1`, multiplicative on coprime nonzero arguments, gives a
multiplicative arithmetic function. -/
theorem w3_count_mult (c : ℕ → ℕ) (hone : c 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → c (m * n) = c m * c n) :
    (toArithmeticFunction (fun n : ℕ => (c n : ℂ))).IsMultiplicative := by
  refine ⟨by simp [toArithmeticFunction, hone], fun {m n} hmn => ?_⟩
  simp only [toArithmeticFunction, ArithmeticFunction.coe_mk]
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp [hm, hn, hmul hm hn hmn]

theorem w3_sum_neg_one_pow (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), ((-1 : ℂ)) ^ j = if 2 ∣ k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with hk | hk
    · have h1 : ¬ 2 ∣ k + 1 := by rw [← even_iff_two_dvd]; simpa using hk.add_one
      rw [if_pos (even_iff_two_dvd.mp hk), if_neg h1, (hk.add_one).neg_one_pow]
      simp
    · have h1 : 2 ∣ k + 1 := by rw [← even_iff_two_dvd]; exact hk.add_one
      rw [if_neg (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hk), if_pos h1,
        (hk.add_one).neg_one_pow]
      simp

/-- Values of the arithmetic function of `χ₄` at prime powers. -/
theorem w3_chi_pow (p x : ℕ) (hp : p ≠ 0) :
    toArithmeticFunction (fun d : ℕ => ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ)) (p ^ x) =
      (((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℂ)) ^ x := by
  change (if p ^ x = 0 then 0 else _) = _
  rw [if_neg (pow_ne_zero x hp), Nat.cast_pow, map_pow, Int.cast_pow]

theorem w3_toArith_one : toArithmeticFunction (1 : ℕ → ℂ) =
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
  ext n
  by_cases hn : n = 0
  · simp [hn, toArithmeticFunction]
  · simp [hn, toArithmeticFunction, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply]

/-- **The ideal-count identity for `ℚ(i)`**, from the generic counting inputs
(`hone`, `hmul`, `hunique`, `hsplit` are proved generically in W1/W2 and plugged in
at integration): `#{I : N I = n} = ∑_{d ∣ n} χ₄(d)` for `n ≠ 0`. -/
theorem idealCount_QI_eq
    (hone : idealCount QI 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n →
      idealCount QI (m * n) = idealCount QI m * idealCount QI n)
    (hunique : ∀ (p : ℕ) [Fact p.Prime] (f : ℕ), 0 < f →
      (primesOver (span {(p : ℤ)}) (𝓞 QI)).ncard = 1 →
      (∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 QI), inertiaDeg P ℤ = f) →
      ∀ k : ℕ, idealCount QI (p ^ k) = if f ∣ k then 1 else 0)
    (hsplit : ∀ (p : ℕ) [Fact p.Prime],
      (primesOver (span {(p : ℤ)}) (𝓞 QI)).ncard = 2 →
      (∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 QI), inertiaDeg P ℤ = 1) →
      ∀ k : ℕ, idealCount QI (p ^ k) = k + 1)
    (n : ℕ) (hn : n ≠ 0) :
    (idealCount QI n : ℂ) =
      (LSeries.convolution (1 : ℕ → ℂ)
        (fun d : ℕ => ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ))) n := by
  have hF := w3_count_mult (idealCount QI) hone hmul
  have hG : (toArithmeticFunction (1 : ℕ → ℂ) * toArithmeticFunction (fun d : ℕ => ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ))).IsMultiplicative := by
    rw [w3_toArith_one]
    exact ArithmeticFunction.isMultiplicative_zeta.natCast.mul w3_chi_mult
  have key : toArithmeticFunction (fun n => (idealCount QI n : ℂ)) =
      toArithmeticFunction 1 * toArithmeticFunction (fun d : ℕ => ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ)) := by
    rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hF _ hG]
    intro p k hp
    have hp0 : p ≠ 0 := hp.ne_zero
    have : Fact p.Prime := ⟨hp⟩
    rw [w3_toArith_one, ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
    rw [Finset.sum_congr rfl (fun x _ => w3_chi_pow p x hp0)]
    simp only [toArithmeticFunction, ArithmeticFunction.coe_mk, pow_ne_zero k hp0, if_false]
    rcases hp.eq_two_or_odd' with rfl | hodd
    · have h2 : ZMod.χ₄ ((2 : ℕ) : ZMod 4) = 0 := by decide
      rw [hunique 2 1 one_pos QI_two.1 QI_two.2 k, h2, Finset.sum_range_succ']
      simp
    · rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd) with h1 | h3
      · rw [hsplit p (QI_one_mod_four p h1).1 (QI_one_mod_four p h1).2 k,
          ZMod.χ₄_nat_one_mod_four h1]
        simp
      · rw [hunique p 2 two_pos (QI_three_mod_four p h3).1 (QI_three_mod_four p h3).2 k,
          ZMod.χ₄_nat_three_mod_four h3, Int.cast_neg, Int.cast_one, w3_sum_neg_one_pow k]
        split_ifs <;> simp
  change _ = (toArithmeticFunction (1 : ℕ → ℂ) *
    toArithmeticFunction (fun d : ℕ => ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ))) n
  rw [← key]
  simp [toArithmeticFunction, hn]

end W3

end GaussianERH

#print axioms GaussianERH.idealCount_one
#print axioms GaussianERH.idealCount_mul
#print axioms GaussianERH.idealCount_prime_pow_of_unique
#print axioms GaussianERH.idealCount_prime_pow_of_split
#print axioms GaussianERH.QI_two
#print axioms GaussianERH.QI_one_mod_four
#print axioms GaussianERH.QI_three_mod_four
#print axioms GaussianERH.idealCount_QI_eq

/-! ## ERH for `ℚ(i)`, assembled (under the Dirichlet GRH hypothesis) -/

/-- **`hcoeff` for `ℚ(i)`, proved.** The number of ideals of norm `n` in the ring of
integers of `ℚ(i) = CyclotomicField 4 ℚ` is `∑_{d ∣ n} χ₄(d)`. -/
theorem hcoeff_QI (n : ℕ) (hn : n ≠ 0) :
    (Nat.card {I : Ideal (𝓞 GaussianERH.QI) // Ideal.absNorm I = n} : ℂ)
      = (LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => chiFour n)) n := by
  have hfun : (fun n : ℕ => chiFour n) = (fun d : ℕ => ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ)) := by
    funext d
    exact chiFour_agrees_ZMod_chiFour d
  rw [hfun]
  exact GaussianERH.idealCount_QI_eq (GaussianERH.idealCount_one _)
    (fun hm hn hmn => GaussianERH.idealCount_mul _ hm hn hmn)
    (by
      intro p _ f hf hS hfP k
      exact GaussianERH.idealCount_prime_pow_of_unique p f hf hS hfP k)
    (by
      intro p _ hS hfP k
      exact GaussianERH.idealCount_prime_pow_of_split p hS hfP k) n hn

/-- The Dedekind-zeta datum of `ℚ(i)`: continuation `ζ · L(χ₄)`, functional equation,
holomorphy and anchoring to Mathlib's `dedekindZeta`, with every input proved. -/
noncomputable def gaussianDatum : DedekindZetaDatum GaussianERH.QI :=
  quadraticDatum (N := 4) four_ne_one_nat chiFour chiFour_isPrimitive chiFour_sq
    chiFour_rootNumber_ne_zero hcoeff_QI

/-- **ERH for `ℚ(i)`**, under `DirichletGRH` (the exact shape of the base project's
`LFunction_ne_zero_of_half_lt_re`, taken here as a hypothesis, not imported). All the
nonvanishing comes from that hypothesis applied to `ζ` and `L(χ₄)`. -/
theorem dedekindERH_QI (hgrh : DirichletGRH) : DedekindERH GaussianERH.QI gaussianDatum :=
  dedekindERH_quadratic_i_assembled hgrh hcoeff_QI

/-- The same for *every* datum of `ℚ(i)` (by `dedekindERH_iff`): a statement about the
field, independent of the chosen continuation data. -/
theorem dedekindERH_QI_of_datum (hgrh : DirichletGRH)
    (D : DedekindZetaDatum GaussianERH.QI) : DedekindERH GaussianERH.QI D :=
  (dedekindERH_iff gaussianDatum D).1 (dedekindERH_QI hgrh)

/-- Critical-line form: under `DirichletGRH`, every zero of the continued Dedekind zeta of
`ℚ(i)` in the open critical strip has real part `1/2`. -/
theorem dedekindZeta_QI_zeros_on_line (hgrh : DirichletGRH)
    (D : DedekindZetaDatum GaussianERH.QI) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → D.ζ s = 0 → s.re = 1 / 2 :=
  dedekindZetaCriticalLine GaussianERH.QI D (dedekindERH_QI_of_datum hgrh D)

#print axioms hcoeff_QI
#print axioms gaussianDatum
#print axioms dedekindERH_QI
#print axioms dedekindERH_QI_of_datum
#print axioms dedekindZeta_QI_zeros_on_line


/-! ## The glue `NumberField.dedekindZeta ℚ = riemannZeta` -/

/-- The ring of integers of `ℚ`, as a `ℤ`-algebra equivalence with `ℤ`. -/
noncomputable def ratAlgEquiv : (𝓞 ℚ) ≃ₐ[ℤ] ℤ where
  __ := Rat.ringOfIntegersEquiv
  commutes' := fun _ => by simp

theorem norm_rat_ofInt (x : 𝓞 ℚ) :
    (Algebra.norm ℤ) x = Rat.ringOfIntegersEquiv x := by
  have h : (Algebra.norm ℤ) (ratAlgEquiv x) = (Algebra.norm ℤ) x :=
    Algebra.norm_eq_of_algEquiv ratAlgEquiv x
  have h2 : (Algebra.norm ℤ) (ratAlgEquiv x) = ratAlgEquiv x := by simp
  exact (h2.symm.trans h).symm

theorem comap_span_singleton_rat (g : ℤ) :
    Ideal.comap Rat.ringOfIntegersEquiv (Ideal.span {(g : ℤ)}) =
      Ideal.span {Rat.ringOfIntegersEquiv.symm g} := by
  ext x
  simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨Rat.ringOfIntegersEquiv.symm c, ?_⟩
    have := congrArg Rat.ringOfIntegersEquiv.symm hc
    simpa [map_mul, Rat.ringOfIntegersEquiv.symm_apply_apply] using this
  · rintro ⟨c, hc⟩
    refine ⟨Rat.ringOfIntegersEquiv c, ?_⟩
    have := congrArg Rat.ringOfIntegersEquiv hc
    simpa [map_mul, Rat.ringOfIntegersEquiv.apply_symm_apply] using this

/-- Every ideal of `𝓞 ℚ` with absolute norm `n` is the principal ideal
generated by the lift of `n`. -/
theorem ideal_rat_eq_span {I : Ideal (𝓞 ℚ)} {n : ℕ} (h : Ideal.absNorm I = n) :
    I = Ideal.span {Rat.ringOfIntegersEquiv.symm (n : ℤ)} := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : ℤ, Ideal.map Rat.ringOfIntegersEquiv I = Ideal.span {g} :=
    ⟨_, (Submodule.IsPrincipal.span_singleton_generator
      (Ideal.map Rat.ringOfIntegersEquiv I)).symm⟩
  have hcomap : Ideal.comap Rat.ringOfIntegersEquiv (Ideal.map Rat.ringOfIntegersEquiv I) = I :=
    Rat.ringOfIntegersEquiv.idealComapOrderIso.right_inv I
  rw [hg, comap_span_singleton_rat] at hcomap
  have hI : I = Ideal.span {Rat.ringOfIntegersEquiv.symm g} := hcomap.symm
  have hgabs : Ideal.absNorm (Ideal.span {Rat.ringOfIntegersEquiv.symm g}) = n := by
    rw [← hI]; exact h
  rw [Ideal.absNorm_span_singleton, norm_rat_ofInt, Rat.ringOfIntegersEquiv.apply_symm_apply] at hgabs
  rcases (by omega : g = (n : ℤ) ∨ g = -((n : ℤ))) with rfl | rfl
  · exact hI
  · rw [hI, map_neg, Ideal.span_singleton_neg]

/-- Exactly one ideal of `𝓞 ℚ` per absolute norm. -/
theorem card_ideal_rat_absNorm (n : ℕ) :
    Nat.card {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} = 1 := by
  have hw : Ideal.absNorm (Ideal.span {Rat.ringOfIntegersEquiv.symm (n : ℤ)}) = n := by
    rw [Ideal.absNorm_span_singleton, norm_rat_ofInt,
      Rat.ringOfIntegersEquiv.apply_symm_apply, Int.natAbs_natCast]
  have hsub : ∀ I : {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n},
      I = ⟨Ideal.span {Rat.ringOfIntegersEquiv.symm (n : ℤ)}, hw⟩ :=
    fun I => Subtype.ext (ideal_rat_eq_span I.2)
  haveI : Nonempty {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} :=
    ⟨⟨Ideal.span {Rat.ringOfIntegersEquiv.symm (n : ℤ)}, hw⟩⟩
  haveI : Subsingleton {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} :=
    ⟨fun a b => by rw [hsub a, hsub b]⟩
  exact Nat.card_unique

/-- The L-series coefficients of the Dedekind zeta function of `ℚ` are
identically `1`. -/
theorem dedekindZeta_rat_coeffs (n : ℕ) :
    ((Nat.card {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} : ℕ) : ℂ) = 1 := by
  rw [card_ideal_rat_absNorm]
  norm_num

/-- **The glue**: Mathlib's Dedekind zeta function of `ℚ` coincides with
Mathlib's Riemann zeta function on the convergence half-plane. -/
theorem dedekindZeta_rat_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta ℚ s = riemannZeta s := by
  unfold NumberField.dedekindZeta
  rw [← LSeries_one_eq_riemannZeta hs]
  congr 1
  funext n
  simpa using dedekindZeta_rat_coeffs n

/-! ## The full loop for K = ℚ: the ERH datum, anchored and bridged -/

/-- The ERH datum for `ℚ`, carried by Mathlib's own Riemann zeta. The anchor
field (`agrees`) is *proved* from the glue theorem above — no hypotheses. -/
noncomputable def riemannZetaDatum : DedekindZetaDatum ℚ where
  ζ := riemannZeta
  Λ := completedRiemannZeta
  γ := Gammaℝ
  ε := 1
  agrees := ⟨2, by norm_num,
    fun s hs => by
      simp only [Set.mem_ofPred] at hs
      exact (dedekindZeta_rat_eq_riemannZeta (by linarith)).symm⟩
  hε := one_ne_zero
  hγ := fun s hs0 _ => gammaR_ne_zero_of_re_pos hs0
  hΛζ := fun s hs0 _ => completedRiemannZeta_eq_gammaR_mul_riemannZeta hs0
  hfe := completedRiemannZeta_one_sub_mul
  holo := fun _ hs => (differentiableAt_riemannZeta hs).differentiableWithinAt

/-- **Closing the loop**: the (machine-verified) Riemann Hypothesis yields the
ERH statement for `ℚ` through the anchored datum. -/
theorem dedekindERH_rat_of_RH (h : RiemannHypothesis) : DedekindERH ℚ riemannZetaDatum := by
  intro s hs hs1 hz
  have htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hr := congrArg Complex.re hn
    simp [Complex.mul_re, Complex.add_re] at hr
    have hnng : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have := h s hz htriv hs1
  linarith

/-- **The converse bridge**: the ERH statement for `ℚ` (through the anchored
datum) implies Mathlib's `RiemannHypothesis`. The argument is the mirror step
of the parent project (`Formalism.VW.rh_of_right`), replayed on the datum. -/
theorem riemannHypothesis_of_dedekindERH_rat (h : DedekindERH ℚ riemannZetaDatum) :
    RiemannHypothesis := by
  have hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
    fun s hs hs1 => h s hs hs1
  unfold RiemannHypothesis
  intro s hs htriv hs1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hs
      norm_num at hs
    have ht : 1 / 2 < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have h1 : (1 - s) ≠ 1 := by
      intro h
      apply hs0
      linear_combination -h
    have hnat : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
      intro n h
      have hr := congrArg Complex.re h
      rw [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hr
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have key := riemannZeta_one_sub hnat h1
    rw [sub_sub_cancel, hs] at key
    have hz' := hz (1 - s) ht h1
    have h2pi : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.2 (Or.inl (mul_ne_zero two_ne_zero hpi)))
    have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hcos : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) ≠ 0 := by
      rw [Ne, Complex.cos_eq_zero_iff]
      rintro ⟨k, hk⟩
      have h3 : ((1 - s) - (2 * (k : ℂ) + 1)) * (Real.pi : ℂ) = 0 := by
        linear_combination 2 * hk
      rcases mul_eq_zero.1 h3 with h | h
      · have hsk : s = -2 * (k : ℂ) := by linear_combination -h
        have hre : s.re = -2 * (k : ℝ) := by
          rw [hsk, Complex.mul_re]
          simp
        rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
        · have : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
          linarith
        · apply hs0
          rw [hsk, hk0]
          simp
        · apply htriv
          refine ⟨(k - 1).toNat, ?_⟩
          have hnk : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
          have h' : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
            have := congrArg (fun m : ℤ => (m : ℂ)) hnk
            push_cast at this
            exact this
          rw [hsk, h']
          ring
      · exact hpi h
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero h2pi hG) hcos) hz') key.symm
  · exact heq
  · exact absurd hs (hz s hgt hs1)

/-- **RH and ERH(ℚ) are equivalent**, machine-checked in both directions. -/
theorem riemannHypothesis_iff_dedekindERH_rat :
    RiemannHypothesis ↔ DedekindERH ℚ riemannZetaDatum :=
  ⟨dedekindERH_rat_of_RH, riemannHypothesis_of_dedekindERH_rat⟩

#print axioms riemannZetaDatum
#print axioms dedekindERH_rat_of_RH
#print axioms riemannHypothesis_of_dedekindERH_rat
#print axioms riemannHypothesis_iff_dedekindERH_rat

#print axioms gammaR_ne_zero_of_re_pos
#print axioms completedRiemannZeta_eq_gammaR_mul_riemannZeta
#print axioms riemannZetaCriticalLine
