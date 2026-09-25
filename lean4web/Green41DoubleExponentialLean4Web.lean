import Mathlib

#eval Lean.versionString

/-!
# Green's Problem 41: standalone Lean4Web proof of the double-exponential bound

This file reproduces the Formal Conjectures definitions `pyjamaSet`, `coveringCopies` and
`minCopies` (`FormalConjectures/GreensOpenProblems/41.lean`) and proves the right-hand side of
`green_41.variants.double_exponential_bound`: for some `C` and `ε₀ > 0`,
`minCopies ε ≤ exp (exp (ε ^ (-C)))` for all `0 < ε ≤ ε₀`. It uses mathlib only.
-/

/- ## Section: `Defs` -/

/-
# Green 41: the Formal Conjectures definitions

The three definitions below are copied from
`FormalConjectures/GreensOpenProblems/41.lean` at Formal Conjectures commit
`40a8592cb6f7e96cb9a8275d96bb3e013feeb1dc` (saved as `reference/FC41.lean.txt`),
with the same `open` declarations. Only the `module`/`public` wrappers are dropped.
-/

namespace Green41

open Complex Set Pointwise

/--
The pyjama set is the set of points in the complex plane whose real part is within $\varepsilon$ of
an integer.
-/
def pyjamaSet (ε : ℝ) : Set ℂ :=
  { z | ∃ k : ℤ, |z.re - (k : ℝ)| ≤ ε }

/-- The set of valid numbers of rotated copies of the pyjama set of width ε that cover the plane. -/
def coveringCopies (ε : ℝ) : Set ℕ :=
  { n : ℕ | ∃ (Θ : Finset ℝ), Θ.card = n ∧
    (⋃ θ ∈ Θ, exp (θ * I) • pyjamaSet ε) = univ }

/-- The minimal number of rotated copies of the pyjama set of width ε needed to cover the plane. -/
noncomputable def minCopies (ε : ℝ) : ℕ :=
  sInf (coveringCopies ε)

/-- The right-hand side of `Green41.green_41.variants.double_exponential_bound` in FC. -/
def DoubleExponentialBound : Prop :=
  ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀, (minCopies ε : ℝ) ≤ Real.exp (Real.exp (ε ^ (-C)))

end Green41

/- ## Section: `Bridge` -/

/-
# From a finite covering by unit rotations to a bound on `minCopies`

`InStripe ε u z` says that `z` lies in the open pyjama stripe of width `ε`
rotated by the unit complex number `u`, i.e. the real part of `u * z` is within
`ε` of an integer. A finite set of unit rotations covering the plane in this
sense bounds the FC quantity `minCopies ε`.
-/

namespace Green41

open Complex Set Pointwise

/-- `z` lies in the open stripe of width `ε` rotated by `u`. -/
def InStripe (ε : ℝ) (u z : ℂ) : Prop :=
  ∃ k : ℤ, |(u * z).re - k| < ε

lemma exp_neg_arg_mul_self {u : ℂ} (hu : ‖u‖ = 1) :
    Complex.exp (((-Complex.arg u : ℝ) : ℂ) * I) * u = 1 := by
  have h := Complex.norm_mul_exp_arg_mul_I u
  rw [hu, Complex.ofReal_one, one_mul] at h
  have h0 : ((-Complex.arg u : ℝ) : ℂ) * I + Complex.arg u * I = 0 := by
    push_cast
    ring
  calc Complex.exp (((-Complex.arg u : ℝ) : ℂ) * I) * u
      = Complex.exp (((-Complex.arg u : ℝ) : ℂ) * I) * Complex.exp (Complex.arg u * I) := by
        rw [h]
    _ = 1 := by rw [← Complex.exp_add, h0, Complex.exp_zero]

/-- A finite family of unit rotations whose open stripes cover `ℂ` bounds `minCopies`. -/
theorem minCopies_le_of_cover {ε : ℝ} (Ω : Finset ℂ) (hunit : ∀ u ∈ Ω, ‖u‖ = 1)
    (hcov : ∀ z : ℂ, ∃ u ∈ Ω, InStripe ε u z) : minCopies ε ≤ Ω.card := by
  classical
  set Θ : Finset ℝ := Ω.image (fun u => -Complex.arg u) with hΘ
  have hmem : Θ.card ∈ coveringCopies ε := by
    refine ⟨Θ, rfl, ?_⟩
    ext z
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨u, hu, k, hk⟩ := hcov z
    refine ⟨-Complex.arg u, Finset.mem_image.mpr ⟨u, hu, rfl⟩, ?_⟩
    rw [Set.mem_smul_set]
    refine ⟨u * z, ⟨k, hk.le⟩, ?_⟩
    rw [smul_eq_mul, ← mul_assoc, exp_neg_arg_mul_self (hunit u hu), one_mul]
  calc minCopies ε ≤ Θ.card := Nat.sInf_le hmem
    _ ≤ Ω.card := Finset.card_image_le

end Green41

/- ## Section: `Endgame` -/

/-
# The end game: from lattice confinement to a covering of the whole plane

This is Lemma 7.1 of the round-2 draft. Suppose the points not covered by a
finite rotation set `Θ` lie within `H` of the lattice `(D / L) ℤ[i]`, and a finite
set `U` of rational rotations `a / b` covers the disc of radius `2 L H`.
If `|D| > 2 L H Q`, where `Q` bounds the denominators, then the rotations
`θ u ν`, `θ u ν̄` (`θ ∈ Θ`, `u ∈ U`) together with `U` cover the plane, where
`ν = 1/(2L) + i √(1 - 1/(4L²))` satisfies `ν + ν̄ = 1/L`.
No coprimality of `a` and `b` is used.
-/

namespace Green41

open Complex ComplexConjugate

/-- A Gaussian integer of absolute value less than one is zero. -/
lemma gaussianInt_eq_zero_of_norm_lt_one {x : GaussianInt} (hx : ‖(x : ℂ)‖ < 1) : x = 0 := by
  have h1 : Complex.normSq (x : ℂ) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have h0 : 0 ≤ ‖(x : ℂ)‖ := norm_nonneg _
    nlinarith
  rw [← GaussianInt.intCast_real_norm] at h1
  have h2 : x.norm < 1 := by exact_mod_cast h1
  have h3 : x.norm = 0 := le_antisymm (by omega) (GaussianInt.norm_nonneg x)
  exact GaussianInt.norm_eq_zero.mp h3

/-- The integer-centre step: two lattice representations of `w` and `(a / b) w` with
errors at most `H` force `b k' = a k` once the lattice step `|D| / L` is large. -/
lemma center_eq {D a b k k' : GaussianInt} {L : ℕ} (hL : 0 < L) {H Q : ℝ} {w : ℂ}
    (hb : (b : ℂ) ≠ 0) (hab : ‖(a : ℂ)‖ = ‖(b : ℂ)‖) (hbQ : ‖(b : ℂ)‖ ≤ Q)
    (hD : 2 * L * H * Q < ‖(D : ℂ)‖)
    (hk : ‖w - (D : ℂ) / L * k‖ ≤ H)
    (hk' : ‖((a : ℂ) / b) * w - (D : ℂ) / L * k'‖ ≤ H) :
    b * k' = a * k := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set X : GaussianInt := a * k - b * k' with hX
  have hXc : (X : ℂ) = (a : ℂ) * k - (b : ℂ) * k' := by
    rw [hX, GaussianInt.toComplex_sub, GaussianInt.toComplex_mul, GaussianInt.toComplex_mul]
  have hkey : (D : ℂ) / L * X
      = (b : ℂ) * (((a : ℂ) / b) * w - (D : ℂ) / L * k') - (a : ℂ) * (w - (D : ℂ) / L * k) := by
    rw [hXc]
    field_simp
    ring
  have hH : 0 ≤ H := le_trans (norm_nonneg _) hk
  have hbound : ‖(D : ℂ) / L * X‖ ≤ 2 * Q * H := by
    rw [hkey]
    calc ‖(b : ℂ) * (((a : ℂ) / b) * w - (D : ℂ) / L * k') - (a : ℂ) * (w - (D : ℂ) / L * k)‖
        ≤ ‖(b : ℂ) * (((a : ℂ) / b) * w - (D : ℂ) / L * k')‖ + ‖(a : ℂ) * (w - (D : ℂ) / L * k)‖ :=
          norm_sub_le _ _
      _ = ‖(b : ℂ)‖ * ‖((a : ℂ) / b) * w - (D : ℂ) / L * k'‖ + ‖(a : ℂ)‖ * ‖w - (D : ℂ) / L * k‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ Q * H + Q * H := by
          rw [hab]
          have hb0 : 0 ≤ ‖(b : ℂ)‖ := norm_nonneg _
          have hQ : 0 ≤ Q := le_trans hb0 hbQ
          gcongr
      _ = 2 * Q * H := by ring
  have hX0 : X = 0 := by
    by_contra hne
    have h1 : 1 ≤ ‖(X : ℂ)‖ := by
      by_contra hlt
      exact hne (gaussianInt_eq_zero_of_norm_lt_one (lt_of_not_ge hlt))
    have hnorm : ‖(D : ℂ) / L * X‖ = ‖(D : ℂ)‖ / L * ‖(X : ℂ)‖ := by
      rw [norm_mul, norm_div, Complex.norm_natCast]
    have hDpos : 0 ≤ ‖(D : ℂ)‖ / L := div_nonneg (norm_nonneg _) hLr.le
    have h2 : ‖(D : ℂ)‖ / L ≤ 2 * Q * H := by
      calc ‖(D : ℂ)‖ / L = ‖(D : ℂ)‖ / L * 1 := by ring
        _ ≤ ‖(D : ℂ)‖ / L * ‖(X : ℂ)‖ := by gcongr
        _ = ‖(D : ℂ) / L * X‖ := hnorm.symm
        _ ≤ 2 * Q * H := hbound
    have h3 : ‖(D : ℂ)‖ ≤ 2 * L * H * Q := by
      rw [div_le_iff₀ hLr] at h2
      linarith
    linarith
  have : a * k - b * k' = 0 := hX0
  exact (sub_eq_zero.mp this).symm

/-- The irrational rotation `ν = 1/(2L) + i √(1 - 1/(4L²))`. -/
noncomputable def nu (L : ℕ) : ℂ :=
  ((1 / (2 * (L : ℝ)) : ℝ) : ℂ) + ((Real.sqrt (1 - 1 / (4 * (L : ℝ) ^ 2)) : ℝ) : ℂ) * I

lemma nu_re (L : ℕ) : (nu L).re = 1 / (2 * (L : ℝ)) := by
  simp [nu]

lemma nu_add_conj {L : ℕ} (hL : 0 < L) : nu L + conj (nu L) = 1 / (L : ℂ) := by
  rw [Complex.add_conj, nu_re]
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  push_cast
  field_simp

lemma norm_nu {L : ℕ} (hL : 0 < L) : ‖nu L‖ = 1 := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hs : 0 ≤ 1 - 1 / (4 * (L : ℝ) ^ 2) := by
    have : 1 / (4 * (L : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  have hre : (nu L).re = 1 / (2 * (L : ℝ)) := by simp [nu]
  have him : (nu L).im = Real.sqrt (1 - 1 / (4 * (L : ℝ) ^ 2)) := by simp [nu]
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  have hn : Complex.normSq (nu L) = 1 := by
    rw [Complex.normSq_apply, hre, him, Real.mul_self_sqrt hs]
    field_simp
    ring
  rw [Complex.norm_def, hn, Real.sqrt_one]

/-- The rotation set of the end game. -/
noncomputable def endgameSet (Θ : Finset ℂ) (U : Finset (GaussianInt × GaussianInt)) (L : ℕ) :
    Finset ℂ := by
  classical
  exact ((Θ ×ˢ U).image fun x => x.1 * ((x.2.1 : ℂ) / x.2.2) * nu L) ∪
    ((Θ ×ˢ U).image fun x => x.1 * ((x.2.1 : ℂ) / x.2.2) * conj (nu L)) ∪
    (U.image fun p => (p.1 : ℂ) / p.2)

lemma card_endgameSet_le (Θ : Finset ℂ) (U : Finset (GaussianInt × GaussianInt)) (L : ℕ) :
    (endgameSet Θ U L).card ≤ 2 * Θ.card * U.card + U.card := by
  classical
  unfold endgameSet
  calc _ ≤ ((Θ ×ˢ U).image fun x => x.1 * ((x.2.1 : ℂ) / x.2.2) * nu L).card +
          ((Θ ×ˢ U).image fun x => x.1 * ((x.2.1 : ℂ) / x.2.2) * conj (nu L)).card +
          (U.image fun p => (p.1 : ℂ) / p.2).card := by
        refine (Finset.card_union_le _ _).trans ?_
        gcongr
        exact Finset.card_union_le _ _
    _ ≤ (Θ ×ˢ U).card + (Θ ×ˢ U).card + U.card := by
        gcongr <;> exact Finset.card_image_le
    _ = 2 * Θ.card * U.card + U.card := by
        rw [Finset.card_product]
        ring

lemma norm_of_mem_endgameSet {Θ : Finset ℂ} {U : Finset (GaussianInt × GaussianInt)} {L : ℕ}
    (hL : 0 < L) (hΘ : ∀ θ ∈ Θ, ‖θ‖ = 1)
    (hU : ∀ p ∈ U, (p.2 : ℂ) ≠ 0 ∧ ‖(p.1 : ℂ)‖ = ‖(p.2 : ℂ)‖) :
    ∀ v ∈ endgameSet Θ U L, ‖v‖ = 1 := by
  classical
  have hq : ∀ p ∈ U, ‖(p.1 : ℂ) / p.2‖ = 1 := by
    intro p hp
    obtain ⟨hb, hab⟩ := hU p hp
    rw [norm_div, hab, div_self (norm_ne_zero_iff.mpr hb)]
  intro v hv
  unfold endgameSet at hv
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product] at hv
  rcases hv with (⟨x, ⟨hx1, hx2⟩, rfl⟩ | ⟨x, ⟨hx1, hx2⟩, rfl⟩) | ⟨p, hp, rfl⟩
  · rw [norm_mul, norm_mul, hΘ _ hx1, hq _ hx2, norm_nu hL]; ring
  · rw [norm_mul, norm_mul, hΘ _ hx1, hq _ hx2, Complex.norm_conj, norm_nu hL]; ring
  · exact hq p hp

/-- Lemma 7.1 of the round-2 draft. -/
theorem endgame_cover {ε H Q : ℝ} {L : ℕ} (hL : 0 < L) {D : GaussianInt}
    (Θ : Finset ℂ) (U : Finset (GaussianInt × GaussianInt))
    (hconf : ∀ w : ℂ, (∀ θ ∈ Θ, ¬ InStripe ε θ w) →
      ∃ k : GaussianInt, ‖w - (D : ℂ) / L * k‖ ≤ H)
    (hU : ∀ p ∈ U, (p.2 : ℂ) ≠ 0 ∧ ‖(p.1 : ℂ)‖ = ‖(p.2 : ℂ)‖ ∧ ‖(p.2 : ℂ)‖ ≤ Q)
    (h1 : ((1 : GaussianInt), (1 : GaussianInt)) ∈ U)
    (hcover : ∀ e : ℂ, ‖e‖ ≤ 2 * L * H → ∃ p ∈ U, InStripe ε ((p.1 : ℂ) / p.2) e)
    (hD : 2 * L * H * Q < ‖(D : ℂ)‖) :
    ∀ z : ℂ, ∃ v ∈ endgameSet Θ U L, InStripe ε v z := by
  classical
  intro z
  by_contra hz
  push Not at hz
  have memν : ∀ θ ∈ Θ, ∀ p ∈ U, θ * ((p.1 : ℂ) / p.2) * nu L ∈ endgameSet Θ U L := by
    intro θ hθ p hp
    unfold endgameSet
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨(θ, p), Finset.mem_product.mpr ⟨hθ, hp⟩, rfl⟩))
  have memν' : ∀ θ ∈ Θ, ∀ p ∈ U, θ * ((p.1 : ℂ) / p.2) * conj (nu L) ∈ endgameSet Θ U L := by
    intro θ hθ p hp
    unfold endgameSet
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(θ, p), Finset.mem_product.mpr ⟨hθ, hp⟩, rfl⟩))
  have memU : ∀ p ∈ U, ((p.1 : ℂ) / p.2) ∈ endgameSet Θ U L := by
    intro p hp
    unfold endgameSet
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have tr : ∀ θ u v : ℂ, InStripe ε θ (u * v * z) ↔ InStripe ε (θ * u * v) z := by
    intro θ u v
    unfold InStripe
    rw [show θ * (u * v * z) = θ * u * v * z by ring]
  -- lattice representations of `u v z` for `v ∈ {ν, ν̄}` and `u ∈ U`
  have rep : ∀ v : ℂ, (v = nu L ∨ v = conj (nu L)) → ∀ p ∈ U, ∃ k : GaussianInt,
      ‖((p.1 : ℂ) / p.2) * v * z - (D : ℂ) / L * k‖ ≤ H := by
    intro v hv p hp
    apply hconf
    intro θ hθ hs
    rw [tr] at hs
    rcases hv with rfl | rfl
    · exact hz _ (memν θ hθ p hp) hs
    · exact hz _ (memν' θ hθ p hp) hs
  choose! kf hkf using rep
  have one_div_one : ((1 : GaussianInt) : ℂ) / ((1 : GaussianInt) : ℂ) = 1 := by
    rw [GaussianInt.toComplex_one, div_one]
  -- the base representations (u = 1)
  have base : ∀ v : ℂ, (v = nu L ∨ v = conj (nu L)) →
      ‖v * z - (D : ℂ) / L * kf v (1, 1)‖ ≤ H := by
    intro v hv
    have := hkf v hv (1, 1) h1
    simpa [one_div_one] using this
  -- integer centres: `u * k_v = k_{u v}` as complex numbers
  have centre : ∀ v : ℂ, (v = nu L ∨ v = conj (nu L)) → ∀ p ∈ U,
      ((kf v p : GaussianInt) : ℂ) = ((p.1 : ℂ) / p.2) * kf v (1, 1) := by
    intro v hv p hp
    obtain ⟨hb, hab, hbQ⟩ := hU p hp
    have h := center_eq (D := D) (a := p.1) (b := p.2) (k := kf v (1, 1)) (k' := kf v p)
      (w := v * z) hL hb hab hbQ hD (base v hv) (by rw [← mul_assoc]; exact hkf v hv p hp)
    have hc : (p.2 : ℂ) * (kf v p : ℂ) = (p.1 : ℂ) * (kf v (1, 1) : ℂ) := by
      rw [← GaussianInt.toComplex_mul, ← GaussianInt.toComplex_mul, h]
    field_simp
    linear_combination hc
  set kν := kf (nu L) (1, 1)
  set kν' := kf (conj (nu L)) (1, 1)
  set k₀ : GaussianInt := kν + kν'
  -- the decomposition `z = D k₀ + e` with `|e| ≤ 2 L H`
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set e : ℂ := z - (D : ℂ) * k₀ with he
  have he_eq : e = (L : ℂ) * ((nu L * z - (D : ℂ) / L * kν) +
      (conj (nu L) * z - (D : ℂ) / L * kν')) := by
    have h2 : (L : ℂ) * ((nu L * z - (D : ℂ) / L * kν) + (conj (nu L) * z - (D : ℂ) / L * kν'))
        = (L : ℂ) * (nu L + conj (nu L)) * z - (L : ℂ) * ((D : ℂ) / L) * ((kν : ℂ) + kν') := by
      ring
    have hL1 : (L : ℂ) * (1 / (L : ℂ)) = 1 := by field_simp
    have hLD : (L : ℂ) * ((D : ℂ) / L) = D := by field_simp
    rw [h2, nu_add_conj hL, hL1, hLD, he, GaussianInt.toComplex_add]
    ring
  have he_norm : ‖e‖ ≤ 2 * L * H := by
    rw [he_eq, norm_mul, Complex.norm_natCast]
    have h1' := base (nu L) (Or.inl rfl)
    have h2' := base (conj (nu L)) (Or.inr rfl)
    calc (L : ℝ) * ‖(nu L * z - (D : ℂ) / L * kν) + (conj (nu L) * z - (D : ℂ) / L * kν')‖
        ≤ (L : ℝ) * (H + H) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add h1' h2')
      _ = 2 * L * H := by ring
  obtain ⟨p, hp, m, hm⟩ := hcover e he_norm
  -- `u k₀` is a Gaussian integer
  set g : GaussianInt := kf (nu L) p + kf (conj (nu L)) p
  have hg : ((p.1 : ℂ) / p.2) * (k₀ : ℂ) = (g : ℂ) := by
    rw [GaussianInt.toComplex_add, GaussianInt.toComplex_add, centre _ (Or.inl rfl) p hp,
      centre _ (Or.inr rfl) p hp]
    ring
  apply hz _ (memU p hp)
  refine ⟨m + (D * g).re, ?_⟩
  have hz_eq : ((p.1 : ℂ) / p.2) * z = ((p.1 : ℂ) / p.2) * e + ((D * g : GaussianInt) : ℂ) := by
    rw [GaussianInt.toComplex_mul, ← hg, he]
    ring
  rw [hz_eq, Complex.add_re, ← GaussianInt.intCast_re]
  push_cast
  convert hm using 2
  ring

end Green41

/- ## Section: `Gaussian` -/

/-
# Gaussian-integer algebra for the orbit `θ₅^s θ₁₃^t`

With `P = 1 + 2i`, `Q = 2 + 3i`, `θ₅ = P / P̄`, `θ₁₃ = Q / Q̄`, the rotations
`rot s t = θ₅^s θ₁₃^t` (`s, t ≤ K`) satisfy `Δ · rot s t = v(s,t) ∈ ℤ[i]`
with `Δ = P̄^K Q̄^K`. Distinct labels give distinct `v`, so every nonzero orbit
difference `r` is `d / Δ` with `d ∈ ℤ[i] \ {0}`. The product `L` of the norms of all
these `d` is a common denominator: `L / r ∈ ℤ[i]`. We also record `|r| ≥ |Δ|⁻¹`.

This is the simple common denominator of the first draft; its size is still
polynomial in `K` after taking logarithms, which is all the final bound needs.
-/

namespace Green41

open Complex ComplexConjugate

/-- `P = 1 + 2i`. -/
def gP : GaussianInt := ⟨1, 2⟩
/-- `P̄ = 1 - 2i`. -/
def gPb : GaussianInt := ⟨1, -2⟩
/-- `Q = 2 + 3i`. -/
def gQ : GaussianInt := ⟨2, 3⟩
/-- `Q̄ = 2 - 3i`. -/
def gQb : GaussianInt := ⟨2, -3⟩

lemma norm_gP : gP.norm = 5 := by decide
lemma norm_gPb : gPb.norm = 5 := by decide
lemma norm_gQ : gQ.norm = 13 := by decide
lemma norm_gQb : gQb.norm = 13 := by decide

lemma norm_toComplex (x : GaussianInt) : ‖(x : ℂ)‖ = Real.sqrt (x.norm : ℝ) := by
  rw [Complex.norm_def, GaussianInt.intCast_real_norm]

lemma norm_dvd_norm {x y : GaussianInt} (h : x ∣ y) : x.norm ∣ y.norm := by
  obtain ⟨c, rfl⟩ := h
  rw [Zsqrtd.norm_mul]
  exact dvd_mul_right _ _

lemma irreducible_of_norm_prime {x : GaussianInt} (hx : (x.norm.natAbs).Prime) :
    Irreducible x := by
  constructor
  · intro hu
    rw [← Zsqrtd.norm_eq_one_iff] at hu
    rw [hu] at hx
    exact Nat.not_prime_one hx
  · intro a b hab
    have h := congrArg (fun z : GaussianInt => z.norm.natAbs) hab
    simp only [Zsqrtd.norm_mul, Int.natAbs_mul] at h
    rw [h] at hx
    rcases Nat.prime_mul_iff.mp hx with ⟨_, hb1⟩ | ⟨_, ha1⟩
    · exact Or.inr (Zsqrtd.norm_eq_one_iff.mp hb1)
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp ha1)

lemma prime_gP : Prime gP :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_norm_prime (by rw [norm_gP]; norm_num))

lemma prime_gQ : Prime gQ :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_norm_prime (by rw [norm_gQ]; norm_num))

lemma gP_not_dvd_gPb : ¬ gP ∣ gPb := by
  intro h
  have h2 : gP ∣ gP + gPb := dvd_add (dvd_refl _) h
  have hsum : gP + gPb = 2 := by decide
  rw [hsum] at h2
  have h3 := norm_dvd_norm h2
  have h4 : (2 : GaussianInt).norm = 4 := by decide
  rw [norm_gP, h4] at h3
  norm_num at h3

lemma gP_not_dvd_gQ : ¬ gP ∣ gQ := by
  intro h
  have h3 := norm_dvd_norm h
  rw [norm_gP, norm_gQ] at h3
  norm_num at h3

lemma gP_not_dvd_gQb : ¬ gP ∣ gQb := by
  intro h
  have h3 := norm_dvd_norm h
  rw [norm_gP, norm_gQb] at h3
  norm_num at h3

lemma gQ_not_dvd_gQb : ¬ gQ ∣ gQb := by
  intro h
  have h2 : gQ ∣ gQ + gQb := dvd_add (dvd_refl _) h
  have hsum : gQ + gQb = 4 := by decide
  rw [hsum] at h2
  have h3 := norm_dvd_norm h2
  have h4 : (4 : GaussianInt).norm = 16 := by decide
  rw [norm_gQ, h4] at h3
  norm_num at h3

lemma gQ_not_dvd_gP : ¬ gQ ∣ gP := by
  intro h
  have h3 := norm_dvd_norm h
  rw [norm_gQ, norm_gP] at h3
  norm_num at h3

lemma gQ_not_dvd_gPb : ¬ gQ ∣ gPb := by
  intro h
  have h3 := norm_dvd_norm h
  rw [norm_gQ, norm_gPb] at h3
  norm_num at h3

lemma toComplex_ne_zero_of_norm {x : GaussianInt} (hx : x.norm ≠ 0) : (x : ℂ) ≠ 0 := by
  intro h
  apply hx
  rw [GaussianInt.toComplex_eq_zero] at h
  rw [h]
  decide

lemma gPb_ne_zero : (gPb : ℂ) ≠ 0 := toComplex_ne_zero_of_norm (by rw [norm_gPb]; norm_num)
lemma gQb_ne_zero : (gQb : ℂ) ≠ 0 := toComplex_ne_zero_of_norm (by rw [norm_gQb]; norm_num)

lemma cnorm_gP : ‖(gP : ℂ)‖ = Real.sqrt 5 := by rw [norm_toComplex, norm_gP]; norm_num
lemma cnorm_gPb : ‖(gPb : ℂ)‖ = Real.sqrt 5 := by rw [norm_toComplex, norm_gPb]; norm_num
lemma cnorm_gQ : ‖(gQ : ℂ)‖ = Real.sqrt 13 := by rw [norm_toComplex, norm_gQ]; norm_num
lemma cnorm_gQb : ‖(gQb : ℂ)‖ = Real.sqrt 13 := by rw [norm_toComplex, norm_gQb]; norm_num

/-- `θ₅ = P / P̄`. -/
noncomputable def θ5 : ℂ := (gP : ℂ) / (gPb : ℂ)
/-- `θ₁₃ = Q / Q̄`. -/
noncomputable def θ13 : ℂ := (gQ : ℂ) / (gQb : ℂ)
/-- The orbit rotation `θ₅^s θ₁₃^t`. -/
noncomputable def rot (s t : ℕ) : ℂ := θ5 ^ s * θ13 ^ t

lemma norm_θ5 : ‖θ5‖ = 1 := by
  rw [θ5, norm_div, cnorm_gP, cnorm_gPb, div_self (by positivity)]

lemma norm_θ13 : ‖θ13‖ = 1 := by
  rw [θ13, norm_div, cnorm_gQ, cnorm_gQb, div_self (by positivity)]

lemma norm_rot (s t : ℕ) : ‖rot s t‖ = 1 := by
  rw [rot, norm_mul, norm_pow, norm_pow, norm_θ5, norm_θ13, one_pow, one_pow, one_mul]

/-- `v(s,t) = P^s P̄^(K-s) Q^t Q̄^(K-t)`. -/
def vv (K s t : ℕ) : GaussianInt := gP ^ s * gPb ^ (K - s) * gQ ^ t * gQb ^ (K - t)

/-- `Δ = P̄^K Q̄^K`. -/
def gΔ (K : ℕ) : GaussianInt := gPb ^ K * gQb ^ K

lemma vv_eq {K s t : ℕ} (hs : s ≤ K) (ht : t ≤ K) :
    (vv K s t : ℂ) = (gΔ K : ℂ) * rot s t := by
  have hPb := gPb_ne_zero
  have hQb := gQb_ne_zero
  simp only [vv, gΔ, rot, θ5, θ13, map_mul, map_pow]
  change (gP : ℂ) ^ s * (gPb : ℂ) ^ (K - s) * (gQ : ℂ) ^ t * (gQb : ℂ) ^ (K - t) =
    (gPb : ℂ) ^ K * (gQb : ℂ) ^ K * (((gP : ℂ) / gPb) ^ s * ((gQ : ℂ) / gQb) ^ t)
  rw [pow_sub₀ _ hPb hs, pow_sub₀ _ hQb ht, div_pow, div_pow]
  field_simp

lemma cnorm_gΔ (K : ℕ) : ‖(gΔ K : ℂ)‖ = Real.sqrt 65 ^ K := by
  have h : (gΔ K : ℂ) = (gPb : ℂ) ^ K * (gQb : ℂ) ^ K := by
    simp only [gΔ, map_mul, map_pow]
  rw [h, norm_mul, norm_pow, norm_pow, cnorm_gPb, cnorm_gQb, ← mul_pow,
    ← Real.sqrt_mul (by norm_num)]
  norm_num

lemma cnorm_vv {K s t : ℕ} (hs : s ≤ K) (ht : t ≤ K) : ‖(vv K s t : ℂ)‖ = Real.sqrt 65 ^ K := by
  rw [vv_eq hs ht, norm_mul, norm_rot, mul_one, cnorm_gΔ]

/-- If `p` is prime and divides neither `x` nor `y`, then `p^m x = p^m' y` forces `m = m'`. -/
lemma pow_exp_eq {p x y : GaussianInt} (hp : Prime p) {m m' : ℕ} (hx : ¬ p ∣ x) (hy : ¬ p ∣ y)
    (h : p ^ m * x = p ^ m' * y) : m = m' := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exfalso
    have h' : p ^ m * x = p ^ m * (p ^ (m' - m) * y) := by
      rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]
    have hx' := mul_left_cancel₀ (pow_ne_zero m hp0) h'
    apply hx
    rw [hx']
    exact dvd_mul_of_dvd_left (dvd_pow_self p (Nat.sub_ne_zero_of_lt hlt)) y
  · exact heq
  · exfalso
    have h' : p ^ m' * y = p ^ m' * (p ^ (m - m') * x) := by
      rw [← h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hgt.le]
    have hy' := mul_left_cancel₀ (pow_ne_zero m' hp0) h'
    apply hy
    rw [hy']
    exact dvd_mul_of_dvd_left (dvd_pow_self p (Nat.sub_ne_zero_of_lt hgt)) x

lemma gP_not_dvd_rest (K s t : ℕ) : ¬ gP ∣ gPb ^ (K - s) * gQ ^ t * gQb ^ (K - t) := by
  intro h
  rcases prime_gP.dvd_or_dvd h with h1 | h1
  · rcases prime_gP.dvd_or_dvd h1 with h2 | h2
    · exact gP_not_dvd_gPb (prime_gP.dvd_of_dvd_pow h2)
    · exact gP_not_dvd_gQ (prime_gP.dvd_of_dvd_pow h2)
  · exact gP_not_dvd_gQb (prime_gP.dvd_of_dvd_pow h1)

lemma gQ_not_dvd_rest (K s t : ℕ) : ¬ gQ ∣ gP ^ s * gPb ^ (K - s) * gQb ^ (K - t) := by
  intro h
  rcases prime_gQ.dvd_or_dvd h with h1 | h1
  · rcases prime_gQ.dvd_or_dvd h1 with h2 | h2
    · exact gQ_not_dvd_gP (prime_gQ.dvd_of_dvd_pow h2)
    · exact gQ_not_dvd_gPb (prime_gQ.dvd_of_dvd_pow h2)
  · exact gQ_not_dvd_gQb (prime_gQ.dvd_of_dvd_pow h1)

lemma vv_inj {K s t s' t' : ℕ} (h : vv K s t = vv K s' t') : s = s' ∧ t = t' := by
  constructor
  · apply pow_exp_eq prime_gP (gP_not_dvd_rest K s t) (gP_not_dvd_rest K s' t')
    have e1 : vv K s t = gP ^ s * (gPb ^ (K - s) * gQ ^ t * gQb ^ (K - t)) := by
      simp only [vv]; ring
    have e2 : vv K s' t' = gP ^ s' * (gPb ^ (K - s') * gQ ^ t' * gQb ^ (K - t')) := by
      simp only [vv]; ring
    rw [← e1, ← e2, h]
  · apply pow_exp_eq prime_gQ (gQ_not_dvd_rest K s t) (gQ_not_dvd_rest K s' t')
    have e1 : vv K s t = gQ ^ t * (gP ^ s * gPb ^ (K - s) * gQb ^ (K - t)) := by
      simp only [vv]; ring
    have e2 : vv K s' t' = gQ ^ t' * (gP ^ s' * gPb ^ (K - s') * gQb ^ (K - t')) := by
      simp only [vv]; ring
    rw [← e1, ← e2, h]

/-- The labels `(s, t)` with `s, t ≤ K`. -/
def labels (K : ℕ) : Finset (ℕ × ℕ) := Finset.range (K + 1) ×ˢ Finset.range (K + 1)

lemma card_labels (K : ℕ) : (labels K).card = (K + 1) ^ 2 := by
  rw [labels, Finset.card_product, Finset.card_range, sq]

lemma mem_labels {K : ℕ} {x : ℕ × ℕ} : x ∈ labels K ↔ x.1 ≤ K ∧ x.2 ≤ K := by
  simp [labels]

/-- Ordered pairs of distinct labels. -/
def labelPairs (K : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (labels K ×ˢ labels K).filter (fun p => p.1 ≠ p.2)

/-- The numerator `v(λ) - v(μ)` of an orbit difference. -/
def dd (K : ℕ) (p : (ℕ × ℕ) × (ℕ × ℕ)) : GaussianInt := vv K p.1.1 p.1.2 - vv K p.2.1 p.2.2

/-- The common denominator `L = ∏ N(v(λ) - v(μ))`. -/
def commonDen (K : ℕ) : ℕ := ∏ p ∈ labelPairs K, (dd K p).norm.natAbs

lemma dd_ne_zero {K : ℕ} {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ labelPairs K) : dd K p ≠ 0 := by
  simp only [labelPairs, Finset.mem_filter] at hp
  intro h
  apply hp.2
  have h' : vv K p.1.1 p.1.2 = vv K p.2.1 p.2.2 := sub_eq_zero.mp h
  obtain ⟨h1, h2⟩ := vv_inj h'
  exact Prod.ext h1 h2

lemma dd_eq {K : ℕ} {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ labelPairs K) :
    (dd K p : ℂ) = (gΔ K : ℂ) * (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) := by
  simp only [labelPairs, Finset.mem_filter, Finset.mem_product, mem_labels] at hp
  rw [dd, GaussianInt.toComplex_sub, vv_eq hp.1.1.1 hp.1.1.2, vv_eq hp.1.2.1 hp.1.2.2]
  ring

lemma commonDen_pos (K : ℕ) : 0 < commonDen K := by
  apply Finset.prod_pos
  intro p hp
  have h := dd_ne_zero hp
  rw [Int.natAbs_pos]
  exact (GaussianInt.norm_pos).mpr h |>.ne'

/-- `L / r` is a Gaussian integer for every nonzero orbit difference `r`. -/
lemma commonDen_div {K : ℕ} {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ labelPairs K) :
    ∃ c : GaussianInt, (c : ℂ) * (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) = (commonDen K : ℂ) := by
  set d := dd K p
  set n := d.norm.natAbs
  have hn : n ∣ commonDen K := Finset.dvd_prod_of_mem (fun q => (dd K q).norm.natAbs) hp
  refine ⟨((commonDen K / n : ℕ) : GaussianInt) * gΔ K * star d, ?_⟩
  have hd := dd_eq hp
  have hnorm : (d : ℂ) * conj (d : ℂ) = (n : ℂ) := by
    rw [Complex.mul_conj, ← GaussianInt.intCast_real_norm]
    have : (n : ℤ) = d.norm := GaussianInt.abs_natCast_norm d
    rw [← this]
    push_cast
    rfl
  calc _ = ((commonDen K / n : ℕ) : ℂ) * conj (d : ℂ) *
          ((gΔ K : ℂ) * (rot p.1.1 p.1.2 - rot p.2.1 p.2.2)) := by
        simp only [map_mul, map_natCast, GaussianInt.toComplex_star]
        ring
    _ = ((commonDen K / n : ℕ) : ℂ) * ((d : ℂ) * conj (d : ℂ)) := by rw [← hd]; ring
    _ = ((commonDen K / n : ℕ) : ℂ) * (n : ℂ) := by rw [hnorm]
    _ = (commonDen K : ℂ) := by
        rw [← Nat.cast_mul, Nat.div_mul_cancel hn]

/-- `|r| ≥ 1 / |Δ|` for every nonzero orbit difference `r`. -/
lemma norm_rot_sub_ge {K : ℕ} {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ labelPairs K) :
    1 / Real.sqrt 65 ^ K ≤ ‖rot p.1.1 p.1.2 - rot p.2.1 p.2.2‖ := by
  have hd := dd_eq hp
  have hd1 : 1 ≤ ‖(dd K p : ℂ)‖ := by
    by_contra hlt
    exact dd_ne_zero hp (gaussianInt_eq_zero_of_norm_lt_one (lt_of_not_ge hlt))
  rw [hd, norm_mul, cnorm_gΔ] at hd1
  have hpos : 0 < Real.sqrt 65 ^ K := by positivity
  rw [div_le_iff₀ hpos]
  linarith [mul_comm (Real.sqrt 65 ^ K) ‖rot p.1.1 p.1.2 - rot p.2.1 p.2.2‖]

/-- `L ≤ (4 · 65^K)^((K+1)^4)`. -/
lemma commonDen_le (K : ℕ) : commonDen K ≤ (4 * 65 ^ K) ^ ((K + 1) ^ 4) := by
  have hfac : ∀ p ∈ labelPairs K, (dd K p).norm.natAbs ≤ 4 * 65 ^ K := by
    intro p hp
    have hp' := hp
    simp only [labelPairs, Finset.mem_filter, Finset.mem_product, mem_labels] at hp'
    have h1 := cnorm_vv (K := K) hp'.1.1.1 hp'.1.1.2
    have h2 := cnorm_vv (K := K) hp'.1.2.1 hp'.1.2.2
    have hle : ‖(dd K p : ℂ)‖ ≤ 2 * Real.sqrt 65 ^ K := by
      rw [dd, GaussianInt.toComplex_sub]
      calc _ ≤ ‖(vv K p.1.1 p.1.2 : ℂ)‖ + ‖(vv K p.2.1 p.2.2 : ℂ)‖ := norm_sub_le _ _
        _ = 2 * Real.sqrt 65 ^ K := by rw [h1, h2]; ring
    have hsq : ((dd K p).norm : ℝ) ≤ 4 * 65 ^ K := by
      rw [GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq]
      have h0 : 0 ≤ ‖(dd K p : ℂ)‖ := norm_nonneg _
      calc ‖(dd K p : ℂ)‖ ^ 2 ≤ (2 * Real.sqrt 65 ^ K) ^ 2 := by gcongr
        _ = 4 * 65 ^ K := by
            rw [mul_pow, ← pow_mul, mul_comm K 2, pow_mul, Real.sq_sqrt (by norm_num)]
            norm_num
    have hnn : 0 ≤ (dd K p).norm := GaussianInt.norm_nonneg _
    have : ((dd K p).norm.natAbs : ℝ) ≤ 4 * 65 ^ K := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hnn)]
      exact hsq
    exact_mod_cast this
  calc commonDen K ≤ (4 * 65 ^ K) ^ (labelPairs K).card :=
        Finset.prod_le_pow_card _ _ _ hfac
    _ ≤ (4 * 65 ^ K) ^ ((K + 1) ^ 4) := by
        apply Nat.pow_le_pow_right (by positivity)
        calc (labelPairs K).card ≤ (labels K ×ˢ labels K).card := Finset.card_filter_le _ _
          _ = (K + 1) ^ 4 := by rw [Finset.card_product, card_labels]; ring

end Green41

/- ## Section: `Confinement` -/

/-
# Lattice confinement (Lemma 5.2 of the round-2 draft)

`KL57With c` is the consequence of Kravitz–Leng, Proposition 5.7, that the argument
uses, restricted to points `p = j_ℂ(w)` and Gaussian integers `q`:
the `p`-adic sizes of `q` are `5^(-v_{P̄}(q))` and `13^(-v_{Q̄}(q))`.
It is an interface: the final FC theorem must derive it, not assume it.

From it we prove the confinement lemma. If `w` is not covered by the orbit rotations
`rot s t` (`s, t ≤ T`), then `w` lies within `√65^K` of the lattice `(D_h / L) ℤ[i]`,
where `D_h = P̄^h Q̄^h` and `L = commonDen K`. The pigeonhole step rounds the orbit points
`rot s t · w` to the nearest Gaussian integer.
-/

namespace Green41

open Complex ComplexConjugate

/- ## `p`-adic sizes of Gaussian integers -/

/-- `|ι₅ q|₅ = 5^(-v_{P̄}(q))`, and `0` for `q = 0`. -/
noncomputable def size5 (q : GaussianInt) : ℝ :=
  if q = 0 then 0 else (5 : ℝ) ^ (-(multiplicity gPb q : ℝ))

/-- `|ι₁₃ q|₁₃ = 13^(-v_{Q̄}(q))`, and `0` for `q = 0`. -/
noncomputable def size13 (q : GaussianInt) : ℝ :=
  if q = 0 then 0 else (13 : ℝ) ^ (-(multiplicity gQb q : ℝ))

lemma size5_nonneg (q : GaussianInt) : 0 ≤ size5 q := by
  unfold size5; split_ifs <;> positivity

lemma size13_nonneg (q : GaussianInt) : 0 ≤ size13 q := by
  unfold size13; split_ifs <;> positivity

lemma gPb_not_isUnit : ¬ IsUnit gPb := by
  rw [← Zsqrtd.norm_eq_one_iff, norm_gPb]; decide

lemma gQb_not_isUnit : ¬ IsUnit gQb := by
  rw [← Zsqrtd.norm_eq_one_iff, norm_gQb]; decide

lemma size5_le_of_dvd {q : GaussianInt} {u : ℕ} (h : gPb ^ u ∣ q) :
    size5 q ≤ 1 / (5 : ℝ) ^ u := by
  unfold size5
  split_ifs with hq
  · positivity
  · have hf : FiniteMultiplicity gPb q := FiniteMultiplicity.of_not_isUnit gPb_not_isUnit hq
    have hu : u ≤ multiplicity gPb q := hf.le_multiplicity_of_pow_dvd h
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (u : ℝ) ≤ (multiplicity gPb q : ℝ) := by exact_mod_cast hu
    linarith

lemma size13_le_of_dvd {q : GaussianInt} {u : ℕ} (h : gQb ^ u ∣ q) :
    size13 q ≤ 1 / (13 : ℝ) ^ u := by
  unfold size13
  split_ifs with hq
  · positivity
  · have hf : FiniteMultiplicity gQb q := FiniteMultiplicity.of_not_isUnit gQb_not_isUnit hq
    have hu : u ≤ multiplicity gQb q := hf.le_multiplicity_of_pow_dvd h
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (u : ℝ) ≤ (multiplicity gQb q : ℝ) := by exact_mod_cast hu
    linarith

lemma dvd_of_size5_lt {q : GaussianInt} {h : ℕ} (hs : size5 q < 1 / (5 : ℝ) ^ h) :
    gPb ^ h ∣ q := by
  unfold size5 at hs
  split_ifs at hs with hq
  · rw [hq]; exact dvd_zero _
  · apply pow_dvd_of_le_multiplicity
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)] at hs
    have h2 := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 5)).mp hs
    have : (h : ℝ) < (multiplicity gPb q : ℝ) := by linarith
    exact_mod_cast this.le

lemma dvd_of_size13_lt {q : GaussianInt} {h : ℕ} (hs : size13 q < 1 / (13 : ℝ) ^ h) :
    gQb ^ h ∣ q := by
  unfold size13 at hs
  split_ifs at hs with hq
  · rw [hq]; exact dvd_zero _
  · apply pow_dvd_of_le_multiplicity
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)] at hs
    have h2 := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 13)).mp hs
    have : (h : ℝ) < (multiplicity gQb q : ℝ) := by linarith
    exact_mod_cast this.le

lemma five_eq : (5 : GaussianInt) = gP * gPb := by decide
lemma thirteen_eq : (13 : GaussianInt) = gQ * gQb := by decide

lemma isCoprime_gPb_gQb : IsCoprime gPb gQb := ⟨-5 * gP, 2 * gQ, by decide⟩

/-- `D_h = P̄^h Q̄^h`. -/
def gD (h : ℕ) : GaussianInt := gPb ^ h * gQb ^ h

lemma gD_dvd_of_size_lt {q : GaussianInt} {h : ℕ}
    (hs : size5 q + size13 q < 1 / (13 : ℝ) ^ h) : gD h ∣ q := by
  have h5 : size5 q < 1 / (5 : ℝ) ^ h := by
    have h13 : 1 / (13 : ℝ) ^ h ≤ 1 / (5 : ℝ) ^ h := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) h
    linarith [size13_nonneg q]
  have h13 : size13 q < 1 / (13 : ℝ) ^ h := by linarith [size5_nonneg q]
  exact (isCoprime_gPb_gQb.pow).mul_dvd (dvd_of_size5_lt h5) (dvd_of_size13_lt h13)

/- ## The Kravitz–Leng interface -/

/-- `η = 5^(-ε^(-c))`. -/
noncomputable def ηKL (c ε : ℝ) : ℝ := (5 : ℝ) ^ (-(ε ^ (-c)))

/-- `δ = 13^(-c η^(-5))`. -/
noncomputable def δKL (c ε : ℝ) : ℝ := (13 : ℝ) ^ (-(c * ηKL c ε ^ (-5 : ℝ)))

lemma ηKL_pos (c ε : ℝ) : 0 < ηKL c ε := by unfold ηKL; positivity
lemma δKL_pos (c ε : ℝ) : 0 < δKL c ε := by unfold δKL; positivity

/-- Kravitz–Leng, Proposition 5.7, for points `j_ℂ(w)` and Gaussian integers `q`,
with a fixed constant `c`. -/
def KL57With (c : ℝ) : Prop :=
  ∀ ε ϖ : ℝ, 0 < ε → ε < 1 / 10 → 0 < ϖ → ϖ < 1 / 10 →
    ∀ (N₀ s₁ t₁ s₂ t₂ : ℕ) (w : ℂ) (q : GaussianInt),
      s₁ ≤ N₀ → t₁ ≤ N₀ → s₂ ≤ N₀ → t₂ ≤ N₀ →
      2 * ϖ ≤ size5 q + size13 q → size5 q + size13 q ≤ δKL c ε →
      ‖(q : ℂ) - (rot s₁ t₁ - rot s₂ t₂) * w‖ ≤ ηKL c ε / 10 →
      ∃ s t : ℕ, (s : ℝ) ≤ N₀ + Real.logb 5 ϖ⁻¹ + c * ηKL c ε ^ (-5 : ℝ) ∧
        (t : ℝ) ≤ N₀ + Real.logb 5 ϖ⁻¹ + c * ηKL c ε ^ (-5 : ℝ) ∧ InStripe ε (rot s t) w

/-- The interface `KL57`: some positive constant works. -/
def KL57 : Prop := ∃ c : ℝ, 0 < c ∧ KL57With c

/- ## Rounding and the pigeonhole step -/

/-- The nearest Gaussian integer, rounding each coordinate. -/
noncomputable def gRound (x : ℂ) : GaussianInt := ⟨round x.re, round x.im⟩

lemma gRound_re (x : ℂ) : ((gRound x : ℂ)).re = (round x.re : ℝ) := by
  simp [gRound, GaussianInt.toComplex_def]

lemma gRound_im (x : ℂ) : ((gRound x : ℂ)).im = (round x.im : ℝ) := by
  simp [gRound, GaussianInt.toComplex_def]

lemma frac_mem (y : ℝ) : -(1 / 2) ≤ y - round y ∧ y - round y < 1 / 2 := by
  rw [round_eq]
  constructor
  · have := Int.floor_le (y + 1 / 2); linarith
  · have := Int.lt_floor_add_one (y + 1 / 2); linarith

/-- The cell of the offset `y - round y ∈ [-1/2, 1/2)` at resolution `1 / G`. -/
noncomputable def cell (G : ℕ) (y : ℝ) : ℤ := ⌊(y - round y + 1 / 2) * G⌋

lemma cell_mem {G : ℕ} (hG : 0 < G) (y : ℝ) : 0 ≤ cell G y ∧ cell G y < G := by
  have hG' : (0 : ℝ) < G := by exact_mod_cast hG
  obtain ⟨h1, h2⟩ := frac_mem y
  constructor
  · apply Int.floor_nonneg.mpr
    have : 0 ≤ y - round y + 1 / 2 := by linarith
    positivity
  · rw [cell, Int.floor_lt]
    push_cast
    have : y - round y + 1 / 2 < 1 := by linarith
    nlinarith

lemma close_of_cell_eq {G : ℕ} (hG : 0 < G) {y₁ y₂ : ℝ} (h : cell G y₁ = cell G y₂) :
    |(y₁ - round y₁) - (y₂ - round y₂)| < 1 / G := by
  have hG' : (0 : ℝ) < G := by exact_mod_cast hG
  unfold cell at h
  have a1 := Int.floor_le ((y₁ - round y₁ + 1 / 2) * G)
  have a2 := Int.lt_floor_add_one ((y₁ - round y₁ + 1 / 2) * G)
  have b1 := Int.floor_le ((y₂ - round y₂ + 1 / 2) * G)
  have b2 := Int.lt_floor_add_one ((y₂ - round y₂ + 1 / 2) * G)
  rw [h] at a1 a2
  have e : ((y₁ - round y₁) - (y₂ - round y₂)) * G =
      (y₁ - round y₁ + 1 / 2) * G - (y₂ - round y₂ + 1 / 2) * G := by ring
  have hAB : |((y₁ - round y₁) - (y₂ - round y₂)) * G| < 1 := by
    rw [e, abs_lt]
    constructor <;> linarith
  rw [abs_mul, abs_of_pos hG'] at hAB
  rw [lt_div_iff₀ hG']
  exact hAB

/-- The box of a point: residues of its rounding mod `M` and the cells of its offset. -/
noncomputable def box (M G : ℕ) (x : ℂ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((round x.re % (M : ℤ), round x.im % (M : ℤ)), (cell G x.re, cell G x.im))

lemma pigeonhole {K M G : ℕ} (hM : 0 < M) (hG : 0 < G) (hK : M ^ 2 * G ^ 2 < (K + 1) ^ 2)
    (w : ℂ) : ∃ p ∈ labelPairs K, box M G (rot p.1.1 p.1.2 * w) = box M G (rot p.2.1 p.2.2 * w) := by
  classical
  set t : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
    (Finset.Ico (0 : ℤ) M ×ˢ Finset.Ico (0 : ℤ) M) ×ˢ (Finset.Ico (0 : ℤ) G ×ˢ Finset.Ico (0 : ℤ) G)
  have ht : t.card = M ^ 2 * G ^ 2 := by
    simp only [t, Finset.card_product, Int.card_Ico, sub_zero, Int.toNat_natCast]
    ring
  have hc : t.card < (labels K).card := by rw [ht, card_labels]; exact hK
  have hmaps : ∀ x ∈ labels K, box M G (rot x.1 x.2 * w) ∈ t := by
    intro x _
    have hM' : (0 : ℤ) < M := by exact_mod_cast hM
    have c1 := cell_mem hG (rot x.1 x.2 * w).re
    have c2 := cell_mem hG (rot x.1 x.2 * w).im
    simp only [t, box, Finset.mem_product, Finset.mem_Ico]
    refine ⟨⟨⟨Int.emod_nonneg _ hM'.ne', Int.emod_lt_of_pos _ hM'⟩,
      ⟨Int.emod_nonneg _ hM'.ne', Int.emod_lt_of_pos _ hM'⟩⟩, ⟨c1, c2⟩⟩
  obtain ⟨x, hx, y, hy, hxy, hbox⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc hmaps
  refine ⟨(x, y), ?_, hbox⟩
  simp only [labelPairs, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hx, hy⟩, hxy⟩

lemma box_eq_consequences {M G : ℕ} (hG : 0 < G) {x y : ℂ} (h : box M G x = box M G y) :
    (M : GaussianInt) ∣ gRound x - gRound y ∧
      ‖((gRound x - gRound y : GaussianInt) : ℂ) - (x - y)‖ < 2 / G := by
  simp only [box, Prod.mk.injEq] at h
  obtain ⟨⟨hre, him⟩, ⟨cre, cim⟩⟩ := h
  constructor
  · have h1 : (M : ℤ) ∣ round x.re - round y.re := (Int.ModEq.dvd hre.symm)
    have h2 : (M : ℤ) ∣ round x.im - round y.im := (Int.ModEq.dvd him.symm)
    have : ((M : ℤ) : GaussianInt) ∣ gRound x - gRound y := by
      rw [Zsqrtd.intCast_dvd]
      exact ⟨h1, h2⟩
    simpa using this
  · have e1 := close_of_cell_eq hG cre
    have e2 := close_of_cell_eq hG cim
    have hre' : (((gRound x - gRound y : GaussianInt) : ℂ) - (x - y)).re =
        -((x.re - round x.re) - (y.re - round y.re)) := by
      rw [Complex.sub_re, Complex.sub_re, GaussianInt.toComplex_sub, Complex.sub_re, gRound_re,
        gRound_re]
      ring
    have him' : (((gRound x - gRound y : GaussianInt) : ℂ) - (x - y)).im =
        -((x.im - round x.im) - (y.im - round y.im)) := by
      rw [Complex.sub_im, Complex.sub_im, GaussianInt.toComplex_sub, Complex.sub_im, gRound_im,
        gRound_im]
      ring
    calc ‖((gRound x - gRound y : GaussianInt) : ℂ) - (x - y)‖
        ≤ |(((gRound x - gRound y : GaussianInt) : ℂ) - (x - y)).re| +
          |(((gRound x - gRound y : GaussianInt) : ℂ) - (x - y)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ < 1 / G + 1 / G := by
          rw [hre', him', abs_neg, abs_neg]
          exact add_lt_add e1 e2
      _ = 2 / G := by ring

/- ## The confinement lemma -/

/-- Lemma 5.2 of the round-2 draft, from `KL57With c`. -/
theorem confinement {c ε : ℝ} (hKL : KL57With c) (hε0 : 0 < ε) (hε1 : ε < 1 / 10)
    {K G u v h T : ℕ} (hGη : 20 / ηKL c ε ≤ G) (hGδ : 2 / δKL c ε ≤ G) (hG2 : 2 ≤ G)
    (hu : G ≤ 5 ^ u) (hv : G ≤ 13 ^ v)
    (hK : (5 ^ u * 13 ^ v) ^ 2 * G ^ 2 < (K + 1) ^ 2) (hh : 1 ≤ h)
    (hT : (K : ℝ) + Real.logb 5 (2 * 13 ^ h) + c * ηKL c ε ^ (-5 : ℝ) ≤ T) (w : ℂ)
    (hw : ∀ s t : ℕ, s ≤ T → t ≤ T → ¬ InStripe ε (rot s t) w) :
    ∃ k : GaussianInt, ‖w - (gD h : ℂ) / (commonDen K : ℂ) * k‖ ≤ Real.sqrt 65 ^ K := by
  have hG0 : 0 < G := by omega
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG0
  set M : ℕ := 5 ^ u * 13 ^ v with hMdef
  have hM : 0 < M := by positivity
  obtain ⟨p, hp, hbox⟩ := pigeonhole hM hG0 hK w
  obtain ⟨hMdvd, hclose⟩ := box_eq_consequences hG0 hbox
  set x := rot p.1.1 p.1.2 * w
  set y := rot p.2.1 p.2.2 * w
  set q : GaussianInt := gRound x - gRound y
  have hxy : x - y = (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) * w := by simp only [x, y]; ring
  have hq_close : ‖(q : ℂ) - (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) * w‖ < 2 / G := by
    rw [← hxy]; exact hclose
  -- sizes of `q`
  have h5u : gPb ^ u ∣ q := by
    have : (5 : GaussianInt) ^ u ∣ (M : GaussianInt) := by
      rw [hMdef]; push_cast; exact dvd_mul_right _ _
    have hPb5 : gPb ^ u ∣ (5 : GaussianInt) ^ u := pow_dvd_pow_of_dvd ⟨gP, by rw [five_eq]; ring⟩ u
    exact hPb5.trans (this.trans hMdvd)
  have h13v : gQb ^ v ∣ q := by
    have : (13 : GaussianInt) ^ v ∣ (M : GaussianInt) := by
      rw [hMdef]; push_cast; exact dvd_mul_left _ _
    have hQb13 : gQb ^ v ∣ (13 : GaussianInt) ^ v :=
      pow_dvd_pow_of_dvd ⟨gQ, by rw [thirteen_eq]; ring⟩ v
    exact hQb13.trans (this.trans hMdvd)
  have hs5 : size5 q ≤ 1 / G := by
    refine (size5_le_of_dvd h5u).trans ?_
    apply one_div_le_one_div_of_le hGr
    exact_mod_cast hu
  have hs13 : size13 q ≤ 1 / G := by
    refine (size13_le_of_dvd h13v).trans ?_
    apply one_div_le_one_div_of_le hGr
    exact_mod_cast hv
  have hη := ηKL_pos c ε
  have hδ := δKL_pos c ε
  by_cases hbig : 1 / (13 : ℝ) ^ h ≤ size5 q + size13 q
  · -- Kravitz–Leng applies and covers `w`: contradiction
    exfalso
    have hp' := hp
    simp only [labelPairs, Finset.mem_filter, Finset.mem_product, mem_labels] at hp'
    set ϖ : ℝ := 1 / (2 * 13 ^ h) with hϖ
    have hϖ0 : 0 < ϖ := by positivity
    have hϖ1 : ϖ < 1 / 10 := by
      rw [hϖ]
      have : (13 : ℝ) ≤ 13 ^ h := by
        calc (13 : ℝ) = 13 ^ 1 := by ring
          _ ≤ 13 ^ h := pow_le_pow_right₀ (by norm_num) hh
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h2ϖ : 2 * ϖ ≤ size5 q + size13 q := by
      rw [hϖ]
      calc 2 * (1 / (2 * (13 : ℝ) ^ h)) = 1 / 13 ^ h := by field_simp
        _ ≤ _ := hbig
    have hsizeδ : size5 q + size13 q ≤ δKL c ε := by
      have : 2 / (G : ℝ) ≤ δKL c ε := by
        rw [div_le_iff₀ hGr]
        rw [div_le_iff₀ hδ] at hGδ
        linarith
      have h12 : (1 : ℝ) / G + 1 / G = 2 / G := by ring
      linarith
    have hcloseη : ‖(q : ℂ) - (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) * w‖ ≤ ηKL c ε / 10 := by
      have : 2 / (G : ℝ) ≤ ηKL c ε / 10 := by
        rw [div_le_iff₀ hGr]
        rw [div_le_iff₀ hη] at hGη
        linarith
      linarith
    obtain ⟨s, t, hs, ht, hst⟩ := hKL ε ϖ hε0 hε1 hϖ0 hϖ1 K p.1.1 p.1.2 p.2.1 p.2.2 w q
      hp'.1.1.1 hp'.1.1.2 hp'.1.2.1 hp'.1.2.2 h2ϖ hsizeδ hcloseη
    have hlog : Real.logb 5 ϖ⁻¹ = Real.logb 5 (2 * 13 ^ h) := by
      rw [hϖ, one_div, inv_inv]
    rw [hlog] at hs ht
    have hsT : s ≤ T := by exact_mod_cast hs.trans hT
    have htT : t ≤ T := by exact_mod_cast ht.trans hT
    exact hw s t hsT htT hst
  · -- `D_h ∣ q`, and the common denominator places `w` near the lattice
    push Not at hbig
    obtain ⟨k₁, hk₁⟩ := gD_dvd_of_size_lt hbig
    obtain ⟨cr, hcr⟩ := commonDen_div hp
    refine ⟨cr * k₁, ?_⟩
    have hr0 : rot p.1.1 p.1.2 - rot p.2.1 p.2.2 ≠ 0 := by
      intro h0
      have := norm_rot_sub_ge hp
      rw [h0, norm_zero] at this
      have : (0 : ℝ) < 1 / Real.sqrt 65 ^ K := by positivity
      linarith
    have hL0 : (commonDen K : ℂ) ≠ 0 := by exact_mod_cast (commonDen_pos K).ne'
    set rr := rot p.1.1 p.1.2 - rot p.2.1 p.2.2 with hrr
    have hkey : w - (gD h : ℂ) / (commonDen K : ℂ) * ((cr * k₁ : GaussianInt) : ℂ) =
        -(((q : ℂ) - rr * w) / rr) := by
      have hq' : (q : ℂ) = (gD h : ℂ) * (k₁ : ℂ) := by
        rw [hk₁, GaussianInt.toComplex_mul]
      have hcr0 : (cr : ℂ) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hcr
        exact hL0 hcr.symm
      rw [GaussianInt.toComplex_mul, hq', ← hcr]
      field_simp
      ring
    rw [hkey, norm_neg, norm_div]
    have hrr_ge := norm_rot_sub_ge hp
    have hrr_pos : 0 < ‖rr‖ := norm_pos_iff.mpr hr0
    rw [div_le_iff₀ hrr_pos]
    have hsq : 0 < Real.sqrt 65 ^ K := by positivity
    have h1 : 1 ≤ Real.sqrt 65 ^ K * ‖rr‖ := by
      rw [div_le_iff₀ hsq] at hrr_ge
      linarith
    have h2 : 2 / (G : ℝ) ≤ 1 := by
      rw [div_le_one hGr]; exact_mod_cast hG2
    calc ‖(q : ℂ) - rr * w‖ ≤ 2 / G := hq_close.le
      _ ≤ 1 := h2
      _ ≤ Real.sqrt 65 ^ K * ‖rr‖ := h1

end Green41

/- ## Section: `DiscCover` -/

/-
# A deterministic cover of a disc by `O(ε⁻¹ log R)` rational rotations

For `e ∈ ℂ` put `g(φ) = Re(e^{iφ} e)`. It has a zero `φ₀ ∈ [-π/2, π/2]`, where
`|g'(φ₀)| = |e|`.

* If `|e| ≤ 16`, some angle of the grid `-π/2 + m ε/16` is within `ε/32` of `φ₀`,
  so `|g| ≤ ε/2` there.
* If `2^k ≤ |e| < 2^(k+1)` with `k ≥ 4`, start from a base angle `β` within `π/32`
  of `φ₀` and step by `ε / 2^(k+1)`. Along the arc `|g'| ≥ |e|/2`, so `g` moves by at
  least `1` while each step moves it by less than `ε`. Hence some step lands within
  `ε/2` of an integer.

Each ideal angle `φ` is then replaced by the rational rotation `c / c̄`, where `c` is the
Gaussian integer nearest to `q e^{iφ/2}`; this moves `Re(u e)` by at most `ε/64`.
-/

namespace Green41

open Complex ComplexConjugate

/- ## The function `g(φ) = Re(e^{iφ} e)` -/

/-- `Re(e^{iφ} e)`. -/
noncomputable def gRe (e : ℂ) (φ : ℝ) : ℝ := e.re * Real.cos φ - e.im * Real.sin φ

/-- `Im(e^{iφ} e)`. -/
noncomputable def gIm (e : ℂ) (φ : ℝ) : ℝ := e.re * Real.sin φ + e.im * Real.cos φ

lemma exp_mul_I_mul (e : ℂ) (φ : ℝ) :
    Complex.exp (φ * I) * e = ⟨gRe e φ, gIm e φ⟩ := by
  apply Complex.ext
  · simp only [gRe, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  · simp only [gIm, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring

lemma gRe_eq (e : ℂ) (φ : ℝ) : gRe e φ = (Complex.exp (φ * I) * e).re := by
  rw [exp_mul_I_mul]

lemma continuous_gRe (e : ℂ) : Continuous (gRe e) := by
  unfold gRe; fun_prop

lemma hasDerivAt_gRe (e : ℂ) (φ : ℝ) : HasDerivAt (gRe e) (-gIm e φ) φ := by
  have h := ((Real.hasDerivAt_cos φ).const_mul e.re).sub ((Real.hasDerivAt_sin φ).const_mul e.im)
  have h' : -gIm e φ = e.re * -Real.sin φ - e.im * Real.cos φ := by unfold gIm; ring
  rw [h']
  exact h

lemma gRe_sq_add_gIm_sq (e : ℂ) (φ : ℝ) : gRe e φ ^ 2 + gIm e φ ^ 2 = ‖e‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hs := Real.sin_sq_add_cos_sq φ
  simp only [gRe, gIm]
  nlinarith [hs]

lemma norm_exp_sub_exp_le (a b : ℝ) :
    ‖Complex.exp (a * I) - Complex.exp (b * I)‖ ≤ |a - b| := by
  have h : Complex.exp (a * I) - Complex.exp (b * I) =
      Complex.exp (b * I) * (Complex.exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  rwa [Real.norm_eq_abs] at this

lemma abs_gRe_sub_le (e : ℂ) (a b : ℝ) : |gRe e a - gRe e b| ≤ ‖e‖ * |a - b| := by
  rw [gRe_eq, gRe_eq, ← Complex.sub_re, ← sub_mul]
  calc |((Complex.exp (a * I) - Complex.exp (b * I)) * e).re|
      ≤ ‖(Complex.exp (a * I) - Complex.exp (b * I)) * e‖ := Complex.abs_re_le_norm _
    _ = ‖Complex.exp (a * I) - Complex.exp (b * I)‖ * ‖e‖ := norm_mul _ _
    _ ≤ |a - b| * ‖e‖ := by gcongr; exact norm_exp_sub_exp_le a b
    _ = ‖e‖ * |a - b| := by ring

lemma abs_gIm_sub_le (e : ℂ) (a b : ℝ) : |gIm e a - gIm e b| ≤ ‖e‖ * |a - b| := by
  have ha : gIm e a = (Complex.exp (a * I) * e).im := by rw [exp_mul_I_mul]
  have hb : gIm e b = (Complex.exp (b * I) * e).im := by rw [exp_mul_I_mul]
  rw [ha, hb, ← Complex.sub_im, ← sub_mul]
  calc |((Complex.exp (a * I) - Complex.exp (b * I)) * e).im|
      ≤ ‖(Complex.exp (a * I) - Complex.exp (b * I)) * e‖ := Complex.abs_im_le_norm _
    _ = ‖Complex.exp (a * I) - Complex.exp (b * I)‖ * ‖e‖ := norm_mul _ _
    _ ≤ |a - b| * ‖e‖ := by gcongr; exact norm_exp_sub_exp_le a b
    _ = ‖e‖ * |a - b| := by ring

lemma gRe_neg_pi_div_two (e : ℂ) : gRe e (-(Real.pi / 2)) = e.im := by
  simp [gRe]

lemma gRe_pi_div_two (e : ℂ) : gRe e (Real.pi / 2) = -e.im := by
  simp [gRe]

lemma exists_zero_gRe (e : ℂ) :
    ∃ φ₀ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2), gRe e φ₀ = 0 := by
  have hab : -(Real.pi / 2) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hc : ContinuousOn (gRe e) (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
    (continuous_gRe e).continuousOn
  rcases le_total 0 e.im with h | h
  · have hmem : (0 : ℝ) ∈ Set.Icc (gRe e (Real.pi / 2)) (gRe e (-(Real.pi / 2))) := by
      rw [gRe_pi_div_two, gRe_neg_pi_div_two]; constructor <;> linarith
    obtain ⟨φ, hφ, h0⟩ := intermediate_value_Icc' hab hc hmem
    exact ⟨φ, hφ, h0⟩
  · have hmem : (0 : ℝ) ∈ Set.Icc (gRe e (-(Real.pi / 2))) (gRe e (Real.pi / 2)) := by
      rw [gRe_pi_div_two, gRe_neg_pi_div_two]; constructor <;> linarith
    obtain ⟨φ, hφ, h0⟩ := intermediate_value_Icc hab hc hmem
    exact ⟨φ, hφ, h0⟩

lemma abs_gIm_of_gRe_eq_zero {e : ℂ} {φ : ℝ} (h : gRe e φ = 0) : |gIm e φ| = ‖e‖ := by
  have h2 := gRe_sq_add_gIm_sq e φ
  rw [h] at h2
  have h3 : gIm e φ ^ 2 = ‖e‖ ^ 2 := by linarith
  rw [← Real.sqrt_sq (norm_nonneg e), ← h3, Real.sqrt_sq_eq_abs]

/- ## A slowly moving finite sequence that travels far meets an integer -/

lemma exists_near_int_of_up {ε : ℝ} (y : ℕ → ℝ) (M : ℕ)
    (hstep : ∀ m < M, |y (m + 1) - y m| < ε) (hspan : y 0 + 1 ≤ y M) :
    ∃ m ≤ M, ∃ n : ℤ, |y m - n| < ε / 2 := by
  classical
  set n : ℤ := ⌈y 0⌉ with hn
  have hn1 : y 0 ≤ n := Int.le_ceil _
  have hn2 : (n : ℝ) < y 0 + 1 := Int.ceil_lt_add_one _
  have hex : ∃ m, (n : ℝ) ≤ y m ∧ m ≤ M := ⟨M, by linarith, le_refl _⟩
  obtain ⟨hm₀a, hm₀b⟩ := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · refine ⟨0, Nat.zero_le _, n, ?_⟩
    rw [h0] at hm₀a
    have hε : 0 < ε := by
      have := hstep 0 (by
        rcases Nat.eq_zero_or_pos M with hM | hM
        · rw [hM] at hspan; linarith
        · exact hM)
      linarith [abs_nonneg (y 1 - y 0)]
    rw [abs_lt]; constructor <;> linarith
  · obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    rw [hm] at hm₀a hm₀b
    have hprev : ¬ ((n : ℝ) ≤ y m ∧ m ≤ M) := Nat.find_min hex (by omega)
    have hmM : m < M := by omega
    have hlt : y m < n := by
      by_contra hc
      exact hprev ⟨le_of_not_gt hc, hmM.le⟩
    have hs := hstep m hmM
    rw [abs_lt] at hs
    by_cases hcase : y (m + 1) - n < n - y m
    · refine ⟨m + 1, hm₀b, n, ?_⟩
      rw [abs_lt]; constructor <;> linarith
    · refine ⟨m, hmM.le, n, ?_⟩
      rw [abs_lt]; constructor <;> linarith

lemma exists_near_int_of_steps {ε : ℝ} (y : ℕ → ℝ) (M : ℕ)
    (hstep : ∀ m < M, |y (m + 1) - y m| < ε) (hspan : 1 ≤ |y M - y 0|) :
    ∃ m ≤ M, ∃ n : ℤ, |y m - n| < ε / 2 := by
  rcases le_or_gt 0 (y M - y 0) with h | h
  · rw [abs_of_nonneg h] at hspan
    exact exists_near_int_of_up y M hstep (by linarith)
  · rw [abs_of_neg h] at hspan
    have hstep' : ∀ m < M, |(-y (m + 1)) - (-y m)| < ε := by
      intro m hm
      rw [show (-y (m + 1)) - (-y m) = -(y (m + 1) - y m) by ring, abs_neg]
      exact hstep m hm
    obtain ⟨m, hm, n, hn⟩ := exists_near_int_of_up (fun m => -y m) M hstep' (by simp; linarith)
    refine ⟨m, hm, -n, ?_⟩
    rw [show y m - ((-n : ℤ) : ℝ) = -((-y m) - n) by push_cast; ring, abs_neg]
    exact hn

/- ## Rational rotations `c / c̄` -/

/-- The Gaussian integer nearest to `q e^{iφ/2}`. -/
noncomputable def cφ (q : ℕ) (φ : ℝ) : GaussianInt :=
  gRound ((q : ℂ) * Complex.exp (((φ / 2 : ℝ) : ℂ) * I))

lemma norm_gRound_sub_le (x : ℂ) : ‖(gRound x : ℂ) - x‖ ≤ 1 := by
  calc ‖(gRound x : ℂ) - x‖ ≤ |((gRound x : ℂ) - x).re| + |((gRound x : ℂ) - x).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / 2 + 1 / 2 := by
        rw [Complex.sub_re, Complex.sub_im, gRound_re, gRound_im]
        gcongr
        · rw [abs_sub_comm]; exact abs_sub_round _
        · rw [abs_sub_comm]; exact abs_sub_round _
    _ = 1 := by norm_num

lemma rat_rot_approx {q : ℕ} (hq : 2 ≤ q) (φ : ℝ) :
    (cφ q φ : ℂ) ≠ 0 ∧ ‖(cφ q φ : ℂ)‖ ≤ q + 1 ∧
      ‖(cφ q φ : ℂ) / conj (cφ q φ : ℂ) - Complex.exp (φ * I)‖ ≤ 2 / (q - 1) := by
  set w₀ : ℂ := Complex.exp (((φ / 2 : ℝ) : ℂ) * I) with hw₀
  have hw : ‖w₀‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  set c : ℂ := (cφ q φ : ℂ) with hc
  set d : ℂ := c - q * w₀ with hd
  have hd1 : ‖d‖ ≤ 1 := norm_gRound_sub_le _
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqw : ‖(q : ℂ) * w₀‖ = q := by rw [norm_mul, hw, mul_one, Complex.norm_natCast]
  have hcd : c = q * w₀ + d := by rw [hd]; ring
  have hc_lo : (q : ℝ) - 1 ≤ ‖c‖ := by
    have h1 : ‖(q : ℂ) * w₀‖ ≤ ‖c‖ + ‖d‖ := by
      calc ‖(q : ℂ) * w₀‖ = ‖c - d‖ := by rw [hcd]; ring_nf
        _ ≤ ‖c‖ + ‖d‖ := norm_sub_le _ _
    linarith
  have hc_hi : ‖c‖ ≤ q + 1 := by
    calc ‖c‖ = ‖(q : ℂ) * w₀ + d‖ := by rw [hcd]
      _ ≤ ‖(q : ℂ) * w₀‖ + ‖d‖ := norm_add_le _ _
      _ ≤ q + 1 := by rw [hqw]; linarith
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc_lo
    linarith
  refine ⟨hc0, hc_hi, ?_⟩
  have hcc0 : conj c ≠ 0 := (map_ne_zero _).mpr hc0
  have hw0 : w₀ ≠ 0 := by intro h0; rw [h0, norm_zero] at hw; norm_num at hw
  have hww : w₀ * conj w₀ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; norm_num
  have hcw0 : conj w₀ ≠ 0 := (map_ne_zero _).mpr hw0
  have hsq : Complex.exp (φ * I) = w₀ ^ 2 := by
    rw [hw₀, sq, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  set z : ℂ := c * conj w₀ with hz
  have hzc : conj z = conj c * w₀ := by rw [hz, map_mul, Complex.conj_conj]
  have hident : c / conj c - Complex.exp (φ * I) = (z - conj z) / (conj c * conj w₀) := by
    rw [hsq, hzc, hz]
    field_simp
    linear_combination (-(conj c * w₀)) * hww
  have hzim : z.im = (d * conj w₀).im := by
    have : z = (q : ℂ) + d * conj w₀ := by
      rw [hz, hcd, add_mul, mul_assoc, hww, mul_one]
    rw [this, Complex.add_im, Complex.natCast_im, zero_add]
  have hden : ‖conj c * conj w₀‖ = ‖c‖ := by
    rw [norm_mul, Complex.norm_conj, Complex.norm_conj, hw, mul_one]
  rw [hident, Complex.sub_conj, norm_div, hden]
  have hnum : ‖((2 * z.im : ℝ) : ℂ) * I‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 2), hzim]
    have : |(d * conj w₀).im| ≤ 1 := by
      calc |(d * conj w₀).im| ≤ ‖d * conj w₀‖ := Complex.abs_im_le_norm _
        _ = ‖d‖ := by rw [norm_mul, Complex.norm_conj, hw, mul_one]
        _ ≤ 1 := hd1
    linarith
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  calc ‖((2 * z.im : ℝ) : ℂ) * I‖ / ‖c‖ ≤ 2 / ‖c‖ := by gcongr
    _ ≤ 2 / (q - 1) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by linarith) hc_lo

/-- The rational rotation pair `(c, c̄)` for the angle `φ`. -/
noncomputable def rotPair (q : ℕ) (φ : ℝ) : GaussianInt × GaussianInt :=
  (cφ q φ, star (cφ q φ))

lemma rotPair_div (q : ℕ) (φ : ℝ) :
    ((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ) = (cφ q φ : ℂ) / conj (cφ q φ : ℂ) := by
  simp [rotPair, GaussianInt.toComplex_star]

/-- Replacing `e^{iφ}` by `c / c̄` changes `Re(u e)` by at most `2|e| / (q - 1)`. -/
lemma re_rotPair_close {q : ℕ} (hq : 2 ≤ q) (φ : ℝ) (e : ℂ) :
    |((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re - gRe e φ| ≤ 2 / (q - 1) * ‖e‖ := by
  rw [rotPair_div, gRe_eq, ← Complex.sub_re, ← sub_mul]
  obtain ⟨_, _, h3⟩ := rat_rot_approx hq φ
  calc |(((cφ q φ : ℂ) / conj (cφ q φ : ℂ) - Complex.exp (φ * I)) * e).re|
      ≤ ‖((cφ q φ : ℂ) / conj (cφ q φ : ℂ) - Complex.exp (φ * I)) * e‖ :=
        Complex.abs_re_le_norm _
    _ = ‖(cφ q φ : ℂ) / conj (cφ q φ : ℂ) - Complex.exp (φ * I)‖ * ‖e‖ := norm_mul _ _
    _ ≤ 2 / (q - 1) * ‖e‖ := by gcongr

/- ## The two covering cases -/

/-- Rounding a nonnegative real to the nearest natural number. -/
lemma exists_nat_near {x : ℝ} (hx : 0 ≤ x) : ∃ m : ℕ, |(m : ℝ) - x| ≤ 1 / 2 ∧ (m : ℝ) ≤ x + 1 / 2 := by
  refine ⟨⌊x + 1 / 2⌋₊, ?_, Nat.floor_le (by linarith)⟩
  have h1 := Nat.floor_le (show 0 ≤ x + 1 / 2 by linarith)
  have h2 := Nat.lt_floor_add_one (x + 1 / 2)
  rw [abs_le]; constructor <;> linarith

lemma small_disc {ε : ℝ} (hε : 0 < ε) {e : ℂ} (he : ‖e‖ ≤ 16) :
    ∃ m ∈ Finset.range (⌈16 * Real.pi / ε⌉₊ + 1),
      |gRe e (-(Real.pi / 2) + m * (ε / 16))| ≤ ε / 2 := by
  obtain ⟨φ₀, ⟨hφ1, hφ2⟩, hz⟩ := exists_zero_gRe e
  have hε16 : 0 < ε / 16 := by positivity
  set x : ℝ := (φ₀ + Real.pi / 2) / (ε / 16) with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hε16.le
  obtain ⟨m, hm1, hm2⟩ := exists_nat_near hx0
  refine ⟨m, ?_, ?_⟩
  · rw [Finset.mem_range]
    have hxle : x ≤ 16 * Real.pi / ε := by
      rw [hx, div_le_div_iff₀ hε16 hε]
      nlinarith [Real.pi_pos]
    have hc := Nat.le_ceil (16 * Real.pi / ε)
    have : (m : ℝ) < ⌈16 * Real.pi / ε⌉₊ + 1 := by linarith
    exact_mod_cast this
  · have hdist : |(-(Real.pi / 2) + m * (ε / 16)) - φ₀| ≤ ε / 32 := by
      have : (-(Real.pi / 2) + m * (ε / 16)) - φ₀ = ((m : ℝ) - x) * (ε / 16) := by
        rw [hx]; field_simp; ring
      rw [this, abs_mul, abs_of_pos hε16]
      nlinarith [hm1]
    calc |gRe e (-(Real.pi / 2) + m * (ε / 16))|
        = |gRe e (-(Real.pi / 2) + m * (ε / 16)) - gRe e φ₀| := by rw [hz, sub_zero]
      _ ≤ ‖e‖ * |(-(Real.pi / 2) + m * (ε / 16)) - φ₀| := abs_gRe_sub_le e _ _
      _ ≤ 16 * (ε / 32) := by gcongr
      _ = ε / 2 := by ring

lemma annulus {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) {k : ℕ} (hk : 4 ≤ k) {e : ℂ}
    (he1 : (2 : ℝ) ^ k ≤ ‖e‖) (he2 : ‖e‖ < 2 ^ (k + 1)) :
    ∃ i ∈ Finset.range 17, ∃ m ∈ Finset.range (⌈4 / ε⌉₊ + 1), ∃ n : ℤ,
      |gRe e (-(Real.pi / 2) + i * (Real.pi / 16) + m * (ε / 2 ^ (k + 1))) - n| < ε / 2 := by
  obtain ⟨φ₀, ⟨hφ1, hφ2⟩, hz⟩ := exists_zero_gRe e
  have hpi := Real.pi_pos
  have hpi4 : Real.pi < 3.2 := by linarith [Real.pi_lt_d2]
  have hpi16 : 0 < Real.pi / 16 := by positivity
  set x : ℝ := (φ₀ + Real.pi / 2) / (Real.pi / 16) with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hpi16.le
  obtain ⟨i, hi1, hi2⟩ := exists_nat_near hx0
  have hx16 : x ≤ 16 := by
    rw [hx, div_le_iff₀ hpi16]; linarith
  have hi16 : i < 17 := by
    have : (i : ℝ) < 17 := by linarith
    exact_mod_cast this
  set β : ℝ := -(Real.pi / 2) + i * (Real.pi / 16) with hβ
  have hβφ : |β - φ₀| ≤ Real.pi / 32 := by
    have : β - φ₀ = ((i : ℝ) - x) * (Real.pi / 16) := by
      rw [hβ, hx]; field_simp; ring
    rw [this, abs_mul, abs_of_pos hpi16]
    nlinarith [hi1]
  set M : ℕ := ⌈4 / ε⌉₊ with hM
  have h2k : (32 : ℝ) ≤ 2 ^ (k + 1) := by
    have : (2 : ℝ) ^ 5 ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this ⊢; linarith
  have h2kpos : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  set dk : ℝ := ε / 2 ^ (k + 1) with hdk
  have hdk0 : 0 < dk := by positivity
  have hMge : 4 / ε ≤ M := Nat.le_ceil _
  have hMle : (M : ℝ) < 4 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hMdk_lo : 2 / 2 ^ k ≤ M * dk := by
    have : 4 / ε * dk = 2 / 2 ^ k := by
      rw [hdk, pow_succ]; field_simp; ring
    rw [← this]; gcongr
  have hMdk_hi : M * dk ≤ 0.13 := by
    have h1 : M * dk ≤ (4 / ε + 1) * dk := by gcongr
    have h2 : (4 / ε + 1) * dk = (4 + ε) / 2 ^ (k + 1) := by
      rw [hdk]; field_simp
    rw [h2] at h1
    have h3 : (4 + ε) / 2 ^ (k + 1) ≤ (4 + ε) / 32 := by
      apply div_le_div_of_nonneg_left (by linarith) (by norm_num) h2k
    linarith
  -- the sequence along the arc
  set y : ℕ → ℝ := fun m => gRe e (β + m * dk) with hy
  have hstep : ∀ m < M, |y (m + 1) - y m| < ε := by
    intro m _
    have h := abs_gRe_sub_le e (β + ((m + 1 : ℕ) : ℝ) * dk) (β + m * dk)
    have hd : |(β + ((m + 1 : ℕ) : ℝ) * dk) - (β + m * dk)| = dk := by
      push_cast; rw [show β + (m + 1) * dk - (β + m * dk) = dk by ring, abs_of_pos hdk0]
    rw [hd] at h
    have : ‖e‖ * dk < ε := by
      calc ‖e‖ * dk < 2 ^ (k + 1) * dk := by gcongr
        _ = ε := by rw [hdk]; field_simp
    exact lt_of_le_of_lt h this
  have hspan : 1 ≤ |y M - y 0| := by
    have hlt : β < β + M * dk := by
      have : 0 < (M : ℝ) * dk := by
        have : (0 : ℝ) < 2 / 2 ^ k := by positivity
        linarith
      linarith
    obtain ⟨ξ, ⟨hξ1, hξ2⟩, hξ⟩ := exists_hasDerivAt_eq_slope (gRe e) (fun x => -gIm e x) hlt
      (continuous_gRe e).continuousOn (fun x _ => hasDerivAt_gRe e x)
    have hMdkpos : 0 < (M : ℝ) * dk := by
      have : (0 : ℝ) < 2 / 2 ^ k := by positivity
      linarith
    have hyM : y M - y 0 = -gIm e ξ * (M * dk) := by
      have hden : β + M * dk - β = M * dk := by ring
      rw [hden] at hξ
      simp only [hy, Nat.cast_zero, zero_mul, add_zero]
      rw [hξ, div_mul_cancel₀ _ hMdkpos.ne']
    have hξφ : |ξ - φ₀| ≤ 0.23 := by
      have h1 : |ξ - β| ≤ M * dk := by
        rw [abs_le]; constructor <;> linarith
      calc |ξ - φ₀| = |(ξ - β) + (β - φ₀)| := by ring_nf
        _ ≤ |ξ - β| + |β - φ₀| := abs_add_le _ _
        _ ≤ 0.13 + Real.pi / 32 := by linarith
        _ ≤ 0.23 := by linarith
    have hgI : ‖e‖ / 2 ≤ |gIm e ξ| := by
      have h0 := abs_gIm_of_gRe_eq_zero hz
      have h1 := abs_gIm_sub_le e ξ φ₀
      have h2 : |gIm e φ₀| ≤ |gIm e ξ| + |gIm e ξ - gIm e φ₀| := by
        calc |gIm e φ₀| = |gIm e ξ - (gIm e ξ - gIm e φ₀)| := by ring_nf
          _ ≤ |gIm e ξ| + |gIm e ξ - gIm e φ₀| := abs_sub _ _
      have h3 : ‖e‖ * |ξ - φ₀| ≤ ‖e‖ * 0.23 := by gcongr
      nlinarith [norm_nonneg e]
    rw [hyM, abs_mul, abs_neg, abs_of_pos hMdkpos]
    calc (1 : ℝ) = (2 ^ k / 2) * (2 / 2 ^ k) := by field_simp
      _ ≤ (‖e‖ / 2) * (M * dk) := by
          gcongr
      _ ≤ |gIm e ξ| * (M * dk) := by
          have : 0 ≤ (M : ℝ) * dk := by positivity
          gcongr
  obtain ⟨m, hm, n, hn⟩ := exists_near_int_of_steps y M hstep hspan
  refine ⟨i, Finset.mem_range.mpr hi16, m, Finset.mem_range.mpr (by omega), n, ?_⟩
  simpa [hy, hβ, add_assoc] using hn

/- ## The deterministic disc cover -/

/-- The grid of angles for the small disc `|e| ≤ 16`. -/
noncomputable def smallAngles (ε : ℝ) : Finset ℝ :=
  (Finset.range (⌈16 * Real.pi / ε⌉₊ + 1)).image (fun m : ℕ => -(Real.pi / 2) + m * (ε / 16))

/-- The arcs of angles for the dyadic annuli `2^k ≤ |e| < 2^(k+1)`, `4 ≤ k ≤ log₂ R`. -/
noncomputable def annAngles (ε R : ℝ) : Finset ℝ :=
  ((Finset.Icc 4 (Nat.log 2 ⌊R⌋₊)) ×ˢ (Finset.range 17 ×ˢ Finset.range (⌈4 / ε⌉₊ + 1))).image
    (fun x : ℕ × ℕ × ℕ => -(Real.pi / 2) + x.2.1 * (Real.pi / 16) + x.2.2 * (ε / 2 ^ (x.1 + 1)))

/-- The parameter `q` of the rational rotations. -/
noncomputable def qPar (ε R : ℝ) : ℕ := ⌈128 * R / ε⌉₊ + 2

/-- The rotation pairs `(a, b)` (`u = a / b`) covering the disc of radius `R`. -/
noncomputable def discSet (ε R : ℝ) : Finset (GaussianInt × GaussianInt) := by
  classical
  exact insert (1, 1) ((smallAngles ε ∪ annAngles ε R).image (rotPair (qPar ε R)))

lemma mem_discSet_of_angle {ε R φ : ℝ} (h : φ ∈ smallAngles ε ∪ annAngles ε R) :
    rotPair (qPar ε R) φ ∈ discSet ε R := by
  classical
  unfold discSet
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨φ, h, rfl⟩)

theorem disc_cover {ε R : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) (hR : 16 ≤ R) :
    ((1 : GaussianInt), (1 : GaussianInt)) ∈ discSet ε R ∧
    (∀ p ∈ discSet ε R, (p.2 : ℂ) ≠ 0 ∧ ‖(p.1 : ℂ)‖ = ‖(p.2 : ℂ)‖ ∧
      ‖(p.2 : ℂ)‖ ≤ 128 * R / ε + 4) ∧
    (∀ e : ℂ, ‖e‖ ≤ R → ∃ p ∈ discSet ε R, InStripe ε ((p.1 : ℂ) / p.2) e) ∧
    ((discSet ε R).card : ℝ) ≤
      3 + 16 * Real.pi / ε + 17 * (4 / ε + 2) * ((Nat.log 2 ⌊R⌋₊ : ℝ) + 1) := by
  classical
  have hR0 : 0 < R := by linarith
  set q := qPar ε R with hqdef
  have hq2 : 2 ≤ q := by rw [hqdef, qPar]; omega
  have hqr : (q : ℝ) ≤ 128 * R / ε + 3 := by
    rw [hqdef, qPar]; push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ 128 * R / ε by positivity)
    linarith
  have hqr' : 128 * R / ε + 1 ≤ (q : ℝ) - 1 := by
    rw [hqdef, qPar]; push_cast
    have := Nat.le_ceil (128 * R / ε)
    linarith
  -- the rational replacement costs at most `ε / 64` inside the disc of radius `R`
  have happrox : ∀ φ : ℝ, ∀ e : ℂ, ‖e‖ ≤ R →
      |((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re - gRe e φ| ≤ ε / 64 := by
    intro φ e he
    refine (re_rotPair_close hq2 φ e).trans ?_
    have hq1 : 0 < (q : ℝ) - 1 := by linarith [show (0:ℝ) < 128 * R / ε + 1 by positivity]
    calc 2 / ((q : ℝ) - 1) * ‖e‖ ≤ 2 / ((q : ℝ) - 1) * R := by gcongr
      _ ≤ 2 / (128 * R / ε) * R := by
          gcongr
          linarith
      _ = ε / 64 := by field_simp; ring
  refine ⟨Finset.mem_insert_self _ _, ?_, ?_, ?_⟩
  · -- denominators
    intro p hp
    unfold discSet at hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · refine ⟨by simp [GaussianInt.toComplex_one], rfl, ?_⟩
      rw [GaussianInt.toComplex_one, norm_one]
      have : 0 ≤ 128 * R / ε := by positivity
      linarith
    · obtain ⟨φ, _, rfl⟩ := Finset.mem_image.mp hp'
      obtain ⟨h1, h2, _⟩ := rat_rot_approx hq2 φ
      simp only [rotPair, GaussianInt.toComplex_star]
      refine ⟨(map_ne_zero _).mpr h1, (Complex.norm_conj _).symm, ?_⟩
      rw [Complex.norm_conj]
      linarith
  · -- covering
    intro e he
    by_cases hsmall : ‖e‖ ≤ 16
    · obtain ⟨m, hm, hg⟩ := small_disc hε hsmall
      set φ := -(Real.pi / 2) + m * (ε / 16)
      have hφ : φ ∈ smallAngles ε ∪ annAngles ε R :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
      refine ⟨rotPair q φ, mem_discSet_of_angle hφ, 0, ?_⟩
      have h := happrox φ e he
      push_cast
      rw [sub_zero]
      calc |((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re|
          ≤ |((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re - gRe e φ| + |gRe e φ| := by
            have := abs_sub_abs_le_abs_sub
              ((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re (gRe e φ)
            linarith
        _ ≤ ε / 64 + ε / 2 := add_le_add h hg
        _ < ε := by linarith
    · push Not at hsmall
      set k := Nat.log 2 ⌊‖e‖⌋₊ with hk
      have hfl16 : 16 ≤ ⌊‖e‖⌋₊ := Nat.le_floor (by exact_mod_cast hsmall.le)
      have hk4 : 4 ≤ k := Nat.le_log_of_pow_le (by norm_num) (by norm_num; exact hfl16)
      have hflpos : ⌊‖e‖⌋₊ ≠ 0 := by omega
      have he1 : (2 : ℝ) ^ k ≤ ‖e‖ := by
        have h1 : 2 ^ k ≤ ⌊‖e‖⌋₊ := Nat.pow_log_le_self 2 hflpos
        have h2 : (⌊‖e‖⌋₊ : ℝ) ≤ ‖e‖ := Nat.floor_le (norm_nonneg _)
        calc (2 : ℝ) ^ k = ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ⌊‖e‖⌋₊ := by exact_mod_cast h1
          _ ≤ ‖e‖ := h2
      have he2 : ‖e‖ < 2 ^ (k + 1) := by
        have h1 : ⌊‖e‖⌋₊ < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
        have h2 : ‖e‖ < ⌊‖e‖⌋₊ + 1 := Nat.lt_floor_add_one _
        have h3 : ((⌊‖e‖⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at h3
        linarith
      have hkR : k ≤ Nat.log 2 ⌊R⌋₊ := Nat.log_mono_right (Nat.floor_le_floor he)
      obtain ⟨i, hi, m, hm, n, hn⟩ := annulus hε hε1 hk4 he1 he2
      set φ := -(Real.pi / 2) + i * (Real.pi / 16) + m * (ε / 2 ^ (k + 1))
      have hφ : φ ∈ smallAngles ε ∪ annAngles ε R := by
        apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨(k, i, m), ?_, rfl⟩
        simp only [Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨hk4, hkR⟩, hi, hm⟩
      refine ⟨rotPair q φ, mem_discSet_of_angle hφ, n, ?_⟩
      have h := happrox φ e he
      calc |((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re - n|
          ≤ |((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re - gRe e φ| +
            |gRe e φ - n| := by
            have := abs_sub_le ((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re
              (gRe e φ) n
            linarith
        _ < ε / 64 + ε / 2 := by linarith
        _ < ε := by linarith
  · -- the number of rotations
    have hc1 : ((smallAngles ε).card : ℝ) ≤ 16 * Real.pi / ε + 2 := by
      have h1 : (smallAngles ε).card ≤ ⌈16 * Real.pi / ε⌉₊ + 1 := by
        unfold smallAngles
        exact Finset.card_image_le.trans (by rw [Finset.card_range])
      have h2 := Nat.ceil_lt_add_one (show 0 ≤ 16 * Real.pi / ε by positivity)
      have h3 : ((smallAngles ε).card : ℝ) ≤ ⌈16 * Real.pi / ε⌉₊ + 1 := by exact_mod_cast h1
      linarith
    have hc2 : ((annAngles ε R).card : ℝ) ≤ 17 * (4 / ε + 2) * ((Nat.log 2 ⌊R⌋₊ : ℝ) + 1) := by
      have h1 : (annAngles ε R).card ≤
          (Nat.log 2 ⌊R⌋₊ + 1) * (17 * (⌈4 / ε⌉₊ + 1)) := by
        unfold annAngles
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_product, Finset.card_product, Finset.card_range, Finset.card_range,
          Nat.card_Icc]
        gcongr
        omega
      have h2 := Nat.ceil_lt_add_one (show 0 ≤ 4 / ε by positivity)
      have h3 : ((annAngles ε R).card : ℝ) ≤
          ((Nat.log 2 ⌊R⌋₊ : ℝ) + 1) * (17 * (⌈4 / ε⌉₊ + 1)) := by exact_mod_cast h1
      have h4 : (17 : ℝ) * (⌈4 / ε⌉₊ + 1) ≤ 17 * (4 / ε + 2) := by linarith
      have h5 : 0 ≤ (Nat.log 2 ⌊R⌋₊ : ℝ) + 1 := by positivity
      nlinarith
    have hU : (discSet ε R).card ≤ 1 + ((smallAngles ε).card + (annAngles ε R).card) := by
      unfold discSet
      calc _ ≤ ((smallAngles ε ∪ annAngles ε R).image (rotPair q)).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ (smallAngles ε ∪ annAngles ε R).card + 1 := by gcongr; exact Finset.card_image_le
        _ ≤ ((smallAngles ε).card + (annAngles ε R).card) + 1 := by
            gcongr; exact Finset.card_union_le _ _
        _ = 1 + ((smallAngles ε).card + (annAngles ε R).card) := by ring
    have hU' : ((discSet ε R).card : ℝ) ≤ 1 + ((smallAngles ε).card + (annAngles ε R).card) := by
      exact_mod_cast hU
    linarith

end Green41

/- ## Section: `Assembly` -/

/-
# Assembling the covering (conditional on `KL57With c`)

For `0 < ε < 1/10` the parameters are chosen in this order:
`G ≥ max(20/η, 2/δ, 1/ε, c η⁻⁵) + 66`, `u = ⌈log₅ G⌉`, `v = ⌈log₁₃ G⌉`, `K = G⁴`,
`L = commonDen K`, `H = √65^K`, `R = 2LH + 16`, `Q = 128R/ε + 4`,
`h = 2 ⌈log₆₅(⌈2LHQ⌉ + 1)⌉`, `T = ⌈K + log₅(2·13^h) + c η⁻⁵⌉`.
The orbit `Θ = {rot s t : s, t ≤ T}` satisfies the confinement lemma, the disc cover
handles radius `R`, and the end game covers the plane with
`(2 (T+1)² + 1) |U|` rotations.
-/

namespace Green41

open Complex ComplexConjugate

section Params

variable (c ε : ℝ)

/-- `max(20/η, 2/δ, 1/ε, c η⁻⁵)`. -/
noncomputable def X0 : ℝ :=
  max (max (20 / ηKL c ε) (2 / δKL c ε)) (max (1 / ε) (c * ηKL c ε ^ (-5 : ℝ)))
/-- The pigeonhole resolution `G`. -/
noncomputable def Gp : ℕ := ⌈X0 c ε⌉₊ + 66
/-- `u = ⌈log₅ G⌉`. -/
noncomputable def up : ℕ := Nat.clog 5 (Gp c ε)
/-- `v = ⌈log₁₃ G⌉`. -/
noncomputable def vp : ℕ := Nat.clog 13 (Gp c ε)
/-- The short-orbit length `K = G⁴`. -/
noncomputable def Kp : ℕ := Gp c ε ^ 4
/-- The common denominator `L`. -/
noncomputable def Lp : ℕ := commonDen (Kp c ε)
/-- The confinement radius `H = √65^K`. -/
noncomputable def Hp : ℝ := Real.sqrt 65 ^ Kp c ε
/-- The disc radius `R = 2LH + 16`. -/
noncomputable def Rp : ℝ := 2 * Lp c ε * Hp c ε + 16
/-- The denominator bound `Q = 128R/ε + 4` of the disc cover. -/
noncomputable def Qp : ℝ := 128 * Rp c ε / ε + 4
/-- The lattice exponent `h`, with `|D_h| = √65^h > 2LHQ`. -/
noncomputable def hp : ℕ := 2 * Nat.clog 65 (⌈2 * (Lp c ε : ℝ) * Hp c ε * Qp c ε⌉₊ + 1)
/-- The orbit length `T`. -/
noncomputable def Tp : ℕ :=
  ⌈(Kp c ε : ℝ) + Real.logb 5 (2 * 13 ^ hp c ε) + c * ηKL c ε ^ (-5 : ℝ)⌉₊
/-- The orbit rotations `rot s t`, `s, t ≤ T`. -/
noncomputable def Θp : Finset ℂ := by
  classical
  exact (labels (Tp c ε)).image (fun p => rot p.1 p.2)
/-- The final rotation set. -/
noncomputable def Ωp : Finset ℂ := endgameSet (Θp c ε) (discSet ε (Rp c ε)) (Lp c ε)

end Params

lemma cnorm_gD (h : ℕ) : ‖(gD h : ℂ)‖ = Real.sqrt 65 ^ h := by
  have e : (gD h : ℂ) = (gPb : ℂ) ^ h * (gQb : ℂ) ^ h := by simp only [gD, map_mul, map_pow]
  rw [e, norm_mul, norm_pow, norm_pow, cnorm_gPb, cnorm_gQb, ← mul_pow,
    ← Real.sqrt_mul (by norm_num)]
  norm_num

section Bounds

variable {c ε : ℝ}

lemma X0_ge :
    20 / ηKL c ε ≤ X0 c ε ∧ 2 / δKL c ε ≤ X0 c ε ∧ 1 / ε ≤ X0 c ε ∧
      c * ηKL c ε ^ (-5 : ℝ) ≤ X0 c ε := by
  unfold X0
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

lemma Gp_ge : X0 c ε ≤ Gp c ε ∧ 66 ≤ Gp c ε := by
  constructor
  · unfold Gp; push_cast
    have := Nat.le_ceil (X0 c ε)
    linarith
  · unfold Gp; omega

lemma up_bounds : Gp c ε ≤ 5 ^ up c ε ∧ 5 ^ up c ε < 5 * Gp c ε := by
  have hG := (Gp_ge (c := c) (ε := ε)).2
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  have hpos : 0 < up c ε := Nat.clog_pos (by norm_num) (by omega)
  have hlt := Nat.pow_pred_clog_lt_self (b := 5) (by norm_num) (show 1 < Gp c ε by omega)
  unfold up at hpos ⊢
  obtain ⟨m, hm⟩ : ∃ m, Nat.clog 5 (Gp c ε) = m + 1 := ⟨Nat.clog 5 (Gp c ε) - 1, by omega⟩
  rw [hm] at hlt ⊢
  have hlt' : 5 ^ m < Gp c ε := by simpa using hlt
  rw [pow_succ]
  omega

lemma vp_bounds : Gp c ε ≤ 13 ^ vp c ε ∧ 13 ^ vp c ε < 13 * Gp c ε := by
  have hG := (Gp_ge (c := c) (ε := ε)).2
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  have hpos : 0 < vp c ε := Nat.clog_pos (by norm_num) (by omega)
  have hlt := Nat.pow_pred_clog_lt_self (b := 13) (by norm_num) (show 1 < Gp c ε by omega)
  unfold vp at hpos ⊢
  obtain ⟨m, hm⟩ : ∃ m, Nat.clog 13 (Gp c ε) = m + 1 := ⟨Nat.clog 13 (Gp c ε) - 1, by omega⟩
  rw [hm] at hlt ⊢
  have hlt' : 13 ^ m < Gp c ε := by simpa using hlt
  rw [pow_succ]
  omega

lemma hK_param :
    (5 ^ up c ε * 13 ^ vp c ε) ^ 2 * Gp c ε ^ 2 < (Kp c ε + 1) ^ 2 := by
  have hG := (Gp_ge (c := c) (ε := ε)).2
  obtain ⟨_, hu⟩ := up_bounds (c := c) (ε := ε)
  obtain ⟨_, hv⟩ := vp_bounds (c := c) (ε := ε)
  set G := Gp c ε
  have hM : 5 ^ up c ε * 13 ^ vp c ε < 65 * G ^ 2 := by
    calc 5 ^ up c ε * 13 ^ vp c ε < (5 * G) * (13 * G) := Nat.mul_lt_mul'' hu hv
      _ = 65 * G ^ 2 := by ring
  have h1 : (5 ^ up c ε * 13 ^ vp c ε) ^ 2 * G ^ 2 < (65 * G ^ 2) ^ 2 * G ^ 2 := by
    have hG0 : 0 < G ^ 2 := by positivity
    have := Nat.pow_lt_pow_left hM (two_ne_zero)
    exact Nat.mul_lt_mul_of_pos_right this hG0
  have h2 : (65 * G ^ 2) ^ 2 * G ^ 2 ≤ G ^ 8 := by
    have : 65 * 65 ≤ G ^ 2 := by nlinarith
    calc (65 * G ^ 2) ^ 2 * G ^ 2 = (65 * 65) * G ^ 6 := by ring
      _ ≤ G ^ 2 * G ^ 6 := Nat.mul_le_mul_right _ this
      _ = G ^ 8 := by ring
  have h3 : G ^ 8 < (Kp c ε + 1) ^ 2 := by
    unfold Kp
    have : G ^ 8 = (G ^ 4) ^ 2 := by ring
    rw [this]
    exact Nat.pow_lt_pow_left (Nat.lt_succ_self _) two_ne_zero
  omega

lemma Hp_ge_one : 1 ≤ Hp c ε := by
  unfold Hp
  exact one_le_pow₀ (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num)

lemma Lp_pos : 0 < Lp c ε := commonDen_pos _

lemma Rp_ge : 16 ≤ Rp c ε ∧ 2 * (Lp c ε : ℝ) * Hp c ε ≤ Rp c ε := by
  unfold Rp
  have h1 : (0 : ℝ) ≤ 2 * Lp c ε * Hp c ε := by
    have := Hp_ge_one (c := c) (ε := ε)
    positivity
  constructor <;> linarith

lemma hp_spec (hε : 0 < ε) : 1 ≤ hp c ε ∧
    2 * (Lp c ε : ℝ) * Hp c ε * Qp c ε < ‖(gD (hp c ε) : ℂ)‖ := by
  set X := 2 * (Lp c ε : ℝ) * Hp c ε * Qp c ε with hX
  have hXpos : 0 < X := by
    have hL : (0 : ℝ) < Lp c ε := by exact_mod_cast Lp_pos
    have hH := Hp_ge_one (c := c) (ε := ε)
    have hQ : 0 < Qp c ε := by
      unfold Qp
      have := (Rp_ge (c := c) (ε := ε)).1
      positivity
    rw [hX]; positivity
  have hceil : 1 ≤ ⌈X⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; rw [Nat.ceil_eq_zero] at h0; linarith)
  set m := Nat.clog 65 (⌈X⌉₊ + 1) with hm
  have hm1 : 0 < m := Nat.clog_pos (by norm_num) (by omega)
  constructor
  · unfold hp; rw [← hm]; omega
  · rw [cnorm_gD]
    unfold hp
    rw [← hm, pow_mul, Real.sq_sqrt (by norm_num)]
    have h1 : ⌈X⌉₊ + 1 ≤ 65 ^ m := Nat.le_pow_clog (by norm_num) _
    have h2 : X < ⌈X⌉₊ + 1 := by
      have := Nat.le_ceil X; linarith
    have h3 : ((⌈X⌉₊ + 1 : ℕ) : ℝ) ≤ ((65 ^ m : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith

end Bounds

/-- The covering assembled from the confinement lemma, the disc cover and the end game. -/
theorem minCopies_le_param {c ε : ℝ} (hKL : KL57With c) (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    (minCopies ε : ℝ) ≤ (2 * ((Tp c ε : ℝ) + 1) ^ 2 + 1) * (discSet ε (Rp c ε)).card := by
  classical
  obtain ⟨hX20, hX2, _, hXc⟩ := X0_ge (c := c) (ε := ε)
  obtain ⟨hGX, hG66⟩ := Gp_ge (c := c) (ε := ε)
  obtain ⟨hu, _⟩ := up_bounds (c := c) (ε := ε)
  obtain ⟨hv, _⟩ := vp_bounds (c := c) (ε := ε)
  obtain ⟨hR16, hRLH⟩ := Rp_ge (c := c) (ε := ε)
  obtain ⟨hh1, hD⟩ := hp_spec (c := c) hε
  obtain ⟨hU1, hU2, hU3, _⟩ := disc_cover hε hε1 hR16
  have hGr : (66 : ℝ) ≤ Gp c ε := by exact_mod_cast hG66
  -- confinement for the orbit `Θ`
  have hconf : ∀ w : ℂ, (∀ θ ∈ Θp c ε, ¬ InStripe ε θ w) →
      ∃ k : GaussianInt, ‖w - (gD (hp c ε) : ℂ) / (Lp c ε : ℂ) * k‖ ≤ Hp c ε := by
    intro w hw
    have hw' : ∀ s t : ℕ, s ≤ Tp c ε → t ≤ Tp c ε → ¬ InStripe ε (rot s t) w := by
      intro s t hs ht
      apply hw
      unfold Θp
      exact Finset.mem_image.mpr ⟨(s, t), mem_labels.mpr ⟨hs, ht⟩, rfl⟩
    exact confinement hKL hε hε1 (by linarith) (by linarith) (by omega) hu hv
      (hK_param (c := c) (ε := ε)) hh1 (Nat.le_ceil _) w hw'
  -- the end game
  have hcov : ∀ z : ℂ, ∃ v ∈ Ωp c ε, InStripe ε v z := by
    intro z
    unfold Ωp
    refine endgame_cover (Q := Qp c ε) Lp_pos (Θp c ε) (discSet ε (Rp c ε)) hconf ?_ hU1 ?_ hD z
    · intro p hp
      obtain ⟨h1, h2, h3⟩ := hU2 p hp
      exact ⟨h1, h2, by unfold Qp; exact h3⟩
    · intro e he
      exact hU3 e (he.trans hRLH)
  have hunit : ∀ v ∈ Ωp c ε, ‖v‖ = 1 := by
    unfold Ωp
    refine norm_of_mem_endgameSet Lp_pos ?_ ?_
    · intro θ hθ
      unfold Θp at hθ
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hθ
      exact norm_rot _ _
    · intro p hp
      obtain ⟨h1, h2, _⟩ := hU2 p hp
      exact ⟨h1, h2⟩
  have hmin := minCopies_le_of_cover (Ωp c ε) hunit hcov
  have hcard := card_endgameSet_le (Θp c ε) (discSet ε (Rp c ε)) (Lp c ε)
  have hΘ : (Θp c ε).card ≤ (Tp c ε + 1) ^ 2 := by
    unfold Θp
    exact Finset.card_image_le.trans (by rw [card_labels])
  have h1 : (minCopies ε : ℝ) ≤ (Ωp c ε).card := by exact_mod_cast hmin
  have h2 : ((Ωp c ε).card : ℝ) ≤
      2 * (Θp c ε).card * (discSet ε (Rp c ε)).card + (discSet ε (Rp c ε)).card := by
    unfold Ωp; exact_mod_cast hcard
  have h3 : ((Θp c ε).card : ℝ) ≤ ((Tp c ε : ℝ) + 1) ^ 2 := by exact_mod_cast hΘ
  have hU0 : (0 : ℝ) ≤ (discSet ε (Rp c ε)).card := by positivity
  calc (minCopies ε : ℝ) ≤ (Ωp c ε).card := h1
    _ ≤ 2 * (Θp c ε).card * (discSet ε (Rp c ε)).card + (discSet ε (Rp c ε)).card := h2
    _ ≤ 2 * ((Tp c ε : ℝ) + 1) ^ 2 * (discSet ε (Rp c ε)).card + (discSet ε (Rp c ε)).card := by
        gcongr
    _ = (2 * ((Tp c ε : ℝ) + 1) ^ 2 + 1) * (discSet ε (Rp c ε)).card := by ring

end Green41

/- ## Section: `Estimates` -/

/-
# Polynomial bookkeeping: `minCopies ε ≤ G^88`

All auxiliary quantities are bounded crudely in terms of `B = (K+1)^5`, `K = G⁴`:
`L ≤ 65^B`, `H ≤ 65^B`, `R ≤ 65^(2B+1)`, `Q ≤ 65^(3B+3)`, `h ≤ 10B + 10`, `T ≤ 44B`,
`|U| ≤ 2300 B²`. Hence `minCopies ε ≤ 10^7 B⁴ ≤ G^88`.
-/

namespace Green41

open Complex ComplexConjugate

section

variable {c ε : ℝ}

/-- `B = (K+1)^5`. -/
noncomputable def Bp (c ε : ℝ) : ℕ := (Kp c ε + 1) ^ 5

lemma one_le_Bp : 1 ≤ Bp c ε := by unfold Bp; exact Nat.one_le_pow _ _ (by omega)

lemma Kp_le_Bp : Kp c ε ≤ Bp c ε := by
  unfold Bp
  calc Kp c ε ≤ Kp c ε + 1 := Nat.le_succ _
    _ = (Kp c ε + 1) ^ 1 := (pow_one _).symm
    _ ≤ (Kp c ε + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)

lemma Gp_le_Kp : Gp c ε ≤ Kp c ε := by
  unfold Kp
  have hG := (Gp_ge (c := c) (ε := ε)).2
  calc Gp c ε = Gp c ε ^ 1 := (pow_one _).symm
    _ ≤ Gp c ε ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)

lemma Gp_le_Bp : Gp c ε ≤ Bp c ε := Gp_le_Kp.trans Kp_le_Bp

lemma Bp_lt_pow : (Bp c ε : ℝ) < 65 ^ Bp c ε := by
  have h : Bp c ε < 65 ^ Bp c ε := Nat.lt_pow_self (by norm_num)
  exact_mod_cast h

lemma Lp_le : (Lp c ε : ℝ) ≤ 65 ^ Bp c ε := by
  have h1 := commonDen_le (Kp c ε)
  have h2 : 4 * 65 ^ Kp c ε ≤ 65 ^ (Kp c ε + 1) := by rw [pow_succ]; omega
  have h3 : (4 * 65 ^ Kp c ε) ^ ((Kp c ε + 1) ^ 4) ≤ 65 ^ Bp c ε := by
    calc (4 * 65 ^ Kp c ε) ^ ((Kp c ε + 1) ^ 4) ≤ (65 ^ (Kp c ε + 1)) ^ ((Kp c ε + 1) ^ 4) :=
          Nat.pow_le_pow_left h2 _
      _ = 65 ^ Bp c ε := by rw [← pow_mul, Bp]; ring_nf
  have h4 : Lp c ε ≤ 65 ^ Bp c ε := by unfold Lp; exact h1.trans h3
  exact_mod_cast h4

lemma Hp_le : Hp c ε ≤ 65 ^ Bp c ε := by
  unfold Hp
  have h1 : Real.sqrt 65 ≤ 65 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc Real.sqrt 65 ^ Kp c ε ≤ 65 ^ Kp c ε := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 _
    _ ≤ 65 ^ Bp c ε := pow_le_pow_right₀ (by norm_num) Kp_le_Bp

lemma Rp_le : Rp c ε ≤ 65 ^ (2 * Bp c ε + 1) := by
  unfold Rp
  have hL := Lp_le (c := c) (ε := ε)
  have hH := Hp_le (c := c) (ε := ε)
  have hH0 : 0 ≤ Hp c ε := le_trans zero_le_one Hp_ge_one
  have hpow : (65 : ℝ) ^ (2 * Bp c ε + 1) = 65 * (65 ^ Bp c ε * 65 ^ Bp c ε) := by
    rw [pow_succ, two_mul, pow_add]; ring
  have h1 : (1 : ℝ) ≤ 65 ^ Bp c ε := one_le_pow₀ (by norm_num)
  have h2 : 2 * (Lp c ε : ℝ) * Hp c ε ≤ 2 * (65 ^ Bp c ε * 65 ^ Bp c ε) := by
    have : (Lp c ε : ℝ) * Hp c ε ≤ 65 ^ Bp c ε * 65 ^ Bp c ε := by
      apply mul_le_mul hL hH hH0 (by positivity)
    nlinarith
  rw [hpow]
  nlinarith

lemma inv_ε_le : 1 / ε ≤ Bp c ε := by
  obtain ⟨_, _, h1, _⟩ := X0_ge (c := c) (ε := ε)
  have h2 := (Gp_ge (c := c) (ε := ε)).1
  have h3 : (Gp c ε : ℝ) ≤ Bp c ε := by exact_mod_cast Gp_le_Bp
  linarith

lemma cη_le : c * ηKL c ε ^ (-5 : ℝ) ≤ Bp c ε := by
  obtain ⟨_, _, _, h1⟩ := X0_ge (c := c) (ε := ε)
  have h2 := (Gp_ge (c := c) (ε := ε)).1
  have h3 : (Gp c ε : ℝ) ≤ Bp c ε := by exact_mod_cast Gp_le_Bp
  linarith

/- Abstract versions of the remaining estimates (to keep the definitions folded). -/

lemma Q_le_aux {B : ℕ} {R x : ℝ} (hR : R ≤ 65 ^ (2 * B + 1)) (hR0 : 0 ≤ R)
    (hx : x ≤ B) (hx0 : 0 ≤ x) : 128 * R * x + 4 ≤ (65 : ℝ) ^ (3 * B + 3) := by
  have hB : (B : ℝ) < 65 ^ B := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 65)
  have hpow : (65 : ℝ) ^ (3 * B + 3) = 65 ^ 2 * (65 ^ (2 * B + 1) * 65 ^ B) := by
    rw [show 3 * B + 3 = 2 + ((2 * B + 1) + B) by ring, pow_add, pow_add]
  have h1 : (1 : ℝ) ≤ 65 ^ (2 * B + 1) * 65 ^ B := by
    have h1a : (1 : ℝ) ≤ 65 ^ (2 * B + 1) := one_le_pow₀ (by norm_num)
    have h1b : (1 : ℝ) ≤ 65 ^ B := one_le_pow₀ (by norm_num)
    nlinarith
  have h3 : R * x ≤ 65 ^ (2 * B + 1) * 65 ^ B :=
    mul_le_mul hR (hx.trans hB.le) hx0 (by positivity)
  rw [hpow]
  nlinarith

lemma Qp_le (hε : 0 < ε) : Qp c ε ≤ 65 ^ (3 * Bp c ε + 3) := by
  have h := Q_le_aux (B := Bp c ε) (Rp_le (c := c) (ε := ε))
    (by linarith [(Rp_ge (c := c) (ε := ε)).1]) (inv_ε_le (c := c) (ε := ε)) (by positivity)
  unfold Qp
  calc 128 * Rp c ε / ε + 4 = 128 * Rp c ε * (1 / ε) + 4 := by ring
    _ ≤ _ := h

lemma X_le_aux {B : ℕ} {L H Q : ℝ} (hL : L ≤ 65 ^ B) (hH : H ≤ 65 ^ B)
    (hQ : Q ≤ 65 ^ (3 * B + 3)) (hL0 : 0 ≤ L) (hH0 : 0 ≤ H) (hQ0 : 0 ≤ Q) :
    2 * L * H * Q ≤ (65 : ℝ) ^ (5 * B + 4) := by
  have hpow : (65 : ℝ) ^ (5 * B + 4) = 65 * (65 ^ B * 65 ^ B * 65 ^ (3 * B + 3)) := by
    rw [show 5 * B + 4 = 1 + (B + B + (3 * B + 3)) by ring, pow_add, pow_add, pow_add, pow_one]
  have h1 : L * H * Q ≤ 65 ^ B * 65 ^ B * 65 ^ (3 * B + 3) :=
    mul_le_mul (mul_le_mul hL hH hH0 (by positivity)) hQ hQ0 (by positivity)
  rw [hpow]
  have h2 : 0 ≤ L * H * Q := by positivity
  nlinarith

lemma Qp_nonneg (hε : 0 < ε) : 0 ≤ Qp c ε := by
  unfold Qp; have := (Rp_ge (c := c) (ε := ε)).1; positivity

lemma X_le (hε : 0 < ε) :
    2 * (Lp c ε : ℝ) * Hp c ε * Qp c ε ≤ 65 ^ (5 * Bp c ε + 4) :=
  X_le_aux Lp_le Hp_le (Qp_le (c := c) hε) (by positivity) (le_trans zero_le_one Hp_ge_one)
    (Qp_nonneg (c := c) hε)

lemma clog_aux {B : ℕ} {X : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ (65 : ℝ) ^ (5 * B + 4)) :
    Nat.clog 65 (⌈X⌉₊ + 1) ≤ 5 * B + 5 := by
  apply Nat.clog_le_of_le_pow
  have hceil : (⌈X⌉₊ : ℝ) < X + 1 := Nat.ceil_lt_add_one hX0
  have h4 : (1 : ℝ) ≤ 65 ^ (5 * B + 4) := one_le_pow₀ (by norm_num)
  have h3 : (65 : ℝ) ^ (5 * B + 5) = 65 * 65 ^ (5 * B + 4) := by
    rw [show 5 * B + 5 = (5 * B + 4) + 1 by ring, pow_succ]; ring
  have h2 : ((⌈X⌉₊ + 1 : ℕ) : ℝ) ≤ ((65 ^ (5 * B + 5) : ℕ) : ℝ) := by
    push_cast
    rw [h3]; linarith
  exact_mod_cast h2

lemma hp_le (hε : 0 < ε) : hp c ε ≤ 10 * Bp c ε + 10 := by
  have hX0 : 0 ≤ 2 * (Lp c ε : ℝ) * Hp c ε * Qp c ε := by
    have hH0 : 0 ≤ Hp c ε := le_trans zero_le_one Hp_ge_one
    have hQ0 := Qp_nonneg (c := c) hε
    positivity
  have h := clog_aux hX0 (X_le (c := c) hε)
  unfold hp
  omega

lemma logb_bound (h : ℕ) : Real.logb 5 (2 * 13 ^ h) ≤ 1 + 2 * h := by
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow]
  have h1 : Real.logb 5 2 ≤ 1 := by
    rw [← Real.logb_self_eq_one (b := 5) (by norm_num)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 5 13 ≤ 2 := by
    have : Real.logb 5 25 = 2 := by
      rw [show (25 : ℝ) = 5 ^ (2 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    rw [← this]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
  have h3 : (0 : ℝ) ≤ h := by positivity
  nlinarith

lemma T_le_aux {B K h : ℕ} {t : ℝ} (hK : K ≤ B) (hh : h ≤ 10 * B + 10) (ht0 : 0 ≤ t)
    (ht : t ≤ B) (hB1 : 1 ≤ B) :
    (⌈(K : ℝ) + Real.logb 5 (2 * 13 ^ h) + t⌉₊ : ℝ) ≤ 44 * B := by
  have hKr : (K : ℝ) ≤ B := by exact_mod_cast hK
  have hhr : (h : ℝ) ≤ 10 * B + 10 := by exact_mod_cast hh
  have hB1r : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hlog := logb_bound h
  have hlog0 : 0 ≤ Real.logb 5 (2 * 13 ^ h) :=
    Real.logb_nonneg (by norm_num) (by
      have : (1 : ℝ) ≤ 13 ^ h := one_le_pow₀ (by norm_num)
      linarith)
  have hnn : 0 ≤ (K : ℝ) + Real.logb 5 (2 * 13 ^ h) + t := by positivity
  have hT := Nat.ceil_lt_add_one hnn
  linarith

lemma Tp_le (hc : 0 ≤ c) (hε : 0 < ε) : (Tp c ε : ℝ) ≤ 44 * Bp c ε := by
  unfold Tp
  exact T_le_aux Kp_le_Bp (hp_le (c := c) hε)
    (by have := ηKL_pos c ε; positivity) (cη_le (c := c) (ε := ε)) one_le_Bp

lemma U_le_aux {B : ℕ} {ε R : ℝ} (hB1 : 1 ≤ B) (hε : 0 < ε) (hiε : 1 / ε ≤ B)
    (hR16 : 16 ≤ R) (hR : R ≤ (65 : ℝ) ^ (2 * B + 1)) :
    3 + 16 * Real.pi / ε + 17 * (4 / ε + 2) * ((Nat.log 2 ⌊R⌋₊ : ℝ) + 1) ≤ 2200 * (B : ℝ) ^ 2 := by
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hfl0 : ⌊R⌋₊ ≠ 0 := by
    have : 16 ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hR16)
    omega
  have hlt : ⌊R⌋₊ < 2 ^ (7 * (2 * B + 1)) := by
    have h1 : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le (by linarith)
    have h2 : (65 : ℝ) ^ (2 * B + 1) < 2 ^ (7 * (2 * B + 1)) := by
      rw [pow_mul]
      exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    have h3 : (⌊R⌋₊ : ℝ) < ((2 ^ (7 * (2 * B + 1)) : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h3
  have hlog : Nat.log 2 ⌊R⌋₊ < 7 * (2 * B + 1) := Nat.log_lt_of_lt_pow hfl0 hlt
  have hlogr : (Nat.log 2 ⌊R⌋₊ : ℝ) + 1 ≤ 21 * B := by
    have : Nat.log 2 ⌊R⌋₊ + 1 ≤ 21 * B := by omega
    exact_mod_cast this
  have hpi : Real.pi ≤ 3.15 := by linarith [Real.pi_lt_d2]
  have h1 : 16 * Real.pi / ε ≤ 51 * B := by
    have : 16 * Real.pi / ε = 16 * Real.pi * (1 / ε) := by ring
    rw [this]
    have hpi0 := Real.pi_pos
    nlinarith
  have h2 : 4 / ε + 2 ≤ 6 * B := by
    have : 4 / ε = 4 * (1 / ε) := by ring
    rw [this]; linarith
  have h3 : 17 * (4 / ε + 2) * ((Nat.log 2 ⌊R⌋₊ : ℝ) + 1) ≤ 17 * (6 * B) * (21 * B) := by
    have h4 : 0 ≤ 4 / ε + 2 := by positivity
    have h5 : 0 ≤ (Nat.log 2 ⌊R⌋₊ : ℝ) + 1 := by positivity
    gcongr
  nlinarith

lemma card_discSet_le (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    ((discSet ε (Rp c ε)).card : ℝ) ≤ 2200 * (Bp c ε : ℝ) ^ 2 := by
  obtain ⟨_, _, _, hcard⟩ := disc_cover hε hε1 (Rp_ge (c := c) (ε := ε)).1
  exact hcard.trans (U_le_aux one_le_Bp hε inv_ε_le (Rp_ge (c := c) (ε := ε)).1 Rp_le)

lemma final_aux {B G : ℕ} {m T U : ℝ} (hG : 66 ≤ G) (hB : B ≤ 32 * G ^ 20) (hB1 : 1 ≤ B)
    (hm : m ≤ (2 * (T + 1) ^ 2 + 1) * U) (hT : T ≤ 44 * B) (hT0 : 0 ≤ T)
    (hU : U ≤ 2200 * (B : ℝ) ^ 2) (hU0 : 0 ≤ U) : m ≤ (G : ℝ) ^ 88 := by
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hGr : (66 : ℝ) ≤ G := by exact_mod_cast hG
  have hBG : (B : ℝ) ≤ 32 * (G : ℝ) ^ 20 := by exact_mod_cast hB
  have h1 : (2 * (T + 1) ^ 2 + 1) ≤ 4051 * (B : ℝ) ^ 2 := by
    have : T + 1 ≤ 45 * B := by linarith
    have h2 : (T + 1) ^ 2 ≤ (45 * (B : ℝ)) ^ 2 := by gcongr
    nlinarith
  have h2 : m ≤ 4051 * (B : ℝ) ^ 2 * (2200 * (B : ℝ) ^ 2) := by
    calc m ≤ (2 * (T + 1) ^ 2 + 1) * U := hm
      _ ≤ 4051 * (B : ℝ) ^ 2 * (2200 * (B : ℝ) ^ 2) := by
          apply mul_le_mul h1 hU hU0 (by positivity)
  have h3 : 4051 * (B : ℝ) ^ 2 * (2200 * (B : ℝ) ^ 2) ≤ 10 ^ 7 * (B : ℝ) ^ 4 := by nlinarith
  have h4 : (B : ℝ) ^ 4 ≤ (32 * (G : ℝ) ^ 20) ^ 4 := by gcongr
  have h5 : (10 : ℝ) ^ 7 * (32 * (G : ℝ) ^ 20) ^ 4 ≤ (G : ℝ) ^ 88 := by
    have hG8 : (10 : ℝ) ^ 7 * 32 ^ 4 ≤ (G : ℝ) ^ 8 := by
      calc (10 : ℝ) ^ 7 * 32 ^ 4 ≤ 66 ^ 8 := by norm_num
        _ ≤ (G : ℝ) ^ 8 := by gcongr
    have : (10 : ℝ) ^ 7 * (32 * (G : ℝ) ^ 20) ^ 4 = (10 ^ 7 * 32 ^ 4) * (G : ℝ) ^ 80 := by ring
    rw [this]
    calc (10 ^ 7 * 32 ^ 4) * (G : ℝ) ^ 80 ≤ (G : ℝ) ^ 8 * (G : ℝ) ^ 80 := by gcongr
      _ = (G : ℝ) ^ 88 := by ring
  calc m ≤ 4051 * (B : ℝ) ^ 2 * (2200 * (B : ℝ) ^ 2) := h2
    _ ≤ 10 ^ 7 * (B : ℝ) ^ 4 := h3
    _ ≤ 10 ^ 7 * (32 * (G : ℝ) ^ 20) ^ 4 := by gcongr
    _ ≤ (G : ℝ) ^ 88 := h5

lemma Bp_le_G (c ε : ℝ) : Bp c ε ≤ 32 * Gp c ε ^ 20 := by
  have hG := (Gp_ge (c := c) (ε := ε)).2
  unfold Bp Kp
  calc (Gp c ε ^ 4 + 1) ^ 5 ≤ (2 * Gp c ε ^ 4) ^ 5 := by
        apply Nat.pow_le_pow_left
        have : 1 ≤ Gp c ε ^ 4 := Nat.one_le_pow _ _ (by omega)
        omega
    _ = 32 * Gp c ε ^ 20 := by ring

/-- `minCopies ε ≤ G^88`, conditional on `KL57With c`. -/
theorem minCopies_le_G_pow (hKL : KL57With c) (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    (minCopies ε : ℝ) ≤ (Gp c ε : ℝ) ^ 88 :=
  final_aux (Gp_ge (c := c) (ε := ε)).2 (Bp_le_G c ε) one_le_Bp
    (minCopies_le_param hKL hε hε1) (Tp_le hc hε) (by positivity)
    (card_discSet_le hε hε1) (by positivity)

end

end Green41

/- ## Section: `Final` -/

/-
# The double-exponential bound, conditional on `KL57`

With `a = ε^(-c)`, `x = 1/ε` and `Y = η⁻⁵ = 5^(5a) ≤ e^(20a)`:
`G ≤ 91 exp(12(1+c)Y + x)`, so `G^88 ≤ exp(S)` with `S ≤ A e^(20a) x`, `A = 10⁴(1+c)`.
For `x ≥ 10 + log A` this is at most `exp(a x²) = exp(ε^(-(c+2)))`.
-/

namespace Green41

open Complex ComplexConjugate

lemma le_exp_self (x : ℝ) : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]

lemma log_le_self_sub_one {x : ℝ} (hx : 0 < x) : Real.log x ≤ x - 1 :=
  Real.log_le_sub_one_of_pos hx

section

variable {c ε : ℝ}

lemma a_ge_one (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε ≤ 1) : 1 ≤ ε ^ (-c) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)

lemma Y_eq (c ε : ℝ) : ηKL c ε ^ (-5 : ℝ) = (5 : ℝ) ^ (5 * ε ^ (-c)) := by
  unfold ηKL
  rw [← Real.rpow_mul (by norm_num)]
  ring_nf

lemma inv_η_le_Y (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 / ηKL c ε ≤ ηKL c ε ^ (-5 : ℝ) := by
  have ha := a_ge_one hc hε hε1
  rw [Y_eq]
  unfold ηKL
  rw [Real.rpow_neg (by norm_num), one_div, inv_inv]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

lemma one_le_Y (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε ≤ 1) : 1 ≤ ηKL c ε ^ (-5 : ℝ) := by
  rw [Y_eq]
  exact Real.one_le_rpow (by norm_num) (by have := a_ge_one hc hε hε1; linarith)

lemma Y_le_exp (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ηKL c ε ^ (-5 : ℝ) ≤ Real.exp (20 * ε ^ (-c)) := by
  have ha := a_ge_one hc hε hε1
  rw [Y_eq, Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  have h5 : Real.log 5 ≤ 4 := by linarith [log_le_self_sub_one (show (0:ℝ) < 5 by norm_num)]
  have h0 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  nlinarith

lemma two_div_δ (c ε : ℝ) : 2 / δKL c ε = 2 * (13 : ℝ) ^ (c * ηKL c ε ^ (-5 : ℝ)) := by
  unfold δKL
  rw [Real.rpow_neg (by norm_num)]
  field_simp

lemma thirteen_rpow_le {y : ℝ} (hy : 0 ≤ y) : (13 : ℝ) ^ y ≤ Real.exp (12 * y) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  have h13 : Real.log 13 ≤ 12 := by linarith [log_le_self_sub_one (show (0:ℝ) < 13 by norm_num)]
  nlinarith

theorem Gp_le_exp (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (Gp c ε : ℝ) ≤ 91 * Real.exp (12 * (1 + c) * ηKL c ε ^ (-5 : ℝ) + 1 / ε) := by
  set Y := ηKL c ε ^ (-5 : ℝ) with hY
  have hY1 : 1 ≤ Y := one_le_Y hc hε hε1
  have hη := ηKL_pos c ε
  set E := Real.exp (12 * (1 + c) * Y + 1 / ε) with hE
  have hx0 : 0 ≤ 1 / ε := by positivity
  have hcY : 0 ≤ c * Y := by positivity
  have hexp_mono : ∀ t : ℝ, t ≤ 12 * (1 + c) * Y + 1 / ε → Real.exp t ≤ E := fun t ht =>
    Real.exp_le_exp.mpr ht
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  -- the four terms of `X0`
  have t1 : 20 / ηKL c ε ≤ 20 * E := by
    have : 20 / ηKL c ε = 20 * (1 / ηKL c ε) := by ring
    rw [this]
    have h1 := inv_η_le_Y hc hε hε1
    have h2 : Y ≤ E := (le_exp_self Y).trans (hexp_mono Y (by nlinarith))
    rw [← hY] at h1
    nlinarith
  have t2 : 2 / δKL c ε ≤ 2 * E := by
    rw [two_div_δ, ← hY]
    have h1 := thirteen_rpow_le hcY
    have h2 : Real.exp (12 * (c * Y)) ≤ E := hexp_mono _ (by nlinarith)
    nlinarith
  have t3 : 1 / ε ≤ E := (le_exp_self _).trans (hexp_mono _ (by nlinarith))
  have t4 : c * Y ≤ E := (le_exp_self _).trans (hexp_mono _ (by nlinarith))
  have hX0 : X0 c ε ≤ 20 * E + 2 * E + E + E := by
    unfold X0
    have h20 : 0 ≤ 20 / ηKL c ε := by positivity
    have h2 : 0 ≤ 2 / δKL c ε := by have := δKL_pos c ε; positivity
    rw [← hY]
    apply max_le <;> apply max_le <;> linarith
  have hX00 : 0 ≤ X0 c ε := by
    unfold X0
    exact le_trans (by positivity) ((le_max_left _ _).trans (le_max_left _ _))
  have hG : (Gp c ε : ℝ) < X0 c ε + 67 := by
    unfold Gp
    push_cast
    have := Nat.ceil_lt_add_one hX00
    linarith
  nlinarith

theorem final_bound (hc : 0 ≤ c) (hε : 0 < ε)
    (hεA : ε ≤ 1 / (10 + Real.log (10000 * (1 + c)))) :
    (91 * Real.exp (12 * (1 + c) * ηKL c ε ^ (-5 : ℝ) + 1 / ε)) ^ 88 ≤
      Real.exp (Real.exp (ε ^ (-(c + 2)))) := by
  set A : ℝ := 10000 * (1 + c) with hA
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith
  set Lg := Real.log A with hLg
  have hLg0 : 0 ≤ Lg := Real.log_nonneg hA1
  have hden : 0 < 10 + Lg := by linarith
  have hε1 : ε ≤ 1 := by
    have : 1 / (10 + Lg) ≤ 1 := by rw [div_le_one hden]; linarith
    linarith
  set x : ℝ := 1 / ε with hx
  have hxge : 10 + Lg ≤ x := by
    rw [hx]
    rw [le_div_iff₀ hε]
    rw [le_div_iff₀ hden] at hεA
    linarith
  have hx10 : 10 ≤ x := by linarith
  set a : ℝ := ε ^ (-c) with ha
  have ha1 : 1 ≤ a := a_ge_one hc hε hε1
  set Y := ηKL c ε ^ (-5 : ℝ) with hY
  have hY1 : 1 ≤ Y := one_le_Y hc hε hε1
  have hYe : Y ≤ Real.exp (20 * a) := Y_le_exp hc hε hε1
  -- the exponent `ε^(-(c+2)) = a x²`
  have hexp_eq : ε ^ (-(c + 2)) = a * x ^ 2 := by
    rw [ha, hx, show -(c + 2) = -c + (-2 : ℝ) by ring, Real.rpow_add hε, Real.rpow_neg hε.le c,
      Real.rpow_neg hε.le 2, Real.rpow_two]
    field_simp
  -- `(91 e^t)^88 = exp(88 log 91 + 88 t)`
  have hpow : (91 * Real.exp (12 * (1 + c) * Y + x)) ^ 88 =
      Real.exp (88 * Real.log 91 + 88 * (12 * (1 + c) * Y + x)) := by
    have h91 : Real.exp (88 * Real.log 91) = 91 ^ 88 := by
      rw [show (88 : ℝ) * Real.log 91 = Real.log (91 ^ 88) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    have h2 : Real.exp (88 * (12 * (1 + c) * Y + x)) = Real.exp (12 * (1 + c) * Y + x) ^ 88 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [show Real.exp (88 * Real.log 91 + 88 * (12 * (1 + c) * Y + x)) =
        Real.exp (88 * Real.log 91) * Real.exp (88 * (12 * (1 + c) * Y + x)) from Real.exp_add _ _,
      h91, h2, mul_pow]
  rw [hpow, hexp_eq]
  apply Real.exp_le_exp.mpr
  -- `S ≤ A e^(20a) x`
  have hlog91 : Real.log 91 ≤ 90 := by linarith [log_le_self_sub_one (show (0:ℝ) < 91 by norm_num)]
  have he20 : 1 ≤ Real.exp (20 * a) := Real.one_le_exp (by linarith)
  have hS : 88 * Real.log 91 + 88 * (12 * (1 + c) * Y + x) ≤ A * Real.exp (20 * a) * x := by
    have h1 : 88 * Real.log 91 ≤ 7920 * Real.exp (20 * a) * x := by
      have : (1 : ℝ) ≤ Real.exp (20 * a) * x := by nlinarith
      nlinarith
    have h2 : 88 * (12 * (1 + c) * Y) ≤ 1056 * (1 + c) * Real.exp (20 * a) * x := by
      have hc1 : 0 ≤ 1 + c := by linarith
      have : Y ≤ Real.exp (20 * a) * x := by nlinarith
      nlinarith
    have h3 : 88 * x ≤ 88 * Real.exp (20 * a) * x := by nlinarith
    rw [hA]
    nlinarith
  -- `A e^(20a) x ≤ e^(a x²)`
  have hlogx : Real.log x ≤ x := by linarith [log_le_self_sub_one (show (0:ℝ) < x by linarith)]
  have hkey : Lg + 20 * a + Real.log x ≤ a * x ^ 2 := by
    have h1 : x ^ 2 - 20 ≤ a * (x ^ 2 - 20) := by
      have : 0 ≤ x ^ 2 - 20 := by nlinarith
      nlinarith
    have h2 : Lg + x ≤ x ^ 2 - 20 := by nlinarith
    nlinarith
  have hAx : A * Real.exp (20 * a) * x = Real.exp (Lg + 20 * a + Real.log x) := by
    rw [Real.exp_add, Real.exp_add, hLg, Real.exp_log (by linarith), Real.exp_log (by linarith)]
  calc 88 * Real.log 91 + 88 * (12 * (1 + c) * Y + x) ≤ A * Real.exp (20 * a) * x := hS
    _ = Real.exp (Lg + 20 * a + Real.log x) := hAx
    _ ≤ Real.exp (a * x ^ 2) := Real.exp_le_exp.mpr hkey

end

/-- The FC right-hand side, conditional on the Kravitz–Leng interface `KL57`. -/
theorem doubleExponentialBound_of_KL57 (h : KL57) : DoubleExponentialBound := by
  obtain ⟨c, hc, hKL⟩ := h
  have hA1 : (1 : ℝ) < 10000 * (1 + c) := by nlinarith
  have hLg : 0 < Real.log (10000 * (1 + c)) := Real.log_pos hA1
  refine ⟨c + 2, 1 / (10 + Real.log (10000 * (1 + c))), by positivity, ?_⟩
  rintro ε ⟨hε0, hεle⟩
  have hε1 : ε < 1 / 10 := by
    have : 1 / (10 + Real.log (10000 * (1 + c))) < 1 / 10 := by
      apply one_div_lt_one_div_of_lt (by norm_num); linarith
    linarith
  have hG := Gp_le_exp (c := c) hc.le hε0 (by linarith)
  have hG0 : (0 : ℝ) ≤ Gp c ε := by positivity
  calc (minCopies ε : ℝ) ≤ (Gp c ε : ℝ) ^ 88 := minCopies_le_G_pow hKL hc.le hε0 hε1
    _ ≤ (91 * Real.exp (12 * (1 + c) * ηKL c ε ^ (-5 : ℝ) + 1 / ε)) ^ 88 := by gcongr
    _ ≤ Real.exp (Real.exp (ε ^ (-(c + 2)))) := final_bound hc.le hε0 hεle

end Green41

/- ## Section: `Residue` -/

/-
# Residues of Gaussian integers modulo `πⁿ`

For a Gaussian prime `π` of prime norm `p` with `π ∤ π̄`, we build a ring hom
`ψ hπ n : ℤ[i] →+* ZMod (p ^ n)` sending `i` to `Im(πⁿ) / Re(πⁿ)`. Its kernel is `πⁿ ℤ[i]`,
and it satisfies the stripe formula `Re(z · π̄ⁿ) ≡ Re(πⁿ) · ψ(z) (mod pⁿ)`
(blueprint §1, (R1)–(R4)).
-/

namespace Green41

open Complex ComplexConjugate

lemma gauss_add_star (z : GaussianInt) : z + star z = (((2 * z.re : ℤ)) : GaussianInt) := by
  ext <;> simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_star, Zsqrtd.im_star,
    Zsqrtd.re_intCast, Zsqrtd.im_intCast] <;> ring

lemma gauss_mul_star_re (z w : GaussianInt) : (z * star w).re = z.re * w.re + z.im * w.im := by
  simp only [Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star]; ring

lemma gauss_mul_star_im (z w : GaussianInt) : (z * star w).im = z.im * w.re - z.re * w.im := by
  simp only [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]; ring

/-- Hypotheses on a digit prime `π`: its norm is the prime `p`, and `π ∤ π̄`. -/
structure DigitPrime (π : GaussianInt) (p : ℕ) : Prop where
  prime : p.Prime
  norm : π.norm = p
  not_dvd_star : ¬ π ∣ star π

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

lemma prime_π : Prime π :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_norm_prime (by rw [hπ.norm]; simpa using hπ.prime))

lemma norm_pow (n : ℕ) : (π ^ n).norm = (p : ℤ) ^ n := by
  rw [← hπ.norm]; exact map_pow Zsqrtd.normMonoidHom π n

lemma natCast_pow_eq (n : ℕ) : ((p ^ n : ℕ) : GaussianInt) = π ^ n * star (π ^ n) := by
  rw [← Zsqrtd.norm_eq_mul_conj, hπ.norm_pow]; push_cast; rfl


lemma not_dvd_re_pow (n : ℕ) : ¬ (p : ℤ) ∣ (π ^ n).re := by
  intro h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero, Zsqrtd.re_one] at h
    exact hπ.prime.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)
  have hπp : π ∣ ((p : ℤ) : GaussianInt) := by
    refine ⟨star π, ?_⟩
    have := hπ.natCast_pow_eq 1
    simp only [pow_one] at this
    rw [← this]; push_cast; rfl
  have h2 : π ∣ (((2 * (π ^ n).re : ℤ)) : GaussianInt) := by
    obtain ⟨k, hk⟩ := h
    refine dvd_trans hπp ⟨2 * k, ?_⟩
    rw [hk]; push_cast; ring
  rw [← gauss_add_star] at h2
  have h3 : π ∣ star (π ^ n) := (dvd_add_right (dvd_pow_self π hn.ne')).mp h2
  rw [star_pow] at h3
  exact hπ.not_dvd_star (hπ.prime_π.dvd_of_dvd_pow h3)

end DigitPrime

/-- An integer prime to `p` is a unit modulo `p ^ n`. -/
lemma isUnit_intCast_of_not_dvd {p : ℕ} (hp : p.Prime) {a : ℤ} (h : ¬ (p : ℤ) ∣ a) (n : ℕ) :
    IsUnit ((a : ℤ) : ZMod (p ^ n)) := by
  have hc : IsCoprime ((p : ℤ) ^ n) a :=
    ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr h).pow_left
  obtain ⟨u, v, huv⟩ := hc
  refine IsUnit.of_mul_eq_one (v : ZMod (p ^ n)) ?_
  have h1 := congrArg (fun x : ℤ => (x : ZMod (p ^ n))) huv
  have hp0 : ((p : ZMod (p ^ n))) ^ n = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one, hp0,
    mul_zero, zero_add] at h1
  simpa [mul_comm] using h1

section Psi

variable {π : GaussianInt} {p : ℕ}

/-- `ψₙ(i) = Im(πⁿ) / Re(πⁿ)` in `ZMod (p ^ n)`. -/
def rootψ (π : GaussianInt) (p n : ℕ) : ZMod (p ^ n) :=
  ((π ^ n).im : ZMod (p ^ n)) * ((π ^ n).re : ZMod (p ^ n))⁻¹

namespace DigitPrime

variable (hπ : DigitPrime π p)
include hπ

lemma isUnit_re (n : ℕ) : IsUnit (((π ^ n).re : ℤ) : ZMod (p ^ n)) :=
  isUnit_intCast_of_not_dvd hπ.prime (hπ.not_dvd_re_pow n) n

lemma re_mul_inv (n : ℕ) :
    (((π ^ n).re : ℤ) : ZMod (p ^ n)) * (((π ^ n).re : ℤ) : ZMod (p ^ n))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ (hπ.isUnit_re n)

lemma re_sq_add_im_sq (n : ℕ) :
    (((π ^ n).re : ℤ) : ZMod (p ^ n)) * ((π ^ n).re : ℤ) +
      (((π ^ n).im : ℤ) : ZMod (p ^ n)) * ((π ^ n).im : ℤ) = 0 := by
  have h := hπ.norm_pow n
  rw [Zsqrtd.norm_def] at h
  have h2 : ((π ^ n).re * (π ^ n).re + (π ^ n).im * (π ^ n).im : ℤ) = (p : ℤ) ^ n := by
    linarith
  have h3 := congrArg (fun x : ℤ => (x : ZMod (p ^ n))) h2
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast] at h3
  rw [h3, ← Nat.cast_pow, ZMod.natCast_self]

lemma rootψ_mul_self (n : ℕ) : rootψ π p n * rootψ π p n = -1 := by
  unfold rootψ
  set R : ZMod (p ^ n) := (((π ^ n).re : ℤ) : ZMod (p ^ n))
  set I : ZMod (p ^ n) := (((π ^ n).im : ℤ) : ZMod (p ^ n))
  have h1 : R * R⁻¹ = 1 := hπ.re_mul_inv n
  have h2 : R * R + I * I = 0 := hπ.re_sq_add_im_sq n
  have h3 : I * I = -(R * R) := by linear_combination h2
  calc I * R⁻¹ * (I * R⁻¹) = (I * I) * (R⁻¹ * R⁻¹) := by ring
    _ = -((R * R⁻¹) * (R * R⁻¹)) := by rw [h3]; ring
    _ = -1 := by rw [h1]; ring

/-- The residue map `ψₙ : ℤ[i] →+* ZMod (pⁿ)`, `x + yi ↦ x + y · Im(πⁿ)/Re(πⁿ)`. -/
def ψ (n : ℕ) : GaussianInt →+* ZMod (p ^ n) :=
  Zsqrtd.lift ⟨rootψ π p n, by rw [hπ.rootψ_mul_self]; simp⟩

lemma ψ_apply (n : ℕ) (z : GaussianInt) :
    hπ.ψ n z = (z.re : ZMod (p ^ n)) + (z.im : ZMod (p ^ n)) * rootψ π p n := rfl

lemma ψ_pow_self (n : ℕ) : hπ.ψ n (π ^ n) = 0 := by
  rw [ψ_apply]
  unfold rootψ
  set R : ZMod (p ^ n) := (((π ^ n).re : ℤ) : ZMod (p ^ n))
  set I : ZMod (p ^ n) := (((π ^ n).im : ℤ) : ZMod (p ^ n))
  have h1 : R * R⁻¹ = 1 := hπ.re_mul_inv n
  have h2 : R * R + I * I = 0 := hπ.re_sq_add_im_sq n
  calc R + I * (I * R⁻¹) = (R * R + I * I) * R⁻¹ + R * (1 - R * R⁻¹) := by ring
    _ = 0 := by rw [h1, h2]; ring

/-- (R1) The kernel of `ψₙ` is `πⁿ ℤ[i]`. -/
lemma ψ_eq_zero_iff (n : ℕ) (z : GaussianInt) : hπ.ψ n z = 0 ↔ π ^ n ∣ z := by
  constructor
  · intro hz
    rw [ψ_apply] at hz
    unfold rootψ at hz
    set R : ZMod (p ^ n) := (((π ^ n).re : ℤ) : ZMod (p ^ n)) with hR
    set I : ZMod (p ^ n) := (((π ^ n).im : ℤ) : ZMod (p ^ n)) with hI
    have h1 : R * R⁻¹ = 1 := hπ.re_mul_inv n
    have h2 : R * R + I * I = 0 := hπ.re_sq_add_im_sq n
    have ha : ((z.re * (π ^ n).re + z.im * (π ^ n).im : ℤ) : ZMod (p ^ n)) = 0 := by
      push_cast
      rw [← hR, ← hI]
      calc (z.re : ZMod (p ^ n)) * R + z.im * I
          = R * (z.re + z.im * (I * R⁻¹)) + z.im * I * (1 - R * R⁻¹) := by ring
        _ = 0 := by rw [hz, h1]; ring
    have hb : ((z.im * (π ^ n).re - z.re * (π ^ n).im : ℤ) : ZMod (p ^ n)) = 0 := by
      push_cast
      rw [← hR, ← hI]
      have hre : (z.re : ZMod (p ^ n)) = -(z.im * (I * R⁻¹)) := by linear_combination hz
      calc (z.im : ZMod (p ^ n)) * R - z.re * I
          = z.im * R - (-(z.im * (I * R⁻¹))) * I := by rw [hre]
        _ = z.im * R⁻¹ * (R * R + I * I) + z.im * R * (1 - R * R⁻¹) := by ring
        _ = 0 := by rw [h1, h2]; ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hb
    have hdiv : (((p ^ n : ℕ) : ℤ) : GaussianInt) ∣ z * star (π ^ n) := by
      rw [Zsqrtd.intCast_dvd]
      constructor
      · rw [gauss_mul_star_re]; simpa using ha
      · rw [gauss_mul_star_im]; simpa using hb
    have hcast : (((p ^ n : ℕ) : ℤ) : GaussianInt) = π ^ n * star (π ^ n) := by
      rw [Int.cast_natCast]; exact hπ.natCast_pow_eq n
    rw [hcast] at hdiv
    have hne : star (π ^ n) ≠ 0 := by
      rw [star_pow]
      exact pow_ne_zero _ (fun h0 => hπ.prime_π.ne_zero (by
        simpa using congrArg star h0))
    exact (mul_dvd_mul_iff_right hne).mp hdiv
  · rintro ⟨y, rfl⟩
    rw [map_mul, hπ.ψ_pow_self, zero_mul]

/-- (R2) The stripe formula: `Re(z · π̄ⁿ) ≡ Re(πⁿ) · ψₙ(z) (mod pⁿ)`. -/
lemma stripe_formula (n : ℕ) (z : GaussianInt) :
    (((z * star (π ^ n)).re : ℤ) : ZMod (p ^ n)) = ((π ^ n).re : ℤ) * hπ.ψ n z := by
  rw [gauss_mul_star_re, ψ_apply]
  unfold rootψ
  have h1 := hπ.re_mul_inv n
  push_cast
  linear_combination (-(z.im : ZMod (p ^ n)) * ((π ^ n).im : ZMod (p ^ n))) * h1

/-- (R3) `ψ(π) ψ(π̄) = p`. -/
lemma ψ_mul_star (n : ℕ) : hπ.ψ n π * hπ.ψ n (star π) = p := by
  rw [← map_mul]
  have := hπ.natCast_pow_eq 1
  simp only [pow_one] at this
  rw [← this, map_natCast]

/-- `ψₙ(z)` is a unit iff `π ∤ z` (for `n ≥ 1`). -/
lemma isUnit_ψ_iff {n : ℕ} (hn : 0 < n) (z : GaussianInt) : IsUnit (hπ.ψ n z) ↔ ¬ π ∣ z := by
  have hp := hπ.prime
  have : Fact (1 < p ^ n) := ⟨Nat.one_lt_pow hn.ne' hp.one_lt⟩
  constructor
  · rintro hu ⟨y, rfl⟩
    rw [map_mul] at hu
    have hπu : IsUnit (hπ.ψ n π) := isUnit_of_mul_isUnit_left hu
    have h0 : hπ.ψ n π ^ n = 0 := by rw [← map_pow, hπ.ψ_pow_self]
    have := (hπu.pow n)
    rw [h0] at this
    exact not_isUnit_zero this
  · intro hz
    by_contra hu
    set x := hπ.ψ n z with hx
    have hxv : ((x.val : ℕ) : ZMod (p ^ n)) = x := ZMod.natCast_zmod_val x
    have hnd : p ∣ x.val := by
      by_contra hnd
      exact hu (hxv ▸ (ZMod.isUnit_natCast_iff_not_dvd_pow hp hn).mpr hnd)
    obtain ⟨k, hk⟩ := hnd
    have hxn : x ^ n = 0 := by
      rw [← hxv, hk, Nat.cast_mul, mul_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
    have : π ^ n ∣ z ^ n := by
      rw [← hπ.ψ_eq_zero_iff, map_pow, ← hx, hxn]
    exact hz (hπ.prime_π.dvd_of_dvd_pow (dvd_trans (dvd_pow_self π hn.ne') this))

/-- (R4) The conjugate residue map `ψ̄ₙ = ψₙ ∘ conj`, with kernel `π̄ⁿ ℤ[i]`. -/
def ψbar (n : ℕ) : GaussianInt →+* ZMod (p ^ n) := (hπ.ψ n).comp (starRingEnd GaussianInt)

lemma ψbar_apply (n : ℕ) (z : GaussianInt) : hπ.ψbar n z = hπ.ψ n (star z) := rfl

lemma ψbar_eq_zero_iff (n : ℕ) (z : GaussianInt) : hπ.ψbar n z = 0 ↔ star π ^ n ∣ z := by
  rw [ψbar_apply, ψ_eq_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨star y, ?_⟩
    have := congrArg star hy
    rwa [star_star, star_mul, star_pow, mul_comm] at this
  · rintro ⟨y, rfl⟩
    exact ⟨star y, by rw [star_mul, star_pow, star_star, mul_comm]⟩

lemma isUnit_ψbar_iff {n : ℕ} (hn : 0 < n) (z : GaussianInt) :
    IsUnit (hπ.ψbar n z) ↔ ¬ star π ∣ z := by
  rw [ψbar_apply, hπ.isUnit_ψ_iff hn]
  constructor
  · rintro h ⟨y, rfl⟩
    exact h ⟨star y, by rw [star_mul, star_star, mul_comm]⟩
  · rintro h ⟨y, hy⟩
    exact h ⟨star y, by rw [← star_star z, hy, star_mul, mul_comm]⟩

end DigitPrime

end Psi

end Green41

/- ## Section: `Orders` -/

/-
# Orders of the multipliers (Kravitz–Leng Lemma 3.2 with `α = 1`)

If `B` has order `p - 1` modulo `p` and `B^(p-1) ≢ 1 (mod p²)`, then `B` has order
`(p - 1) p^(k-1)` modulo `p^k` for every `k ≥ 1` (lifting the exponent), so its powers run
through all units of `ZMod (p^k)` (blueprint §2).
-/

namespace Green41

lemma natCast_pow_eq_one_iff {B : ℕ} (hB : 0 < B) (M m : ℕ) :
    (B : ZMod M) ^ m = 1 ↔ M ∣ B ^ m - 1 := by
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm,
    Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hB)]

section LTE

variable {p : ℕ}

/-- LTE: `p^k ∣ B^m - 1 ↔ (p - 1) p^(k-1) ∣ m`. -/
lemma pow_sub_one_dvd_iff (hpr : p.Prime) (hodd : Odd p) {B : ℕ} (hB : 2 ≤ B)
    (h1 : orderOf (B : ZMod p) = p - 1) (h2 : (B : ZMod (p ^ 2)) ^ (p - 1) ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    p ^ k ∣ B ^ m - 1 ↔ (p - 1) * p ^ (k - 1) ∣ m := by
  have hp : Fact p.Prime := ⟨hpr⟩
  have hp2 : 2 ≤ p := hpr.two_le
  have hB0 : 0 < B := by omega
  set x := B ^ (p - 1) with hxdef
  have hx1 : 1 < x := Nat.one_lt_pow (by omega) (by omega)
  have hpx : p ∣ x - 1 := by
    have h := pow_orderOf_eq_one (B : ZMod p)
    rw [h1] at h
    exact (natCast_pow_eq_one_iff hB0 p (p - 1)).mp h
  have hnx : ¬ p ∣ x := by
    intro h
    have h3 : p ∣ x - (x - 1) := Nat.dvd_sub h hpx
    rw [Nat.sub_sub_self hx1.le] at h3
    exact hpr.one_lt.ne' (Nat.dvd_one.mp h3)
  have hv1 : padicValNat p (x - 1) = 1 := by
    have hne : x - 1 ≠ 0 := by omega
    have hge : 1 ≤ padicValNat p (x - 1) := (padicValNat_dvd_iff_le hne).mp (by simpa using hpx)
    have hlt : ¬ 2 ≤ padicValNat p (x - 1) := by
      intro h
      apply h2
      rw [natCast_pow_eq_one_iff hB0]
      exact (padicValNat_dvd_iff_le hne).mpr h
    omega
  have hlte : ∀ m' : ℕ, m' ≠ 0 → padicValNat p (x ^ m' - 1) = 1 + padicValNat p m' := by
    intro m' hm'
    have := padicValNat.pow_sub_pow hodd hx1 hpx hnx hm'
    rw [one_pow] at this
    rw [this, hv1]
  have hxm : ∀ m' : ℕ, m' ≠ 0 → x ^ m' - 1 ≠ 0 := by
    intro m' hm'
    have : 1 < x ^ m' := Nat.one_lt_pow hm' hx1
    omega
  constructor
  · intro hdvd
    have hpm : p ∣ B ^ m - 1 := dvd_trans (dvd_pow_self p (by omega)) hdvd
    have hord : p - 1 ∣ m := by
      rw [← h1]
      apply orderOf_dvd_of_pow_eq_one
      exact (natCast_pow_eq_one_iff hB0 p m).mpr hpm
    obtain ⟨m', rfl⟩ := hord
    rcases Nat.eq_zero_or_pos m' with rfl | hm'
    · simp
    rw [pow_mul] at hdvd
    have hle : k ≤ padicValNat p (x ^ m' - 1) := (padicValNat_dvd_iff_le (hxm m' hm'.ne')).mp hdvd
    rw [hlte m' hm'.ne'] at hle
    have : p ^ (k - 1) ∣ m' := (padicValNat_dvd_iff_le hm'.ne').mpr (by omega)
    exact mul_dvd_mul_left _ this
  · rintro ⟨c, rfl⟩
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp
    have hm' : p ^ (k - 1) * c ≠ 0 := by positivity
    rw [mul_assoc, pow_mul]
    apply (padicValNat_dvd_iff_le (hxm _ hm')).mpr
    rw [hlte _ hm', padicValNat.mul (by positivity) hc.ne', padicValNat.prime_pow]
    omega

/-- The order of `B` modulo `p^k` is `(p - 1) p^(k-1)`. -/
lemma orderOf_natCast_prime_pow (hpr : p.Prime) (hodd : Odd p) {B : ℕ} (hB : 2 ≤ B)
    (h1 : orderOf (B : ZMod p) = p - 1) (h2 : (B : ZMod (p ^ 2)) ^ (p - 1) ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) :
    orderOf (B : ZMod (p ^ k)) = (p - 1) * p ^ (k - 1) := by
  have hB0 : 0 < B := by omega
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [natCast_pow_eq_one_iff hB0, pow_sub_one_dvd_iff hpr hodd hB h1 h2 hk]
  · rw [← pow_sub_one_dvd_iff hpr hodd hB h1 h2 hk, ← natCast_pow_eq_one_iff hB0]
    exact pow_orderOf_eq_one _

end LTE

/-- If `orderOf x` equals the number of units, every unit is a power `x^t` with
`t < orderOf x`. -/
lemma exists_pow_eq_of_orderOf_eq_card {n : ℕ} [NeZero n] (x : ZMod n)
    (hx : orderOf x = Nat.card (ZMod n)ˣ) (u : ZMod n) (hu : IsUnit u) :
    ∃ t < orderOf x, x ^ t = u := by
  have hpos : 0 < orderOf x := by rw [hx, Nat.card_eq_fintype_card]; exact Fintype.card_pos
  have hxu : IsUnit x := IsUnit.of_pow_eq_one (pow_orderOf_eq_one x) hpos.ne'
  set X := hxu.unit with hX
  have hord : orderOf X = orderOf x := by rw [← orderOf_units, IsUnit.unit_spec]
  have himg : (Finset.range (orderOf X)).image (fun t => X ^ t) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn, Finset.card_range, hord, hx, Nat.card_eq_fintype_card]
    intro a ha b hb hab
    exact pow_injOn_Iio_orderOf (by simpa using ha) (by simpa using hb) hab
  have hmem : hu.unit ∈ (Finset.range (orderOf X)).image (fun t => X ^ t) := by
    rw [himg]; exact Finset.mem_univ _
  obtain ⟨t, ht, hteq⟩ := Finset.mem_image.mp hmem
  refine ⟨t, by rw [← hord]; simpa using ht, ?_⟩
  have := congrArg (fun y : (ZMod n)ˣ => (y : ZMod n)) hteq
  simpa [hX] using this

/-- Units of `ZMod (p^k)`: there are `(p - 1) p^(k-1)` of them. -/
lemma card_units_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    Nat.card (ZMod (p ^ k))ˣ = (p - 1) * p ^ (k - 1) := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp (by omega),
    mul_comm]

/-- In `ZMod (p^2)`, a nilpotent element squares to zero. -/
lemma sq_eq_zero_of_pow_eq_zero {p : ℕ} (hp : p.Prime) {y : ZMod (p ^ 2)} {n : ℕ}
    (hy : y ^ n = 0) : y * y = 0 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hv : ((y.val : ℕ) : ZMod (p ^ 2)) = y := ZMod.natCast_zmod_val y
  have hdvd : p ∣ y.val := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      rw [pow_zero] at hy
      have h1 : (1 : ZMod (p ^ 2)) ≠ 0 := by
        have : Fact (1 < p ^ 2) := ⟨Nat.one_lt_pow (by norm_num) hp.one_lt⟩
        exact one_ne_zero
      exact h1 hy
    · rw [← hv, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff] at hy
      exact hp.dvd_of_dvd_pow (dvd_trans (dvd_pow_self p (by norm_num)) hy)
  obtain ⟨c, hc⟩ := hdvd
  rw [← hv, hc, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  exact ⟨c * c, by ring⟩

section Multiplier

variable {π : GaussianInt} {p : ℕ}

namespace DigitPrime

variable (hπ : DigitPrime π p)
include hπ

/-- The multiplier `ψₙ(ρ) / ψₙ(ρ̄)` of `ρ/ρ̄` on `ℤ[i]/πⁿ`. -/
def mult (ρ : GaussianInt) (n : ℕ) : ZMod (p ^ n) := hπ.ψ n ρ * (hπ.ψ n (star ρ))⁻¹

lemma mult_mul {ρ : GaussianInt} {n : ℕ} (hn : 0 < n) (hρ : ¬ π ∣ star ρ) :
    hπ.mult ρ n * hπ.ψ n (star ρ) = hπ.ψ n ρ := by
  unfold mult
  rw [mul_assoc, mul_comm _ (hπ.ψ n (star ρ)),
    ZMod.mul_inv_of_unit _ ((hπ.isUnit_ψ_iff hn _).mpr hρ), mul_one]

lemma isUnit_mult {ρ : GaussianInt} {n : ℕ} (hn : 0 < n) (hρ : ¬ π ∣ ρ) (hρ' : ¬ π ∣ star ρ) :
    IsUnit (hπ.mult ρ n) := by
  have h := hπ.mult_mul hn hρ'
  have hu : IsUnit (hπ.ψ n ρ) := (hπ.isUnit_ψ_iff hn _).mpr hρ
  rw [← h] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- The composite `ℤ[i] → ZMod (pⁿ) → ZMod (p²)` is determined by the image `x` of `i`. -/
lemma cast_ψ {n : ℕ} (hn : 2 ≤ n) (z : GaussianInt) :
    ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 2)) (hπ.ψ n z) =
      (z.re : ZMod (p ^ 2)) + z.im * ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 2))
        (rootψ π p n) := by
  rw [ψ_apply, map_add, map_mul, map_intCast, map_intCast]

lemma cast_root_mul_self {n : ℕ} (hn : 2 ≤ n) :
    ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 2)) (rootψ π p n) *
      ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 2)) (rootψ π p n) = -1 := by
  rw [← map_mul, hπ.rootψ_mul_self, map_neg, map_one]

lemma cast_ψ_π_sq {n : ℕ} (hn : 2 ≤ n) :
    ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 2)) (hπ.ψ n π) *
      ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 2)) (hπ.ψ n π) = 0 := by
  apply sq_eq_zero_of_pow_eq_zero hπ.prime (n := n)
  rw [← map_pow, ← map_pow, hπ.ψ_pow_self, map_zero]

end DigitPrime

end Multiplier

end Green41

/- ## Section: `Instances` -/

/-
# The two digit primes and their multipliers

Case 1 of the blueprint uses the digit prime `P = 1 + 2i` (norm 5) with multiplier `θ₁₃`;
case 2 uses `Q = 2 + 3i` (norm 13) with multiplier `θ₅`. The residues of the multipliers
modulo `p²` are forced by `rₙ² = -1` and `ψₙ(π)` nilpotent, and determine their orders.

| multiplier | mod `p²` | order mod `pᵏ` |
|---|---|---|
| `θ₁₃` on `ℤ[i]/Pⁿ` | 8 | `4·5^(k-1)` |
| `θ₁₃⁻¹` on `ℤ[i]/Pⁿ` | 22 | `4·5^(k-1)` |
| `θ₅` on `ℤ[i]/Qⁿ` | 11 | `12·13^(k-1)` |
| `θ₅⁻¹` on `ℤ[i]/Qⁿ` | 123 | `12·13^(k-1)` |
-/

namespace Green41

lemma star_gP : star gP = gPb := rfl
lemma star_gQ : star gQ = gQb := rfl
lemma star_gPb : star gPb = gP := rfl
lemma star_gQb : star gQb = gQ := rfl

lemma prime_gPb : Prime gPb :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_norm_prime (by rw [norm_gPb]; norm_num))

lemma prime_gQb : Prime gQb :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_norm_prime (by rw [norm_gQb]; norm_num))

lemma gQ_not_dvd_gQb' : ¬ gQ ∣ gQb := gQ_not_dvd_gQb

/-- `P = 1 + 2i` is a digit prime of norm 5. -/
lemma digitPrime_P : DigitPrime gP 5 where
  prime := by norm_num
  norm := by rw [norm_gP]; rfl
  not_dvd_star := by rw [star_gP]; exact gP_not_dvd_gPb

/-- `Q = 2 + 3i` is a digit prime of norm 13. -/
lemma digitPrime_Q : DigitPrime gQ 13 where
  prime := by norm_num
  norm := by rw [norm_gQ]; rfl
  not_dvd_star := by rw [star_gQ]; exact gQ_not_dvd_gQb

/-- The residue of a `ZMod (pⁿ)` element modulo `p²`, through its value. -/
lemma val_cast_eq_castHom {p n : ℕ} [NeZero (p ^ n)] (hn : 2 ≤ n) (a : ZMod (p ^ n)) :
    ((a.val : ℕ) : ZMod (p ^ 2)) = ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 2)) a := by
  rw [ZMod.natCast_val, ZMod.castHom_apply]

section NumericFacts

lemma zmod25_fact (x b : ZMod 25) (hx : x * x = -1) (hπ : (1 + 2 * x) * (1 + 2 * x) = 0)
    (hb : b * (2 + (-3) * x) = 2 + 3 * x) : b = 8 := by
  revert x b; decide

lemma zmod25_fact' (x b : ZMod 25) (hx : x * x = -1) (hπ : (1 + 2 * x) * (1 + 2 * x) = 0)
    (hb : b * (2 + 3 * x) = 2 + (-3) * x) : b = 22 := by
  revert x b; decide

set_option maxRecDepth 100000 in
lemma zmod169_root (x : ZMod 169) (hx : x * x = -1) (hπ : (2 + 3 * x) * (2 + 3 * x) = 0) :
    x = 99 := by
  revert x; decide

set_option maxRecDepth 100000 in
lemma zmod169_fact (b : ZMod 169) (hb : b * (1 + (-2) * 99) = 1 + 2 * 99) : b = 11 := by
  revert b; decide

set_option maxRecDepth 100000 in
lemma zmod169_fact' (b : ZMod 169) (hb : b * (1 + 2 * 99) = 1 + (-2) * 99) : b = 123 := by
  revert b; decide

end NumericFacts

/-- `θ₁₃ ≡ 8 (mod 25)` on `ℤ[i]/Pⁿ`. -/
lemma mult_P_Q_mod25 {n : ℕ} (hn : 2 ≤ n) :
    (((digitPrime_P.mult gQ n).val : ℕ) : ZMod (5 ^ 2)) = 8 := by
  have : NeZero (5 ^ n) := ⟨by positivity⟩
  have h := congrArg (ZMod.castHom (pow_dvd_pow 5 hn) (ZMod (5 ^ 2)))
    (digitPrime_P.mult_mul (by omega) (ρ := gQ) (by rw [star_gQ]; exact gP_not_dvd_gQb))
  rw [map_mul, digitPrime_P.cast_ψ hn, digitPrime_P.cast_ψ hn] at h
  have hx := digitPrime_P.cast_root_mul_self hn
  have hπ := digitPrime_P.cast_ψ_π_sq hn
  rw [digitPrime_P.cast_ψ hn] at hπ
  rw [val_cast_eq_castHom hn]
  exact zmod25_fact _ _ hx (by simpa [gP] using hπ) (by simpa [gQ, star_gQ, gQb] using h)

/-- `θ₁₃⁻¹ ≡ 22 (mod 25)` on `ℤ[i]/Pⁿ`. -/
lemma mult_P_Qb_mod25 {n : ℕ} (hn : 2 ≤ n) :
    (((digitPrime_P.mult (star gQ) n).val : ℕ) : ZMod (5 ^ 2)) = 22 := by
  have : NeZero (5 ^ n) := ⟨by positivity⟩
  have h := congrArg (ZMod.castHom (pow_dvd_pow 5 hn) (ZMod (5 ^ 2)))
    (digitPrime_P.mult_mul (by omega) (ρ := star gQ) (by rw [star_star]; exact gP_not_dvd_gQ))
  rw [map_mul, digitPrime_P.cast_ψ hn, digitPrime_P.cast_ψ hn] at h
  have hx := digitPrime_P.cast_root_mul_self hn
  have hπ := digitPrime_P.cast_ψ_π_sq hn
  rw [digitPrime_P.cast_ψ hn] at hπ
  rw [val_cast_eq_castHom hn]
  exact zmod25_fact' _ _ hx (by simpa [gP] using hπ) (by simpa [gQ, star_gQ, gQb] using h)

/-- `θ₅ ≡ 11 (mod 169)` on `ℤ[i]/Qⁿ`. -/
lemma mult_Q_P_mod169 {n : ℕ} (hn : 2 ≤ n) :
    (((digitPrime_Q.mult gP n).val : ℕ) : ZMod (13 ^ 2)) = 11 := by
  have : NeZero (13 ^ n) := ⟨by positivity⟩
  have h := congrArg (ZMod.castHom (pow_dvd_pow 13 hn) (ZMod (13 ^ 2)))
    (digitPrime_Q.mult_mul (by omega) (ρ := gP) (by rw [star_gP]; exact gQ_not_dvd_gPb))
  rw [map_mul, digitPrime_Q.cast_ψ hn, digitPrime_Q.cast_ψ hn] at h
  have hx := digitPrime_Q.cast_root_mul_self hn
  have hπ := digitPrime_Q.cast_ψ_π_sq hn
  rw [digitPrime_Q.cast_ψ hn] at hπ
  have hr := zmod169_root _ hx (by simpa [gQ] using hπ)
  rw [hr] at h
  rw [val_cast_eq_castHom hn]
  exact zmod169_fact _ (by simpa [gP, star_gP, gPb] using h)

/-- `θ₅⁻¹ ≡ 123 (mod 169)` on `ℤ[i]/Qⁿ`. -/
lemma mult_Q_Pb_mod169 {n : ℕ} (hn : 2 ≤ n) :
    (((digitPrime_Q.mult (star gP) n).val : ℕ) : ZMod (13 ^ 2)) = 123 := by
  have : NeZero (13 ^ n) := ⟨by positivity⟩
  have h := congrArg (ZMod.castHom (pow_dvd_pow 13 hn) (ZMod (13 ^ 2)))
    (digitPrime_Q.mult_mul (by omega) (ρ := star gP) (by rw [star_star]; exact gQ_not_dvd_gP))
  rw [map_mul, digitPrime_Q.cast_ψ hn, digitPrime_Q.cast_ψ hn] at h
  have hx := digitPrime_Q.cast_root_mul_self hn
  have hπ := digitPrime_Q.cast_ψ_π_sq hn
  rw [digitPrime_Q.cast_ψ hn] at hπ
  have hr := zmod169_root _ hx (by simpa [gQ] using hπ)
  rw [hr] at h
  rw [val_cast_eq_castHom hn]
  exact zmod169_fact' _ (by simpa [gP, star_gP, gPb] using h)

/-- From the residue modulo `p²` to the order modulo `pᵏ`. -/
lemma orderOf_of_mod_sq {p : ℕ} (hpr : p.Prime) (hodd : Odd p) {B r : ℕ}
    (hBr : (B : ZMod (p ^ 2)) = (r : ZMod (p ^ 2))) (hr : 2 ≤ r) (hrp : r < p ^ 2)
    (h1 : orderOf ((r % p : ℕ) : ZMod p) = p - 1) (h2 : (r : ZMod (p ^ 2)) ^ (p - 1) ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) :
    orderOf (B : ZMod (p ^ k)) = (p - 1) * p ^ (k - 1) := by
  have hmod : B % p ^ 2 = r := by
    rw [ZMod.natCast_eq_natCast_iff'] at hBr
    rw [hBr, Nat.mod_eq_of_lt hrp]
  have hB : 2 ≤ B := by
    have := Nat.mod_le B (p ^ 2); omega
  apply orderOf_natCast_prime_pow hpr hodd hB _ (by rwa [hBr]) hk
  have : (B : ZMod p) = ((r % p : ℕ) : ZMod p) := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod]
    rw [← hmod, Nat.mod_mod_of_dvd _ (dvd_pow_self p (by norm_num))]
  rw [this, h1]

lemma orderOf_three_zmod5 : orderOf ((8 % 5 : ℕ) : ZMod 5) = 5 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

lemma orderOf_two_zmod5 : orderOf ((22 % 5 : ℕ) : ZMod 5) = 5 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

lemma orderOf_eleven_zmod13 : orderOf ((11 % 13 : ℕ) : ZMod 13) = 13 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

lemma orderOf_six_zmod13 : orderOf ((123 % 13 : ℕ) : ZMod 13) = 13 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

/-- The order of `θ₁₃` on `ℤ[i]/Pⁿ`, read modulo `5ᵏ`. -/
lemma orderOf_mult_P_Q {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    orderOf (((digitPrime_P.mult gQ n).val : ℕ) : ZMod (5 ^ k)) = 4 * 5 ^ (k - 1) :=
  orderOf_of_mod_sq (r := 8) (by norm_num) (by decide) (by rw [mult_P_Q_mod25 hn]; rfl)
    (by norm_num) (by norm_num) orderOf_three_zmod5 (by decide) hk

/-- The order of `θ₁₃⁻¹` on `ℤ[i]/Pⁿ`, read modulo `5ᵏ`. -/
lemma orderOf_mult_P_Qb {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    orderOf (((digitPrime_P.mult (star gQ) n).val : ℕ) : ZMod (5 ^ k)) = 4 * 5 ^ (k - 1) :=
  orderOf_of_mod_sq (r := 22) (by norm_num) (by decide) (by rw [mult_P_Qb_mod25 hn]; rfl)
    (by norm_num) (by norm_num) orderOf_two_zmod5 (by decide) hk

/-- The order of `θ₅` on `ℤ[i]/Qⁿ`, read modulo `13ᵏ`. -/
lemma orderOf_mult_Q_P {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    orderOf (((digitPrime_Q.mult gP n).val : ℕ) : ZMod (13 ^ k)) = 12 * 13 ^ (k - 1) :=
  orderOf_of_mod_sq (r := 11) (by norm_num) (by decide) (by rw [mult_Q_P_mod169 hn]; rfl)
    (by norm_num) (by norm_num) orderOf_eleven_zmod13 (by decide) hk

/-- The order of `θ₅⁻¹` on `ℤ[i]/Qⁿ`, read modulo `13ᵏ`. -/
lemma orderOf_mult_Q_Pb {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    orderOf (((digitPrime_Q.mult (star gP) n).val : ℕ) : ZMod (13 ^ k)) = 12 * 13 ^ (k - 1) :=
  orderOf_of_mod_sq (r := 123) (by norm_num) (by decide) (by rw [mult_Q_Pb_mod169 hn]; rfl)
    (by norm_num) (by norm_num) orderOf_six_zmod13 (by decide) hk

end Green41

/- ## Section: `Labels` -/

/-
# Cells, labels and the stripe value of a label (blueprint §3, §5)

For the cell generator `g = π̄^α ρ̄^β / πⁿ`, the label of `x ∈ ℂ` is `ψₙ(⌊x/g⌋)`.
* (L1) `x` lies within `√2 |g|` of `g ⌊x/g⌋`.
* (L3) `⌊(x - x')/g⌋ = ⌊x/g⌋ - ⌊x'/g⌋ - d` with `d ∈ {0, 1, i, 1+i}`.
  Hence, if the labels of differences of a finite set `Z` cover `ZMod (pⁿ)`, then
  `pⁿ ≤ 4 |labels(Z)|²`.
* (L4) The stripe value `Re(σʲ τʷ g m)` is `val(Xⱼ bʷ ψₙ(m)) / p^(n-j)` modulo `1`.
-/

namespace Green41

open Complex ComplexConjugate

/- ## Gaussian floor -/

/-- `⌊z⌋ = ⌊Re z⌋ + ⌊Im z⌋ i`. -/
noncomputable def gaussFloor (z : ℂ) : GaussianInt := ⟨⌊z.re⌋, ⌊z.im⌋⟩

lemma gaussFloor_re (z : ℂ) : ((gaussFloor z : ℂ)).re = (⌊z.re⌋ : ℝ) := by
  simp [gaussFloor, GaussianInt.toComplex_def]

lemma gaussFloor_im (z : ℂ) : ((gaussFloor z : ℂ)).im = (⌊z.im⌋ : ℝ) := by
  simp [gaussFloor, GaussianInt.toComplex_def]

/-- (L1) `‖z - ⌊z⌋‖ < √2`. -/
lemma norm_sub_gaussFloor_lt (z : ℂ) : ‖z - gaussFloor z‖ < Real.sqrt 2 := by
  have h1 := Int.fract_nonneg z.re
  have h2 := Int.fract_lt_one z.re
  have h3 := Int.fract_nonneg z.im
  have h4 := Int.fract_lt_one z.im
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [sub_re, sub_im, gaussFloor_re, gaussFloor_im]
  have e1 : z.re - ⌊z.re⌋ = Int.fract z.re := rfl
  have e2 : z.im - ⌊z.im⌋ = Int.fract z.im := rfl
  rw [e1, e2]
  apply Real.sqrt_lt_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  nlinarith

lemma floor_sub_cases (a b : ℝ) : ⌊a - b⌋ = ⌊a⌋ - ⌊b⌋ ∨ ⌊a - b⌋ = ⌊a⌋ - ⌊b⌋ - 1 := by
  have h : a - b = ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) + (Int.fract a - Int.fract b) := by
    rw [Int.fract, Int.fract]; push_cast; ring
  have ha0 := Int.fract_nonneg a
  have ha1 := Int.fract_lt_one a
  have hb0 := Int.fract_nonneg b
  have hb1 := Int.fract_lt_one b
  rw [h, Int.floor_intCast_add]
  rcases le_or_gt 0 (Int.fract a - Int.fract b) with h0 | h0
  · left
    have : ⌊Int.fract a - Int.fract b⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, by linarith⟩
    rw [this, add_zero]
  · right
    have : ⌊Int.fract a - Int.fract b⌋ = -1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; ring

/-- The four corrections `{0, 1, i, 1 + i}`. -/
def corrections : Finset GaussianInt := {0, 1, ⟨0, 1⟩, ⟨1, 1⟩}

lemma card_corrections : corrections.card = 4 := by decide

/-- (L3) `⌊u - v⌋ = ⌊u⌋ - ⌊v⌋ - d` with `d ∈ {0, 1, i, 1 + i}`. -/
lemma gaussFloor_sub (u v : ℂ) :
    ∃ d ∈ corrections, gaussFloor (u - v) = gaussFloor u - gaussFloor v - d := by
  have hre := floor_sub_cases u.re v.re
  have him := floor_sub_cases u.im v.im
  have hr : (u - v).re = u.re - v.re := sub_re u v
  have hi : (u - v).im = u.im - v.im := sub_im u v
  rcases hre with hre | hre <;> rcases him with him | him
  · refine ⟨0, by simp [corrections], ?_⟩
    ext <;> simp [gaussFloor, hr, hi, hre, him]
  · refine ⟨⟨0, 1⟩, by simp [corrections], ?_⟩
    ext <;> simp [gaussFloor, hr, hi, hre, him]
  · refine ⟨1, by simp [corrections], ?_⟩
    ext <;> simp [gaussFloor, hr, hi, hre, him]
  · refine ⟨⟨1, 1⟩, by simp [corrections], ?_⟩
    ext <;> simp [gaussFloor, hr, hi, hre, him]

/- ## Labels and counting -/

/-- The cell generator `g = π̄^α ρ̄^β / πⁿ`. -/
noncomputable def cellGen (π ρ : GaussianInt) (n α β : ℕ) : ℂ :=
  ((star π : GaussianInt) : ℂ) ^ α * ((star ρ : GaussianInt) : ℂ) ^ β / (π : ℂ) ^ n

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)

/-- The label `ψₙ(⌊x/g⌋)` of `x ∈ ℂ`. -/
noncomputable def label (ρ : GaussianInt) (n α β : ℕ) (x : ℂ) : ZMod (p ^ n) :=
  hπ.ψ n (gaussFloor (x / cellGen π ρ n α β))

include hπ in
/-- (§5) If every residue is the label of a difference of two points of `Z`, then
`pⁿ ≤ 4 · |labels(Z)|²`. -/
lemma pow_le_four_mul_card_sq (ρ : GaussianInt) (n α β : ℕ) (Z : Finset ℂ)
    (hall : ∀ l : ZMod (p ^ n), ∃ x ∈ Z, ∃ x' ∈ Z, hπ.label ρ n α β (x - x') = l) :
    p ^ n ≤ 4 * ((Z.image (hπ.label ρ n α β)).card) ^ 2 := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  set Y := Z.image (hπ.label ρ n α β)
  set S := (Y ×ˢ Y) ×ˢ corrections
  let f : (ZMod (p ^ n) × ZMod (p ^ n)) × GaussianInt → ZMod (p ^ n) :=
    fun t => t.1.1 - t.1.2 - hπ.ψ n t.2
  have hsub : (Finset.univ : Finset (ZMod (p ^ n))) ⊆ S.image f := by
    intro l _
    obtain ⟨x, hx, x', hx', hl⟩ := hall l
    obtain ⟨d, hd, hfl⟩ := gaussFloor_sub (x / cellGen π ρ n α β) (x' / cellGen π ρ n α β)
    rw [Finset.mem_image]
    refine ⟨((hπ.label ρ n α β x, hπ.label ρ n α β x'), d), ?_, ?_⟩
    · simp only [S, Y, Finset.mem_product, Finset.mem_image]
      exact ⟨⟨⟨x, hx, rfl⟩, ⟨x', hx', rfl⟩⟩, hd⟩
    · rw [← hl]
      simp only [f, label, sub_div, hfl, map_sub]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ZMod.card] at h1
  calc p ^ n ≤ (S.image f).card := h1
    _ ≤ S.card := Finset.card_image_le
    _ = 4 * Y.card ^ 2 := by
      simp only [S, Finset.card_product, card_corrections]; ring

end DigitPrime

/- ## The stripe value of a label (L4) -/

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

lemma toComplex_ne_zero : (π : ℂ) ≠ 0 := by
  rw [Ne, GaussianInt.toComplex_eq_zero]; exact hπ.prime_π.ne_zero

lemma toComplex_star_ne_zero : ((star π : GaussianInt) : ℂ) ≠ 0 := by
  rw [GaussianInt.toComplex_star]; exact (map_ne_zero _).mpr hπ.toComplex_ne_zero

lemma pow_mul_conj_pow (n : ℕ) : (π : ℂ) ^ n * ((star π : GaussianInt) : ℂ) ^ n = (p : ℂ) ^ n := by
  have h := congrArg (fun z : GaussianInt => (z : ℂ)) (hπ.natCast_pow_eq n)
  simp only [map_natCast, map_mul, map_pow, star_pow, Nat.cast_pow] at h
  exact h.symm

/-- `Re(z / πⁿ) ≡ val(Re(πⁿ) ψₙ(z)) / pⁿ (mod 1)`. -/
lemma re_div_pow (n : ℕ) (z : GaussianInt) : ∃ k : ℤ,
    ((z : ℂ) / (π : ℂ) ^ n).re =
      ((((((π ^ n).re : ℤ) : ZMod (p ^ n)) * hπ.ψ n z).val : ℕ) : ℝ) / (p : ℝ) ^ n + k := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  have hπ0 := hπ.toComplex_ne_zero
  have hpc : ((p : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hπ.prime.ne_zero)
  have hπb0 := hπ.toComplex_star_ne_zero
  have hdiv : (z : ℂ) / (π : ℂ) ^ n =
      ((z * star (π ^ n) : GaussianInt) : ℂ) / (((p : ℝ) ^ n : ℝ) : ℂ) := by
    rw [map_mul, star_pow, map_pow]
    push_cast
    rw [← hπ.pow_mul_conj_pow n]
    field_simp
  set A := (z * star (π ^ n)).re with hA
  set X := (((π ^ n).re : ℤ) : ZMod (p ^ n)) * hπ.ψ n z with hX
  have hsf : ((A : ℤ) : ZMod (p ^ n)) = X := hπ.stripe_formula n z
  have hv : (((X.val : ℕ) : ℤ) : ZMod (p ^ n)) = X := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hcong : ((p ^ n : ℕ) : ℤ) ∣ A - (X.val : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]; rw [hv, hsf]
  obtain ⟨k, hk⟩ := hcong
  refine ⟨k, ?_⟩
  rw [hdiv, Complex.div_ofReal_re, ← GaussianInt.intCast_re, ← hA]
  have hA' : (A : ℝ) = (X.val : ℝ) + ((p : ℝ) ^ n) * k := by
    have : A = (X.val : ℤ) + ((p ^ n : ℕ) : ℤ) * k := by linarith
    rw [this]; push_cast; ring
  rw [hA']
  have hpr : ((p : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hπ.prime.ne_zero)
  field_simp

omit hπ in
/-- `val(pʲ Y) / pⁿ ≡ val(Y) / p^(n-j) (mod 1)`. -/
lemma val_pow_mul_div {p n j : ℕ} (hp : 0 < p) (hj : j ≤ n) (Y : ZMod (p ^ n)) : ∃ k : ℤ,
    ((((p : ZMod (p ^ n)) ^ j * Y).val : ℕ) : ℝ) / (p : ℝ) ^ n =
      ((Y.val : ℕ) : ℝ) / (p : ℝ) ^ (n - j) + k := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne'⟩
  have hcast : (p : ZMod (p ^ n)) ^ j * Y = ((p ^ j * Y.val : ℕ) : ZMod (p ^ n)) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [hcast, ZMod.val_natCast]
  obtain ⟨q, hq⟩ : ∃ q, p ^ j * Y.val = p ^ j * Y.val % p ^ n + p ^ n * q :=
    ⟨_, (Nat.mod_add_div _ _).symm⟩
  refine ⟨-(q : ℤ), ?_⟩
  have hR : ((p ^ j * Y.val % p ^ n : ℕ) : ℝ) = (p : ℝ) ^ j * Y.val - (p : ℝ) ^ n * q := by
    have h1 := congrArg (fun x : ℕ => (x : ℝ)) hq
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at h1
    linarith
  rw [hR]
  have hpn : (p : ℝ) ^ n = (p : ℝ) ^ j * (p : ℝ) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj]
  have hpj : (p : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne')
  have hpnj : (p : ℝ) ^ (n - j) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne')
  rw [hpn]
  field_simp
  push_cast
  ring

/-- The unit factor `Xⱼ = Re(πⁿ) ψ(π̄)^(-j) ψ(π̄)^(α-j) ψ(ρ̄)^β` of (L4). -/
noncomputable def Xfac (ρ : GaussianInt) (n α β j : ℕ) : ZMod (p ^ n) :=
  (((π ^ n).re : ℤ) : ZMod (p ^ n)) * ((hπ.ψ n (star π))⁻¹) ^ j * hπ.ψ n (star π) ^ (α - j) *
    hπ.ψ n (star ρ) ^ β

/-- (L4) `Re(σʲ τʷ g m) ≡ val(Xⱼ bʷ ψₙ(m)) / p^(n-j) (mod 1)`. -/
lemma re_label_formula {ρ : GaussianInt} (hρ' : ¬ π ∣ star ρ) (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0)
    {n α β j w : ℕ} (hn : 0 < n) (hj : j ≤ α) (hw : w ≤ β) (hjn : j ≤ n) (m : GaussianInt) :
    ∃ k : ℤ, (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ j * ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ w *
        (cellGen π ρ n α β * m)).re =
      (((hπ.Xfac ρ n α β j * hπ.mult ρ n ^ w * hπ.ψ n m).val : ℕ) : ℝ) / (p : ℝ) ^ (n - j) +
        k := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  set z : GaussianInt := π ^ j * star π ^ (α - j) * ρ ^ w * star ρ ^ (β - w) * m with hz
  have hπ0 := hπ.toComplex_ne_zero
  have hπb0 := hπ.toComplex_star_ne_zero
  have hcx : ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ j * ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ w *
      (cellGen π ρ n α β * m) = (z : ℂ) / (π : ℂ) ^ n := by
    simp only [hz, cellGen, map_mul, map_pow, div_pow]
    obtain ⟨a, rfl⟩ : ∃ a, α = a + j := ⟨α - j, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, β = b + w := ⟨β - w, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
    field_simp
    ring
  obtain ⟨k₁, hk₁⟩ := hπ.re_div_pow n z
  have hunit : hπ.ψ n (star π) * (hπ.ψ n (star π))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ ((hπ.isUnit_ψ_iff hn _).mpr hπ.not_dvd_star)
  have hψπ : hπ.ψ n π = (p : ZMod (p ^ n)) * (hπ.ψ n (star π))⁻¹ := by
    rw [← hπ.ψ_mul_star n, mul_assoc, hunit, mul_one]
  have hψρ : hπ.ψ n ρ = hπ.mult ρ n * hπ.ψ n (star ρ) := (hπ.mult_mul hn hρ').symm
  have hX : (((π ^ n).re : ℤ) : ZMod (p ^ n)) * hπ.ψ n z =
      (p : ZMod (p ^ n)) ^ j * (hπ.Xfac ρ n α β j * hπ.mult ρ n ^ w * hπ.ψ n m) := by
    simp only [hz, map_mul, map_pow, hψπ, hψρ, Xfac]
    obtain ⟨b, rfl⟩ : ∃ b, β = b + w := ⟨β - w, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  obtain ⟨k₂, hk₂⟩ := val_pow_mul_div hπ.prime.pos hjn
    (hπ.Xfac ρ n α β j * hπ.mult ρ n ^ w * hπ.ψ n m)
  refine ⟨k₁ + k₂, ?_⟩
  rw [hcx, hk₁, hX, hk₂]
  push_cast; ring

end DigitPrime

end Green41

/- ## Section: `StepA` -/

/-
# Step A: the orbit meets every label (blueprint §4)

This replaces Kravitz–Leng Theorem 5.1. Write `q = π̄^v ρ̄^E q₂` with `π̄ ∤ q₂`, and let
`j = v + D` with `D = n - α + 4`. For `t < (p - 1) p^(n+3)`,
`σʲ τᵗ q = ρ̄^β W_t / π̄^D` with `W_t = πʲ ρᵗ ρ̄^(E-β-t) q₂`.
The residues `W_t mod π̄^(n+4)` run over all units, so every cell `g(m₀ + [0,1)²)` modulo
`M = π̄^α ρ̄^β ℤ[i]` receives a point `σʲ τᵗ (q + e')`, provided `|e'| < 0.42 |g|`.
-/

namespace Green41

open Complex ComplexConjugate

/- ## Helpers on floors, rounding and norms -/

lemma gaussFloor_add_intCast (m : GaussianInt) (z : ℂ) :
    gaussFloor ((m : ℂ) + z) = m + gaussFloor z := by
  have hre : ((m : ℂ) + z).re = ((m.re : ℤ) : ℝ) + z.re := by
    rw [add_re, ← GaussianInt.intCast_re]
  have him : ((m : ℂ) + z).im = ((m.im : ℤ) : ℝ) + z.im := by
    rw [add_im, ← GaussianInt.intCast_im]
  ext
  · simp only [gaussFloor, Zsqrtd.re_add]; rw [hre, Int.floor_intCast_add]
  · simp only [gaussFloor, Zsqrtd.im_add]; rw [him, Int.floor_intCast_add]

lemma gaussFloor_half_add {u : ℂ} (hu : ‖u‖ < 1 / 2) : gaussFloor ((1 + I) / 2 + u) = 0 := by
  have h1 : |u.re| < 1 / 2 := lt_of_le_of_lt (Complex.abs_re_le_norm u) hu
  have h2 : |u.im| < 1 / 2 := lt_of_le_of_lt (Complex.abs_im_le_norm u) hu
  rw [abs_lt] at h1 h2
  ext
  · simp only [gaussFloor, Zsqrtd.re_zero]
    rw [Int.floor_eq_zero_iff]
    simp only [add_re, div_re, one_re, I_re, normSq_ofNat, Set.mem_Ico]
    norm_num; constructor <;> linarith
  · simp only [gaussFloor, Zsqrtd.im_zero]
    rw [Int.floor_eq_zero_iff]
    simp only [add_im, div_im, one_im, I_im, normSq_ofNat, Set.mem_Ico]
    norm_num; constructor <;> linarith

lemma norm_sub_gRound_lt_one (x : ℂ) : ‖x - gRound x‖ < 1 := by
  have h1 := frac_mem x.re
  have h2 := frac_mem x.im
  rw [Complex.norm_def, Complex.normSq_apply]
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  simp only [sub_re, sub_im, gRound_re, gRound_im]
  apply Real.sqrt_lt_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  nlinarith

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

/-- A Gaussian integer prime to `π̄` within distance `2` of any point. -/
lemma exists_coprime_near (c : ℂ) : ∃ W : GaussianInt, ¬ star π ∣ W ∧ ‖c - W‖ < 2 := by
  have h1 := norm_sub_gRound_lt_one c
  by_cases hdvd : star π ∣ gRound c
  · refine ⟨gRound c + 1, ?_, ?_⟩
    · intro h
      have h1' : star π ∣ (1 : GaussianInt) := (dvd_add_right hdvd).mp h
      have hu : IsUnit (star π) := isUnit_of_dvd_one h1'
      have : IsUnit π := by simpa using hu.star
      exact hπ.prime_π.not_isUnit this
    · calc ‖c - ((gRound c + 1 : GaussianInt) : ℂ)‖ = ‖(c - gRound c) - 1‖ := by
            rw [map_add, map_one]; ring_nf
        _ ≤ ‖c - gRound c‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ < 2 := by rw [norm_one]; linarith
  · exact ⟨gRound c, hdvd, by linarith⟩

lemma norm_toComplex_π : ‖(π : ℂ)‖ = Real.sqrt p := by
  rw [norm_toComplex, hπ.norm]; norm_cast

lemma norm_toComplex_star_π : ‖((star π : GaussianInt) : ℂ)‖ = Real.sqrt p := by
  rw [GaussianInt.toComplex_star, Complex.norm_conj, hπ.norm_toComplex_π]

lemma norm_sigma : ‖(π : ℂ) / ((star π : GaussianInt) : ℂ)‖ = 1 := by
  rw [norm_div, hπ.norm_toComplex_π, hπ.norm_toComplex_star_π,
    div_self (Real.sqrt_pos.mpr (by exact_mod_cast hπ.prime.pos)).ne']

/-- `‖π̄^D / ρ̄^β‖ · ‖g‖ = p²` when `D + α = n + 4`. -/
lemma norm_shift_mul_norm_cellGen {ρ : GaussianInt} (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0)
    {n α β D : ℕ} (hD : D + α = n + 4) :
    ‖((star π : GaussianInt) : ℂ) ^ D / ((star ρ : GaussianInt) : ℂ) ^ β‖ *
      ‖cellGen π ρ n α β‖ = (p : ℝ) ^ 2 := by
  have hsp : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hπ.prime.pos)).ne'
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (by positivity)
  have h1 : ‖((star π : GaussianInt) : ℂ) ^ D‖ = Real.sqrt p ^ D := by
    rw [_root_.norm_pow, hπ.norm_toComplex_star_π]
  have h2 : ‖((star π : GaussianInt) : ℂ) ^ α‖ = Real.sqrt p ^ α := by
    rw [_root_.norm_pow, hπ.norm_toComplex_star_π]
  have h3 : ‖(π : ℂ) ^ n‖ = Real.sqrt p ^ n := by rw [_root_.norm_pow, hπ.norm_toComplex_π]
  set X := ‖((star ρ : GaussianInt) : ℂ) ^ β‖ with hX
  have hX0 : X ≠ 0 := by rw [hX, _root_.norm_pow]; exact pow_ne_zero _ (norm_ne_zero_iff.mpr hρ0)
  have hsn : Real.sqrt p ^ n ≠ 0 := pow_ne_zero _ hsp
  unfold cellGen
  rw [norm_div, norm_div, norm_mul, h1, h2, h3, ← hX]
  calc Real.sqrt p ^ D / X * (Real.sqrt p ^ α * X / Real.sqrt p ^ n)
      = Real.sqrt p ^ (D + α) / Real.sqrt p ^ n := by rw [pow_add]; field_simp
    _ = (p : ℝ) ^ 2 := by
      rw [hD, pow_add, show Real.sqrt p ^ 4 = (Real.sqrt p ^ 2) ^ 2 by ring, hsq]
      field_simp

/-- A Gaussian integer is `≡` its value modulo `πⁿ`: the natural-number representative of a
residue has that residue. -/
lemma ψ_natCast_val (n : ℕ) (l : ZMod (p ^ n)) : hπ.ψ n ((l.val : ℕ) : GaussianInt) = l := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

lemma not_star_dvd_self : ¬ star π ∣ π := by
  rintro ⟨y, hy⟩
  apply hπ.not_dvd_star
  refine ⟨star y, ?_⟩
  have h := congrArg star hy
  rw [star_mul, star_star] at h
  rw [h, mul_comm]

lemma prime_star_π : Prime (star π) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_norm_prime (by rw [Zsqrtd.norm_conj, hπ.norm]; simpa using hπ.prime))

/-- **Step A.** Every residue `l` is the label of `σʲ τᵗ (q + e')` for some
`t < (p - 1) p^(n+3)`, where `q = π̄^v ρ̄^E q₂` and `j = v + (n - α + 4)`. -/
theorem stepA (hp5 : 5 ≤ p) {ρ : GaussianInt} (hρ1 : ¬ π ∣ ρ)
    (hρ4 : ¬ star π ∣ star ρ) (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0)
    {n α β : ℕ} (hα : α ≤ n)
    (hord : orderOf (hπ.mult (star ρ) (n + 4)) = (p - 1) * p ^ (n + 3))
    {v E : ℕ} (hE : (p - 1) * p ^ (n + 3) + β ≤ E) {q₂ : GaussianInt} (hq₂ : ¬ star π ∣ q₂)
    {e' : ℂ} (he' : ‖e'‖ < 21 / 50 * ‖cellGen π ρ n α β‖) (l : ZMod (p ^ n)) :
    ∃ t < (p - 1) * p ^ (n + 3),
      hπ.label ρ n α β (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ (v + (n - α + 4)) *
        ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ t *
        ((((star π) ^ v * (star ρ) ^ E * q₂ : GaussianInt) : ℂ) + e')) = l := by
  set D := n - α + 4 with hD
  set T := (p - 1) * p ^ (n + 3) with hT
  set g := cellGen π ρ n α β with hg
  have hπ0 := hπ.toComplex_ne_zero
  have hπb0 := hπ.toComplex_star_ne_zero
  have hg0 : g ≠ 0 := by
    simp only [hg, cellGen]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hπb0) (pow_ne_zero _ hρ0)) (pow_ne_zero _ hπ0)
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg0
  have hk0 : 0 < n + 4 := by omega
  -- the target cell
  set m₀ : GaussianInt := ((l.val : ℕ) : GaussianInt) with hm₀
  set c₀ : ℂ := g * ((m₀ : ℂ) + (1 + I) / 2) with hc₀
  set h : ℂ := ((star π : GaussianInt) : ℂ) ^ D / ((star ρ : GaussianInt) : ℂ) ^ β with hh
  have hh0 : h ≠ 0 := div_ne_zero (pow_ne_zero _ hπb0) (pow_ne_zero _ hρ0)
  have hhg : ‖h‖ * ‖g‖ = (p : ℝ) ^ 2 := hπ.norm_shift_mul_norm_cellGen hρ0 (by omega)
  obtain ⟨W, hW, hWnear⟩ := hπ.exists_coprime_near (h * c₀)
  -- units modulo `π̄^(n+4)`
  set W₀ : GaussianInt := π ^ (v + D) * star ρ ^ (E - β) * q₂ with hW₀
  have hW₀u : IsUnit (hπ.ψbar (n + 4) W₀) := by
    rw [hπ.isUnit_ψbar_iff hk0]
    intro hdvd
    have hprime : Prime (star π) := hπ.prime_star_π
    rcases hprime.dvd_or_dvd hdvd with h1 | h1
    · rcases hprime.dvd_or_dvd h1 with h2 | h2
      · exact hπ.not_star_dvd_self (hprime.dvd_of_dvd_pow h2)
      · exact hρ4 (hprime.dvd_of_dvd_pow h2)
    · exact hq₂ h1
  have hWu : IsUnit (hπ.ψbar (n + 4) W) := (hπ.isUnit_ψbar_iff hk0 W).mpr hW
  set c := hπ.ψbar (n + 4) W * (hπ.ψbar (n + 4) W₀)⁻¹ with hc
  have hinv : hπ.ψbar (n + 4) W₀ * (hπ.ψbar (n + 4) W₀)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hW₀u
  have hcu : IsUnit c := hWu.mul (IsUnit.of_mul_eq_one_right _ hinv)
  have : NeZero (p ^ (n + 4)) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  have hcard : orderOf (hπ.mult (star ρ) (n + 4)) = Nat.card (ZMod (p ^ (n + 4)))ˣ := by
    rw [hord, card_units_prime_pow hπ.prime hk0, hT, show n + 4 - 1 = n + 3 by omega]
  obtain ⟨t, htlt, hteq⟩ := exists_pow_eq_of_orderOf_eq_card _ hcard c hcu
  rw [hord] at htlt
  refine ⟨t, htlt, ?_⟩
  -- the orbit point `W_t`
  set Wt : GaussianInt := π ^ (v + D) * ρ ^ t * star ρ ^ (E - β - t) * q₂ with hWt
  have hρu : IsUnit (hπ.ψ (n + 4) ρ) := (hπ.isUnit_ψ_iff hk0 ρ).mpr hρ1
  have hρinv : hπ.ψ (n + 4) ρ * (hπ.ψ (n + 4) ρ)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hρu
  have hψWt : hπ.ψbar (n + 4) Wt = hπ.ψbar (n + 4) W₀ * hπ.mult (star ρ) (n + 4) ^ t := by
    obtain ⟨e, he⟩ : ∃ e, E - β = e + t := ⟨E - β - t, by omega⟩
    have he2 : E - β - t = e := by omega
    rw [hWt, hW₀, he2, he]
    simp only [ψbar_apply, mult, star_star, map_mul, map_pow]
    rw [pow_add (hπ.ψ (n + 4) ρ) e t, mul_pow (hπ.ψ (n + 4) (star ρ))]
    have hone : hπ.ψ (n + 4) ρ ^ t * ((hπ.ψ (n + 4) ρ)⁻¹) ^ t = 1 := by
      rw [← mul_pow, hρinv, one_pow]
    linear_combination (-(hπ.ψ (n + 4) (star π) ^ (v + D) * hπ.ψ (n + 4) ρ ^ e *
      hπ.ψ (n + 4) (star q₂) * hπ.ψ (n + 4) (star ρ) ^ t)) * hone
  have hdiff : star π ^ (n + 4) ∣ Wt - W := by
    rw [← hπ.ψbar_eq_zero_iff, map_sub, hψWt, hteq, hc]
    rw [mul_comm (hπ.ψbar (n + 4) W), ← mul_assoc, hinv, one_mul, sub_self]
  obtain ⟨Δ, hΔ⟩ := hdiff
  -- complex bookkeeping
  set σt : ℂ := ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ (v + D) *
    ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ t with hσt
  have hcx : σt * (((star π) ^ v * (star ρ) ^ E * q₂ : GaussianInt) : ℂ) = (Wt : ℂ) / h := by
    have hEsplit : ((star ρ : GaussianInt) : ℂ) ^ E = ((star ρ : GaussianInt) : ℂ) ^ (E - β - t) *
        ((star ρ : GaussianInt) : ℂ) ^ β * ((star ρ : GaussianInt) : ℂ) ^ t := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    simp only [hσt, hWt, hh, map_mul, map_pow, div_pow]
    rw [hEsplit, pow_add, pow_add]
    field_simp
    ring
  have hWt' : (Wt : ℂ) = (W : ℂ) + ((star π : GaussianInt) : ℂ) ^ (n + 4) * (Δ : ℂ) := by
    have hWW : Wt = W + star π ^ (n + 4) * Δ := by rw [← hΔ]; ring
    rw [hWW, map_add, map_mul, map_pow]
  have hgπ : ((star π : GaussianInt) : ℂ) ^ (n + 4) / h = g * (π : ℂ) ^ n := by
    simp only [hh, hg, cellGen]
    have hn4 : n + 4 = α + D := by omega
    rw [hn4, pow_add]
    field_simp
  have hkey : σt * ((((star π) ^ v * (star ρ) ^ E * q₂ : GaussianInt) : ℂ) + e') =
      (W : ℂ) / h + g * (π : ℂ) ^ n * Δ + σt * e' := by
    rw [mul_add, hcx, hWt', ← hgπ]
    ring
  set u : ℂ := ((W : ℂ) / h - c₀ + σt * e') / g with hu
  have hy : (σt * ((((star π) ^ v * (star ρ) ^ E * q₂ : GaussianInt) : ℂ) + e')) / g =
      (((m₀ + π ^ n * Δ : GaussianInt) : ℂ)) + ((1 + I) / 2 + u) := by
    rw [hkey, hu, hc₀]
    simp only [map_add, map_mul, map_pow]
    field_simp
    ring
  have hunorm : ‖u‖ < 1 / 2 := by
    have hρn : ‖((star ρ : GaussianInt) : ℂ)‖ = ‖(ρ : ℂ)‖ := by
      rw [GaussianInt.toComplex_star, Complex.norm_conj]
    have hρ0' : ‖(ρ : ℂ)‖ ≠ 0 := by rw [← hρn]; exact norm_ne_zero_iff.mpr hρ0
    have hτ : ‖σt * e'‖ = ‖e'‖ := by
      rw [hσt, norm_mul, norm_mul, _root_.norm_pow, _root_.norm_pow, hπ.norm_sigma, norm_div, hρn,
        div_self hρ0']
      simp
    have hW1 : ‖(W : ℂ) / h - c₀‖ = ‖h * c₀ - W‖ / ‖h‖ := by
      rw [norm_sub_rev (h * c₀), ← norm_div]; congr 1; field_simp
    have hhpos : 0 < ‖h‖ := norm_pos_iff.mpr hh0
    have hW2 : ‖(W : ℂ) / h - c₀‖ < 2 / 25 * ‖g‖ := by
      rw [hW1, div_lt_iff₀ hhpos]
      have hp2 : (25 : ℝ) ≤ (p : ℝ) ^ 2 := by
        have : (5 : ℝ) ≤ p := by exact_mod_cast hp5
        nlinarith
      nlinarith [hhg]
    rw [hu, norm_div, div_lt_iff₀ hgpos]
    calc ‖(W : ℂ) / h - c₀ + σt * e'‖ ≤ ‖(W : ℂ) / h - c₀‖ + ‖σt * e'‖ := norm_add_le _ _
      _ < 1 / 2 * ‖g‖ := by rw [hτ]; linarith
  simp only [label]
  rw [← hg, hy, gaussFloor_add_intCast, gaussFloor_half_add hunorm, add_zero, map_add,
    map_mul, hπ.ψ_pow_self, zero_mul, add_zero, hm₀, hπ.ψ_natCast_val]

end DigitPrime

end Green41

/- ## Section: `DigitPigeonhole` -/

/-
# Digit pigeonhole (Gayfulin–Moshchevitin Lemma 4, abstract form; blueprint §6)

Let `Y` be a set of naturals `< pⁿ` with `pⁿ ≤ 4 |Y|²`. Take `ℓ = 4L` and `n = 8(A + ℓ)`.
Then there are a level `s` with `A + ℓ ≤ s ≤ n` and a residue `λ` mod `p^(s-ℓ)` over which
`Y` has at least `p^L` distinct residues mod `p^s`.

Proof: with levels `s_i = n - iℓ` (`i ≤ J`, `s_J ∈ [A, A + ℓ)`), the number of residues of
`Y` at level `s_i` is at most `p^L` times the number at level `s_{i+1}` unless some fiber is
large. Telescoping gives `|Y| ≤ p^(s_J) p^(LJ)`, which is too small.
-/

namespace Green41

/-- The residues mod `p^s` of the elements of `Y` lying over `λ` mod `p^(s-ℓ)`. -/
def digitFiber (p s ℓ lam : ℕ) (Y : Finset ℕ) : Finset ℕ :=
  (Y.filter (fun y => y % p ^ (s - ℓ) = lam)).image (· % p ^ s)

lemma card_image_mod_le_card_image_mul {p : ℕ} {s ℓ L : ℕ}
    (Y : Finset ℕ) (hfib : ∀ lam, (digitFiber p s ℓ lam Y).card ≤ p ^ L) :
    (Y.image (· % p ^ s)).card ≤ p ^ L * (Y.image (· % p ^ (s - ℓ))).card := by
  have hdvd : p ^ (s - ℓ) ∣ p ^ s := pow_dvd_pow p (Nat.sub_le s ℓ)
  have himg : (Y.image (· % p ^ s)).image (· % p ^ (s - ℓ)) = Y.image (· % p ^ (s - ℓ)) := by
    rw [Finset.image_image]
    congr 1
    funext y
    exact Nat.mod_mod_of_dvd y hdvd
  rw [← himg]
  apply Finset.card_le_mul_card_image
  intro lam _
  calc ((Y.image (· % p ^ s)).filter (fun x => x % p ^ (s - ℓ) = lam)).card
      = (digitFiber p s ℓ lam Y).card := by
        congr 1
        ext x
        simp only [digitFiber, Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨y, hy, rfl⟩, hx⟩
          exact ⟨y, ⟨hy, by rwa [Nat.mod_mod_of_dvd y hdvd] at hx⟩, rfl⟩
        · rintro ⟨y, ⟨hy, hyl⟩, rfl⟩
          exact ⟨⟨y, hy, rfl⟩, by rwa [Nat.mod_mod_of_dvd y hdvd]⟩
    _ ≤ p ^ L := hfib lam

/-- **Digit pigeonhole.** -/
theorem digit_pigeonhole {p : ℕ} (hp : 5 ≤ p) {n A L : ℕ} (hL : 0 < L)
    (hn : n = 8 * (A + 4 * L)) (Y : Finset ℕ) (hY : ∀ y ∈ Y, y < p ^ n)
    (hcard : p ^ n ≤ 4 * Y.card ^ 2) :
    ∃ s, A + 4 * L ≤ s ∧ s ≤ n ∧ ∃ lam : ℕ, p ^ L ≤ (digitFiber p s (4 * L) lam Y).card := by
  by_contra hcon
  push Not at hcon
  have hp0 : 0 < p := by omega
  set ℓ := 4 * L with hℓ
  have hℓpos : 0 < ℓ := by omega
  set J := (n - A) / ℓ with hJ
  have hJℓ : J * ℓ ≤ n - A := Nat.div_mul_le_self (n - A) ℓ
  have hJℓ' : n - A < J * ℓ + ℓ := by
    have := Nat.lt_div_mul_add (a := n - A) hℓpos; rw [hJ]; linarith
  have hAn : A ≤ n := by omega
  -- telescoping over the levels `n - i ℓ`
  have htel : ∀ i, i ≤ J → Y.card ≤ (Y.image (· % p ^ (n - i * ℓ))).card * (p ^ L) ^ i := by
    intro i
    induction i with
    | zero =>
      intro _
      simp only [zero_mul, Nat.sub_zero, pow_zero, mul_one]
      apply le_of_eq
      rw [Finset.card_image_of_injOn]
      intro a ha b hb hab
      simp only at hab
      rwa [Nat.mod_eq_of_lt (hY a ha), Nat.mod_eq_of_lt (hY b hb)] at hab
    | succ i ih =>
      intro hi
      have hi' : i ≤ J := by omega
      have hs1 : A + ℓ ≤ n - i * ℓ := by
        have : (i + 1) * ℓ ≤ J * ℓ := Nat.mul_le_mul_right ℓ hi
        rw [add_mul, one_mul] at this
        omega
      have hstep := card_image_mod_le_card_image_mul (p := p) (s := n - i * ℓ) (ℓ := ℓ) (L := L)
        Y (fun lam => (hcon _ hs1 (by omega) lam).le)
      have heq : n - i * ℓ - ℓ = n - (i + 1) * ℓ := by rw [add_mul, one_mul]; omega
      rw [heq] at hstep
      calc Y.card ≤ (Y.image (· % p ^ (n - i * ℓ))).card * (p ^ L) ^ i := ih hi'
        _ ≤ (p ^ L * (Y.image (· % p ^ (n - (i + 1) * ℓ))).card) * (p ^ L) ^ i :=
            Nat.mul_le_mul_right _ hstep
        _ = (Y.image (· % p ^ (n - (i + 1) * ℓ))).card * (p ^ L) ^ (i + 1) := by ring
  have hlast := htel J le_rfl
  set sJ := n - J * ℓ with hsJ
  have hsJlt : sJ < A + ℓ := by omega
  have hcardJ : (Y.image (· % p ^ sJ)).card ≤ p ^ sJ := by
    calc (Y.image (· % p ^ sJ)).card ≤ (Finset.range (p ^ sJ)).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))
      _ = p ^ sJ := Finset.card_range _
  have hY2 : Y.card ≤ p ^ (sJ + L * J) := by
    calc Y.card ≤ (Y.image (· % p ^ sJ)).card * (p ^ L) ^ J := hlast
      _ ≤ p ^ sJ * (p ^ L) ^ J := Nat.mul_le_mul_right _ hcardJ
      _ = p ^ (sJ + L * J) := by rw [← pow_mul, ← pow_add]
  have hexp : 2 * (sJ + L * J) + 1 ≤ n := by
    have h4 : 4 * (L * J) = n - sJ := by
      have : J * ℓ = n - sJ := by omega
      rw [← this, hℓ]; ring
    omega
  have hlt : 4 * Y.card ^ 2 < p ^ n := by
    calc 4 * Y.card ^ 2 ≤ 4 * (p ^ (sJ + L * J)) ^ 2 := by
          apply Nat.mul_le_mul_left; exact Nat.pow_le_pow_left hY2 2
      _ = 4 * p ^ (2 * (sJ + L * J)) := by rw [← pow_mul, mul_comm (sJ + L * J) 2]
      _ < p * p ^ (2 * (sJ + L * J)) := by
          apply Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = p ^ (2 * (sJ + L * J) + 1) := by rw [pow_succ]; ring
      _ ≤ p ^ n := Nat.pow_le_pow_right hp0 hexp
  omega

end Green41

/- ## Section: `DiscreteCore` -/

/-
# The discrete core (Gayfulin–Moshchevitin Lemmas 5–8, simplified; blueprint §7)

Let `N = p^ℓ` with `p ≥ 5`, let `B` have `w ↦ Bʷ mod N` injective on `[0, S)`, where
`S = (p - 1) p^(ℓ-1)`, let `γ ∈ ℝ`, and let `𝔜` be a finite set of naturals with distinct
residues mod `N`, with `25 H³ < 4 |𝔜|` and `H ε² ≥ 2`. Then some point `Bʷ (y/N + γ)` lies
within `ε/2` of an integer.

Proof: sum the Fejér-type kernel `|Σ_{a<H} e(a t)|²` over all points. Each term is at most
`1/ε²` if the point is `ε/2`-far from the integers. The diagonal of the expanded sum is
`H S |𝔜|`. An off-diagonal frequency `m` contributes at most `N √(|𝔜| |m|)`, by
Cauchy–Schwarz, injectivity of `w ↦ Bʷ`, orthogonality of additive characters mod `N`, and a
bucket count of `{y' : N ∣ m (y - y')}`.
-/

namespace Green41

open Complex Finset

/-- `e(x) = exp(2πix)`. -/
noncomputable def ex (x : ℝ) : ℂ := Complex.exp (I * ((2 * Real.pi * x : ℝ) : ℂ))

lemma norm_ex (x : ℝ) : ‖ex x‖ = 1 := by
  unfold ex; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _

lemma ex_add (x y : ℝ) : ex (x + y) = ex x * ex y := by
  unfold ex; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ex_intCast (k : ℤ) : ex k = 1 := by
  unfold ex
  rw [Complex.exp_eq_one_iff]
  exact ⟨k, by push_cast; ring⟩

lemma ex_add_intCast (x : ℝ) (k : ℤ) : ex (x + k) = ex x := by
  rw [ex_add, ex_intCast, mul_one]

lemma ex_zero : ex 0 = 1 := by simpa using ex_intCast 0

lemma ex_nat_mul (a : ℕ) (x : ℝ) : ex (a * x) = ex x ^ a := by
  unfold ex; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma ex_neg (x : ℝ) : ex (-x) = (starRingEnd ℂ) (ex x) := by
  unfold ex
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

lemma ex_eq_one_iff (x : ℝ) : ex x = 1 ↔ ∃ k : ℤ, x = k := by
  unfold ex
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h2 : (((2 * Real.pi * x : ℝ)) : ℂ) = ((2 * Real.pi * k : ℝ) : ℂ) := by
      have hI : I ≠ 0 := I_ne_zero
      apply mul_left_cancel₀ hI
      rw [hk]; push_cast; ring
    have h3 : 2 * Real.pi * x = 2 * Real.pi * k := by exact_mod_cast h2
    have hpi : 2 * Real.pi ≠ 0 := by positivity
    exact mul_left_cancel₀ hpi h3
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; ring⟩

/-- `‖e(x) - 1‖ ≥ 4 |x - k|` for the nearest integer `k = round x`. -/
lemma norm_ex_sub_one_ge (x : ℝ) : 4 * |x - round x| ≤ ‖ex x - 1‖ := by
  set y := x - round x with hy
  have hxy : ex x = ex y := by
    rw [hy, sub_eq_add_neg, ← Int.cast_neg, ex_add_intCast]
  rw [hxy]
  have hy1 : |y| ≤ 1 / 2 := by
    rw [hy]; exact abs_sub_round x
  unfold ex
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_two]
  have hs : 2 * |y| ≤ |Real.sin (2 * Real.pi * y / 2)| := by
    rw [show 2 * Real.pi * y / 2 = Real.pi * y by ring]
    rcases le_or_gt 0 y with h0 | h0
    · rw [abs_of_nonneg h0]
      have h1 : Real.pi * y ≤ Real.pi / 2 := by
        have := abs_of_nonneg h0 ▸ hy1; nlinarith [Real.pi_pos]
      have := Real.mul_le_sin (by positivity) h1
      have hnn : 0 ≤ 2 / Real.pi * (Real.pi * y) := by positivity
      rw [abs_of_nonneg (by linarith)]
      calc 2 * y = 2 / Real.pi * (Real.pi * y) := by field_simp
        _ ≤ Real.sin (Real.pi * y) := this
    · rw [abs_of_neg h0]
      have h1 : Real.pi * (-y) ≤ Real.pi / 2 := by
        have := abs_of_neg h0 ▸ hy1; nlinarith [Real.pi_pos]
      have := Real.mul_le_sin (by nlinarith [Real.pi_pos]) h1
      have hsin : Real.sin (Real.pi * y) = -Real.sin (Real.pi * (-y)) := by
        rw [mul_neg, Real.sin_neg, neg_neg]
      have hnn : 0 ≤ 2 / Real.pi * (Real.pi * -y) := by
        have : 0 ≤ -y := by linarith
        positivity
      rw [hsin, abs_neg, abs_of_nonneg (by linarith)]
      calc 2 * -y = 2 / Real.pi * (Real.pi * -y) := by field_simp
        _ ≤ Real.sin (Real.pi * -y) := this
  linarith

/-- Fejér bound: if `x` is `δ`-far from the integers, `‖Σ_{a<H} e(a x)‖ ≤ 1/(2δ)`. -/
lemma norm_geom_ex_le {x δ : ℝ} (hδ : 0 < δ) (hfar : δ ≤ |x - round x|) (H : ℕ) :
    ‖∑ a ∈ range H, ex (a * x)‖ ≤ 1 / (2 * δ) := by
  have hge := norm_ex_sub_one_ge x
  have hne : ex x ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hge
    linarith
  have hpos : 0 < ‖ex x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  simp_rw [ex_nat_mul]
  rw [geom_sum_eq hne, norm_div]
  have hnum : ‖ex x ^ H - 1‖ ≤ 2 := by
    calc ‖ex x ^ H - 1‖ ≤ ‖ex x ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_ex, one_pow, norm_one]; norm_num
  rw [div_le_div_iff₀ hpos (by positivity)]
  nlinarith

/-- Orthogonality: `Σ_{u<N} e(u x / N) = N` if `N ∣ x` and `0` otherwise. -/
lemma sum_ex_div (N : ℕ) (hN : 0 < N) (x : ℤ) :
    ∑ u ∈ range N, ex (u * x / N) = if (N : ℤ) ∣ x then (N : ℂ) else 0 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hterm : ∀ u : ℕ, ex (u * x / N) = ex ((x : ℝ) / N) ^ u := by
    intro u; rw [← ex_nat_mul]; congr 1; ring
  simp_rw [hterm]
  split_ifs with hdvd
  · obtain ⟨k, hk⟩ := hdvd
    have : ex ((x : ℝ) / N) = 1 := by
      rw [ex_eq_one_iff]; exact ⟨k, by rw [hk]; push_cast; field_simp⟩
    simp [this]
  · have hne : ex ((x : ℝ) / N) ≠ 1 := by
      rw [Ne, ex_eq_one_iff]
      rintro ⟨k, hk⟩
      apply hdvd
      refine ⟨k, ?_⟩
      have : (x : ℝ) = N * k := by rw [← hk]; field_simp
      exact_mod_cast this
    rw [geom_sum_eq hne]
    have hpow : ex ((x : ℝ) / N) ^ N = 1 := by
      rw [← ex_nat_mul, show (N : ℝ) * ((x : ℝ) / N) = ((x : ℤ) : ℝ) by field_simp, ex_intCast]
    rw [hpow, sub_self, zero_div]

/-- `‖Σ zᵢ‖² = Re Σᵢ Σⱼ zᵢ z̄ⱼ`. -/
lemma norm_sum_sq_eq {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ 2 = (∑ i ∈ s, ∑ j ∈ s, z i * (starRingEnd ℂ) (z j)).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj,
    map_sum, Finset.sum_mul_sum]

lemma ex_mul_conj (a b : ℝ) : ex a * (starRingEnd ℂ) (ex b) = ex (a - b) := by
  rw [← ex_neg, ← ex_add, sub_eq_add_neg]

/-- Bucket count: among residues that are pairwise `N ∣ m (y - y')`, there are at most `|m|`. -/
lemma card_filter_dvd_le {N : ℕ} (hN : 0 < N) {m : ℤ} (hm : m ≠ 0) (Y : Finset ℕ)
    (hinj : Set.InjOn (· % N) Y) (y : ℕ) :
    (Y.filter (fun y' : ℕ => (N : ℤ) ∣ m * ((y : ℤ) - (y' : ℤ)))).card ≤ m.natAbs := by
  set S := Y.filter (fun y' : ℕ => (N : ℤ) ∣ m * ((y : ℤ) - (y' : ℤ)))
  set M := m.natAbs with hM
  have hMpos : 0 < M := Int.natAbs_pos.mpr hm
  have hMz : (M : ℤ) = |m| := Int.natCast_natAbs m
  calc S.card ≤ (range M).card := by
        apply Finset.card_le_card_of_injOn (fun y' => (y' % N) * M / N)
        · intro y' _
          simp only [coe_range, Set.mem_Iio]
          rw [Nat.div_lt_iff_lt_mul hN]
          calc y' % N * M < N * M := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hN) hMpos
            _ = M * N := mul_comm _ _
        · intro y₁ hy₁ y₂ hy₂ hb
          replace hy₁ := Finset.mem_filter.mp (Finset.mem_coe.mp hy₁)
          replace hy₂ := Finset.mem_filter.mp (Finset.mem_coe.mp hy₂)
          by_contra hne
          set r₁ := y₁ % N with hr₁
          set r₂ := y₂ % N with hr₂
          have hr : r₁ ≠ r₂ := fun h => hne (hinj hy₁.1 hy₂.1 h)
          have e1 : (y₁ : ℤ) = (r₁ : ℤ) + (N : ℤ) * ((y₁ / N : ℕ) : ℤ) := by
            have h := Nat.mod_add_div y₁ N
            rw [← hr₁] at h
            exact_mod_cast h.symm
          have e2 : (y₂ : ℤ) = (r₂ : ℤ) + (N : ℤ) * ((y₂ / N : ℕ) : ℤ) := by
            have h := Nat.mod_add_div y₂ N
            rw [← hr₂] at h
            exact_mod_cast h.symm
          -- `N ∣ m (r₁ - r₂)`
          have hd : (N : ℤ) ∣ m * ((r₁ : ℤ) - (r₂ : ℤ)) := by
            have h1 := dvd_sub hy₂.2 hy₁.2
            have hid : m * ((r₁ : ℤ) - (r₂ : ℤ)) = (m * ((y : ℤ) - y₂) - m * ((y : ℤ) - y₁)) -
                (N : ℤ) * (m * (((y₁ / N : ℕ) : ℤ) - ((y₂ / N : ℕ) : ℤ))) := by
              rw [e1, e2]; ring
            rw [hid]
            exact dvd_sub h1 (dvd_mul_right _ _)
          have hne0 : m * ((r₁ : ℤ) - (r₂ : ℤ)) ≠ 0 := by
            apply mul_ne_zero hm
            intro h0; apply hr; exact_mod_cast sub_eq_zero.mp h0
          have hle := Int.le_of_dvd (abs_pos.mpr hne0) ((dvd_abs _ _).mpr hd)
          -- same bucket: `|r₁ M - r₂ M| < N`
          have hq := Nat.div_add_mod (r₁ * M) N
          have hq2 := Nat.div_add_mod (r₂ * M) N
          simp only at hb
          rw [hb] at hq
          have hm1 := Nat.mod_lt (r₁ * M) hN
          have hm2 := Nat.mod_lt (r₂ * M) hN
          have hq' : (N : ℤ) * ((r₂ * M / N : ℕ) : ℤ) + ((r₁ * M % N : ℕ) : ℤ) = (r₁ : ℤ) * M := by
            exact_mod_cast hq
          have hq2' : (N : ℤ) * ((r₂ * M / N : ℕ) : ℤ) + ((r₂ * M % N : ℕ) : ℤ) = (r₂ : ℤ) * M := by
            exact_mod_cast hq2
          have hm1' : ((r₁ * M % N : ℕ) : ℤ) < N := by exact_mod_cast hm1
          have hm2' : ((r₂ * M % N : ℕ) : ℤ) < N := by exact_mod_cast hm2
          have hm1'' : (0 : ℤ) ≤ ((r₁ * M % N : ℕ) : ℤ) := Int.natCast_nonneg _
          have hm2'' : (0 : ℤ) ≤ ((r₂ * M % N : ℕ) : ℤ) := Int.natCast_nonneg _
          have habs : |(r₁ : ℤ) * M - (r₂ : ℤ) * M| < N := by
            rw [abs_lt]; constructor <;> linarith
          have hEq : |m * ((r₁ : ℤ) - (r₂ : ℤ))| = |(r₁ : ℤ) * M - (r₂ : ℤ) * M| := by
            rw [show (r₁ : ℤ) * M - (r₂ : ℤ) * M = (M : ℤ) * ((r₁ : ℤ) - (r₂ : ℤ)) by ring,
              abs_mul, abs_mul, hMz, abs_abs]
          linarith
    _ = M := card_range _

/-- `Σ_{u<N} ‖Σ_y e(m u y / N)‖² ≤ N |Y| |m|`. -/
lemma sum_norm_sq_char_le {N : ℕ} (hN : 0 < N) {m : ℤ} (hm : m ≠ 0) (Y : Finset ℕ)
    (hinj : Set.InjOn (· % N) Y) :
    ∑ u ∈ range N, ‖∑ y ∈ Y, ex (m * u * y / N)‖ ^ 2 ≤ N * Y.card * m.natAbs := by
  have hexpand : ∀ u : ℕ, ‖∑ y ∈ Y, ex (m * u * y / N)‖ ^ 2 =
      (∑ y ∈ Y, ∑ y' ∈ Y, ex (u * (m * ((y : ℤ) - (y' : ℤ)) : ℤ) / N)).re := by
    intro u
    rw [norm_sum_sq_eq]
    congr 1
    apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro y' _
    rw [ex_mul_conj]; congr 1; push_cast; ring
  simp_rw [hexpand]
  rw [← Complex.re_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := range N)]
  simp_rw [sum_ex_div N hN]
  have hcount : ∀ y ∈ Y, (∑ y' ∈ Y, (if (N : ℤ) ∣ m * ((y : ℤ) - (y' : ℤ)) then (N : ℂ) else 0)).re ≤
      N * m.natAbs := by
    intro y _
    rw [← Finset.sum_filter, Complex.re_sum]
    simp only [Complex.natCast_re, Finset.sum_const, nsmul_eq_mul]
    have := card_filter_dvd_le hN hm Y hinj y
    have h2 : ((Y.filter (fun y' : ℕ => (N : ℤ) ∣ m * ((y : ℤ) - (y' : ℤ)))).card : ℝ) ≤ m.natAbs := by
      exact_mod_cast this
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  rw [Complex.re_sum]
  calc ∑ y ∈ Y, (∑ y' ∈ Y, (if (N : ℤ) ∣ m * ((y : ℤ) - (y' : ℤ)) then (N : ℂ) else 0)).re
      ≤ ∑ y ∈ Y, ((N : ℝ) * m.natAbs) := Finset.sum_le_sum hcount
    _ = N * Y.card * m.natAbs := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Replacing `Bʷ` by its residue and reindexing by the injective map `w ↦ Bʷ mod N`. -/
lemma sum_w_norm_sq_le {N S B : ℕ} (hN : 0 < N) {m : ℤ} (hm : m ≠ 0) (Y : Finset ℕ)
    (hinj : Set.InjOn (· % N) Y)
    (hB : Set.InjOn (fun w : ℕ => ((B : ZMod N) ^ w)) (Set.Iio S)) :
    ∑ w ∈ range S, ‖∑ y ∈ Y, ex (m * ((B : ℝ) ^ w) * y / N)‖ ^ 2 ≤ N * Y.card * m.natAbs := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hres : ∀ w : ℕ, ‖∑ y ∈ Y, ex (m * ((B : ℝ) ^ w) * y / N)‖ =
      ‖∑ y ∈ Y, ex (m * ((B ^ w % N : ℕ) : ℝ) * y / N)‖ := by
    intro w
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    have hdiv := Nat.mod_add_div (B ^ w) N
    set q := B ^ w / N with hq
    set r := B ^ w % N with hr
    have h' : ((B : ℝ) ^ w) = (r : ℝ) + N * (q : ℝ) := by
      exact_mod_cast hdiv.symm
    have : (m : ℝ) * ((B : ℝ) ^ w) * y / N = m * (r : ℝ) * y / N + ((m * (q : ℤ) * y : ℤ) : ℝ) := by
      rw [h']; push_cast; field_simp
    rw [this, ex_add_intCast]
  simp_rw [hres]
  set f : ℕ → ℝ := fun u => ‖∑ y ∈ Y, ex (m * (u : ℝ) * y / N)‖ ^ 2 with hf
  have hinjU : Set.InjOn (fun w => B ^ w % N) (range S : Set ℕ) := by
    intro w₁ hw₁ w₂ hw₂ h
    apply hB (by simpa using hw₁) (by simpa using hw₂)
    simp only at h ⊢
    rw [← Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff']
    exact h
  calc ∑ w ∈ range S, f (B ^ w % N)
      = ∑ u ∈ (range S).image (fun w => B ^ w % N), f u := (Finset.sum_image hinjU).symm
    _ ≤ ∑ u ∈ range N, f u := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro u hu
          obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hu
          exact Finset.mem_range.mpr (Nat.mod_lt _ hN)
        · intro u _ _; positivity
    _ ≤ N * Y.card * m.natAbs := sum_norm_sq_char_le hN hm Y hinj

/-- Cauchy–Schwarz over `w`: `‖Σ_w σ_w(m)‖ ≤ N √(|Y| |m|)`. -/
lemma norm_sum_w_le {N S B : ℕ} (hN : 0 < N) (hSN : S ≤ N) {m : ℤ} (hm : m ≠ 0) (Y : Finset ℕ)
    (hinj : Set.InjOn (· % N) Y)
    (hB : Set.InjOn (fun w : ℕ => ((B : ZMod N) ^ w)) (Set.Iio S)) (γ : ℝ) :
    ‖∑ w ∈ range S, ∑ y ∈ Y, ex (m * ((B : ℝ) ^ w * ((y : ℝ) / N + γ)))‖ ≤
      N * Real.sqrt (Y.card * m.natAbs) := by
  have hfac : ∀ w, ‖∑ y ∈ Y, ex (m * ((B : ℝ) ^ w * ((y : ℝ) / N + γ)))‖ =
      ‖∑ y ∈ Y, ex (m * ((B : ℝ) ^ w) * y / N)‖ := by
    intro w
    have : ∑ y ∈ Y, ex (m * ((B : ℝ) ^ w * ((y : ℝ) / N + γ))) =
        ex (m * (B : ℝ) ^ w * γ) * ∑ y ∈ Y, ex (m * ((B : ℝ) ^ w) * y / N) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [← ex_add]
      congr 1
      ring
    rw [this, norm_mul, norm_ex, one_mul]
  set a : ℕ → ℝ := fun w => ‖∑ y ∈ Y, ex (m * ((B : ℝ) ^ w) * y / N)‖ with ha
  have hsum : ∑ w ∈ range S, a w ≤ N * Real.sqrt (Y.card * m.natAbs) := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := range S) (f := a)
    rw [card_range] at hcs
    have hsq := sum_w_norm_sq_le hN hm Y hinj hB
    have hbound : (∑ w ∈ range S, a w) ^ 2 ≤ ((N : ℝ) * Real.sqrt (Y.card * m.natAbs)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      calc (∑ w ∈ range S, a w) ^ 2 ≤ S * ∑ w ∈ range S, a w ^ 2 := hcs
        _ ≤ N * (N * Y.card * m.natAbs) := by
            apply mul_le_mul (by exact_mod_cast hSN) hsq (by positivity) (by positivity)
        _ = (N : ℝ) ^ 2 * (Y.card * m.natAbs) := by ring
    exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun w _ => norm_nonneg _) (by positivity)
      two_ne_zero).mp hbound
  calc ‖∑ w ∈ range S, ∑ y ∈ Y, ex (m * ((B : ℝ) ^ w * ((y : ℝ) / N + γ)))‖
      ≤ ∑ w ∈ range S, ‖∑ y ∈ Y, ex (m * ((B : ℝ) ^ w * ((y : ℝ) / N + γ)))‖ := norm_sum_le _ _
    _ = ∑ w ∈ range S, a w := by
        apply Finset.sum_congr rfl; intro w _; rw [hfac]
    _ ≤ N * Real.sqrt (Y.card * m.natAbs) := hsum

lemma sum_comm4 {α β γ δ M : Type*} [AddCommMonoid M] (A : Finset α) (B : Finset β)
    (C : Finset γ) (D : Finset δ) (f : α → β → γ → δ → M) :
    ∑ w ∈ A, ∑ y ∈ B, ∑ a ∈ C, ∑ a' ∈ D, f w y a a' =
      ∑ a ∈ C, ∑ a' ∈ D, ∑ w ∈ A, ∑ y ∈ B, f w y a a' := by
  simp_rw [← Finset.sum_product' (s := C) (t := D)]
  rw [Finset.sum_congr rfl (fun w _ => Finset.sum_comm)]
  rw [Finset.sum_comm]

/-- **Discrete core.** Some point `Bʷ (y/N + γ)` (`w < S`, `y ∈ Y`) is within `ε/2` of an
integer. -/
theorem discrete_core {p ℓ S H B : ℕ} (hp : 5 ≤ p) (hS : S = (p - 1) * p ^ (ℓ - 1)) (hℓ : 1 ≤ ℓ)
    {ε : ℝ} (hε : 0 < ε) (hH : 2 ≤ (H : ℝ) * ε ^ 2)
    (hB : Set.InjOn (fun w : ℕ => ((B : ZMod (p ^ ℓ)) ^ w)) (Set.Iio S))
    (γ : ℝ) (Y : Finset ℕ) (hinj : Set.InjOn (· % p ^ ℓ) Y) (hY : 25 * H ^ 3 < 4 * Y.card) :
    ∃ w < S, ∃ y ∈ Y, |(B : ℝ) ^ w * ((y : ℝ) / ((p ^ ℓ : ℕ) : ℝ) + γ) -
      round ((B : ℝ) ^ w * ((y : ℝ) / ((p ^ ℓ : ℕ) : ℝ) + γ))| < ε / 2 := by
  by_contra hcon
  push Not at hcon
  set N := p ^ ℓ with hNdef
  have hN : 0 < N := by positivity
  have hpl : p ^ ℓ = p * p ^ (ℓ - 1) := by rw [← pow_succ']; congr 1; omega
  have hSN : S ≤ N := by
    rw [hS, hNdef, hpl]; exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)
  have h5S : 4 * N ≤ 5 * S := by
    rw [hS, hNdef, hpl]
    have h4 : 4 * p ≤ 5 * (p - 1) := by omega
    calc 4 * (p * p ^ (ℓ - 1)) = (4 * p) * p ^ (ℓ - 1) := by ring
      _ ≤ (5 * (p - 1)) * p ^ (ℓ - 1) := Nat.mul_le_mul_right _ h4
      _ = 5 * ((p - 1) * p ^ (ℓ - 1)) := by ring
  have hHpos : 0 < H := by
    rcases Nat.eq_zero_or_pos H with h0 | h0
    · rw [h0] at hH; simp at hH; linarith
    · exact h0
  have hYpos : 0 < Y.card := by omega
  set t : ℕ → ℕ → ℝ := fun w y => (B : ℝ) ^ w * ((y : ℝ) / N + γ) with ht
  -- upper bound on the kernel sum
  have hterm : ∀ w ∈ range S, ∀ y ∈ Y, ‖∑ a ∈ range H, ex (a * t w y)‖ ^ 2 ≤ (1 / ε) ^ 2 := by
    intro w hw y hy
    have hfar := hcon w (Finset.mem_range.mp hw) y hy
    have h := norm_geom_ex_le (x := t w y) (δ := ε / 2) (by positivity) hfar H
    rw [show 1 / (2 * (ε / 2)) = 1 / ε by field_simp] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hup : ∑ w ∈ range S, ∑ y ∈ Y, ‖∑ a ∈ range H, ex (a * t w y)‖ ^ 2 ≤
      S * Y.card * (1 / ε) ^ 2 := by
    calc _ ≤ ∑ w ∈ range S, ∑ y ∈ Y, (1 / ε) ^ 2 :=
          Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun y hy => hterm w hw y hy
      _ = S * Y.card * (1 / ε) ^ 2 := by simp [Finset.sum_const, card_range]; ring
  -- expansion of the kernel
  have hexp : ∑ w ∈ range S, ∑ y ∈ Y, ‖∑ a ∈ range H, ex (a * t w y)‖ ^ 2 =
      ∑ a ∈ range H, ∑ a' ∈ range H,
        (∑ w ∈ range S, ∑ y ∈ Y, ex ((((a : ℤ) - (a' : ℤ) : ℤ) : ℝ) * t w y)).re := by
    have h1 : ∀ w y, ‖∑ a ∈ range H, ex (a * t w y)‖ ^ 2 =
        ∑ a ∈ range H, ∑ a' ∈ range H, (ex ((((a : ℤ) - (a' : ℤ) : ℤ) : ℝ) * t w y)).re := by
      intro w y
      rw [norm_sum_sq_eq, Complex.re_sum]
      apply Finset.sum_congr rfl; intro a _
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl; intro a' _
      rw [ex_mul_conj]; congr 2; push_cast; ring
    simp_rw [h1]
    rw [sum_comm4]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro a' _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro w _
    rw [Complex.re_sum]
  -- lower bound, term by term
  set c : ℝ := N * Real.sqrt (Y.card * H) with hc
  have hc0 : 0 ≤ c := by positivity
  have hlow : ∀ a ∈ range H, ∀ a' ∈ range H,
      (if a = a' then (S : ℝ) * Y.card else 0) - c ≤
        (∑ w ∈ range S, ∑ y ∈ Y, ex ((((a : ℤ) - (a' : ℤ) : ℤ) : ℝ) * t w y)).re := by
    intro a ha a' ha'
    by_cases haa : a = a'
    · subst haa
      have hX : (∑ w ∈ range S, ∑ y ∈ Y, ex ((((a : ℤ) - (a : ℤ) : ℤ) : ℝ) * t w y)) =
          (S : ℂ) * Y.card := by
        simp only [sub_self, Int.cast_zero, zero_mul, ex_zero, Finset.sum_const, card_range,
          nsmul_eq_mul, mul_one]
      rw [hX, ite_eq_left rfl]
      have hre : ((S : ℂ) * (Y.card : ℂ)).re = (S : ℝ) * Y.card := by
        rw [← Nat.cast_mul, Complex.natCast_re, Nat.cast_mul]
      rw [hre]; linarith
    · simp only [haa, ite_false, zero_sub]
      set m : ℤ := (a : ℤ) - (a' : ℤ) with hmdef
      have hm : m ≠ 0 := by intro h; apply haa; omega
      have hmH : m.natAbs ≤ H := by
        have h1 := Finset.mem_range.mp ha
        have h2 := Finset.mem_range.mp ha'
        omega
      have hnorm := norm_sum_w_le hN hSN hm Y hinj hB γ
      have h2 : Real.sqrt (Y.card * m.natAbs) ≤ Real.sqrt (Y.card * H) := by
        apply Real.sqrt_le_sqrt
        have : (m.natAbs : ℝ) ≤ H := by exact_mod_cast hmH
        nlinarith [(Nat.cast_nonneg Y.card : (0 : ℝ) ≤ Y.card)]
      have h3 := neg_le_of_abs_le (Complex.abs_re_le_norm
        (∑ w ∈ range S, ∑ y ∈ Y, ex ((m : ℝ) * t w y)))
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      calc -c ≤ -(N * Real.sqrt (Y.card * m.natAbs)) := by
            rw [hc]; nlinarith
        _ ≤ -‖∑ w ∈ range S, ∑ y ∈ Y, ex ((m : ℝ) * t w y)‖ := by
            simp only [ht] at hnorm ⊢; linarith
        _ ≤ _ := h3
  have hinner : ∀ a ∈ range H, ∑ a' ∈ range H, ((if a = a' then (S : ℝ) * Y.card else 0) - c) =
      S * Y.card - H * c := by
    intro a ha
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, ite_eq_left ha, Finset.sum_const, card_range,
      nsmul_eq_mul]
  have hsumlow : (H : ℝ) * (S * Y.card) - (H : ℝ) ^ 2 * c ≤
      ∑ a ∈ range H, ∑ a' ∈ range H,
        (∑ w ∈ range S, ∑ y ∈ Y, ex ((((a : ℤ) - (a' : ℤ) : ℤ) : ℝ) * t w y)).re := by
    calc (H : ℝ) * (S * Y.card) - (H : ℝ) ^ 2 * c = ∑ a ∈ range H, ((S : ℝ) * Y.card - H * c) := by
          rw [Finset.sum_const, card_range, nsmul_eq_mul]; ring
      _ = ∑ a ∈ range H, ∑ a' ∈ range H, ((if a = a' then (S : ℝ) * Y.card else 0) - c) := by
          apply Finset.sum_congr rfl; intro a ha; rw [hinner a ha]
      _ ≤ _ := Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun a' ha' => hlow a ha a' ha'
  -- combine
  have hHε : (1 / ε) ^ 2 ≤ (H : ℝ) / 2 := by
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hYr : (0 : ℝ) < Y.card := by exact_mod_cast hYpos
  have hSr : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmain : (H : ℝ) * (S * Y.card) - (H : ℝ) ^ 2 * c ≤ S * Y.card * ((H : ℝ) / 2) := by
    calc (H : ℝ) * (S * Y.card) - (H : ℝ) ^ 2 * c ≤ S * Y.card * (1 / ε) ^ 2 := by
          rw [← hexp] at hsumlow; linarith
      _ ≤ S * Y.card * ((H : ℝ) / 2) := by
          apply mul_le_mul_of_nonneg_left hHε; positivity
  -- `S Y ≤ 2 H c`
  have h1 : (S : ℝ) * Y.card ≤ 2 * H * c := by nlinarith
  have hc2 : c ^ 2 = (N : ℝ) ^ 2 * (Y.card * H) := by
    rw [hc, mul_pow, Real.sq_sqrt (by positivity)]
  have h2 : ((S : ℝ) * Y.card) ^ 2 ≤ (2 * H * c) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  simp only [mul_pow] at h2
  rw [hc2] at h2
  have h3 : (S : ℝ) ^ 2 * Y.card ≤ 4 * (H : ℝ) ^ 3 * N ^ 2 := by
    have : (S : ℝ) ^ 2 * Y.card * Y.card ≤ 4 * (H : ℝ) ^ 3 * N ^ 2 * Y.card := by nlinarith
    exact le_of_mul_le_mul_right this hYr
  have h5 : (4 : ℝ) * N ≤ 5 * S := by exact_mod_cast h5S
  have h5sq : (16 : ℝ) * N ^ 2 ≤ 25 * S ^ 2 := by
    have := mul_le_mul h5 h5 (by positivity) (by positivity)
    nlinarith
  have h6 : (16 : ℝ) * N ^ 2 * Y.card ≤ 25 * S ^ 2 * Y.card :=
    mul_le_mul_of_nonneg_right h5sq hYr.le
  have h7 : (16 : ℝ) * Y.card * N ^ 2 ≤ 100 * (H : ℝ) ^ 3 * N ^ 2 := by nlinarith
  have h8 : (16 : ℝ) * Y.card ≤ 100 * (H : ℝ) ^ 3 :=
    le_of_mul_le_mul_right h7 (by positivity)
  have h9 : (25 : ℝ) * (H : ℝ) ^ 3 < 4 * Y.card := by exact_mod_cast hY
  linarith

end Green41

/- ## Section: `MinorArc` -/

/-
# The minor-arc proposition (blueprint §8)

Chain Step A (§4), the counting of labels (§5), the digit pigeonhole (§6) and the
discrete core (§7) to hit the stripe. This file proves the generic statement for a digit
prime `π` with multiplier prime `ρ`. `KL57.lean` instantiates it with `(P, Q)` and `(Q, P)`
and fixes the parameters.
-/

namespace Green41

open Complex ComplexConjugate Finset

/- ## Arithmetic of the fiber -/

/-- The value `val(X bʷ y) / p^s` modulo `1`, read on a fiber over `λ` mod `p^(s-ℓ)`. -/
lemma frac_on_fiber {p n s ℓ : ℕ} (hp : 0 < p) (hsn : s ≤ n) (hℓs : ℓ ≤ s) (X B yv lam w : ℕ)
    (hlam : yv % p ^ (s - ℓ) = lam) :
    ∃ k : ℤ, ((X * B ^ w * yv % p ^ n : ℕ) : ℝ) / (p : ℝ) ^ s =
      (B : ℝ) ^ w * (((X * (yv % p ^ s / p ^ (s - ℓ)) : ℕ) : ℝ) / ((p ^ ℓ : ℕ) : ℝ) +
        ((X * lam : ℕ) : ℝ) / (p : ℝ) ^ s) + k := by
  set r := yv % p ^ s with hr
  set z := r / p ^ (s - ℓ) with hz
  set Q := yv / p ^ s with hQ
  set M := X * B ^ w * yv with hM
  have hdvd : p ^ (s - ℓ) ∣ p ^ s := pow_dvd_pow p (Nat.sub_le s ℓ)
  have hrl : r % p ^ (s - ℓ) = lam := by rw [hr, Nat.mod_mod_of_dvd _ hdvd, hlam]
  have hr1 : r = lam + p ^ (s - ℓ) * z := by
    have := Nat.mod_add_div r (p ^ (s - ℓ)); rw [hrl] at this; exact this.symm
  have hy1 : yv = r + p ^ s * Q := by
    have := Nat.mod_add_div yv (p ^ s); exact this.symm
  have hM1 : M % p ^ n + p ^ n * (M / p ^ n) = M := Nat.mod_add_div M (p ^ n)
  set qM := M / p ^ n with hqM
  refine ⟨(X * B ^ w * Q : ℕ) - (p ^ (n - s) * qM : ℕ), ?_⟩
  have hpr : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hps : (p : ℝ) ^ s = (p : ℝ) ^ (s - ℓ) * (p : ℝ) ^ ℓ := by
    rw [← pow_add, Nat.sub_add_cancel hℓs]
  have hpn : (p : ℝ) ^ n = (p : ℝ) ^ s * (p : ℝ) ^ (n - s) := by
    rw [← pow_add, Nat.add_sub_cancel' hsn]
  have eM : ((M % p ^ n : ℕ) : ℝ) = (M : ℝ) - (p : ℝ) ^ n * (qM : ℝ) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hM1
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at this
    linarith
  have eMv : (M : ℝ) = X * (B : ℝ) ^ w * ((lam : ℝ) + (p : ℝ) ^ (s - ℓ) * z + (p : ℝ) ^ s * Q) := by
    rw [hM, hy1, hr1]; push_cast; ring
  rw [eM, eMv]
  push_cast
  rw [hpn, hps]
  field_simp
  ring

/-- Multiplication by a unit is injective on residues `< p^ℓ`. -/
lemma mul_mod_inj {p ℓ X z₁ z₂ : ℕ} (hX : Nat.Coprime X p) (h1 : z₁ < p ^ ℓ) (h2 : z₂ < p ^ ℓ)
    (h : X * z₁ % p ^ ℓ = X * z₂ % p ^ ℓ) : z₁ = z₂ := by
  have hc : Nat.gcd (p ^ ℓ) X = 1 := by
    rw [Nat.gcd_comm]; exact (Nat.Coprime.pow_right ℓ hX)
  have hmod : z₁ ≡ z₂ [MOD p ^ ℓ] := Nat.ModEq.cancel_left_of_coprime hc h
  unfold Nat.ModEq at hmod
  rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod

/- ## The generic minor-arc theorem -/

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

lemma isUnit_Xfac {ρ : GaussianInt} (hρ2 : ¬ π ∣ star ρ) {n α β j : ℕ} (hn : 0 < n) :
    IsUnit (hπ.Xfac ρ n α β j) := by
  unfold Xfac
  have h1 := hπ.isUnit_re n
  have h2 : IsUnit (hπ.ψ n (star π)) := (hπ.isUnit_ψ_iff hn _).mpr hπ.not_dvd_star
  have h2' : IsUnit ((hπ.ψ n (star π))⁻¹) :=
    IsUnit.of_mul_eq_one_right _ (ZMod.mul_inv_of_unit _ h2)
  have h3 : IsUnit (hπ.ψ n (star ρ)) := (hπ.isUnit_ψ_iff hn _).mpr hρ2
  exact ((h1.mul (h2'.pow j)).mul (h2.pow _)).mul (h3.pow _)

lemma coprime_val_of_isUnit {n : ℕ} (hn : 0 < n) {X : ZMod (p ^ n)} (hX : IsUnit X) :
    Nat.Coprime X.val p := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  rw [← ZMod.natCast_zmod_val X, ZMod.isUnit_iff_coprime] at hX
  exact Nat.Coprime.coprime_dvd_right (dvd_pow_self p hn.ne') hX

omit hπ in
lemma norm_rotOf {ρ : GaussianInt} (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0) :
    ‖(ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)‖ = 1 := by
  have h : ‖((star ρ : GaussianInt) : ℂ)‖ = ‖(ρ : ℂ)‖ := by
    rw [GaussianInt.toComplex_star, Complex.norm_conj]
  rw [norm_div, h, div_self]
  rw [← h]; exact norm_ne_zero_iff.mpr hρ0

/-- **Minor arcs, generic form.** -/
theorem minor_arc_core (hp5 : 5 ≤ p) {ρ : GaussianInt}
    (hρ1 : ¬ π ∣ ρ) (hρ2 : ¬ π ∣ star ρ) (hρ4 : ¬ star π ∣ star ρ)
    (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0)
    {n α β A L ℓ S H : ℕ} (hL : 0 < L) (hℓ : ℓ = 4 * L) (hS : S = (p - 1) * p ^ (ℓ - 1))
    (hSβ : S ≤ β) (hnA : n = 8 * (A + ℓ)) (hα : α = n - A)
    (hordA : orderOf (hπ.mult (star ρ) (n + 4)) = (p - 1) * p ^ (n + 3))
    (hordB : orderOf (((hπ.mult ρ n).val : ℕ) : ZMod (p ^ ℓ)) = S)
    {ε : ℝ} (hε : 0 < ε) (hH : 2 ≤ (H : ℝ) * ε ^ 2) (hHL : 25 * H ^ 3 < 4 * p ^ L)
    (hg : Real.sqrt 2 * ‖cellGen π ρ n α β‖ ≤ ε / 2)
    (w : ℂ) {N₀ a₁ b₁ a₂ b₂ v E : ℕ} (ha₁ : a₁ ≤ N₀) (hb₁ : b₁ ≤ N₀) (ha₂ : a₂ ≤ N₀)
    (hb₂ : b₂ ≤ N₀) (hE : (p - 1) * p ^ (n + 3) + β ≤ E) {q₂ : GaussianInt}
    (hq₂ : ¬ star π ∣ q₂)
    (he' : ‖(((star π) ^ v * (star ρ) ^ E * q₂ : GaussianInt) : ℂ) -
        (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
            ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
          ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
            ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ <
        21 / 50 * ‖cellGen π ρ n α β‖) :
    ∃ a b : ℕ, a ≤ N₀ + v + (A + 4) + n ∧ b ≤ N₀ + (p - 1) * p ^ (n + 3) + S ∧
      ∃ k : ℤ, |(((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a *
        ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b * w).re - k| < ε := by
  set σ : ℂ := (π : ℂ) / ((star π : GaussianInt) : ℂ) with hσ
  set τ : ℂ := (ρ : ℂ) / ((star ρ : GaussianInt) : ℂ) with hτ
  set g := cellGen π ρ n α β with hg_def
  set T := (p - 1) * p ^ (n + 3) with hT
  set j := v + (n - α + 4) with hj
  set q : ℂ := (((star π) ^ v * (star ρ) ^ E * q₂ : GaussianInt) : ℂ) with hq
  set r : ℂ := σ ^ a₁ * τ ^ b₁ - σ ^ a₂ * τ ^ b₂ with hr
  set e' : ℂ := r * w - q with he'_def
  have he'n : ‖e'‖ < 21 / 50 * ‖g‖ := by rw [he'_def, norm_sub_rev]; exact he'
  have hrw : r * w = q + e' := by rw [he'_def]; ring
  have hn0 : 0 < n := by omega
  have hαn : α ≤ n := by omega
  have hp0 : 0 < p := by omega
  -- Step A
  have hA : ∀ l : ZMod (p ^ n), ∃ t < T, hπ.label ρ n α β (σ ^ j * τ ^ t * (q + e')) = l :=
    fun l => hπ.stepA hp5 hρ1 hρ4 hρ0 hαn hordA hE hq₂ he'n l
  -- the orbit
  set Z : Finset ℂ := ((range (N₀ + j + 1)) ×ˢ (range (N₀ + T + 1))).image
    (fun ab => σ ^ ab.1 * τ ^ ab.2 * w) with hZ
  have hmemZ : ∀ a b, a ≤ N₀ + j → b ≤ N₀ + T → σ ^ a * τ ^ b * w ∈ Z := by
    intro a b ha hb
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, rfl⟩
  have hall : ∀ l : ZMod (p ^ n), ∃ x ∈ Z, ∃ x' ∈ Z, hπ.label ρ n α β (x - x') = l := by
    intro l
    obtain ⟨t, ht, hl⟩ := hA l
    refine ⟨σ ^ (j + a₁) * τ ^ (t + b₁) * w, hmemZ _ _ (by omega) (by omega),
      σ ^ (j + a₂) * τ ^ (t + b₂) * w, hmemZ _ _ (by omega) (by omega), ?_⟩
    rw [← hl, ← hrw]
    congr 1
    rw [hr]; ring
  -- counting
  have hcount := hπ.pow_le_four_mul_card_sq ρ n α β Z hall
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  set Yl := Z.image (hπ.label ρ n α β) with hYl
  set Yn : Finset ℕ := Yl.image ZMod.val with hYn
  have hYncard : Yn.card = Yl.card := Finset.card_image_of_injective _ (ZMod.val_injective (p ^ n))
  have hYnlt : ∀ y ∈ Yn, y < p ^ n := by
    intro y hy; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy; exact ZMod.val_lt x
  -- digit pigeonhole
  obtain ⟨s, hs1, hs2, lam, hfib⟩ := digit_pigeonhole hp5 hL (by rw [hnA, hℓ]) Yn hYnlt
    (by rw [hYncard]; exact hcount)
  rw [← hℓ] at hs1 hfib
  set F := digitFiber p s ℓ lam Yn with hF
  set j' := n - s with hj'
  set X := hπ.Xfac ρ n α β j' with hXdef
  have hXu : IsUnit X := hπ.isUnit_Xfac hρ2 hn0
  have hXc : Nat.Coprime X.val p := hπ.coprime_val_of_isUnit hn0 hXu
  have hX0 : X.val ≠ 0 := by
    intro h0; rw [h0, Nat.coprime_zero_left] at hXc; omega
  have hd : p ^ (s - ℓ) ∣ p ^ s := pow_dvd_pow p (Nat.sub_le s ℓ)
  have hFmem : ∀ r ∈ F, ∃ y ∈ Yn, y % p ^ (s - ℓ) = lam ∧ r = y % p ^ s := by
    intro r hr
    simp only [hF, digitFiber, Finset.mem_image, Finset.mem_filter] at hr
    obtain ⟨y, ⟨hy, hyl⟩, rfl⟩ := hr
    exact ⟨y, hy, hyl, rfl⟩
  have hzlt : ∀ r ∈ F, r / p ^ (s - ℓ) < p ^ ℓ := by
    intro r hr
    obtain ⟨y, _, _, rfl⟩ := hFmem r hr
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' (by omega : ℓ ≤ s)]
    exact Nat.mod_lt _ (by positivity)
  have hrinj : Set.InjOn (fun r => r / p ^ (s - ℓ)) F := by
    intro r₁ h₁ r₂ h₂ h
    obtain ⟨y₁, _, hy₁, rfl⟩ := hFmem r₁ h₁
    obtain ⟨y₂, _, hy₂, rfl⟩ := hFmem r₂ h₂
    have e1 := Nat.mod_add_div (y₁ % p ^ s) (p ^ (s - ℓ))
    have e2 := Nat.mod_add_div (y₂ % p ^ s) (p ^ (s - ℓ))
    rw [Nat.mod_mod_of_dvd _ hd, hy₁] at e1
    rw [Nat.mod_mod_of_dvd _ hd, hy₂] at e2
    simp only at h
    rw [← e1, ← e2, h]
  set Yd : Finset ℕ := F.image (fun r => X.val * (r / p ^ (s - ℓ))) with hYd
  have hYdinj : Set.InjOn (fun r => X.val * (r / p ^ (s - ℓ))) F := by
    intro r₁ h₁ r₂ h₂ h
    apply hrinj h₁ h₂
    simp only at h ⊢
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hX0) h
  have hYdcard : Yd.card = F.card := Finset.card_image_of_injOn hYdinj
  have hYdmod : Set.InjOn (· % p ^ ℓ) Yd := by
    intro y₁ h₁ y₂ h₂ h
    obtain ⟨r₁, hr₁, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨r₂, hr₂, rfl⟩ := Finset.mem_image.mp h₂
    simp only at h ⊢
    rw [mul_mod_inj hXc (hzlt r₁ hr₁) (hzlt r₂ hr₂) h]
  -- discrete core
  set B := (hπ.mult ρ n).val with hB
  have hBinj : Set.InjOn (fun w : ℕ => ((B : ZMod (p ^ ℓ)) ^ w)) (Set.Iio S) := by
    rw [← hordB]; exact pow_injOn_Iio_orderOf
  have hYdbig : 25 * H ^ 3 < 4 * Yd.card := by rw [hYdcard]; omega
  set γ : ℝ := ((X.val * lam : ℕ) : ℝ) / (p : ℝ) ^ s with hγ
  obtain ⟨w', hw', y', hy', hclose⟩ :=
    discrete_core hp5 hS (by omega : 1 ≤ ℓ) hε hH hBinj γ Yd hYdmod hYdbig
  -- unwind the chosen point
  obtain ⟨r₀, hr₀F, rfl⟩ := Finset.mem_image.mp hy'
  obtain ⟨yv, hyvYn, hyvl, rfl⟩ := hFmem r₀ hr₀F
  obtain ⟨yl, hylYl, rfl⟩ := Finset.mem_image.mp hyvYn
  obtain ⟨x, hxZ, rfl⟩ := Finset.mem_image.mp hylYl
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hxZ
  simp only [Finset.mem_product, Finset.mem_range] at hab
  -- the stripe value of the label
  set m := gaussFloor ((σ ^ a * τ ^ b * w) / g) with hm
  have hlabel : hπ.label ρ n α β (σ ^ a * τ ^ b * w) = hπ.ψ n m := rfl
  obtain ⟨k₁, hk₁⟩ := hπ.re_label_formula hρ2 hρ0 (n := n) (α := α) (β := β) (j := j') (w := w')
    hn0 (by omega) (by omega) (by omega) m
  have hnj : n - j' = s := by omega
  rw [hnj] at hk₁
  have hval : (X * hπ.mult ρ n ^ w' * hπ.ψ n m).val =
      X.val * B ^ w' * (hπ.ψ n m).val % p ^ n := by
    rw [← ZMod.val_natCast]
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [hlabel] at hyvl
  obtain ⟨k₂, hk₂⟩ := frac_on_fiber hp0 (by omega : s ≤ n) (by omega : ℓ ≤ s) X.val B
    ((hπ.ψ n m).val) lam w' hyvl
  -- the final exponents
  refine ⟨a + j', b + w', by omega, by omega, ?_⟩
  have hsplit : σ ^ (a + j') * τ ^ (b + w') * w =
      σ ^ j' * τ ^ w' * (g * m) + σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * w - g * m) := by
    rw [pow_add, pow_add]; ring
  have hg0 : g ≠ 0 := by
    simp only [hg_def, cellGen]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hπ.toComplex_star_ne_zero)
      (pow_ne_zero _ hρ0)) (pow_ne_zero _ hπ.toComplex_ne_zero)
  have hnear : ‖σ ^ a * τ ^ b * w - g * m‖ < Real.sqrt 2 * ‖g‖ := by
    have : σ ^ a * τ ^ b * w - g * m = g * ((σ ^ a * τ ^ b * w) / g - m) := by
      field_simp
    rw [this, norm_mul, mul_comm]
    exact mul_lt_mul_of_pos_right (norm_sub_gaussFloor_lt _) (norm_pos_iff.mpr hg0)
  have hunit : ‖σ ^ j' * τ ^ w'‖ = 1 := by
    rw [norm_mul, _root_.norm_pow, _root_.norm_pow, hσ, hπ.norm_sigma, hτ, norm_rotOf hρ0,
      one_pow, one_pow, one_mul]
  have hre2 : |(σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * w - g * m)).re| < ε / 2 := by
    calc |(σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * w - g * m)).re|
        ≤ ‖σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * w - g * m)‖ := Complex.abs_re_le_norm _
      _ = ‖σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * w - g * m)‖ := rfl
      _ = ‖σ ^ a * τ ^ b * w - g * m‖ := by rw [norm_mul, hunit, one_mul]
      _ < Real.sqrt 2 * ‖g‖ := hnear
      _ ≤ ε / 2 := hg
  refine ⟨round ((B : ℝ) ^ w' * (((X.val * ((hπ.ψ n m).val % p ^ s / p ^ (s - ℓ)) : ℕ) : ℝ) /
      ((p ^ ℓ : ℕ) : ℝ) + γ)) + k₁ + k₂, ?_⟩
  rw [← hγ] at hk₂
  have hc2 := hclose
  push_cast at hc2
  rw [hlabel] at hc2
  rw [hsplit, add_re, hk₁, hval, hk₂]
  push_cast
  rw [abs_lt] at hc2 hre2 ⊢
  constructor <;> linarith [hc2.1, hc2.2, hre2.1, hre2.2]

end DigitPrime

end Green41

/- ## Section: `Params` -/

/-
# Parameters for the minor-arc proposition (blueprint §8)

All parameters are functions of the prime `p` and of `K = ⌈1/ε⌉₊`:
`c = clog_p K`, `L = 6c + 4`, `ℓ = 4L`, `S = (p-1) p^(ℓ-1)`, `A = 2S + 2c + 3`,
`n = 8(A + ℓ)`, `α = n - A`, `H = 2K²`.
The key size bound is `n + 4 ≤ 25 · 13^40 · K^24` for `5 ≤ p ≤ 13`.
-/

namespace Green41

/-- `c = clog_p K`. -/
def pc (p K : ℕ) : ℕ := Nat.clog p K
/-- `L = 6c + 4`. -/
def pL (p K : ℕ) : ℕ := 6 * pc p K + 4
/-- `ℓ = 4L`. -/
def pℓ (p K : ℕ) : ℕ := 4 * pL p K
/-- `S = (p - 1) p^(ℓ-1)`. -/
def pS (p K : ℕ) : ℕ := (p - 1) * p ^ (pℓ p K - 1)
/-- `A = 2S + 2c + 3`. -/
def pA (p K : ℕ) : ℕ := 2 * pS p K + 2 * pc p K + 3
/-- `n = 8(A + ℓ)`. -/
def pn (p K : ℕ) : ℕ := 8 * (pA p K + pℓ p K)
/-- `α = n - A`. -/
def pα (p K : ℕ) : ℕ := pn p K - pA p K
/-- `H = 2K²`. -/
def pH (K : ℕ) : ℕ := 2 * K ^ 2

lemma pL_pos (p K : ℕ) : 0 < pL p K := by unfold pL; omega

lemma pℓ_ge (p K : ℕ) : 16 ≤ pℓ p K := by unfold pℓ pL; omega

lemma pn_eq (p K : ℕ) : pn p K = 8 * (pA p K + pℓ p K) := rfl

lemma pα_eq (p K : ℕ) : pα p K = pn p K - pA p K := rfl

lemma pA_le_pn (p K : ℕ) : pA p K ≤ pn p K := by unfold pn; omega

lemma pS_le (p K : ℕ) : pS p K ≤ p ^ pℓ p K := by
  unfold pS
  have hℓ := pℓ_ge p K
  have : p ^ pℓ p K = p * p ^ (pℓ p K - 1) := by
    rw [← pow_succ']; congr 1
  rw [this]
  exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)

lemma pow_pc_le (p K : ℕ) (hp : 2 ≤ p) (hK : 2 ≤ K) : p ^ pc p K ≤ p * K := by
  unfold pc
  rcases Nat.eq_zero_or_pos (Nat.clog p K) with h0 | h0
  · rw [h0, pow_zero]; nlinarith
  · have h1 := Nat.pow_pred_clog_lt_self (by omega : 1 < p) (by omega : 1 < K)
    have : p ^ Nat.clog p K = p * p ^ (Nat.clog p K).pred := by
      rw [← pow_succ']; congr 1; exact (Nat.succ_pred_eq_of_pos h0).symm
    rw [this]
    exact Nat.mul_le_mul_left _ h1.le

lemma le_pow_pc (p K : ℕ) (hp : 2 ≤ p) : K ≤ p ^ pc p K := Nat.le_pow_clog (by omega) K

lemma pow_pL_eq (p K : ℕ) : p ^ pL p K = p ^ 4 * (p ^ pc p K) ^ 6 := by
  unfold pL; rw [← pow_mul, ← pow_add]; ring_nf

lemma pow_pℓ_eq (p K : ℕ) : p ^ pℓ p K = (p ^ pL p K) ^ 4 := by
  unfold pℓ; rw [← pow_mul]; ring_nf

/-- `625 K⁶ ≤ p^L`. -/
lemma pow_pL_ge (p K : ℕ) (hp : 5 ≤ p) : 625 * K ^ 6 ≤ p ^ pL p K := by
  rw [pow_pL_eq]
  have h1 : 625 ≤ p ^ 4 := by
    calc 625 = 5 ^ 4 := by norm_num
      _ ≤ p ^ 4 := Nat.pow_le_pow_left hp 4
  have h2 : K ^ 6 ≤ (p ^ pc p K) ^ 6 := Nat.pow_le_pow_left (le_pow_pc p K (by omega)) 6
  exact Nat.mul_le_mul h1 h2

/-- `25 H³ < 4 p^L`. -/
lemma pH_cube_lt (p K : ℕ) (hp : 5 ≤ p) (hK : 1 ≤ K) : 25 * pH K ^ 3 < 4 * p ^ pL p K := by
  have h := pow_pL_ge p K hp
  unfold pH
  have hK6 : 1 ≤ K ^ 6 := Nat.one_le_pow _ _ hK
  have : 25 * (2 * K ^ 2) ^ 3 = 200 * K ^ 6 := by ring
  rw [this]
  omega

/-- `p^ℓ ≤ p^40 K^24`. -/
lemma pow_pℓ_le (p K : ℕ) (hp : 2 ≤ p) (hK : 2 ≤ K) : p ^ pℓ p K ≤ p ^ 40 * K ^ 24 := by
  rw [pow_pℓ_eq, pow_pL_eq]
  have h := pow_pc_le p K hp hK
  calc (p ^ 4 * (p ^ pc p K) ^ 6) ^ 4 ≤ (p ^ 4 * (p * K) ^ 6) ^ 4 := by
        apply Nat.pow_le_pow_left
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 6)
    _ = p ^ 40 * K ^ 24 := by ring

/-- `n + 4 ≤ 25 p^40 K^24`. -/
lemma pn_add_four_le (p K : ℕ) (hp : 5 ≤ p) (hK : 2 ≤ K) :
    pn p K + 4 ≤ 25 * (p ^ 40 * K ^ 24) := by
  have hS := pS_le p K
  have hℓ := pℓ_ge p K
  have hℓp : 3 * pℓ p K + 3 ≤ p ^ pℓ p K := by
    have h2 : pℓ p K + 1 ≤ 2 ^ pℓ p K := Nat.lt_two_pow_self
    have h4 : 2 ^ pℓ p K * 2 ^ pℓ p K ≤ p ^ pℓ p K := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
    nlinarith
  have hc : pc p K ≤ pℓ p K := by unfold pℓ pL; omega
  have hpl := pow_pℓ_le p K (by omega) hK
  have hA : pA p K + pℓ p K ≤ 3 * p ^ pℓ p K := by unfold pA; omega
  unfold pn
  have : 1 ≤ p ^ pℓ p K := Nat.one_le_pow _ _ (by omega)
  omega

end Green41

/- ## Section: `KL57Proof` -/

/-
# Proof of the Kravitz–Leng interface `KL57With 100`

For `ε < 1/10` put `K = ⌈1/ε⌉₊` and take the parameters of `Params.lean`. Case 1
(`size5 q ≥ size13 q`) uses the digit prime `P` with multiplier `Q`; case 2 uses `Q` with `P`.
Both go through the generic `DigitPrime.minor_arc_core`.
-/

namespace Green41

open Complex ComplexConjugate

/- ## Real bounds -/

lemma rpow_neg_hundred {ε : ℝ} (hε : 0 < ε) : ε ^ (-(100 : ℝ)) = (1 / ε) ^ 100 := by
  rw [Real.rpow_neg hε.le, show (100 : ℝ) = ((100 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    one_div, inv_pow]

lemma ηKL_hundred {ε : ℝ} (hε : 0 < ε) : ηKL 100 ε = (5 : ℝ) ^ (-((1 / ε) ^ 100)) := by
  unfold ηKL; rw [rpow_neg_hundred hε]

lemma ηKL_rpow_neg_five {ε : ℝ} (hε : 0 < ε) :
    ηKL 100 ε ^ (-5 : ℝ) = (5 : ℝ) ^ (5 * (1 / ε) ^ 100) := by
  rw [ηKL_hundred hε, ← Real.rpow_mul (by norm_num)]
  congr 1; ring

/-- The key size bound: `n + 4 ≤ (5/2) (1/ε)^100`. -/
lemma pn_small {p : ℕ} (hp5 : 5 ≤ p) (hp13 : p ≤ 13) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    ((pn p ⌈1 / ε⌉₊ : ℕ) : ℝ) + 4 ≤ 5 / 2 * (1 / ε) ^ 100 := by
  set u := 1 / ε with hu
  have hu10 : 10 < u := by rw [hu, lt_div_iff₀ hε]; linarith
  set K := ⌈u⌉₊ with hK
  have hK1 : (1 : ℝ) < K := lt_of_lt_of_le (by linarith) (Nat.le_ceil u)
  have hK2 : 2 ≤ K := by
    have : 1 < K := by exact_mod_cast hK1
    omega
  have hKu : (K : ℝ) ≤ 2 * u := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ u)
    linarith
  have hnat := pn_add_four_le p K hp5 hK2
  have h1 : ((pn p K + 4 : ℕ) : ℝ) ≤ ((25 * (p ^ 40 * K ^ 24) : ℕ) : ℝ) := by exact_mod_cast hnat
  push_cast at h1
  have hp' : (p : ℝ) ≤ 13 := by exact_mod_cast hp13
  have h2 : (p : ℝ) ^ 40 ≤ 13 ^ 40 := pow_le_pow_left₀ (by positivity) hp' 40
  have h3 : (K : ℝ) ^ 24 ≤ (2 * u) ^ 24 := pow_le_pow_left₀ (by positivity) hKu 24
  have hu76 : (10 : ℝ) ^ 76 ≤ u ^ 76 := pow_le_pow_left₀ (by norm_num) hu10.le 76
  have hnum : (25 : ℝ) * 13 ^ 40 * 2 ^ 24 ≤ 5 / 2 * 10 ^ 76 := by norm_num
  have hu24 : (0 : ℝ) ≤ u ^ 24 := by positivity
  calc ((pn p K : ℕ) : ℝ) + 4 ≤ 25 * ((p : ℝ) ^ 40 * (K : ℝ) ^ 24) := h1
    _ ≤ 25 * ((13 : ℝ) ^ 40 * (2 * u) ^ 24) := by gcongr
    _ = 25 * 13 ^ 40 * 2 ^ 24 * u ^ 24 := by ring
    _ ≤ 5 / 2 * 10 ^ 76 * u ^ 24 := by gcongr
    _ ≤ 5 / 2 * u ^ 76 * u ^ 24 := by gcongr
    _ = 5 / 2 * u ^ 100 := by ring

/-- `√2 g ≤ ε/2` from `g² ≤ ε²/125`. -/
lemma sqrt_two_mul_le {g ε : ℝ} (hg0 : 0 ≤ g) (hε : 0 < ε) (h : g ^ 2 ≤ ε ^ 2 / 125) :
    Real.sqrt 2 * g ≤ ε / 2 := by
  have h2 : (Real.sqrt 2 * g) ^ 2 ≤ (ε / 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2

/- ## The cell generator -/

lemma sqrt_pow_sq {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : (Real.sqrt x ^ k) ^ 2 = x ^ k := by
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hx]

lemma norm_cellGen_sq {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (n α β : ℕ) :
    ‖cellGen π ρ n α β‖ ^ 2 = (p : ℝ) ^ α * (ρ.norm : ℝ) ^ β / (p : ℝ) ^ n := by
  have hρn : ‖((star ρ : GaussianInt) : ℂ)‖ = Real.sqrt (ρ.norm : ℝ) := by
    rw [norm_toComplex, Zsqrtd.norm_conj]
  unfold cellGen
  rw [norm_div, norm_mul, _root_.norm_pow, _root_.norm_pow, _root_.norm_pow,
    hπ.norm_toComplex_star_π, hπ.norm_toComplex_π, hρn, div_pow, mul_pow,
    sqrt_pow_sq (Nat.cast_nonneg p), sqrt_pow_sq (Nat.cast_nonneg p),
    sqrt_pow_sq (by exact_mod_cast GaussianInt.norm_nonneg ρ)]

/-- `‖g‖² = N(ρ)^β / p^A` when `α + A = n`. -/
lemma norm_cellGen_sq' {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) {n α β A : ℕ}
    (hnA : α + A = n) :
    ‖cellGen π ρ n α β‖ ^ 2 = (ρ.norm : ℝ) ^ β / (p : ℝ) ^ A := by
  rw [norm_cellGen_sq hπ, ← hnA, pow_add]
  have hp0 : (p : ℝ) ^ α ≠ 0 := pow_ne_zero _ (by exact_mod_cast hπ.prime.ne_zero)
  field_simp

/-- Upper bound on the cell: `‖g‖² ≤ ε²/125`. -/
lemma norm_cellGen_sq_le {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (hp5 : 5 ≤ p)
    (hρn : (ρ.norm : ℝ) ≤ (p : ℝ) ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ‖cellGen π ρ (pn p ⌈1 / ε⌉₊) (pα p ⌈1 / ε⌉₊) (pS p ⌈1 / ε⌉₊)‖ ^ 2 ≤ ε ^ 2 / 125 := by
  set K := ⌈1 / ε⌉₊ with hK
  rw [norm_cellGen_sq' hπ (A := pA p K) (by unfold pα; have := pA_le_pn p K; omega)]
  have hpr : (0 : ℝ) < p := by exact_mod_cast hπ.prime.pos
  have hpc : (K : ℝ) ≤ (p : ℝ) ^ pc p K := by exact_mod_cast le_pow_pc p K (by omega)
  have hKe : 1 / ε ≤ K := Nat.le_ceil _
  have hA : (p : ℝ) ^ pA p K = ((p : ℝ) ^ 2) ^ pS p K * ((p : ℝ) ^ pc p K) ^ 2 * (p : ℝ) ^ 3 := by
    unfold pA; rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; ring_nf
  rw [hA, div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : (ρ.norm : ℝ) ^ pS p K ≤ ((p : ℝ) ^ 2) ^ pS p K :=
    pow_le_pow_left₀ (by exact_mod_cast GaussianInt.norm_nonneg ρ) hρn _
  have h2 : (125 : ℝ) ≤ (p : ℝ) ^ 3 := by
    have : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    nlinarith
  have h3 : 1 ≤ ε ^ 2 * ((p : ℝ) ^ pc p K) ^ 2 := by
    have : 1 ≤ ε * (p : ℝ) ^ pc p K := by
      calc (1 : ℝ) = ε * (1 / ε) := by field_simp
        _ ≤ ε * K := by gcongr
        _ ≤ ε * (p : ℝ) ^ pc p K := by gcongr
    nlinarith
  have hq : (0 : ℝ) ≤ ((p : ℝ) ^ 2) ^ pS p K := by positivity
  calc (ρ.norm : ℝ) ^ pS p K * 125 ≤ ((p : ℝ) ^ 2) ^ pS p K * 125 := by gcongr
    _ ≤ ((p : ℝ) ^ 2) ^ pS p K * ((p : ℝ) ^ 3 * (ε ^ 2 * ((p : ℝ) ^ pc p K) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hq; nlinarith
    _ = ε ^ 2 * (((p : ℝ) ^ 2) ^ pS p K * ((p : ℝ) ^ pc p K) ^ 2 * (p : ℝ) ^ 3) := by ring

/-- Lower bound on the cell: `5^(-A) ≤ ‖g‖`. -/
lemma norm_cellGen_ge {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (hp13 : p ≤ 13)
    (hρ1 : 1 ≤ (ρ.norm : ℝ)) {n α β A : ℕ} (hnA : α + A = n) :
    (1 / 5 : ℝ) ^ A ≤ ‖cellGen π ρ n α β‖ := by
  have hsq := norm_cellGen_sq' hπ (ρ := ρ) (β := β) hnA
  have hpr : (0 : ℝ) < p := by exact_mod_cast hπ.prime.pos
  have h1 : ((1 / 5 : ℝ) ^ A) ^ 2 ≤ ‖cellGen π ρ n α β‖ ^ 2 := by
    rw [hsq, ← pow_mul, le_div_iff₀ (by positivity)]
    have hp' : (p : ℝ) ≤ 25 := by have : (p : ℝ) ≤ 13 := by exact_mod_cast hp13
                                  linarith
    have h2 : (p : ℝ) ^ A ≤ 25 ^ A := pow_le_pow_left₀ hpr.le hp' A
    have h3 : (1 : ℝ) ≤ (ρ.norm : ℝ) ^ β := one_le_pow₀ hρ1
    have h4 : (1 / 5 : ℝ) ^ (A * 2) * 25 ^ A = 1 := by
      rw [mul_comm A 2, pow_mul, ← mul_pow]; norm_num
    calc (1 / 5 : ℝ) ^ (A * 2) * (p : ℝ) ^ A ≤ (1 / 5 : ℝ) ^ (A * 2) * 25 ^ A := by gcongr
      _ = 1 := h4
      _ ≤ (ρ.norm : ℝ) ^ β := h3
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h1

/- ## Budget bounds -/

/-- `p^(n+4) < 100 η^(-5)`. -/
lemma pow_n4_lt {p : ℕ} (hp5 : 5 ≤ p) (hp13 : p ≤ 13) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    ((p ^ (pn p ⌈1 / ε⌉₊ + 4) : ℕ) : ℝ) < 100 * ηKL 100 ε ^ (-5 : ℝ) := by
  set n := pn p ⌈1 / ε⌉₊
  have hsmall := pn_small hp5 hp13 hε hε1
  rw [ηKL_rpow_neg_five hε]
  have hp' : (p : ℝ) ≤ 25 := by
    have : (p : ℝ) ≤ 13 := by exact_mod_cast hp13
    linarith
  have h1 : ((p ^ (n + 4) : ℕ) : ℝ) ≤ (25 : ℝ) ^ (n + 4) := by
    push_cast; exact pow_le_pow_left₀ (by positivity) hp' _
  have h2 : (25 : ℝ) ^ (n + 4) = (5 : ℝ) ^ ((2 * (n + 4) : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, pow_mul]; norm_num
  have h3 : (5 : ℝ) ^ ((2 * (n + 4) : ℕ) : ℝ) ≤ (5 : ℝ) ^ (5 * (1 / ε) ^ 100) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast; linarith
  have h4 : (0 : ℝ) < (5 : ℝ) ^ (5 * (1 / ε) ^ 100) := by positivity
  linarith

lemma budget_A {p K : ℕ} (hp5 : 5 ≤ p) : pA p K + 4 + pn p K ≤ p ^ (pn p K + 4) := by
  have hA := pA_le_pn p K
  have h1 : pn p K + 4 < 2 ^ (pn p K + 4) := Nat.lt_two_pow_self
  have h2 : 2 ^ (pn p K + 4) * 2 ≤ p ^ (pn p K + 4) := by
    calc 2 ^ (pn p K + 4) * 2 ≤ 2 ^ (pn p K + 4) * 2 ^ (pn p K + 4) := by
          apply Nat.mul_le_mul_left; exact Nat.le_self_pow (by omega) 2
      _ = 4 ^ (pn p K + 4) := by rw [← mul_pow]; norm_num
      _ ≤ p ^ (pn p K + 4) := Nat.pow_le_pow_left (by omega) _
  omega

lemma budget_T {p K : ℕ} (hp5 : 5 ≤ p) :
    (p - 1) * p ^ (pn p K + 3) + pS p K ≤ p ^ (pn p K + 4) := by
  have hS := pS_le p K
  have hℓ : pℓ p K ≤ pn p K + 3 := by unfold pn; omega
  have h1 : p ^ pℓ p K ≤ p ^ (pn p K + 3) := Nat.pow_le_pow_right (by omega) hℓ
  have h2 : p ^ (pn p K + 4) = (p - 1) * p ^ (pn p K + 3) + p ^ (pn p K + 3) := by
    set X := p ^ (pn p K + 3) with hX
    have h3 : p ^ (pn p K + 4) = p * X := by rw [hX, ← pow_succ']
    have h4 : (p - 1) * X + X = ((p - 1) + 1) * X := by ring
    rw [h3, h4, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  omega

/-- `η ≤ 5^(-A)`. -/
lemma ηKL_le_five_pow_neg {p : ℕ} (hp5 : 5 ≤ p) (hp13 : p ≤ 13) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1 / 10) : ηKL 100 ε ≤ (1 / 5 : ℝ) ^ pA p ⌈1 / ε⌉₊ := by
  have hsmall := pn_small hp5 hp13 hε hε1
  have hA : (pA p ⌈1 / ε⌉₊ : ℝ) * 8 ≤ pn p ⌈1 / ε⌉₊ := by
    have : pA p ⌈1 / ε⌉₊ * 8 ≤ pn p ⌈1 / ε⌉₊ := by unfold pn; omega
    exact_mod_cast this
  have h5 : (1 / 5 : ℝ) ^ pA p ⌈1 / ε⌉₊ = (5 : ℝ) ^ (-(pA p ⌈1 / ε⌉₊ : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  rw [ηKL_hundred hε, h5]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hu : (0 : ℝ) ≤ (1 / ε) ^ 100 := by positivity
  linarith

/- ## The generic case -/

theorem case_core {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (hp5 : 5 ≤ p) (hp13 : p ≤ 13)
    (hρ1 : ¬ π ∣ ρ) (hρ2 : ¬ π ∣ star ρ) (hρ4 : ¬ star π ∣ star ρ)
    (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0) (hρn : (ρ.norm : ℝ) ≤ (p : ℝ) ^ 2)
    (hρn1 : 1 ≤ (ρ.norm : ℝ))
    (hordA : ∀ k, 2 ≤ k → orderOf (hπ.mult (star ρ) k) = (p - 1) * p ^ (k - 1))
    (hordB : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
      orderOf (((hπ.mult ρ n).val : ℕ) : ZMod (p ^ ℓ)) = (p - 1) * p ^ (ℓ - 1))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) (w : ℂ) (q : GaussianInt) {N₀ a₁ b₁ a₂ b₂ v : ℕ}
    (ha₁ : a₁ ≤ N₀) (hb₁ : b₁ ≤ N₀) (ha₂ : a₂ ≤ N₀) (hb₂ : b₂ ≤ N₀)
    (hdiv : ∀ E : ℕ, (E : ℝ) < 100 * ηKL 100 ε ^ (-5 : ℝ) →
      ∃ q₂ : GaussianInt, ¬ star π ∣ q₂ ∧ q = star π ^ v * star ρ ^ E * q₂)
    (hclose : ‖(q : ℂ) - (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
        ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ ≤ ηKL 100 ε / 10) :
    ∃ a b : ℕ, (a : ℝ) ≤ N₀ + v + 100 * ηKL 100 ε ^ (-5 : ℝ) ∧
      (b : ℝ) ≤ N₀ + 100 * ηKL 100 ε ^ (-5 : ℝ) ∧
      ∃ k : ℤ, |(((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a *
        ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b * w).re - k| < ε := by
  set K := ⌈1 / ε⌉₊ with hK
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) (Nat.le_ceil (1 / ε))
    exact_mod_cast this
  have hn2 : 2 ≤ pn p K := by unfold pn; have := pℓ_ge p K; omega
  have hℓ1 : 1 ≤ pℓ p K := by have := pℓ_ge p K; omega
  set E := (p - 1) * p ^ (pn p K + 3) + pS p K with hE
  have hM := pow_n4_lt hp5 hp13 hε hε1
  have hEM : E ≤ p ^ (pn p K + 4) := budget_T hp5
  have hAM : pA p K + 4 + pn p K ≤ p ^ (pn p K + 4) := budget_A hp5
  have hEreal : (E : ℝ) < 100 * ηKL 100 ε ^ (-5 : ℝ) := by
    have : (E : ℝ) ≤ ((p ^ (pn p K + 4) : ℕ) : ℝ) := by exact_mod_cast hEM
    linarith
  obtain ⟨q₂, hq₂, hqeq⟩ := hdiv E hEreal
  -- the cell
  set g := cellGen π ρ (pn p K) (pα p K) (pS p K) with hg
  have hαA : pα p K + pA p K = pn p K := by unfold pα; have := pA_le_pn p K; omega
  have hglow : (1 / 5 : ℝ) ^ pA p K ≤ ‖g‖ := norm_cellGen_ge hπ hp13 hρn1 hαA
  have hηA := ηKL_le_five_pow_neg hp5 hp13 hε hε1
  have hgpos : 0 < ‖g‖ := lt_of_lt_of_le (by positivity) hglow
  have he' : ‖(((star π) ^ v * (star ρ) ^ E * q₂ : GaussianInt) : ℂ) -
      (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
        ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ < 21 / 50 * ‖g‖ := by
    rw [← hqeq]
    have hη0 : 0 < ηKL 100 ε := ηKL_pos 100 ε
    linarith
  have hgε : Real.sqrt 2 * ‖g‖ ≤ ε / 2 :=
    sqrt_two_mul_le (norm_nonneg _) hε (norm_cellGen_sq_le hπ hp5 hρn hε)
  have hH : 2 ≤ (pH K : ℝ) * ε ^ 2 := by
    have hKe : 1 / ε ≤ K := Nat.le_ceil _
    have h1 : 1 ≤ (K : ℝ) * ε := by
      calc (1 : ℝ) = (1 / ε) * ε := by field_simp
        _ ≤ K * ε := by gcongr
    unfold pH; push_cast; nlinarith
  have hHL : 25 * pH K ^ 3 < 4 * p ^ pL p K := pH_cube_lt p K hp5 hK1
  have hA4 := hordA (pn p K + 4) (by omega)
  rw [show pn p K + 4 - 1 = pn p K + 3 by omega] at hA4
  obtain ⟨a, b, ha, hb, k, hk⟩ := hπ.minor_arc_core hp5 hρ1 hρ2 hρ4 hρ0
    (n := pn p K) (α := pα p K) (β := pS p K) (A := pA p K) (L := pL p K) (ℓ := pℓ p K)
    (S := pS p K) (H := pH K) (pL_pos p K) rfl rfl le_rfl rfl rfl hA4
    (hordB (pn p K) (pℓ p K) hn2 hℓ1) hε hH hHL hgε w ha₁ hb₁ ha₂ hb₂ le_rfl hq₂ he'
  refine ⟨a, b, ?_, ?_, k, hk⟩
  · have h1 : (a : ℝ) ≤ N₀ + v + ((pA p K + 4 + pn p K : ℕ) : ℝ) := by
      have : a ≤ N₀ + v + (pA p K + 4 + pn p K) := by omega
      exact_mod_cast this
    have h2 : ((pA p K + 4 + pn p K : ℕ) : ℝ) ≤ ((p ^ (pn p K + 4) : ℕ) : ℝ) := by
      exact_mod_cast hAM
    linarith
  · have h1 : (b : ℝ) ≤ N₀ + (E : ℝ) := by
      have : b ≤ N₀ + E := by omega
      exact_mod_cast this
    have h2 : (E : ℝ) ≤ ((p ^ (pn p K + 4) : ℕ) : ℝ) := by exact_mod_cast hEM
    linarith

/- ## Decomposing `q` -/

lemma decomp_pow {a b q : GaussianInt} (ha : Prime a) (hcop : IsCoprime a b) (hq : q ≠ 0)
    {E : ℕ} (hE : b ^ E ∣ q) : ∃ q₂, ¬ a ∣ q₂ ∧ q = a ^ multiplicity a q * b ^ E * q₂ := by
  have hf : FiniteMultiplicity a q := FiniteMultiplicity.of_not_isUnit ha.not_isUnit hq
  set v := multiplicity a q with hv
  have hdvd : a ^ v ∣ q := pow_multiplicity_dvd a q
  obtain ⟨q₁, hq₁⟩ := hdvd
  have hnd : ¬ a ∣ q₁ := by
    rintro ⟨c, hc⟩
    apply hf.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self v)
    exact ⟨c, by rw [hq₁, hc, pow_succ]; ring⟩
  have hb : b ^ E ∣ q₁ := by
    have h1 : b ^ E ∣ a ^ v * q₁ := hq₁ ▸ hE
    exact (hcop.symm.pow).dvd_of_dvd_mul_left h1
  obtain ⟨q₂, hq₂⟩ := hb
  refine ⟨q₂, fun h => hnd (by rw [hq₂]; exact dvd_mul_of_dvd_right h _), ?_⟩
  rw [hq₁, hq₂]; ring

lemma size5_eq {q : GaussianInt} (hq : q ≠ 0) :
    size5 q = (5 : ℝ) ^ (-(multiplicity gPb q : ℝ)) := by
  unfold size5; rw [ite_eq_right hq]

lemma size13_eq {q : GaussianInt} (hq : q ≠ 0) :
    size13 q = (13 : ℝ) ^ (-(multiplicity gQb q : ℝ)) := by
  unfold size13; rw [ite_eq_right hq]

lemma le_logb_of_rpow_neg {b ϖ : ℝ} (hb : 1 < b) (hϖ : 0 < ϖ) {v : ℕ}
    (h : ϖ ≤ b ^ (-(v : ℝ))) : (v : ℝ) ≤ Real.logb b ϖ⁻¹ := by
  rw [Real.le_logb_iff_rpow_le hb (inv_pos.mpr hϖ)]
  rw [Real.rpow_neg (by linarith)] at h
  have hpos : 0 < b ^ (v : ℝ) := by positivity
  rw [le_inv_comm₀ hϖ hpos] at h
  exact h

lemma gPb_not_dvd_gQb : ¬ gPb ∣ gQb := by
  rintro ⟨c, hc⟩
  apply gP_not_dvd_gQ
  refine ⟨star c, ?_⟩
  have := congrArg star hc
  rwa [star_gQb, star_mul, star_gPb, mul_comm] at this

lemma gQb_not_dvd_gPb : ¬ gQb ∣ gPb := by
  rintro ⟨c, hc⟩
  apply gQ_not_dvd_gP
  refine ⟨star c, ?_⟩
  have := congrArg star hc
  rwa [star_gPb, star_mul, star_gQb, mul_comm] at this

lemma natCast_val_eq {m : ℕ} [NeZero m] (a : ZMod m) : ((a.val : ℕ) : ZMod m) = a :=
  ZMod.natCast_zmod_val a

/- ## The interface -/

/-- **Kravitz–Leng, Proposition 5.7, for points of `ℂ`**, with the constant `c = 100`. -/
theorem kl57With_100 : KL57With 100 := by
  intro ε ϖ hε0 hε1 hϖ0 hϖ1 N₀ s₁ t₁ s₂ t₂ w q hs₁ ht₁ hs₂ ht₂ hlow hup hclose
  have h5n := size5_nonneg q
  have h13n := size13_nonneg q
  have hq : q ≠ 0 := by
    rintro rfl
    simp only [size5, size13, ite_true] at hlow
    linarith
  have hlog0 : 0 ≤ Real.logb 5 ϖ⁻¹ :=
    Real.logb_nonneg (by norm_num) (by rw [le_inv_comm₀ one_pos hϖ0]; linarith)
  set X := 100 * ηKL 100 ε ^ (-5 : ℝ) with hX
  have hX0 : 0 ≤ X := mul_nonneg (by norm_num) (Real.rpow_nonneg (ηKL_pos 100 ε).le _)
  have hδ : δKL 100 ε = (13 : ℝ) ^ (-X) := rfl
  by_cases h513 : size13 q ≤ size5 q
  · -- Case 1: digit prime `P`, multiplier `Q`.
    set v := multiplicity gPb q with hv
    have hvϖ : (v : ℝ) ≤ Real.logb 5 ϖ⁻¹ := by
      apply le_logb_of_rpow_neg (by norm_num) hϖ0
      rw [← size5_eq hq]; linarith
    have hdiv : ∀ E : ℕ, (E : ℝ) < X →
        ∃ q₂ : GaussianInt, ¬ star gP ∣ q₂ ∧ q = star gP ^ v * star gQ ^ E * q₂ := by
      intro E hE
      have hlt : size13 q < 1 / (13 : ℝ) ^ E := by
        have h1 : (13 : ℝ) ^ (-X) < (13 : ℝ) ^ (-(E : ℝ)) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
        have hE' : (13 : ℝ) ^ (-(E : ℝ)) = 1 / (13 : ℝ) ^ E := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
        rw [hE', ← hδ] at h1
        linarith
      exact decomp_pow prime_gPb isCoprime_gPb_gQb hq (dvd_of_size13_lt hlt)
    have hordA : ∀ k, 2 ≤ k → orderOf (digitPrime_P.mult (star gQ) k) = (5 - 1) * 5 ^ (k - 1) := by
      intro k hk
      have : NeZero (5 ^ k) := ⟨by positivity⟩
      have := orderOf_mult_P_Qb (n := k) (k := k) hk (by omega)
      rwa [natCast_val_eq] at this
    have hordB : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
        orderOf (((digitPrime_P.mult gQ n).val : ℕ) : ZMod (5 ^ ℓ)) = (5 - 1) * 5 ^ (ℓ - 1) :=
      fun n ℓ hn hℓ => orderOf_mult_P_Q hn hℓ
    obtain ⟨a, b, ha, hb, k, hk⟩ := case_core digitPrime_P le_rfl (by norm_num) gP_not_dvd_gQ
      gP_not_dvd_gQb gPb_not_dvd_gQb gQb_ne_zero (by rw [norm_gQ]; norm_num)
      (by rw [norm_gQ]; norm_num) hordA hordB hε0 hε1 w q hs₁ ht₁ hs₂ ht₂ hdiv hclose
    exact ⟨a, b, by linarith, by linarith, k, hk⟩
  · -- Case 2: digit prime `Q`, multiplier `P`.
    push Not at h513
    set v := multiplicity gQb q with hv
    have hvϖ : (v : ℝ) ≤ Real.logb 5 ϖ⁻¹ := by
      apply le_logb_of_rpow_neg (by norm_num) hϖ0
      have h1 : ϖ ≤ size13 q := by linarith
      rw [size13_eq hq] at h1
      have h2 : (13 : ℝ) ^ (-(v : ℝ)) ≤ (5 : ℝ) ^ (-(v : ℝ)) := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
        apply inv_anti₀ (by positivity)
        exact Real.rpow_le_rpow (by norm_num) (by norm_num) (Nat.cast_nonneg _)
      linarith
    have hdiv : ∀ E : ℕ, (E : ℝ) < X →
        ∃ q₂ : GaussianInt, ¬ star gQ ∣ q₂ ∧ q = star gQ ^ v * star gP ^ E * q₂ := by
      intro E hE
      have hlt : size5 q < 1 / (5 : ℝ) ^ E := by
        have h1 : (13 : ℝ) ^ (-X) ≤ (5 : ℝ) ^ (-X) := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
          apply inv_anti₀ (by positivity)
          exact Real.rpow_le_rpow (by norm_num) (by norm_num) hX0
        have h2 : (5 : ℝ) ^ (-X) < (5 : ℝ) ^ (-(E : ℝ)) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
        have hE' : (5 : ℝ) ^ (-(E : ℝ)) = 1 / (5 : ℝ) ^ E := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
        rw [hE'] at h2
        rw [← hδ] at h1
        linarith
      exact decomp_pow prime_gQb isCoprime_gPb_gQb.symm hq (dvd_of_size5_lt hlt)
    have hordA : ∀ k, 2 ≤ k →
        orderOf (digitPrime_Q.mult (star gP) k) = (13 - 1) * 13 ^ (k - 1) := by
      intro k hk
      have : NeZero (13 ^ k) := ⟨by positivity⟩
      have := orderOf_mult_Q_Pb (n := k) (k := k) hk (by omega)
      rwa [natCast_val_eq] at this
    have hordB : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
        orderOf (((digitPrime_Q.mult gP n).val : ℕ) : ZMod (13 ^ ℓ)) =
          (13 - 1) * 13 ^ (ℓ - 1) :=
      fun n ℓ hn hℓ => orderOf_mult_Q_P hn hℓ
    have hrot : ∀ s t : ℕ, rot s t = ((gQ : ℂ) / ((star gQ : GaussianInt) : ℂ)) ^ t *
        ((gP : ℂ) / ((star gP : GaussianInt) : ℂ)) ^ s := by
      intro s t; unfold rot θ5 θ13; rw [star_gP, star_gQ]; ring
    rw [hrot s₁ t₁, hrot s₂ t₂] at hclose
    obtain ⟨a, b, ha, hb, k, hk⟩ := case_core digitPrime_Q (by norm_num) le_rfl gQ_not_dvd_gP
      gQ_not_dvd_gPb gQb_not_dvd_gPb gPb_ne_zero (by rw [norm_gP]; norm_num)
      (by rw [norm_gP]; norm_num) hordA hordB hε0 hε1 w q ht₁ hs₁ ht₂ hs₂ hdiv hclose
    refine ⟨b, a, by linarith, by linarith, k, ?_⟩
    rw [hrot b a]
    exact hk

/-- The interface `KL57` holds. -/
theorem kl57 : KL57 := ⟨100, by norm_num, kl57With_100⟩

end Green41

/- ## The target -/

namespace Green41

open Complex Set Pointwise

/-- The double-exponential bound, with no hypotheses. -/
theorem doubleExponentialBound : DoubleExponentialBound :=
  doubleExponentialBound_of_KL57 kl57

/-- The Formal Conjectures statement with the answer `True`. -/
theorem green_41.variants.double_exponential_bound : True ↔
    ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀, (minCopies ε : ℝ) ≤ Real.exp (Real.exp (ε ^ (-C))) :=
  ⟨fun _ => doubleExponentialBound, fun _ => trivial⟩

#print axioms green_41.variants.double_exponential_bound

end Green41
