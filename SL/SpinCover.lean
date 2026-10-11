import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Section 2.2, Step 1: from `SU(2)` to `SO(3)` via the variables `X, Y, Z`

For `(z₁, z₂) ∈ ℂ²` the paper introduces the new (real) variables
`X = z₁ z̄₁ - z₂ z̄₂`, `Y = z₁ z̄₂ + z₂ z̄₁`, `Z = i (z₁ z̄₂ - z₂ z̄₁)`,
which are bilinear in `z₁, z₂, z̄₁, z̄₂`.  A matrix `g ∈ SU(2)` acts on `(z₁, z₂)`
(and simultaneously, through the conjugate-imaginary matrix, on `(z̄₁, z̄₂)`),
and the induced action on `(X, Y, Z)` is given by a real `3 × 3` matrix `rho g`.
We prove that `rho g ∈ SO(3)`, that `rho` is a group homomorphism
`SU(2) →* SO(3)` with kernel `{I₂, -I₂}`, and hence that for a finite subgroup
`G ≤ SU(2)` the image `Ḡ ≤ SO(3)` is finite with `|G| = 2 |Ḡ|` if `-I₂ ∈ G` and
`|G| = |Ḡ|` otherwise.
-/

namespace Section22
open Matrix Complex ComplexConjugate

/-- The group `SU(2)` of `2 × 2` complex unitary matrices of determinant `1`. -/
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ
/-- The group `SO(3)` of `3 × 3` real orthogonal matrices of determinant `1`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- The variable `X(z₁, z₂) = z₁ z̄₁ - z₂ z̄₂` (a real number). -/
noncomputable def coordX (z : Fin 2 → ℂ) : ℝ := normSq (z 0) - normSq (z 1)
/-- The variable `Y(z₁, z₂) = z₁ z̄₂ + z₂ z̄₁` (a real number). -/
noncomputable def coordY (z : Fin 2 → ℂ) : ℝ := 2 * (z 0 * conj (z 1)).re
/-- The variable `Z(z₁, z₂) = i (z₁ z̄₂ - z₂ z̄₁)` (a real number). -/
noncomputable def coordZ (z : Fin 2 → ℂ) : ℝ := -2 * (z 0 * conj (z 1)).im

/-- The vector `(X, Y, Z) ∈ ℝ³` attached to `(z₁, z₂) ∈ ℂ²`. -/
noncomputable def coordXYZ (z : Fin 2 → ℂ) : Fin 3 → ℝ := ![coordX z, coordY z, coordZ z]

theorem coordX_eq (z : Fin 2 → ℂ) : (coordX z : ℂ) = z 0 * conj (z 0) - z 1 * conj (z 1) := by
  simp [coordX, Complex.mul_conj]

theorem coordY_eq (z : Fin 2 → ℂ) : (coordY z : ℂ) = z 0 * conj (z 1) + z 1 * conj (z 0) := by
  apply Complex.ext <;> simp [coordY] <;> ring

theorem coordZ_eq (z : Fin 2 → ℂ) :
    (coordZ z : ℂ) = I * (z 0 * conj (z 1) - z 1 * conj (z 0)) := by
  apply Complex.ext <;> simp [coordZ] <;> ring

/-- The real `3 × 3` matrix describing the action of `g = (a b; -b̄ ā) ∈ SU(2)`
on the variables `(X, Y, Z)`; it only depends on the first row `(a, b)` of `g`. -/
noncomputable def rho (g : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![normSq (g 0 0) - normSq (g 0 1), 2 * (g 0 0 * conj (g 0 1)).re,
      2 * (g 0 0 * conj (g 0 1)).im;
     -2 * (g 0 0 * g 0 1).re, (g 0 0 ^ 2 - g 0 1 ^ 2).re, (g 0 0 ^ 2 + g 0 1 ^ 2).im;
     2 * (g 0 0 * g 0 1).im, -(g 0 0 ^ 2 - g 0 1 ^ 2).im, (g 0 0 ^ 2 + g 0 1 ^ 2).re]

/-- The shape of a matrix of `SU(2)` (Remark 9 of the paper):
`g = (a b; -b̄ ā)` with `|a|² + |b|² = 1`. -/
theorem su2_entries {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g ∈ specialUnitaryGroup (Fin 2) ℂ) :
    g 1 0 = -conj (g 0 1) ∧ g 1 1 = conj (g 0 0) ∧ normSq (g 0 0) + normSq (g 0 1) = 1 := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff] at hg
  obtain ⟨hu, hd⟩ := hg
  have e00 := congrFun (congrFun hu 0) 0
  have e01 := congrFun (congrFun hu 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at e00 e01
  rw [det_fin_two] at hd
  have e01' := congrArg conj e01
  simp at e01'
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(g 1 0)) * e00 + g 0 0 * e01' - conj (g 0 1) * hd
  · linear_combination (-(g 1 1)) * e00 + conj (g 0 0) * hd + g 0 1 * e01'
  · have := congrArg Complex.re e00
    simpa [Complex.normSq_apply, Complex.mul_re] using this

theorem su2_eq {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g ∈ specialUnitaryGroup (Fin 2) ℂ) :
    g = !![g 0 0, g 0 1; -conj (g 0 1), conj (g 0 0)] := by
  obtain ⟨h1, h2, -⟩ := su2_entries hg
  conv_lhs => rw [Matrix.eta_fin_two g, h1, h2]

theorem coordXYZ_mulVec_aux (a b : ℂ) (z : Fin 2 → ℂ) :
    coordXYZ (!![a, b; -conj b, conj a] *ᵥ z) = rho !![a, b; -conj b, conj a] *ᵥ coordXYZ z := by
  ext i
  fin_cases i <;>
  simp [coordXYZ, coordX, coordY, coordZ, rho, mulVec, dotProduct, Fin.sum_univ_succ,
    normSq_apply, pow_two] <;> ring

/-- **Change of variables.** For `g ∈ SU(2)`, applying `g` to `(z₁, z₂)` transforms
the variables `(X, Y, Z)` linearly by the real matrix `rho g`. -/
theorem coordXYZ_mulVec {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g ∈ specialUnitaryGroup (Fin 2) ℂ) (z : Fin 2 → ℂ) :
    coordXYZ (g *ᵥ z) = rho g *ᵥ coordXYZ z := by
  rw [su2_eq hg]
  exact coordXYZ_mulVec_aux _ _ z

theorem rho_mul_transpose_aux (a b : ℂ) :
    rho !![a, b; -conj b, conj a] * (rho !![a, b; -conj b, conj a])ᵀ =
      (normSq a + normSq b) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [rho, Matrix.mul_apply, Fin.sum_univ_succ, normSq_apply, pow_two] <;> ring

theorem rho_det_aux (a b : ℂ) :
    (rho !![a, b; -conj b, conj a]).det = (normSq a + normSq b) ^ 3 := by
  simp [rho, det_fin_three, normSq_apply, pow_two]; ring

/-- For `g ∈ SU(2)`, the matrix `rho g` is a rotation: `rho g ∈ SO(3)`. -/
theorem rho_mem_SO3 {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g ∈ specialUnitaryGroup (Fin 2) ℂ) :
    rho g ∈ specialOrthogonalGroup (Fin 3) ℝ := by
  have hs := (su2_entries hg).2.2
  rw [su2_eq hg]
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [rho_mul_transpose_aux, hs]; simp
  · rw [rho_det_aux, hs]; simp

/-- Two real `3 × 3` matrices agreeing on all vectors of the form `(X, Y, Z)(z)` are equal. -/
theorem matrix_eq_of_coordXYZ {M N : Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ z, M *ᵥ coordXYZ z = N *ᵥ coordXYZ z) : M = N := by
  have e0 : coordXYZ ![1, 0] = ![1, 0, 0] := by
    ext i; fin_cases i <;> simp [coordXYZ, coordX, coordY, coordZ]
  have e1 : coordXYZ ![1, 1] = ![0, 2, 0] := by
    ext i; fin_cases i <;> simp [coordXYZ, coordX, coordY, coordZ]
  have e2 : coordXYZ ![1, I] = ![0, 0, 2] := by
    ext i; fin_cases i <;> simp [coordXYZ, coordX, coordY, coordZ]
  have hv : ∀ v : Fin 3 → ℝ, M *ᵥ v = N *ᵥ v := by
    intro v
    have hv : v = v 0 • coordXYZ ![1, 0] + (v 1 / 2) • coordXYZ ![1, 1]
        + (v 2 / 2) • coordXYZ ![1, I] := by
      rw [e0, e1, e2]; ext i; fin_cases i <;> simp
    rw [hv]
    simp only [mulVec_add, mulVec_smul, h]
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

/-- `rho` is multiplicative on `SU(2)`. -/
theorem rho_mul {g h : Matrix (Fin 2) (Fin 2) ℂ} (hg : g ∈ specialUnitaryGroup (Fin 2) ℂ)
    (hh : h ∈ specialUnitaryGroup (Fin 2) ℂ) : rho (g * h) = rho g * rho h := by
  apply matrix_eq_of_coordXYZ
  intro z
  rw [← coordXYZ_mulVec (mul_mem hg hh), ← mulVec_mulVec, coordXYZ_mulVec hg,
    coordXYZ_mulVec hh, mulVec_mulVec]

theorem rho_one : rho 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rho]

/-- The group homomorphism `SU(2) →* SO(3)`, `g ↦ ḡ`, obtained from the change of
variables `(X, Y, Z)`. -/
noncomputable def rhoHom : SU2 →* SO3 where
  toFun g := ⟨rho g, rho_mem_SO3 g.2⟩
  map_one' := Subtype.ext rho_one
  map_mul' g h := Subtype.ext (rho_mul g.2 h.2)

@[simp] theorem rhoHom_apply (g : SU2) : ((rhoHom g : SO3) : Matrix (Fin 3) (Fin 3) ℝ) = rho g :=
  rfl

/-- The defining property of `rhoHom`: `(X, Y, Z)(g z) = ḡ (X, Y, Z)(z)`. -/
theorem coordXYZ_rhoHom (g : SU2) (z : Fin 2 → ℂ) :
    coordXYZ ((g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ z) =
      ((rhoHom g : SO3) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ coordXYZ z :=
  coordXYZ_mulVec g.2 z

/-- A matrix `g ∈ SU(2)` gives the identity rotation iff `g = ± I₂`. -/
theorem rho_eq_one_iff {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g ∈ specialUnitaryGroup (Fin 2) ℂ) :
    rho g = 1 ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro h
    obtain ⟨-, -, hs⟩ := su2_entries hg
    have h00 := congrFun (congrFun h 0) 0
    have h11 := congrFun (congrFun h 1) 1
    have h12 := congrFun (congrFun h 1) 2
    simp [rho] at h00 h11 h12
    have hb : g 0 1 = 0 := by
      rw [← Complex.normSq_eq_zero]; linarith
    rw [hb] at h11 h12
    simp at h11 h12
    have ha2 : g 0 0 ^ 2 = 1 := Complex.ext (by simpa using h11) (by simpa using h12)
    have ha : g 0 0 = 1 ∨ g 0 0 = -1 := by
      have hm : (g 0 0 - 1) * (g 0 0 + 1) = 0 := by linear_combination ha2
      rcases mul_eq_zero.mp hm with h | h
      · left; linear_combination h
      · right; linear_combination h
    rcases ha with ha | ha
    · left; rw [su2_eq hg, ha, hb]; ext i j; fin_cases i <;> fin_cases j <;> simp
    · right; rw [su2_eq hg, ha, hb]; ext i j; fin_cases i <;> fin_cases j <;> simp
  · rintro (rfl | rfl)
    · exact rho_one
    · ext i j; fin_cases i <;> fin_cases j <;> simp [rho]

/-- The kernel of `rhoHom` is `{I₂, -I₂}`. -/
theorem rhoHom_eq_one_iff (g : SU2) :
    rhoHom g = 1 ↔ (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (g : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  rw [← rho_eq_one_iff g.2, ← rhoHom_apply]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact Subtype.ext h

open Classical in
/-- **Step 1 (cardinality).** For a finite subgroup `G ≤ SU(2)`, the corresponding group
of rotations `Ḡ = rhoHom(G) ≤ SO(3)` satisfies `|G| = 2 |Ḡ|` if `-I₂ ∈ G` and
`|G| = |Ḡ|` otherwise. -/
theorem card_eq_card_map_rhoHom (G : Subgroup SU2) [Finite G] :
    Nat.card G = (if ∃ g ∈ G, (g : Matrix (Fin 2) (Fin 2) ℂ) = -1 then 2 else 1) *
      Nat.card (G.map rhoHom) := by
  set f : G →* SO3 := rhoHom.comp G.subtype with hf
  have hrange : f.range = G.map rhoHom := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange, ← Subgroup.index_ker, ← Subgroup.card_mul_index f.ker]
  congr 1
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  have hmem : ∀ x : G, x ∈ f.ker ↔
      ((x : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ ((x : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    intro x
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.coe_subtype, rhoHom_eq_one_iff]
  have hne : (1 : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1 := by
    intro h
    have := congrFun (congrFun h 0) 0
    norm_num at this
  split_ifs with h
  · obtain ⟨m, hmG, hm⟩ := h
    have : (f.ker : Set G) = {1, ⟨m, hmG⟩} := by
      ext x
      simp only [SetLike.mem_coe, hmem, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (h1 | h1)
        · left; exact Subtype.ext (Subtype.ext h1)
        · right; exact Subtype.ext (Subtype.ext (h1.trans hm.symm))
      · rintro (rfl | rfl)
        · left; rfl
        · right; exact hm
    rw [this, Set.ncard_pair]
    intro h1
    apply hne
    have := congrArg (fun x : G => ((x : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) h1
    simpa [hm] using this
  · push Not at h
    have : (f.ker : Set G) = {1} := by
      ext x
      simp only [SetLike.mem_coe, hmem, Set.mem_singleton_iff]
      constructor
      · rintro (h1 | h1)
        · exact Subtype.ext (Subtype.ext h1)
        · exact absurd h1 (h x x.2)
      · rintro rfl; left; rfl
    rw [this, Set.ncard_singleton]

/-- The group of rotations `Ḡ ≤ SO(3)` attached to a finite `G ≤ SU(2)` is finite. -/
instance finite_map_rhoHom (G : Subgroup SU2) [Finite G] : Finite (G.map rhoHom) := by
  change Finite ((G.map rhoHom : Set SO3))
  rw [Subgroup.coe_map]
  have : Finite (G : Set SU2) := ‹Finite G›
  infer_instance

end Section22

#min_imports
