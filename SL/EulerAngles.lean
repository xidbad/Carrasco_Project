import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import SL.SpinCover

/-!
# Section 2.2, Step 1: the decomposition `g = g₁ g₂ g₃` and the rotations `ḡ₁, ḡ₂, ḡ₃`

Every `g ∈ SU(2)` factors as `g = g₁ g₂ g₃` with
`g₁ = diag(cos θ₁ - i sin θ₁, cos θ₁ + i sin θ₁)`, `g₂ = (cos θ₂ sin θ₂; -sin θ₂ cos θ₂)`,
`g₃ = diag(cos θ₃ - i sin θ₃, cos θ₃ + i sin θ₃)`, where `cos θ₂ = p = |a|`, `sin θ₂ = q = |b|`.
In the variables `(X, Y, Z)` these act as rotations around the `X`-axis, the `Z`-axis and the
`X`-axis through the angles `2θ₁, 2θ₂, 2θ₃`.
-/

namespace Section22
open Matrix Complex ComplexConjugate

/-- The matrices `g₁` and `g₃` of the paper: `diag(cos θ - i sin θ, cos θ + i sin θ)`. -/
noncomputable def diagRot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ) - I * Real.sin θ, 0; 0, (Real.cos θ : ℂ) + I * Real.sin θ]

/-- The matrix `g₂` of the paper: `(cos θ sin θ; -sin θ cos θ)`. -/
noncomputable def realRot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), Real.sin θ; -(Real.sin θ : ℂ), Real.cos θ]

/-- Rotation of `ℝ³` around the `X`-axis through the angle `φ` (the matrices `ḡ₁, ḡ₃`). -/
noncomputable def rotX (φ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, Real.cos φ, -Real.sin φ; 0, Real.sin φ, Real.cos φ]

/-- Rotation of `ℝ³` around the `Z`-axis through the angle `φ`, written as in the paper
(the matrix `ḡ₂`). -/
noncomputable def rotZ (φ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos φ, Real.sin φ, 0; -Real.sin φ, Real.cos φ, 0; 0, 0, 1]

theorem diagRot_mem (θ : ℝ) : diagRot θ ∈ specialUnitaryGroup (Fin 2) ℂ := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagRot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
      apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;>
      nlinarith [Real.sin_sq_add_cos_sq θ]
  · rw [det_fin_two]
    simp [diagRot]
    apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;>
      nlinarith [Real.sin_sq_add_cos_sq θ]

theorem realRot_mem (θ : ℝ) : realRot θ ∈ specialUnitaryGroup (Fin 2) ℂ := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realRot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
      apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;>
      nlinarith [Real.sin_sq_add_cos_sq θ]
  · rw [det_fin_two]
    simp [realRot]
    apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- `ḡ₁ = rho g₁` (and `ḡ₃ = rho g₃`) is the rotation around the `X`-axis through `2θ`. -/
theorem rho_diagRot (θ : ℝ) : rho (diagRot θ) = rotX (2 * θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, diagRot, rotX, normSq_apply, pow_two, Real.cos_two_mul, Real.sin_two_mul,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- `ḡ₂ = rho g₂` is the rotation around the `Z`-axis through `2θ`. -/
theorem rho_realRot (θ : ℝ) : rho (realRot θ) = rotZ (2 * θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, realRot, rotZ, normSq_apply, pow_two, Real.cos_two_mul, Real.sin_two_mul,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The transformation of the variables `X, Y, Z` under `g₁` (and `g₃`). -/
theorem coords_diagRot (θ : ℝ) (z : Fin 2 → ℂ) :
    coordX (diagRot θ *ᵥ z) = coordX z ∧
    coordY (diagRot θ *ᵥ z) = coordY z * Real.cos (2 * θ) - coordZ z * Real.sin (2 * θ) ∧
    coordZ (diagRot θ *ᵥ z) = coordY z * Real.sin (2 * θ) + coordZ z * Real.cos (2 * θ) := by
  have h := coordXYZ_mulVec (diagRot_mem θ) z
  rw [rho_diagRot] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [coordXYZ, rotX, mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
  refine ⟨h0, ?_, ?_⟩
  · rw [h1]; ring
  · rw [h2]; ring

/-- The transformation of the variables `X, Y, Z` under `g₂`. -/
theorem coords_realRot (θ : ℝ) (z : Fin 2 → ℂ) :
    coordX (realRot θ *ᵥ z) = coordX z * Real.cos (2 * θ) + coordY z * Real.sin (2 * θ) ∧
    coordY (realRot θ *ᵥ z) = -coordX z * Real.sin (2 * θ) + coordY z * Real.cos (2 * θ) ∧
    coordZ (realRot θ *ᵥ z) = coordZ z := by
  have h := coordXYZ_mulVec (realRot_mem θ) z
  rw [rho_realRot] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [coordXYZ, rotZ, mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
  refine ⟨?_, ?_, h2⟩
  · rw [h0]; ring
  · rw [h1]; ring

/-- Two matrices of `SU(2)` with the same first row coincide. -/
theorem su2_ext {g h : Matrix (Fin 2) (Fin 2) ℂ} (hg : g ∈ specialUnitaryGroup (Fin 2) ℂ)
    (hh : h ∈ specialUnitaryGroup (Fin 2) ℂ) (h0 : g 0 0 = h 0 0) (h1 : g 0 1 = h 0 1) :
    g = h := by
  rw [su2_eq hg, su2_eq hh, h0, h1]

theorem cos_sub_I_sin (θ : ℝ) :
    (Real.cos θ : ℂ) - I * Real.sin θ = exp (-(θ : ℂ) * I) := by
  rw [show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]; ring

theorem cos_add_I_sin (θ : ℝ) :
    (Real.cos θ : ℂ) + I * Real.sin θ = exp ((θ : ℂ) * I) := by
  rw [exp_mul_I]; push_cast; ring

/-- **Step 1 (decomposition).** Every `g = (a b; -b̄ ā) ∈ SU(2)` can be written as
`g = g₁ g₂ g₃` with `cos θ₂ = p = |a|` and `sin θ₂ = q = |b|`. -/
theorem euler_decomposition {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g ∈ specialUnitaryGroup (Fin 2) ℂ) :
    ∃ θ₁ θ₂ θ₃ : ℝ, Real.cos θ₂ = ‖g 0 0‖ ∧ Real.sin θ₂ = ‖g 0 1‖ ∧
      g = diagRot θ₁ * realRot θ₂ * diagRot θ₃ := by
  obtain ⟨-, -, hs⟩ := su2_entries hg
  set a := g 0 0
  set b := g 0 1
  have hs' : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; exact hs
  have ha1 : ‖a‖ ≤ 1 := by nlinarith [norm_nonneg a, norm_nonneg b]
  set θ₂ := Real.arccos ‖a‖
  have hc : Real.cos θ₂ = ‖a‖ := Real.cos_arccos (by linarith [norm_nonneg a]) ha1
  have hsn : Real.sin θ₂ = ‖b‖ := by
    rw [Real.sin_arccos]
    rw [show 1 - ‖a‖ ^ 2 = ‖b‖ ^ 2 by linarith]
    exact Real.sqrt_sq (norm_nonneg b)
  refine ⟨-(a.arg + b.arg) / 2, θ₂, (b.arg - a.arg) / 2, hc, hsn, ?_⟩
  apply su2_ext hg (mul_mem (mul_mem (diagRot_mem _) (realRot_mem _)) (diagRot_mem _))
  · simp only [diagRot, realRot, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, zero_mul, add_zero, mul_zero]
    rw [cos_sub_I_sin, cos_sub_I_sin, hc, mul_right_comm, ← exp_add, mul_comm]
    refine (Complex.norm_mul_exp_arg_mul_I a).symm.trans ?_
    congr 2
    push_cast; ring
  · simp only [diagRot, realRot, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, zero_mul, add_zero, mul_zero, zero_add]
    rw [cos_sub_I_sin, cos_add_I_sin, hsn, mul_right_comm, ← exp_add, mul_comm]
    refine (Complex.norm_mul_exp_arg_mul_I b).symm.trans ?_
    congr 2
    push_cast; ring

/-- **Step 1 (rotations).** For `g ∈ SU(2)` the rotation `ḡ = rho g ∈ SO(3)` is the product
of a rotation around the `X`-axis through `2θ₁`, a rotation around the `Z`-axis through `2θ₂`
and a rotation around the `X`-axis through `2θ₃`. -/
theorem rho_eq_rotX_rotZ_rotX {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g ∈ specialUnitaryGroup (Fin 2) ℂ) :
    ∃ θ₁ θ₂ θ₃ : ℝ, g = diagRot θ₁ * realRot θ₂ * diagRot θ₃ ∧
      rho g = rotX (2 * θ₁) * rotZ (2 * θ₂) * rotX (2 * θ₃) := by
  obtain ⟨θ₁, θ₂, θ₃, -, -, h⟩ := euler_decomposition hg
  refine ⟨θ₁, θ₂, θ₃, h, ?_⟩
  rw [h, rho_mul (mul_mem (diagRot_mem _) (realRot_mem _)) (diagRot_mem _),
    rho_mul (diagRot_mem _) (realRot_mem _), rho_diagRot, rho_diagRot, rho_realRot]

end Section22

#min_imports
