import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
import Mathlib.RingTheory.FiniteType
import SL.cyclic1

/-!
# `SU(2) ≅ U` and the `2 : 1` homomorphism `SU(2) → SO(3)`
-/

open Matrix Complex

noncomputable section

namespace Section23

/-- Every `A ∈ SU(2)` has the shape `!![a, b; -b̄, ā]` with `|a|² + |b|² = 1`. -/
lemma su2_entries (A : SU2) :
    (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = -(starRingEnd ℂ) ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1) ∧
    (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = (starRingEnd ℂ) ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ∧
    normSq ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) + normSq ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1)
      = 1 := by
  obtain ⟨M, hM⟩ := A
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff] at hM
  obtain ⟨hu, hdet⟩ := hM
  have hu' : star M * M = 1 := mul_eq_one_comm.mp hu
  have hadj : M * M.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  have hstar : star M = M.adjugate := by
    calc star M = star M * (M * M.adjugate) := by rw [hadj, mul_one]
      _ = M.adjugate := by rw [← mul_assoc, hu', one_mul]
  rw [Matrix.adjugate_fin_two] at hstar
  have e01 := congrFun (congrFun hstar 0) 1
  have e11 := congrFun (congrFun hstar 1) 1
  have h00 := congrFun (congrFun hu 0) 0
  simp [Matrix.star_apply] at e01 e11 h00
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.mul_conj] at h00
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (starRingEnd ℂ) e01
  · simpa using congrArg (starRingEnd ℂ) e11
  · exact_mod_cast h00

/-- The quaternion `a + b j` attached to the matrix `!![a, b; -b̄, ā]`. -/
def quatOfMat (M : Matrix (Fin 2) (Fin 2) ℂ) : Quaternion ℝ :=
  ⟨(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im⟩

/-- The matrix `!![a, b; -b̄, ā]` attached to the quaternion `a + b j`. -/
def matOfQuat (q : Quaternion ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩;
    -(starRingEnd ℂ) ⟨q.imJ, q.imK⟩, (starRingEnd ℂ) ⟨q.re, q.imI⟩]

lemma normSq_entries (A : SU2) :
    ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2 + ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im ^ 2 +
    ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re ^ 2 + ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im ^ 2
      = 1 := by
  have := (su2_entries A).2.2
  simp only [Complex.normSq_apply] at this
  linarith

lemma quatOfMat_mem (A : SU2) : quatOfMat A ∈ UnitQuat := by
  have h := normSq_entries A
  rw [Unitary.mem_iff]
  constructor <;> ext <;> simp [quatOfMat] <;> sorry -- nlinarith [h]

lemma unitQuat_normSq (q : UnitQuat) :
    (q : Quaternion ℝ).re ^ 2 + (q : Quaternion ℝ).imI ^ 2 + (q : Quaternion ℝ).imJ ^ 2 +
      (q : Quaternion ℝ).imK ^ 2 = 1 := by
  have h := Unitary.coe_star_mul_self q
  rw [Quaternion.star_mul_self] at h
  have h' : Quaternion.normSq (q : Quaternion ℝ) = 1 := by
    have := congrArg (fun p : Quaternion ℝ => p.re) h
    simpa only [Quaternion.re_coe, Quaternion.re_one] using this
  rw [Quaternion.normSq_def'] at h'
  exact h'

lemma matOfQuat_mem (q : UnitQuat) : matOfQuat q ∈ SU2 := by
  have h := unitQuat_normSq q
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matOfQuat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
      apply Complex.ext <;> simp <;> nlinarith [h]
  · simp [matOfQuat, Matrix.det_fin_two]
    apply Complex.ext <;> simp <;> nlinarith [h]

lemma quatOfMat_mul (A B : SU2) :
    quatOfMat ((A * B : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = quatOfMat A * quatOfMat B := by
  obtain ⟨hA1, hA2, -⟩ := su2_entries A
  obtain ⟨hB1, hB2, -⟩ := su2_entries B
  simp only [Submonoid.coe_mul]
  ext <;> simp [quatOfMat, Matrix.mul_apply, Fin.sum_univ_two, hB1, hB2] <;> ring

/-- The isomorphism `SU(2) ≅ U = {q ∈ ℍ : q q* = 1}`, `!![a, b; -b̄, ā] ↦ a + b j`. -/
def SU2EquivUnitQuat : SU2 ≃* UnitQuat where
  toFun A := ⟨quatOfMat A, quatOfMat_mem A⟩
  invFun q := ⟨matOfQuat q, matOfQuat_mem q⟩
  left_inv A := by
    obtain ⟨h1, h2, -⟩ := su2_entries A
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matOfQuat, quatOfMat, h1, h2]
  right_inv q := by
    apply Subtype.ext
    ext <;> simp [matOfQuat, quatOfMat]
  map_mul' A B := Subtype.ext (quatOfMat_mul A B)

lemma SU2EquivUnitQuat_apply (A : SU2) :
    (SU2EquivUnitQuat A : Quaternion ℝ) =
      ⟨((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re, ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im,
        ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re, ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im⟩ :=
  rfl

lemma SU2EquivUnitQuat_diagHom (z : Circle) : SU2EquivUnitQuat (diagHom z) = quatHom z := by
  apply Subtype.ext
  ext <;> simp [SU2EquivUnitQuat_apply, diagHom, diagMat, quatHom, quatOf]

/-- The matrix, in the basis `i, j, k` of the pure quaternions, of `v ↦ q v q̄`. -/
def rotMatOfQuat (q : Quaternion ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let w := q.re; let x := q.imI; let y := q.imJ; let z := q.imK
  !![w^2 + x^2 - y^2 - z^2, 2 * (x * y - w * z), 2 * (x * z + w * y);
     2 * (x * y + w * z), w^2 - x^2 + y^2 - z^2, 2 * (y * z - w * x);
     2 * (x * z - w * y), 2 * (y * z + w * x), w^2 - x^2 - y^2 + z^2]

lemma rotMatOfQuat_mem' (q : Quaternion ℝ) (h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1) :
    rotMatOfQuat q ∈ SO3 := by
  obtain ⟨w, x, y, z⟩ := q
  simp only at h
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotMatOfQuat, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | linear_combination (w^2 + x^2 + y^2 + z^2 + 1) * h
        | ring
  · simp [rotMatOfQuat, Matrix.det_fin_three]
    linear_combination ((w^2 + x^2 + y^2 + z^2)^2 + (w^2 + x^2 + y^2 + z^2) + 1) * h

lemma rotMatOfQuat_mem (q : UnitQuat) : rotMatOfQuat q ∈ SO3 :=
  rotMatOfQuat_mem' q (unitQuat_normSq q)

lemma rotMatOfQuat_mul (p q : Quaternion ℝ) :
    rotMatOfQuat (p * q) = rotMatOfQuat p * rotMatOfQuat q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotMatOfQuat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- The `2 : 1` homomorphism `U → SO(3)`, `q ↦ (v ↦ q v q̄)` on the pure quaternions. -/
def quatToRot : UnitQuat →* SO3 where
  toFun q := ⟨rotMatOfQuat q, rotMatOfQuat_mem q⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotMatOfQuat] <;> sorry
  map_mul' p q := Subtype.ext (rotMatOfQuat_mul p q)

lemma quatToRot_eq_one_iff (q : UnitQuat) : quatToRot q = 1 ↔ q = 1 ∨ q = -1 := by
  constructor
  · intro hq
    have h := unitQuat_normSq q
    have e : ∀ i j, rotMatOfQuat q i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := fun i j =>
      congrFun (congrFun (congrArg Subtype.val hq) i) j
    have e00 := e 0 0; have e11 := e 1 1; have e22 := e 2 2
    have e01 := e 0 1; have e10 := e 1 0; have e02 := e 0 2; have e20 := e 2 0
    have e12 := e 1 2; have e21 := e 2 1
    simp [rotMatOfQuat] at e00 e11 e22 e01 e10 e02 e20 e12 e21
    have hx : (q : Quaternion ℝ).imI = 0 := by nlinarith
    have hy : (q : Quaternion ℝ).imJ = 0 := by nlinarith
    have hz : (q : Quaternion ℝ).imK = 0 := by nlinarith
    have hw : (q : Quaternion ℝ).re ^ 2 = 1 := by rw [hx, hy, hz] at h; linarith
    have hw' : (q : Quaternion ℝ).re = 1 ∨ (q : Quaternion ℝ).re = -1 := by
      have h0 : ((q : Quaternion ℝ).re - 1) * ((q : Quaternion ℝ).re + 1) = 0 := by
        linear_combination hw
      rcases mul_eq_zero.mp h0 with h' | h'
      · left; linarith
      · right; linarith
    rcases hw' with hw | hw
    · sorry -- left; apply Subtype.ext; ext <;> simp [hx, hy, hz, hw]
    · sorry -- right; apply Subtype.ext; rw [Unitary.coe_neg]; ext <;> simp [hx, hy, hz, hw]
  · rintro (rfl | rfl)
    · exact map_one _
    · sorry
      -- apply Subtype.ext
      -- ext i j
      -- fin_cases i <;> fin_cases j <;> simp [quatToRot, rotMatOfQuat, Unitary.coe_neg]

lemma quatToRot_quatHom (z : Circle) : quatToRot (quatHom z) = rotHom (z ^ 2) := by
  have h := circle_re_sq_add_im_sq z
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatToRot, rotMatOfQuat, quatHom, quatOf, rotHom, rotXMat, pow_two,
      Circle.coe_mul] <;> nlinarith [h]

/-- The `2 : 1` homomorphism `π : SU(2) → SO(3)` (via `SU(2) ≅ U`). -/
def coverMap : SU2 →* SO3 := quatToRot.comp SU2EquivUnitQuat.toMonoidHom

/-- The kernel of `π : SU(2) → SO(3)` is `{I₂, -I₂}`. -/
theorem coverMap_eq_one_iff (A : SU2) :
    coverMap A = 1 ↔
      (A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  obtain ⟨h1, h2, -⟩ := su2_entries A
  rw [coverMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, quatToRot_eq_one_iff]
  constructor
  · rintro (h | h)
    · left
      have h' := congrArg Subtype.val h
      rw [SU2EquivUnitQuat_apply] at h'
      simp only [Quaternion.ext_iff] at h'
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, h2] <;> apply Complex.ext <;> simp_all
    · sorry
      -- right
      -- have h' := congrArg Subtype.val h
      -- rw [SU2EquivUnitQuat_apply, Unitary.coe_neg] at h'
      -- simp only [Quaternion.ext_iff] at h'
      -- ext i j
      -- fin_cases i <;> fin_cases j <;> simp [h1, h2] <;> apply Complex.ext <;> simp_all
  · rintro (h | h) <;> sorry
    -- · left; apply Subtype.ext; rw [SU2EquivUnitQuat_apply, h]; ext <;> simp
    -- · right; apply Subtype.ext; rw [SU2EquivUnitQuat_apply, h, Unitary.coe_neg]; ext <;> simp

lemma coverMap_diagHom (z : Circle) : coverMap (diagHom z) = rotHom (z ^ 2) := by
  rw [coverMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, SU2EquivUnitQuat_diagHom,
    quatToRot_quatHom]

end Section23

#min_imports
