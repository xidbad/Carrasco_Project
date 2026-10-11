import SL.SpinCover
import Mathlib.Analysis.Matrix.PosDef

/-!
# Section 2.2, item 1: finite subgroups of `SL(2, ℂ)`, the conjugate-imaginary group `G*`
and the finite group of rotations `Ḡ ≤ SO(3)`

* `conjugateGroup G` is the conjugate-imaginary group `G*` of the paper; it is isomorphic to `G`
  and its elements map `(z̄₁, z̄₂)` to the conjugate of `g (z₁, z₂)`.
* A finite subgroup of `SL(2, ℂ)` is conjugate (inside `SL(2, ℂ)`) to a subgroup of `SU(2)`
  (this is the reduction to `SU(2)` that the paper takes from its earlier results).
* Consequently every finite `G ≤ SL(2, ℂ)` yields a finite group of rotations `Ḡ ≤ SO(3)` with
  `|G| = 2 |Ḡ|` if `-I₂ ∈ G` and `|G| = |Ḡ|` otherwise.
-/

namespace Section22
open Matrix Complex ComplexConjugate ComplexOrder

/-- The group `SL(2, ℂ)`. -/
abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) ℂ

/-- Entrywise complex conjugation `SL(2, ℂ) →* SL(2, ℂ)`. -/
noncomputable def conjHom : SL2 →* SL2 := SpecialLinearGroup.map (starRingEnd ℂ)

theorem conjHom_injective : Function.Injective conjHom := by
  intro g h hgh
  ext i j
  have := congrArg (fun x : SL2 => (x : Matrix (Fin 2) (Fin 2) ℂ) i j) hgh
  exact (starRingEnd ℂ).injective (by simpa [conjHom] using this)

/-- The *conjugate-imaginary group* `G*` of `G ≤ SL(2, ℂ)`. -/
noncomputable def conjugateGroup (G : Subgroup SL2) : Subgroup SL2 := G.map conjHom

/-- `G*` is isomorphic to `G`. -/
noncomputable def conjugateGroupEquiv (G : Subgroup SL2) : G ≃* conjugateGroup G :=
  G.equivMapOfInjective conjHom conjHom_injective

/-- The element `g* ∈ G*` maps `(z̄₁, z̄₂)` to `(conj (a z₁ + b z₂), conj (c z₁ + d z₂))`. -/
theorem conjHom_mulVec (g : SL2) (z : Fin 2 → ℂ) :
    ((conjHom g : SL2) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (fun i => conj (z i)) =
      fun i => conj (((g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ z) i) := by
  ext i
  simp [conjHom, mulVec, dotProduct, Fin.sum_univ_two]

/-- A positive definite `2 × 2` Hermitian matrix is, up to a positive scalar, of the form
`Pᴴ P` with `det P = 1`. -/
theorem exists_det_one_conjTranspose_mul_self {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.PosDef) :
    ∃ (P : Matrix (Fin 2) (Fin 2) ℂ) (c : ℝ), P.det = 1 ∧ 0 < c ∧ Pᴴ * P = (c : ℂ) • M := by
  have hH := hM.isHermitian
  have h00 := hM.diag_pos (i := 0)
  have hdet := hM.det_pos
  rw [Complex.pos_iff] at h00 hdet
  have h10 : M 1 0 = conj (M 0 1) := (hH.apply 1 0).symm
  have h11 : M 1 1 = ((M 1 1).re : ℂ) := by
    have := hH.apply 1 1
    have := congrArg Complex.im this
    simp at this
    exact Complex.ext rfl (by simp; linarith)
  set r := (M 0 0).re with hr
  set D := (M.det).re with hD
  set β := M 0 1
  have hM00 : M 0 0 = r := Complex.ext rfl (by simpa using h00.2.symm)
  have hMdet : M.det = D := Complex.ext rfl (by simpa using hdet.2.symm)
  rw [det_fin_two, hM00, h10, h11] at hMdet
  have hrpos : 0 < r := h00.1
  have hDpos : 0 < D := hdet.1
  set δ := (M 1 1).re
  have hδ : r * δ - normSq β = D := by
    have := congrArg Complex.re hMdet
    simp [Complex.mul_re] at this
    rw [normSq_apply]; linarith
  set s := Real.sqrt D
  have hspos : 0 < s := Real.sqrt_pos.mpr hDpos
  set t := Real.sqrt s
  have htpos : 0 < t := Real.sqrt_pos.mpr hspos
  have hsr : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hrpos).ne'
  have hrr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hrpos.le
  have hDr : Real.sqrt (D / r) * Real.sqrt (D / r) = D / r := Real.mul_self_sqrt (by positivity)
  have htt : t * t = s := Real.mul_self_sqrt hspos.le
  have hss : s * s = D := Real.mul_self_sqrt hDpos.le
  have hdS : Real.sqrt r * Real.sqrt (D / r) = s := by
    rw [← Real.sqrt_mul hrpos.le, mul_div_cancel₀ _ hrpos.ne']
  set S : Matrix (Fin 2) (Fin 2) ℂ := !![(Real.sqrt r : ℂ), β / Real.sqrt r; 0, Real.sqrt (D / r)]
  refine ⟨((1 / t : ℝ) : ℂ) • S, 1 / s, ?_, by positivity, ?_⟩
  · rw [det_smul, det_fin_two]
    simp only [S, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    have : (1 / t) ^ 2 * (Real.sqrt r * Real.sqrt (D / r)) = 1 := by
      rw [hdS]; field_simp; nlinarith
    simp only [Fintype.card_fin, mul_zero, sub_zero]
    exact_mod_cast this
  · have htC : (t : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
    have hsrC : (Real.sqrt r : ℂ) ≠ 0 := by exact_mod_cast hsr
    have hr0C : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have httC : (t : ℂ) * t = s := by exact_mod_cast htt
    have hrrC : (Real.sqrt r : ℂ) * Real.sqrt r = r := by exact_mod_cast hrr
    have hDrC : (Real.sqrt (D / r) : ℂ) * Real.sqrt (D / r) = D / r := by exact_mod_cast hDr
    have hδC : (r : ℂ) * δ - conj β * β = D := by linear_combination hMdet
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S, Matrix.mul_apply, Fin.sum_univ_two, hM00, h10, h11]
    · rw [← httC, ← hrrC]; ring
    · rw [← httC]; field_simp; rfl
    · rw [← httC]; field_simp
    · rw [show (↑t)⁻¹ * ((starRingEnd ℂ) β / ↑√r) * ((↑t)⁻¹ * (β / ↑√r)) +
          (↑t)⁻¹ * ↑√(D / r) * ((↑t)⁻¹ * ↑√(D / r)) =
          (t * t : ℂ)⁻¹ * (conj β * β / (√r * √r) + √(D / r) * √(D / r)) by field_simp]
      rw [hrrC, hDrC, httC]
      congr 1
      field_simp
      linear_combination (-1 : ℂ) * hδC

/-- For a finite subgroup `G ≤ SL(2, ℂ)` there is a `G`-invariant positive definite
Hermitian form. -/
theorem exists_invariant_posDef (G : Subgroup SL2) [Finite G] :
    ∃ M : Matrix (Fin 2) (Fin 2) ℂ, M.PosDef ∧
      ∀ g ∈ G, (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * M * g = M := by
  classical
  haveI := Fintype.ofFinite G
  refine ⟨∑ g : G, ((g : SL2) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (g : SL2), ?_, ?_⟩
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))]
    have hsum : ∀ s : Finset G, (∑ x ∈ s, (((x : SL2) : Matrix (Fin 2) (Fin 2) ℂ))ᴴ *
        ((x : SL2) : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef :=
      fun s => posSemidef_sum s (fun x _ => posSemidef_conjTranspose_mul_self _)
    have h1 : (((1 : G) : SL2) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
        (((1 : G) : SL2) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp
    rw [h1]
    exact (PosDef.one (R := ℂ) (n := Fin 2)).add_posSemidef (hsum _)
  · intro h hh
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight ⟨h, hh⟩) _ _ (fun g => ?_)
    simp [conjTranspose_mul, Matrix.mul_assoc]

/-- A finite subgroup of `SL(2, ℂ)` is conjugate in `SL(2, ℂ)` to a subgroup of `SU(2)`. -/
theorem exists_conj_mem_SU2 (G : Subgroup SL2) [Finite G] :
    ∃ P : SL2, ∀ g ∈ G, ((P * g * P⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) ℂ) ∈
      specialUnitaryGroup (Fin 2) ℂ := by
  obtain ⟨M, hM, hinv⟩ := exists_invariant_posDef G
  obtain ⟨P, c, hdet, -, hPM⟩ := exists_det_one_conjTranspose_mul_self hM
  set P' : SL2 := ⟨P, hdet⟩ with hP'
  refine ⟨P', fun g hg => ?_⟩
  rw [mem_specialUnitaryGroup_iff]
  refine ⟨?_, (P' * g * P'⁻¹).prop⟩
  rw [mem_unitaryGroup_iff']
  have hcoe : ((P' * g * P'⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) ℂ) =
      P * (g : Matrix (Fin 2) (Fin 2) ℂ) * adjugate P := by
    rfl
  rw [hcoe]
  set Q := adjugate P
  have hPQ : P * Q = 1 := by rw [mul_adjugate, hdet, one_smul]
  have key : (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (Pᴴ * P) * g = Pᴴ * P := by
    rw [hPM, Matrix.mul_smul, Matrix.smul_mul, hinv g hg]
  calc star (P * (g : Matrix (Fin 2) (Fin 2) ℂ) * Q) * (P * (g : Matrix (Fin 2) (Fin 2) ℂ) * Q)
      = Qᴴ * ((g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (Pᴴ * P) * g) * Q := by
        rw [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = (P * Q)ᴴ * (P * Q) := by
        rw [key, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hPQ]; simp

open Classical in
/-- **Section 2.2, item 1.** Let `G ⊂ SL(2, ℂ)` be finite. After a change of coordinates
`g ↦ P g P⁻¹` (with `P ∈ SL(2, ℂ)`), `G` becomes a group `H ≤ SU(2)` isomorphic to `G`, and the
change of variables `X, Y, Z` gives a finite group of rotations `Ḡ = rhoHom(H) ≤ SO(3)` with
`|G| = 2 |Ḡ|` if `-I₂ ∈ G` and `|G| = |Ḡ|` otherwise. -/
theorem finite_SL2_to_SO3 (G : Subgroup SL2) [Finite G] :
    ∃ (P : SL2) (H : Subgroup SU2) (e : G ≃* H),
      (∀ g : G, (((e g : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) =
        ((P * g * P⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      Finite (H.map rhoHom) ∧
      Nat.card G = (if ∃ g ∈ G, (g : Matrix (Fin 2) (Fin 2) ℂ) = -1 then 2 else 1) *
        Nat.card (H.map rhoHom) := by
  obtain ⟨P, hP⟩ := exists_conj_mem_SU2 G
  let φ : G →* SU2 :=
    { toFun := fun g => ⟨((P * g * P⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) ℂ), hP g g.2⟩
      map_one' := by ext1; simp
      map_mul' := fun g h => by
        apply Subtype.ext
        change ((P * ((g * h : G) : SL2) * P⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) ℂ) =
          ((P * g * P⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) ℂ) * ((P * h * P⁻¹ : SL2) : Matrix _ _ ℂ)
        show _ = ((P * g * P⁻¹ * (P * h * P⁻¹) : SL2) : Matrix (Fin 2) (Fin 2) ℂ)
        congr 1
        simp only [Subgroup.coe_mul]
        group }
  have hφ : Function.Injective φ := by
    intro g h hgh
    have := congrArg (fun x : SU2 => (x : Matrix (Fin 2) (Fin 2) ℂ)) hgh
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk] at this
    have h2 : (P * (g : SL2) * P⁻¹ : SL2) = P * (h : SL2) * P⁻¹ := Subtype.ext this
    exact Subtype.ext (by simpa using h2)
  haveI : Finite φ.range := Finite.of_equiv G (MonoidHom.ofInjective hφ).toEquiv
  refine ⟨P, φ.range, MonoidHom.ofInjective hφ, fun g => rfl, inferInstance, ?_⟩
  have hcard : Nat.card G = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
  rw [hcard, card_eq_card_map_rhoHom]
  congr 2
  set Pm : Matrix (Fin 2) (Fin 2) ℂ := (P : Matrix (Fin 2) (Fin 2) ℂ)
  set Qm : Matrix (Fin 2) (Fin 2) ℂ := ((P⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) ℂ)
  have hPQ : Pm * Qm = 1 :=
    congrArg (fun x : SL2 => (x : Matrix (Fin 2) (Fin 2) ℂ)) (mul_inv_cancel P)
  have hQP : Qm * Pm = 1 :=
    congrArg (fun x : SL2 => (x : Matrix (Fin 2) (Fin 2) ℂ)) (inv_mul_cancel P)
  apply propext
  constructor
  · rintro ⟨x, ⟨g, rfl⟩, hx⟩
    refine ⟨g, g.2, ?_⟩
    change Pm * ((g : SL2) : Matrix (Fin 2) (Fin 2) ℂ) * Qm = -1 at hx
    calc ((g : SL2) : Matrix (Fin 2) (Fin 2) ℂ)
        = (Qm * Pm) * ((g : SL2) : Matrix (Fin 2) (Fin 2) ℂ) * (Qm * Pm) := by
          rw [hQP, Matrix.one_mul, Matrix.mul_one]
      _ = Qm * (Pm * ((g : SL2) : Matrix (Fin 2) (Fin 2) ℂ) * Qm) * Pm := by
          simp only [Matrix.mul_assoc]
      _ = -1 := by rw [hx, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hQP]
  · rintro ⟨g, hg, hg1⟩
    refine ⟨φ ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩, ?_⟩
    change Pm * (g : Matrix (Fin 2) (Fin 2) ℂ) * Qm = -1
    rw [hg1, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hPQ]

end Section22

#min_imports
