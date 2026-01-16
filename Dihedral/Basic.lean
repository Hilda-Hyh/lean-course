import Mathlib

--无限二面体群由sr0、sr1生成
open DihedralGroup
notation "D∞" => DihedralGroup 0

example (n : ℕ) (i : ZMod n) : sr i * sr i = 1 := sr_mul_self i

example (i : ZMod 0) : sr i ≠ 1 := by
  have h1: r (0 : ZMod 0) = 1 := r_zero
  by_contra h
  have h2: r (0 : ZMod 0) = sr (i : ZMod 0) := by rw [←h1] at h; exact h.symm
  contradiction

lemma r1_in_D :
  r (1 : ZMod 0) ∈ (Subgroup.closure ({sr (0 : ZMod 0), sr (1)} : Set (DihedralGroup 0))) := by
  have h_r1 : r (1 : ZMod 0) = sr 0 * sr 1 := by simp only [sr_mul_sr, sub_zero]
  rw [h_r1]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem (sr 0) rfl))
--r k = (s0 * s1) ^ k
lemma r_zpow_in_D : ∀ k : ℤ, r (k : ZMod 0) ∈ (Subgroup.closure ({sr (0 : ZMod 0),
  sr (1 : ZMod 0)} : Set (DihedralGroup 0))) := by
  intro k
  have h_r1 := r1_in_D
  have : (r (1 : ZMod 0)) ^ (k : _) = r (k : ZMod 0) := by simp only [r_zpow, one_mul, r.injEq]; rfl
  rw [← this]
  exact Subgroup.zpow_mem _ h_r1 (k : _)
--sr i = s0 * (s0 * s1) ^ i
lemma sri_in_D : ∀ i : ZMod 0, sr i ∈ (Subgroup.closure ({sr (0 : ZMod 0),
  sr (1 : ZMod 0)} : Set (DihedralGroup 0))) := by
  intro i
  have : sr (0 : ZMod 0) * r (i : ZMod 0) = sr i := by simp only [sr_mul_r, zero_add]
  have hk := r_zpow_in_D (i : ℤ)
  rw [← this]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) hk

theorem D_generated_by_sr0_sr1 :
  (Subgroup.closure ({sr (0 : ZMod 0), sr (1 : ZMod 0)} : Set (DihedralGroup 0))) = ⊤ := by
  apply eq_top_iff.mpr
  intro g
  cases g with
  | r a => intro g; exact r_zpow_in_D (a : ℤ)
  | sr b => intro g; exact sri_in_D b

def s0 : DihedralGroup 0 := sr (0 : ZMod 0)
def s1 : DihedralGroup 0 := sr (1 : ZMod 0)
--CoxeterMatrix非对角线上的元素为0
theorem s0s1_infty_order (k : ℕ) (hk : k ≠ 0) : (s0 * s1) ^ k ≠ 1 := by
  have h1 : s0 * s1 = r (1 : ZMod 0) := by simp_all only [ne_eq]; rfl
  have h2 : (s0 * s1) ^ k = r (k : ZMod 0) := by simp_all only [ne_eq, r_pow, one_mul]
  intro eq
  have hr : r (k : ZMod 0) = 1 := by simp_all only [ne_eq, r_pow, one_mul]
  have h : r (k : ZMod 0) = r (0 : ZMod 0) := by
    rw [←DihedralGroup.r_zero] at hr
    exact hr
  have hk' : (k : ZMod 0) = (0 : ZMod 0) := by
    injection hr with h_arg
  simp_all only [ne_eq, r_pow, mul_zero, r_zero, Nat.cast_eq_zero]

--D∞ is a CoxeterSystem with CoxeterMatrix M
open DihedralGroup CoxeterSystem

def B : Type := Fin 2
def M : CoxeterMatrix (Fin 2) :=
{ M := !![1, 0; 0, 1],
  isSymm := by apply Matrix.IsSymm.ext; simp
  diagonal := by simp
  off_diagonal := by simp}

def f : Fin 2 → DihedralGroup 0
| 0 => s0
| 1 => s1

lemma f_sq_one (i : Fin 2) : (f i) * (f i) = 1 := by
  fin_cases i
  all_goals
    simp [f]
    rfl

lemma f_is_liftable : M.IsLiftable f := by
  change  ∀ i i', (f i * f i') ^ M i i' = 1
  intro i j
  simp only [M, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  fin_cases i
  <;>
  fin_cases j
  <;>simp
  <;>rfl

lemma fi_inv (i : Fin 2) : (f i)⁻¹ = f i := by
  exact inv_eq_of_mul_eq_one_left (f_sq_one i)

def φ : M.Group →* DihedralGroup 0 := (M.toCoxeterSystem).lift ⟨f, f_is_liftable⟩

def s0m := M.simple (0 : Fin 2)
def s1m := M.simple (1 : Fin 2)
def cs' := M.toCoxeterSystem

lemma conj_eq_inv {z : ℤ} : s0m * (s0m * s1m)^ z * s0m =( (s0m * s1m)⁻¹)^ z := by
  have ss0 := cs'.simple_sq (0 : Fin 2)
  have ss1 := cs'.simple_sq (1 : Fin 2)
  have h1 : s0m * (s0m * s1m) * s0m = (s0m * s1m)⁻¹ := by
    calc s0m * (s0m * s1m) * s0m = (s0m * s0m) * s1m * s0m := by group
      _ = 1 * s1m * s0m := by congr
      _ = s1m * s0m := by simp
      _ = (s0m * s1m)⁻¹ := by
        group
        simp_all only [Fin.isValue, CoxeterMatrix.toCoxeterSystem_simple,
          Int.reduceNeg, zpow_neg, zpow_one, cs']
        congr
        · symm
          exact inv_eq_of_mul_eq_one_left ss1
        · symm
          exact inv_eq_of_mul_eq_one_left ss0
  induction z using Int.induction_on with
  | zero =>
      simp only [zpow_zero, mul_one]
      exact ss0
  | succ n ih=>
      calc s0m * (s0m * s1m) ^ (n + 1) * s0m
    _ = s0m * (s0m * s1m) ^ n * (s0m * s1m) * s0m := by rw [pow_succ];group
    _ = s0m * (s0m * s1m) ^ n *(s0m * s0m) * (s0m * s1m) * s0m := by
      rw [show s0m *s0m = 1 by exact ss0, mul_one]
    _ = (s0m * (s0m * s1m) ^ n *s0m) * (s0m * (s0m * s1m) * s0m) := by group
    _ = (s0m * s1m)⁻¹ ^ (n + 1) := by
      simp only [zpow_natCast, mul_inv_rev, h1] at ih ⊢;rw [ih, pow_succ]
  | pred n ih =>
    calc s0m * (s0m * s1m) ^ (-(n : ℤ)- 1) * s0m
    _ = s0m * (s0m * s1m) ^ (-(n : ℤ)) * (s0m * s1m)⁻¹ * s0m := by rw [zpow_sub];group
    _ = s0m * (s0m * s1m) ^ (-(n : ℤ)) *(s0m * s0m) * (s0m * s1m)⁻¹ * s0m := by
      rw [show s0m *s0m = 1 by exact ss0, mul_one]
    _ = (s0m * (s0m * s1m) ^ (-(n : ℤ)) * s0m) * s0m * (s0m * s1m)⁻¹ * s0m := by group
    _ = (s0m * s1m)⁻¹ ^ (-(n : ℤ)) * s0m * (s0m * (s0m * s1m) * s0m) * s0m := by
      rw [ih]; congr; rw [← h1]
    _ = (s0m * s1m)⁻¹ ^ (-(n : ℤ)) * (s0m * s0m) * (s0m * s1m) * (s0m * s0m) := by group
    _ = (s0m * s1m)⁻¹ ^ (-(n : ℤ)) * (s0m * s1m) := by
      rw [show s0m *s0m = 1 by exact ss0, mul_one, mul_one]
    _ = (s0m * s1m)⁻¹ ^ (-(n : ℤ) - 1) := by rw [zpow_sub];congr

def ψ : DihedralGroup 0 →* M.Group where
  toFun := fun x =>
    match x with
    | DihedralGroup.r i =>
      (s0m * s1m) ^ (i.cast : ℤ)
    | DihedralGroup.sr i =>
      s0m * (s0m * s1m) ^ (i.cast : ℤ)
  map_one' := by
    rw [show (1 : D∞) = r (0 : ZMod 0) by rfl]
    simp only [ZMod.cast_zero, zpow_zero]
  map_mul' := by
    rintro (a | a) (b | b)
    all_goals
      simp; group
    · calc s0m * (s0m * s1m) ^ ((b.cast : ℤ) - a.cast)
        _ =s0m * (s0m * s1m) ^ ((b.cast : ℤ) - a.cast) * 1 := by rw [mul_one]
        _ =s0m * (s0m * s1m) ^ ((b.cast : ℤ) - a.cast) * (s0m * s0m) := by
          congr; symm ;exact cs'.simple_sq (0 : Fin 2)
        _ =(s0m * (s0m * s1m) ^ ((b.cast : ℤ) - a.cast) * s0m) *s0m := by group
        _ =((s0m * s1m)⁻¹ ^ (((b.cast : ℤ) - a.cast))) * s0m := by rw [conj_eq_inv]
        _ =(s0m * s1m) ^ (a.cast : ℤ) * (s0m * s1m)⁻¹ ^ (b.cast : ℤ) * s0m := by
          rw [inv_zpow, ←zpow_neg, neg_sub, zpow_sub, inv_zpow]
        _ =(s0m * s1m) ^ (a.cast : ℤ) *s0m * (s0m * s1m)^ (b.cast : ℤ) * (s0m * s0m) := by
          rw [←conj_eq_inv];group
        _ =(s0m * s1m) ^ (a.cast : ℤ) * s0m * (s0m * s1m) ^ (b.cast : ℤ) := by
          rw [show s0m *s0m = 1 by exact cs'.simple_sq (0 : Fin 2), mul_one]
    · rw [conj_eq_inv, inv_zpow, ←zpow_neg, ← zpow_add, add_comm]
      rfl

noncomputable def mulEquiv : D∞ ≃* M.Group where
  toFun := ψ.toFun
  invFun := φ.toFun
  left_inv := by
    intro x
    cases x with
    | r i =>
      dsimp [ψ]
      have : φ ((s0m * s1m) ^ (i.cast : ℤ)) = (f 0 * f 1) ^ (i.cast : ℤ) := by simp; congr
      rw [this, f, f, show (s0 * s1) = r 1 by rfl]
      simp
    | sr i =>
      simp only [ψ, OneHom.toFun_eq_coe, OneHom.coe_mk, MonoidHom.toOneHom_coe, map_mul, map_zpow]
      rw [show φ (s0m) = f 0 by rfl, show φ (s1m) = f 1 by rfl]
      dsimp [f]
      rw [show (s0 * s1) = r 1 by rfl, show s0 = sr (0 : ZMod 0) by rfl]
      simp
  right_inv := by
    have h : (ψ.comp φ) = { toFun := fun x => x,
                            map_one' := by simp,
                            map_mul' := by intros; simp } := by
      apply (M.toCoxeterSystem).ext_simple
      intro i
      simp only [MonoidHom.comp_apply]
      have hφ := (M.toCoxeterSystem).lift_apply_simple (f_is_liftable) i
      fin_cases i
      all_goals
        dsimp [ψ]; simp_all only [Fin.zero_eta, Fin.isValue, CoxeterMatrix.toCoxeterSystem_simple]
      · rfl
      · dsimp [φ] at *
        rw [hφ, f, s1]
        simp only [dvd_refl, ZMod.cast_one, zpow_one, Fin.isValue]
        group
        change M.simple 0 ^2 * M.simple 1 = M.simple 1
        simp only [Fin.isValue, mul_eq_right]
        exact (M.toCoxeterSystem).simple_sq (0 : Fin 2)
    intro g
    exact congrArg (fun m => m.toFun g) h
  map_mul' := by
    exact ψ.map_mul'

noncomputable def cs : CoxeterSystem M (DihedralGroup 0) :=
  { mulEquiv := mulEquiv}
