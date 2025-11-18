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

lemma r_zpow_in_D : ∀ k : ℤ, r (k : ZMod 0) ∈ (Subgroup.closure ({sr (0 : ZMod 0),
  sr (1 : ZMod 0)} : Set (DihedralGroup 0))) := by
  intro k
  have h_r1 := r1_in_D
  have : (r (1 : ZMod 0)) ^ (k : _) = r (k : ZMod 0) := by simp only [r_zpow, one_mul, r.injEq]; rfl
  rw [← this]
  exact Subgroup.zpow_mem _ h_r1 (k : _)

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
  simp_all

--D∞ is a CoxeterSystem with CoxeterMatrix M
open DihedralGroup CoxeterSystem

def M : CoxeterMatrix (Fin 2) :=
{ M := Matrix.of fun (i j : Fin 2) =>
    match i, j with
    | (0 : Fin 2), (0 : Fin 2) => 1
    | (1 : Fin 2), (1 : Fin 2) => 1
    | _, _ => 0,
  isSymm := by apply Matrix.IsSymm.ext; simp
  diagonal := by simp
  off_diagonal := by simp}

def f : Fin 2 → DihedralGroup 0
| 0 => s0
| 1 => s1

lemma f_sq_one (i : Fin 2) : (f i) * (f i) = 1 := by
  fin_cases i
  · simp; rfl
  · simp; rfl

lemma f_is_liftable : M.IsLiftable f := by
  change  ∀ i i', (f i * f i') ^ M i i' = 1
  intro i j
  unfold M
  simp
  aesop

def φ : M.Group →* DihedralGroup 0 := (M.toCoxeterSystem).lift ⟨f, f_is_liftable⟩

def s0m := M.simple (0 : Fin 2)
def s1m := M.simple (1 : Fin 2)

def ψ : DihedralGroup 0 →* M.Group :=
{ toFun := fun x =>
    match x with
    | DihedralGroup.r i =>
      let k : ℤ := (i : ℤ)
      (s0m * s1m)^k
    | DihedralGroup.sr i =>
      let k : ℤ := (i : ℤ)
      s0m * (s0m * s1m)^k,
  map_one' := by
    rw [show (1 : D∞) = r (0 : ZMod 0) by rfl]
    simp only [zpow_zero]
  map_mul' := by
    rintro (a | a) (b | b)
    all_goals
      simp
      group
    · let ai : ℤ := (a : ℤ)
      let bi : ℤ := (b : ℤ)
      have h1 : s0m * (s0m * s1m) * s0m = (s0m * s1m)⁻¹ := by sorry
      calc s0m * (s0m * s1m) ^ (bi - ai)
        _ =s0m * (s0m * s1m) ^ (bi - ai) * 1 := by rw [mul_one]
        _ =s0m * (s0m * s1m) ^ (bi - ai) * (s0m * s0m) := by congr; dsimp [s0m]; sorry
        _ =(s0m * (s0m * s1m) ^ (bi - ai) * s0m) *s0m := by group
        _ =((s0m * s1m) ^ (-(bi - ai))) * s0m := by sorry
      sorry
    · sorry
      }

noncomputable def mulEquiv : D∞ ≃* M.Group :=
{ toFun := ψ.toFun,
  invFun := φ.toFun,
  left_inv := by
    intro x
    cases x with
    | r i =>
      dsimp [ψ]
      let k : ℤ := (i : ℤ)
      have : φ ((s0m * s1m) ^ k) = (f 0 * f 1) ^ k := by simp; congr
      rw [this, f, f, show (s0 * s1) = r 1 by rfl]
      simp
      rfl
    | sr i =>
      dsimp [ψ]
      simp
      rw [show φ (s0m) = f 0 by rfl, show φ (s1m) = f 1 by rfl]
      dsimp [f]
      rw [show (s0 * s1) = r 1 by rfl, show s0 = sr (0 : ZMod 0) by rfl]
      simp
      rfl
  right_inv := by
    have h : (ψ.comp φ) = { toFun := fun x => x,
                            map_one' := by simp,
                            map_mul' := by intros; simp } := by
      apply (M.toCoxeterSystem).ext_simple
      intro i
      simp only [MonoidHom.comp_apply]
      have hφ := (M.toCoxeterSystem).lift_apply_simple (f_is_liftable) i
      fin_cases i
      · dsimp [ψ]; simp_all; rfl
      · dsimp [ψ]; simp_all
        dsimp [φ] at *
        rw [hφ, f, s1]
        simp only [zpow_one, Fin.isValue]
        group
        change M.simple 0 ^2 * M.simple 1 = M.simple 1
        simp
        exact (M.toCoxeterSystem).simple_sq (0 : Fin 2)
    intro g
    exact congrArg (fun m => m.toFun g) h
  map_mul' := by
    exact ψ.map_mul' }

noncomputable def cs : CoxeterSystem M (DihedralGroup 0) :=
  { mulEquiv := mulEquiv}

theorem length_s0 : cs.length s0 = 1 := by
  have : cs.simple 0 = s0 := rfl
  simpa [this] using length_simple cs (0 : Fin 2)

notation "ℓ" => cs.length

--需定义List的规约
