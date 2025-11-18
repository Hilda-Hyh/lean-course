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

lemma all_sr_in_closure : ∀ i : ZMod 0, sr i ∈ (Subgroup.closure ({sr (0 : ZMod 0),
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
  | sr b => intro g; exact all_sr_in_closure b



#check CoxeterSystem.length
