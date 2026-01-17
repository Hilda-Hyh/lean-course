import Mathlib
import Dihedral.Basic
import Dihedral.Length
import Dihedral.Degree

open CoxeterSystem DihedralGroup Nat
notation "gD" => getDegree
def CanReachWithin (u v : Vertex) (d : Degree) : Prop :=
  exists d', HasChain u v d' ∧ d' ≤ d

--Definition 2.4: 曲线邻域 Gamma_d(u)
def CurveNeighborhood (u : Vertex) (d : Degree) : Set Vertex :=
  { v | CanReachWithin u v d ∧
        ∀ v' : Vertex, CanReachWithin u v' d → Lt v v' → v = v' }

-- 定义集合 A_d(u)
def Ad (u : Vertex) (d : Degree) : Set Vertex :=
  { v | cs.length (u * v) = cs.length u + cs.length v ∧ gD v ≤ d }

-- 定义极大元 (Maximal Element)
def IsMaximalIn (v : Vertex) (S : Set Vertex) : Prop :=
  v ∈ S ∧ ∀ v' ∈ S, v ≤ v' → v = v'

-- 定义集合 S 中的极大元子集
def maximalElements (S : Set Vertex) : Set Vertex :=
  { v | IsMaximalIn v S }

theorem lemma_3_1 (u : Vertex) (d : Degree) :
    (u ≠ 1 ∨ (u = 1 ∧ d.a ≠ d.b)) →
      ∃! v, IsMaximalIn v (Ad u d) := by
  intro h_cond
  rcases h_cond with (h_ne_one | ⟨h_eq_one, h_d_neq⟩)
  · sorry
  · sorry
  -- Ad u d 是有限集，因此必然存在极大元。可能需要用到Zorn？


theorem lemma_3_1_b (a : ℕ) :
    -- 第二部分：d = (a, a) 且 u = 1 的情况
    let S := Ad 1 (Degree.mk a a)
    { v | IsMaximalIn v S } = {(s0*s1)^a , (s1*s0)^a } := by
  sorry

def root_from_degree (d : Degree) : Root :=
  if d.a > d.b then
    ⟨d.b + 1, d.b, Or.inl rfl⟩
  else
    ⟨d.a, d.a + 1, Or.inr rfl⟩

def s_alpha_d (d : Degree) : Vertex := s_α (root_from_degree d)

def s0s1_pow (a : ℕ) : Vertex := listToGroup (alternating 0 (2 * a))
def s1s0_pow (a : ℕ) : Vertex := listToGroup (alternating 1 (2 * a))

-- 结论 A: 证明对于单位元1，曲线邻域就是 Ad(1) 的极大元集合
theorem curve_neighborhood_eq_max_Ad_identity (d : Degree) :
    CurveNeighborhood 1 d = { v | IsMaximalIn v (Ad 1 d) } := by
  sorry

-- 结论 B: Theorem 3.3 的具体计算公式
theorem theorem_3_3 (d : Degree) :
    CurveNeighborhood 1 d =
      if d.a ≠ d.b then
        { s_alpha_d d }
      else
        { s0s1_pow d.a, s1s0_pow d.a } := by
  sorry

-- Lemma 3.4: 关于 u, z ∈ Ad(1) 和 v ∈ Γd(u) 的性质
theorem lemma_3_4_a (u : Vertex) (d : Degree) (z : Vertex) (v : Vertex)
    (hz : z ∈ Ad 1 d) (hv : v ∈ CurveNeighborhood u d) :
    cs.length (u * z) ≤ cs.length v ∧ gD (u⁻¹ * v) ≤ d := by
  sorry

theorem lemma_3_4_b (u : Vertex) (d : Degree) (z : Vertex) (v : Vertex)
    (hz : z ∈ CurveNeighborhood 1 d) (hv : v ∈ CurveNeighborhood u d) :
    cs.length (u⁻¹ * v) ≤ cs.length z := by
  sorry

theorem lemma_3_5 (u v : Vertex) (d : Degree) :
    v ∈ CurveNeighborhood u d → (u⁻¹ * v) ∈ Ad u d := by
  intro hv
  constructor
  · by_cases hu : u = 1
    · simp [hu]
    · -- 对于 u ≠ 1，使用反证法
      by_contra h_not_eq

      have h_le : cs.length (u * (u⁻¹ * v)) ≤ cs.length u + cs.length (u⁻¹ * v) :=
        cs.length_mul_le u (u⁻¹ * v)
      simp only [mul_inv_cancel_left] at h_le h_not_eq

      have h_strict : cs.length v < cs.length u + cs.length (u⁻¹ * v) :=
        Nat.lt_of_le_of_ne h_le h_not_eq
      sorry

  ·
    sorry

-- ... (前文代码保持不变) ...

-- 辅助引理：Ad u d 中的元素必然在 Ad 1 d 中
lemma Ad_subset_Ad_one (u : Vertex) (d : Degree) (v : Vertex) (h : v ∈ Ad u d) : v ∈ Ad 1 d := by
  rw [Ad] at *
  simp only [one_mul, cs.length_one, zero_add, Set.mem_setOf_eq]
  exact And.imp_left (fun a ↦ trivial) h

-- 辅助引理：有限偏序集中，任意元素都小于等于某个极大元
lemma exists_max_ge_in_Ad (u : Vertex) (d : Degree) (z : Vertex) (hz : z ∈ Ad u d) :
    ∃ w, IsMaximalIn w (Ad u d) ∧ z ≤ w := by
  sorry

-- 辅助引理：如果 w ∈ Ad u d，则 u * w 在 d 范围内可达
-- 这联系了 Ad (基于长度和度数) 和 CurveNeighborhood (基于链)
lemma reachable_of_Ad (u : Vertex) (d : Degree) (w : Vertex) (h : w ∈ Ad u d) :
    CanReachWithin u (u * w) d := by
  sorry

-- 如果 x, y ∈ Ad u d, 则 x ≤ y ↔ u * x ≤ u * y
lemma mul_le_mul_left_of_Ad (u : Vertex) (d : Degree) (x y : Vertex)
    (hx : x ∈ Ad u d) (hy : y ∈ Ad u d) :
    x ≤ y ↔ u * x ≤ u * y := by
  sorry

lemma h_maximal_in_gamma : ∀ v' : Vertex,
    CanReachWithin u v' d → Lt (u * w) v' → (u * w) = v' := by
  intro v' h_reach_v' h_lt
  sorry

theorem main_theorem (u : Vertex) (d : Degree) :
    CurveNeighborhood u d = { v | ∃ w, IsMaximalIn w (Ad u d) ∧ v = u * w } := by
  apply Set.ext
  intro v
  constructor
  · -- (⊆): v ∈ Ω_d(u) → v = u * w (w 为极大元)
    intro hv
    -- 根据 Lemma 3.5, z = u⁻¹v ∈ Ad u d
    have h_z_in_Ad : (u⁻¹ * v) ∈ Ad u d := lemma_3_5 u v d hv
    let z := u⁻¹ * v
    obtain ⟨w, hw_max, h_z_le_w⟩ := exists_max_ge_in_Ad u d z h_z_in_Ad
    have hw_in_Ad1 : w ∈ Ad 1 d := Ad_subset_Ad_one u d w hw_max.1
    -- 应用 Lemma 3.4.a 得到长度不等式
    have h_len_ineq := lemma_3_4_a u d w v hw_in_Ad1 hv
    rcases h_len_ineq with ⟨h_len_uw_le_v, _⟩
    have h_len_v : cs.length v = cs.length u + cs.length z := by
      have : v = u * z := by simp [z]
      rw [this]
      exact h_z_in_Ad.1
    have h_len_uw : cs.length (u * w) = cs.length u + cs.length w := hw_max.1.1
    rw [h_len_v, h_len_uw] at h_len_uw_le_v
    have h_len_w_le_z : cs.length w ≤ cs.length z := Nat.le_of_add_le_add_left h_len_uw_le_v
    have h_z_eq_w : z = w := by
      rcases h_z_le_w with h|h'
      · exfalso
        have : z < w := h
        rw [lemma_2_3] at this
        linarith
      · exact h'
    use w
    constructor
    · exact hw_max
    · simp only [z] at h_z_eq_w
      rw [← h_z_eq_w, mul_inv_cancel_left]
  · --  (⊇): v = u * w (w 为极大元) → v ∈ Ω_d(u)
    rintro ⟨w, hw_max, rfl⟩
    have h_reach : CanReachWithin u (u * w) d := reachable_of_Ad u d w hw_max.1
    rw [CurveNeighborhood]
    simp only [Set.mem_setOf_eq]
    constructor
    · exact h_reach
    · exact h_maximal_in_gamma
