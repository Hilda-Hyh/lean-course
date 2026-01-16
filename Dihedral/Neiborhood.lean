import Mathlib
import Dihedral.Basic
import Dihedral.Length
import Dihedral.Degree

open CoxeterSystem DihedralGroup Nat

def CanReachWithin (u v : Vertex) (d : Degree) : Prop :=
  exists d', HasChain u v d' ∧ d' ≤ d

--Definition 2.4: 曲线邻域 Gamma_d(u)
def CurveNeighborhood (u : Vertex) (d : Degree) : Set Vertex :=
  { v | CanReachWithin u v d ∧
        ∀ v' : Vertex, CanReachWithin u v' d → Lt v v' → v = v' }

-- 定义标量乘法
def Degree.scale (n : ℕ) (d : Degree) : Degree :=
  ⟨n * d.d0, n * d.d1⟩

instance : HMul ℕ Degree Degree where
  hMul := Degree.scale

-- 定义度数减法（如果 d1 ≥ d2
def Degree.sub (d1 d2 : Degree) : Degree :=
  ⟨d1.d0 - d2.d0, d1.d1 - d2.d1⟩

lemma two_5_main (u v : Vertex) (d : Degree) :
    HasChain u v d →
    ∃ (r s : ℕ), d.d0 = (getDegree (u⁻¹ * v)).d0 + 2 * r ∧
                 d.d1 = (getDegree (u⁻¹ * v)).d1 + 2 * s := by
  intro h
  sorry


lemma two_5_consequence (u v : Vertex) (d : Degree) (h : HasChain u v d) :
    getDegree (u⁻¹ * v) ≤ d := by
  obtain ⟨r, s, hr, hs⟩ := two_5_main u v d h
  constructor
  · rw [hr]; exact Nat.le_add_right _ _
  · rw [hs]; exact Nat.le_add_right _ _

-- 定义集合 A_d(u)
def Ad (u : Vertex) (d : Degree) : Set Vertex :=
  { v | cs.length (u * v) = cs.length u + cs.length v ∧ getDegree v ≤ d }

-- 定义极大元 (Maximal Element)
def IsMaximalIn (v : Vertex) (S : Set Vertex) : Prop :=
  v ∈ S ∧ ∀ v' ∈ S, v ≤ v' → v = v'

-- 定义集合 S 中的极大元子集
def maximalElements (S : Set Vertex) : Set Vertex :=
  { v | IsMaximalIn v S }

theorem lemma_3_1 (u : Vertex) (d : Degree) :
    -- 第一部分：唯一极大元的情况
    (u ≠ 1 ∨ (u = 1 ∧ d.d0 ≠ d.d1)) →
      ∃! v, IsMaximalIn v (Ad u d) := by
  sorry

theorem lemma_3_1_balanced (a : ℕ) :
    -- 第二部分：d = (a, a) 且 u = 1 的情况
    let S := Ad 1 (Degree.mk a a)
    { v | IsMaximalIn v S } = {(s0*s1)^a , (s1*s0)^a } := by
  sorry

def root_from_degree (d : Degree) : Root :=
  if d.d0 > d.d1 then
    ⟨d.d1 + 1, d.d1, Or.inl rfl⟩
  else
    ⟨d.d0, d.d0 + 1, Or.inr rfl⟩

def s_alpha_d (d : Degree) : Vertex := s_α (root_from_degree d)

def s0s1_pow (a : ℕ) : Vertex := listToGroup (alternating 0 (2 * a))
def s1s0_pow (a : ℕ) : Vertex := listToGroup (alternating 1 (2 * a))

-- 结论 A: 证明对于恒等元，曲线邻域就是 Ad(1) 的极大元集合
theorem curve_neighborhood_eq_max_Ad_identity (d : Degree) :
    CurveNeighborhood 1 d = { v | IsMaximalIn v (Ad 1 d) } := by
  sorry

-- 结论 B: Theorem 3.3 的具体计算公式
theorem theorem_3_3 (d : Degree) :
    CurveNeighborhood 1 d =
      if d.d0 ≠ d.d1 then
        { s_alpha_d d }
      else
        { s0s1_pow d.d0, s1s0_pow d.d0 } := by
  sorry

-- Lemma 3.4: 关于 u, z ∈ Ad(1) 和 v ∈ Γd(u) 的性质
lemma lemma_3_4_a (u : Vertex) (d : Degree) (z : Vertex) (v : Vertex)
    (hz : z ∈ Ad 1 d) (hv : v ∈ CurveNeighborhood u d) :
    cs.length (u * z) ≤ cs.length v ∧ getDegree (u⁻¹ * v) ≤ d := by
  constructor
  · -- 证明 l(uz) ≤ l(v)
    -- 1. 因为 z ∈ Ad(1)，存在从 1 到 z 且度数为 d(z) ≤ d 的链
    -- 2. 在左侧乘上 u，得到从 u 到 uz 且度数相同的链
    -- 3. 由于 v 是从 u 出发度数 ≤ d 的极大元（由 CurveNeighborhood 定义），故其长度必不小于 uz
    sorry
  · -- 证明 d(u⁻¹v) ≤ d
    -- 1. 因为 v ∈ Γd(u)，存在从 u 到 v 且度数 ≤ d 的链
    -- 2. 在左侧乘上 u⁻¹，得到从 1 到 u⁻¹v 且度数相同的链
    -- 3. 根据 Lemma 2.5，该度数必大于等于 d(u⁻¹v)
    sorry

lemma lemma_3_4_b (u : Vertex) (d : Degree) (z : Vertex) (v : Vertex)
    (hz : z ∈ CurveNeighborhood 1 d) (hv : v ∈ CurveNeighborhood u d) :
    cs.length (u⁻¹ * v) ≤ cs.length z := by
  -- 证明逻辑：
  -- 1. z 是 Ad(1) 中的极大元
  -- 2. 由 lemma_3_4_a 知 u⁻¹v ∈ Ad(1)
  -- 3. 在无限二面体群 D∞ 中，Ad(1) 的所有极大元具有相同的长度
  -- 4. 因此，作为 Ad(1) 中的元素，u⁻¹v 的长度不能超过极大元 z 的长度
  sorry

theorem lemma_3_5 (u v : Vertex) (d : Degree) :
    v ∈ CurveNeighborhood u d → (u⁻¹ * v) ∈ Ad u d := by
  intro hv
  constructor
  · -- 第一部分：证明长度相加 ℓ(u * (u⁻¹ * v)) = ℓ u + ℓ (u⁻¹ * v)
    -- 由于 u * (u⁻¹ * v) = v，即 ℓ v = ℓ u + ℓ (u⁻¹ * v)
    by_cases hu : u = 1
    · simp [hu]
    · -- 对于 u ≠ 1，使用反证法
      by_contra h_not_eq

      -- 如果长度不相加，则由 length_add_or_cancel，有 ℓ v < ℓ u + ℓ (u⁻¹ * v)
      have h_le : cs.length (u * (u⁻¹ * v)) ≤ cs.length u + cs.length (u⁻¹ * v) :=
        cs.length_mul_le u (u⁻¹ * v)

      -- 简化：u * (u⁻¹ * v) = v
      simp only [mul_inv_cancel_left] at h_le h_not_eq

      have h_strict : cs.length v < cs.length u + cs.length (u⁻¹ * v) :=
        Nat.lt_of_le_of_ne h_le h_not_eq

      -- 这会导致在 Bruhat 序中 v 不是极大的，矛盾
      -- 具体证明需要更多关于 CurveNeighborhood 定义的细节
      sorry

  · -- 第二部分：证明度数满足限制 getDegree (u⁻¹ * v) ≤ d
    -- 从 v ∈ CurveNeighborhood u d，存在从 u 到 v 的链，其度数 ≤ d
    -- 左乘 u⁻¹ 保持度数，所以 getDegree (u⁻¹ * v) ≤ d
    sorry

theorem main_theorem (u : Vertex) (d : Degree) (hd : d ≠ 0) :
    CurveNeighborhood u d = { v | ∃ w, IsMaximalIn w (Ad u d) ∧ v = u * w } := by
  apply Set.ext
  intro v
  constructor
  · -- 方向 1: v ∈ Ω_d(u) → v = u * w 其中 w 是 Ad(u) 的极大元
    intro hv
    have h_in_Ad : (u⁻¹ * v) ∈ Ad u d := lemma_3_5 u v d hv
    sorry
  · -- 方向 2: v = u * w (w 为极大元) → v ∈ Ω_d(u)
    rintro ⟨w, hw_max, rfl⟩
    sorry
