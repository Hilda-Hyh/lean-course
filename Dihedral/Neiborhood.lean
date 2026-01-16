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

lemma lemma_2_5_a (u v : Vertex) (d : Degree) :
    HasChain u v d →
    ∃ (r s : ℕ), d.d0 = (getDegree (u⁻¹ * v)).d0 + 2 * r ∧
                 d.d1 = (getDegree (u⁻¹ * v)).d1 + 2 * s := by
  intro h
  sorry


lemma lemma_2_5_b (u v : Vertex) (d : Degree) (h : HasChain u v d) :
    getDegree (u⁻¹ * v) ≤ d := by
  obtain ⟨r, s, hr, hs⟩ := lemma_2_5_a u v d h
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
  intro h_cond
  -- Ad u d 是有限集，因此必然存在极大元。

  sorry

theorem lemma_3_1_b (a : ℕ) :
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
  sorry

lemma lemma_3_4_b (u : Vertex) (d : Degree) (z : Vertex) (v : Vertex)
    (hz : z ∈ CurveNeighborhood 1 d) (hv : v ∈ CurveNeighborhood u d) :
    cs.length (u⁻¹ * v) ≤ cs.length z := by
  sorry

theorem lemma_3_5 (u v : Vertex) (d : Degree) :
    v ∈ CurveNeighborhood u d → (u⁻¹ * v) ∈ Ad u d := by
  intro hv
  constructor
  ·
    by_cases hu : u = 1
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
