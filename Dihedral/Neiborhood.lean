import Mathlib
import Dihedral.Basic
import Dihedral.Length
import Dihedral.Degree

open CoxeterSystem DihedralGroup Nat
notation "gD" => getDegree
-- (Reachable Set)
def ReachableSet (u : Vertex) (d : Degree) : Set Vertex :=
  { v | exists d', HasChain u v d' ∧ d' ≤ d }

def IsMaximalIn (v : Vertex) (S : Set Vertex) : Prop :=
  v ∈ S ∧ ∀ v' ∈ S, v ≤ v' → v = v'

-- 定义 CurveNeighborhood
def CurveNeighborhood (u : Vertex) (d : Degree) : Set Vertex :=
  { v | IsMaximalIn v (ReachableSet u d) }

-- 定义集合 A_d(u)
def Ad (u : Vertex) (d : Degree) : Set Vertex :=
  { v | cs.length (u * v) = cs.length u + cs.length v ∧ gD v ≤ d }

-- 定义集合 S 中的极大元子集
def maximalElements (S : Set Vertex) : Set Vertex :=
  { v | IsMaximalIn v S }

lemma h_len_bound : ∀ v ∈ Ad u d, ℓ v ≤ d.a + d.b + 1 := by
    intro v hv
    obtain ⟨h, h_deg⟩ := hv
    induction v using alternating_cases with
    | h s n =>
      simp_all only [length_alternating]
      induction n using n_mod_2_induction with
      | h0 k =>
        simp  only[getDegree_alternating] at h_deg
        simp only [mul_mod_right, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          mul_div_cancel_left₀] at h_deg
        have : 2 * k ≤ d.a + d.b :=
          by simpa [two_mul, Nat.add_comm] using
              Nat.add_le_add h_deg.1 h_deg.2
        exact Nat.le_trans this (Nat.le_succ _)
      | h1 k =>
        simp  only[getDegree_alternating] at h_deg
        fin_cases s
        · simp only [mul_add_mod_self_left, mod_succ, one_ne_zero, ↓reduceIte, Fin.zero_eta,
          Fin.isValue] at h_deg
          have h' := by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using Nat.add_le_add h_deg.1 h_deg.2
          rw [← two_mul, show 2 * ((1 + 2 * k) / 2) = 2 * k by omega, add_comm] at h'
          exact Nat.le_trans h' (Nat.le_succ _)
        · simp only [mul_add_mod_self_left, mod_succ, one_ne_zero, ↓reduceIte, Fin.mk_one,
            Fin.isValue] at h_deg
          have := by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using Nat.add_le_add h_deg.1 h_deg.2
          rw [← two_mul, show 2 * ((1 + 2 * k) / 2) = 2 * k by omega] at this
          have h' : 2 * k + 2 ≤ d.a + d.b + 1 := by omega
          exact Nat.succ_le_succ_iff.mp <|
            Nat.le_trans (Nat.le_succ _) (Nat.succ_le_succ h')

lemma h_finite : (Ad u d).Finite := by
    let limit := d.a + d.b + 1
    let S_bound := {v : D∞ | ℓ v ≤ limit}
    have h_subset : Ad u d ⊆ S_bound := fun v hv => h_len_bound v hv
    apply Set.Finite.subset _ h_subset
    -- The set of elements with bounded length is finite
    have : S_bound = ⋃ k ∈ Finset.range (limit + 1), {v | ℓ v = k} := by
      ext x
      simp only [S_bound, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
      constructor
      · intro h; use ℓ x; constructor <;> linarith
      · rintro ⟨i, hi, hx⟩; rw [hx]; linarith
    rw [this]
    have hfinite :
        (⋃ k ∈ (Finset.range (limit + 1) : Set ℕ),
          {v | cs.length v = k}).Finite := by
      apply Set.Finite.biUnion (Finset.finite_toSet _)
      intro k hk
      have h_finite_image : (Set.range (fun (s : Fin 2) => listToGroup (alternating s k))).Finite :=
        Set.finite_range _
      apply Set.Finite.subset h_finite_image
      intro v hv
      simp only [Set.mem_setOf_eq] at hv
      revert hv
      apply alternating_cases (P := fun v => ℓ v =
         k → v ∈ Set.range fun s => listToGroup (alternating s k))
      intro s n h_len
      rw [length_alternating] at h_len
      subst h_len
      exact Set.mem_range_self s
    simpa using hfinite

lemma h_nonempty : (Ad u d).Nonempty := ⟨1, ⟨by simp, by
    simp [getDegree_one]; constructor<;> linarith⟩⟩

lemma  h_chain {u : Vertex} (h : u ≠ 1) : IsChain (· ≤ ·) (Ad u d) := by
  intro x hx y hy hxy
  simp only
  --simp only [not_or] at h
  --obtain ⟨h1, h2⟩ := h
  obtain ⟨hv, hv'⟩ := hx
  obtain ⟨hw, hw'⟩ := hy
  change ((Lt x y) ∨ (x = y)) ∨ ((Lt y x) ∨ (y = x))
  simp [hxy, hxy.symm]
  sorry

theorem lemma_3_1_1 (u : Vertex) (d : Degree) :
    (u ≠ 1) → ∃! v, IsMaximalIn v (Ad u d) := by
  intro h_cond
  obtain ⟨m, hm⟩ := Set.Finite.exists_maximalFor (fun x => x) (Ad u d) h_finite h_nonempty
  refine ⟨m, ?_⟩
  dsimp [IsMaximalIn]
  constructor
  · constructor
    · exact hm.1
    · intro v' hv' h_le
      have := by apply hm.2  hv'  h_le
      exact le_antisymm h_le this
  · rintro y ⟨hy_in, hy_max⟩
    have h_total : m ≤ y ∨ y ≤ m := by
      by_cases eq : m = y
      · left; rw [eq]
      · apply h_chain h_cond hm.1 hy_in eq
    cases h_total with
    | inl h_le =>
      symm
      have := hm.2 hy_in h_le
      exact le_antisymm h_le this
    | inr h_le =>
      apply hy_max m hm.1 h_le

theorem lemma_3_1_2 (u : Vertex) (d : Degree) :
     (u = 1 ∧ d.a ≠ d.b) →
      ∃! v, IsMaximalIn v (Ad u d) := by sorry

theorem lemma_3_1_3 (a : ℕ) :
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

-- 辅助引理：Ad u d 中的元素必然在 Ad 1 d 中
lemma Ad_subset_Ad_one (u : Vertex) (d : Degree) (v : Vertex) (h : v ∈ Ad u d) : v ∈ Ad 1 d := by
  rw [Ad] at *
  simp only [one_mul, cs.length_one, zero_add, Set.mem_setOf_eq]
  exact And.imp_left (fun a ↦ trivial) h

-- 引理：有限偏序集中，任意元素都小于等于某个极大元
lemma exists_max_in_Ad (u : Vertex) (d : Degree) (z : Vertex) (hz : z ∈ Ad u d) :
    ∃ w, IsMaximalIn w (Ad u d) ∧ z ≤ w := by
  --使用lemma 3.1分类
  sorry

-- 引理：如果 w ∈ Ad u d，则 u * w 在 d 范围内可达
lemma reachable_of_Ad (u : Vertex) (d : Degree) (w : Vertex) (h : w ∈ Ad u d) :
    u*w ∈ ReachableSet u  d := by
  sorry

-- 如果 x, y 都在 Ad u d 中（即长度对 u 可加），则 x ≤ y ↔ u * x ≤ u * y
lemma mul_le_mul_left_of_length_add (u : Vertex) (x y : Vertex)
    (hx : cs.length (u * x) = cs.length u + cs.length x)
    (hy : cs.length (u * y) = cs.length u + cs.length y) :
    x ≤ y ↔ u * x ≤ u * y := by
  sorry

lemma Lt_iff_le_and_ne (a b : Vertex) : Lt a b ↔ a ≤ b ∧ a ≠ b := by
  rw [Lt, le_iff_lt_or_eq]
  constructor
  · intro h
    constructor
    · left; exact h
    · rcases h with ⟨d, chain, ne⟩; exact ne
  · rintro ⟨(h_lt | h_eq), h_ne⟩
    · exact h_lt
    · contradiction


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
    obtain ⟨w, hw_max, h_z_le_w⟩ := exists_max_in_Ad u d z h_z_in_Ad
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
    have h_reach : u * w ∈ ReachableSet u  d := reachable_of_Ad u d w hw_max.1
    constructor
    · exact h_reach
    · intro v' h_reach_v' h_lt_v_v'
      sorry
