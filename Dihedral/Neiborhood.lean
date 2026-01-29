import Mathlib
import Dihedral.Basic
import Dihedral.Length
import Dihedral.Degree

open CoxeterSystem DihedralGroup Nat
-- notation "gD" => getDegree
-- (Reachable Set)
def ReachableSet (u : Vertex) (d : Degree) : Set Vertex :=
  { v | ∃ d', HasChain u v d' ∧ d' ≤ d }

def IsMaximalIn (v : Vertex) (S : Set Vertex) : Prop :=
  v ∈ S ∧ ∀ v' ∈ S, v ≤ v' → v = v'

-- 定义 CurveNeighborhood
def CurveNeighborhood (u : Vertex) (d : Degree) : Set Vertex :=
  { v | IsMaximalIn v (ReachableSet u d) }

-- 定义集合 A_d(u)
def Ad (u : Vertex) (d : Degree) : Set Vertex :=
  { v |  ℓ (u * v) = ℓ u +  ℓ v ∧ φ v ≤ d }

-- 定义集合 S 中的极大元子集
def maximalElements (S : Set Vertex) : Set Vertex :=
  { v | IsMaximalIn v S }
--欲证明有限集
lemma h_len_bound : ∀ v ∈ Ad u d, ℓ v ≤ d.a + d.b + 1 := by
    intro v hv
    obtain ⟨h, h_deg⟩ := hv
    induction v using alternating_cases with
    | h s n =>
      simp_all only [length_alternating]
      induction n using n_mod_2_induction with
      | h0 k =>
        erw [getDegree_alternating_even, Degreele_le_def] at h_deg
        linarith
      | h1 k =>
        fin_cases s
        · erw [getDegree_alternating_odd_0, Degreele_le_def] at h_deg
          linarith
        · erw [getDegree_alternating_odd_1, Degreele_le_def] at h_deg
          linarith

lemma h_finite : (Ad u d).Finite := by
    let limit := d.a + d.b + 1
    let S_bound := {v : D∞ | ℓ v ≤ limit}
    have h_subset : Ad u d ⊆ S_bound := fun v hv => h_len_bound v hv
    apply Set.Finite.subset _ h_subset
    have : S_bound = ⋃ k ∈ Finset.range (limit + 1), {v | ℓ v = k} := by
      ext x
      simp only [S_bound, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
      constructor
      · intro h; use ℓ x; constructor <;> linarith
      · rintro ⟨i, hi, hx⟩; rw [hx]; linarith
    rw [this]
    have hfinite :
        (⋃ k ∈ (Finset.range (limit + 1) : Set ℕ),
          {v | ℓ v = k}).Finite := by
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
    simp [getDegree_one]⟩⟩

lemma h_chain {u : Vertex} (h : u ≠ 1) : IsChain (· ≤ ·) (Ad u d) := by
  intro x hx y hy hxy
  suffices h : (x < y) ∨ (y < x) by tauto
  rcases hx with ⟨hv, hv'⟩
  rcases hy with ⟨hw, hw'⟩
  rcases d with ⟨a,b⟩
  simp_all only [ne_eq, Degreele_le_def, lemma_2_3, lt_or_lt_iff_ne]
  cases u with
  | sr nu =>
    rcases x with ⟨nx⟩ | ⟨nx⟩ <;>
    rcases y with ⟨ny⟩ | ⟨ny⟩
    · simp_all; grind
    · simp_all; grind
    · simp_all; grind
    · simp only [sr_mul_sr] at hv hw
      rw [length_sr', length_sr', length_r] at hv hw
      rw [length_sr', length_sr']
      simp_all only [getDegree_sr, sr.injEq]
      change ℤ at *
      have : nx < ny ∨ ny < nx := Int.ne_iff_lt_or_gt.mp hxy
      omega
  | r nu =>
    have nun0 : nu ≠ 0 := by
      intro p
      simp [p] at h
    rcases x with ⟨nx⟩ | ⟨nx⟩ <;>
    rcases y with ⟨ny⟩ | ⟨ny⟩
    · simp_all only [ne_eq, getDegree_r, r_mul_r, length_r, r.injEq, mul_eq_mul_left_iff,
      OfNat.ofNat_ne_zero, or_false]
      change ℤ at *
      grind
    · simp_all; grind
    · simp_all; grind
    · simp only [r_mul_sr] at hv hw
      rw [length_sr', length_sr', length_r] at hv hw
      rw [length_sr', length_sr']
      simp_all only [ne_eq, getDegree_sr, sr.injEq]
      change ℤ at *
      grind

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

lemma lemma_3_hl (d : Degree) : Ad 1 d = {x : Vertex | φ x ≤ d} := by
  simp [Ad]

theorem lemma_3_1_2 (d : Degree) :
     (d.a ≠ d.b) → ∃! v, IsMaximalIn v (Ad 1 d) := by
      intro ne
      rcases d with ⟨a, b⟩
      dsimp [IsMaximalIn]
      rw [Nat.ne_iff_lt_or_gt]at ne
      simp only [lemma_3_hl]
      rcases ne with h | h
      · use s_α ⟨a, a + 1, Or.inr rfl⟩
        simp only [Degreele_le_def, s_α, gt_iff_lt, add_lt_iff_neg_left, _root_.not_lt_zero,
          reduceIte, Fin.isValue, show a + (a + 1) = 2 * a + 1 by omega, alternating_prod_odd,
          one_ne_zero, Set.mem_setOf_eq, and_imp]
        simp only at h
        split_ands
        · simp[getDegree_sr]
        · simp[getDegree_sr]
          omega
        · intro v h1 h2 h3
          have h3 : ( ℓ (sr (a + 1:ℕ)) < ℓ v) ∨ (sr (a + 1:ℕ) = v) := by
            rw [← lemma_2_3] ; exact h3
          cases v with
          | r n =>
            rw [length_sr', length_r] at h3
            simp_all [getDegree_r]
            omega
          | sr n =>
            repeat rw [length_sr'] at h3
            simp_all only [getDegree_sr, cast_add, cast_one, sr.injEq]
            by_contra p
            simp [p] at h3
            omega
        · intro v h1 h2 h3
          cases v with
          | r n =>
            simp_all only [getDegree_r, reduceCtorEq]
            specialize h3 (sr ((a:ℕ)+1:ℤ))
            simp_all only [getDegree_sr, add_sub_cancel_right, Int.natAbs_natCast, le_refl,
              reduceCtorEq, imp_false, forall_const]
            norm_cast at h3
            refine h3 h (le_of_eq_or_lt ?_)
            simp only [cast_add, cast_one, reduceCtorEq, false_or]
            have h: ℓ (r n) < ℓ (sr ((a:ℕ)+1:ℤ)) := by
              rw [length_r,length_sr']; omega
            exact (lemma_2_3 _ _).mpr h
          | sr n =>
            specialize h3 (sr ((a:ℕ)+1:ℤ))
            simp_all only [getDegree_sr, add_sub_cancel_right, Int.natAbs_natCast, le_refl,
              sr.injEq, forall_const]
            apply h3
            · omega
            · apply le_of_eq_or_lt
              rw [lemma_2_3, length_sr',length_sr']
              grind
      · use s_α ⟨b + 1, b, Or.inl rfl⟩
        simp only [Degreele_le_def, s_α, gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, reduceIte,
          Fin.isValue, Set.mem_setOf_eq, and_imp]
        repeat rw[show b + 1+b = 2*b + 1 by omega, getDegree_alternating_odd_0 b]
        simp_all only [le_refl, and_true, Fin.isValue, alternating_prod_odd, reduceIte]
        split_ands
        · exact h
        · intro v h1 h2 h3
          have h3 : ( ℓ (sr (-(b:ℤ))) < ℓ v) ∨ (sr (-(b:ℤ)) = v) := by
            rw [← lemma_2_3] ; exact h3
          cases v with
          | r n =>
            rw [length_sr', length_r] at h3
            simp_all [getDegree_r]
            omega
          | sr n =>
            repeat rw [length_sr'] at h3
            simp_all only [getDegree_sr, sr.injEq]
            by_contra p
            simp [p] at h3
            omega
        · intro v h1 h2 h3
          cases v with
          | r n =>
            simp_all only [getDegree_r, reduceCtorEq]
            specialize h3 (sr (-b:ℤ))
            simp_all only [getDegree_sr, Int.natAbs_neg, Int.natAbs_natCast, le_refl, reduceCtorEq,
              imp_false, forall_const]
            norm_cast at h3
            refine h3 (by omega) (le_of_eq_or_lt ?_)
            simp only [reduceCtorEq, false_or]
            have h: ℓ (r n) < ℓ (sr (-b:ℤ)) := by
              rw [length_r,length_sr']; omega
            exact (lemma_2_3 _ _).mpr h
          | sr n =>
            specialize h3 (sr (-b:ℤ))
            simp_all only [getDegree_sr, Int.natAbs_neg, Int.natAbs_natCast, le_refl, sr.injEq,
              forall_const]
            apply h3
            · omega
            · apply le_of_eq_or_lt
              rw [lemma_2_3, length_sr',length_sr']
              grind

lemma h_r_pos (a : ℕ) : (s0 * s1) ^ a = r (a : ℤ) := by
  simp [s0, s1]

lemma h_r_neg (a : ℕ) : (s1 * s0) ^ a = r (-(a : ℤ)) := by
  simp [s0, s1]

theorem lemma_3_1_3 (a : ℕ) (v : Vertex) :
    -- d = (a, a) 且 u = 1 的情况
    let S := Ad 1 (Degree.mk a a)
    IsMaximalIn v S ↔ v = (s0*s1)^a ∨ v = (s1*s0)^a := by
  simp only [lemma_3_hl, Degreele_le_def]
  rw [h_r_pos, h_r_neg]
  have h_len_le : ∀ x, getDegree x ≤ Degree.mk a a → ℓ x ≤ 2 * a := by
    intro x h_deg
    rcases x with (_ | k)
    --  r k
    · simp only [getDegree_r, Degreele_le_def] at h_deg
      rw [length_r]
      omega
    -- sr k
    · simp only [getDegree_sr, Degreele_le_def] at h_deg
      rw [length_sr]
      split_ifs with h_pos
      · by_cases hk0 : k = 0
        · simp [hk0] at h_deg ⊢
        · omega
      · omega
  --  r a , r (-a) ∈ S
  have h_mem_pos : getDegree (r (a : ℤ)) ≤ Degree.mk a a := by
    simp only [getDegree_r, Int.natAbs_natCast, le_refl]
  have h_mem_neg : getDegree (r (-(a : ℤ))) ≤ Degree.mk a a := by
    simp only [getDegree_r, Int.natAbs_neg, Int.natAbs_natCast, le_refl]
  -- 极大性
  have h_maximal_iff_len : IsMaximalIn v {x | getDegree x ≤ Degree.mk a a} ↔
                           getDegree v ≤ Degree.mk a a ∧ ℓ v = 2 * a := by
    constructor
    · rintro ⟨h_in, h_max⟩
      constructor
      · exact h_in
      · -- 反证：if ℓ小于 2a，小于 r a
        by_contra h_len_ne
        have h_len_lt : ℓ v < 2 * a := lt_of_le_of_ne (h_len_le v h_in) h_len_ne
        -- 构造一个长度为 2a 的元素 w = r a
        let a' := (a : ZMod 0)
        let w := r a'
        have h_w_in : w ∈ {x | getDegree x ≤ Degree.mk a a} := h_mem_pos
        have h_len_w : ℓ w = 2 * a := by simp [w, length_r, a']; omega
        have h_lt : v < w := (lemma_2_3 v w).mpr (by rw [h_len_w]; exact h_len_lt)
        have h_le : v ≤ w := le_of_lt h_lt
        have h_eq := h_max w h_w_in h_le
        rw [h_eq] at h_len_lt
        rw [h_len_w] at h_len_lt
        exact lt_irrefl _ h_len_lt
    · rintro ⟨h_in, h_len_eq⟩
      constructor
      · exact h_in
      · intro v' h_in' h_le
        rcases h_le with h_lt | h_eq
        · have h_len_lt : ℓ v < ℓ v' := (lemma_2_3 v v').mp h_lt
          rw [h_len_eq] at h_len_lt
          have h_bound := h_len_le v' h_in'
          linarith
        · exact h_eq
  have h_set_eq : {x | getDegree x ≤ { a := a, b := a }} =
     {x | (getDegree x).a ≤ a ∧ (getDegree x).b ≤ a} := by
    ext x;simp only [Degreele_le_def, Set.mem_setOf_eq]
  rw [← h_set_eq, h_maximal_iff_len]
  constructor
  · rintro ⟨h_deg, h_len⟩
    cases v with
    | r k =>
      simp [length_r] at h_len
      have hk : k.natAbs = a := by linarith
      rw [Int.natAbs_eq_iff] at hk
      rcases hk with rfl | rfl
      · left; rfl
      · right; rfl
    | sr k =>
      simp [length_sr] at h_len
      split_ifs at h_len
      <;>omega
  · rintro (rfl | rfl)
    · exact ⟨h_mem_pos, by simp [length_r]⟩
    · exact ⟨h_mem_neg, by simp [length_r]⟩

def root_from_degree (d : Degree) : Root :=
  if d.a > d.b then
    ⟨d.b + 1, d.b, Or.inl rfl⟩
  else
    ⟨d.a, d.a + 1, Or.inr rfl⟩

def s_alpha_d (d : Degree) : Vertex := s_α (root_from_degree d)

def s0s1_pow (a : ℕ) : Vertex := listToGroup (alternating 0 (2 * a))
def s1s0_pow (a : ℕ) : Vertex := listToGroup (alternating 1 (2 * a))

lemma s0s1_pow_equiv (a : ℕ) : s0s1_pow a = (s0*s1)^a := by
  simp [s0s1_pow, s0, s1]

lemma s1s0_pow_equiv (a : ℕ) : s1s0_pow a = (s1*s0)^a := by
  simp [s1s0_pow, s0, s1]

-- 辅助定义：计算交替字序列中的最后一个生成元索引
-- 如果序列长度为 n，起始为 s，则第 n 个元素（从 0 开始计数）是 s + n (mod 2)
def last_index (s : Fin 2) (n : ℕ) : Fin 2 :=
  if n % 2 == 0 then s else (if s = 0 then 1 else 0)

-- 对应的简单根
def root_for_index (i : Fin 2) : Root :=
  if i = 0 then α0 else α1

-- alternating s (n + 1) 生成的群元素等于 alternating s n 生成的元素右乘一个新的生成元
lemma listToGroup_alternating_succ_right (s : Fin 2) (n : ℕ) :
    listToGroup (alternating s (n + 1)) = listToGroup (alternating s n) * f (last_index s n) := by
  induction n generalizing s with
  | zero =>
    simp [alternating, listToGroup, last_index]
  | succ n ih =>
    rw [alternating]
    simp only [listToGroup, List.map_cons, List.prod_cons]
    rw [← listToGroup, ← listToGroup]
    rw [ih (s + 1), ← mul_assoc]
    congr 1
    dsimp [last_index]
    fin_cases s
    all_goals
    · simp; grind

-- 沿着alternating增加一步，度数增加对应的简单根的度数
lemma getDegree_alternating_succ (s : Fin 2) (n : ℕ) :
    φ (listToGroup (alternating s (n + 1))) =
    φ (listToGroup (alternating s n)) + (root_for_index (last_index s n)).toDegree := by
  -- 分奇偶讨论 n
  induction n using n_mod_2_induction with
  | h0 k =>
    simp only [alternating_prod_odd, Fin.isValue, alternating_prod_even, root_for_index, last_index,
      mul_mod_right, BEq.rfl, reduceIte]
    fin_cases s
    · simp only[Fin.zero_eta, Fin.isValue, reduceIte, getDegree_sr, Int.natAbs_neg,
      Int.natAbs_natCast, getDegree_r, Root.toDegree, α0]
      rw [show (-(k : ℤ)-1).natAbs = k+1 by omega]
      rfl
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, reduceIte, getDegree_sr,
      add_sub_cancel_right, Int.natAbs_natCast, getDegree_r, Int.natAbs_neg, Root.toDegree, α1]
      rfl
  | h1 k =>
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
    simp only [alternating_prod_odd, Fin.isValue, root_for_index, last_index, mul_add_mod_self_left,
      mod_succ, Nat.reduceBEq, Bool.false_eq_true, reduceIte, ite_eq_right_iff, one_ne_zero,
      imp_false, ite_not, alternating_prod_even]
    fin_cases s
    · simp only[Fin.zero_eta, Fin.isValue, reduceIte, getDegree_sr, Int.natAbs_neg,
      Int.natAbs_natCast, getDegree_r, Root.toDegree, α1]
      rw [show (-(k : ℤ)-1).natAbs = k+1 by omega]
      rfl
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, reduceIte, getDegree_sr,
      add_sub_cancel_right, Int.natAbs_natCast, getDegree_r, Int.natAbs_neg, Root.toDegree, α0]
      rfl

lemma trivial_chain (u : Vertex) : HasChain 1 u (φ u) := by
  induction u using alternating_cases with
  | h s n =>
  induction n generalizing s with
  | zero =>
    simp only [listToGroup, alternating, List.map_nil, List.prod_nil]
    exact HasChain.refl 1
  | succ n ih =>
    let u := listToGroup (alternating s n)
    let v := listToGroup (alternating s (n + 1))
    let i := last_index s n
    let α := root_for_index i
    have h_chain_u := ih s
    have h_edge : IsEdge u v α := by
      dsimp [IsEdge, v, u]
      rw [listToGroup_alternating_succ_right]
      congr
      simp only [last_index, beq_iff_eq, Fin.isValue, root_for_index, α, i]
      by_cases h' : n % 2 = 0
      all_goals
        simp only [h', reduceIte, Fin.isValue, ite_eq_right_iff, one_ne_zero, imp_false, ite_not]
        fin_cases s
        all_goals
          simp; rfl
    rw [getDegree_alternating_succ]
    apply HasChain.step h_chain_u h_edge

-- 结论 A: 证明对于单位元1，曲线邻域就是 Ad(1) 的极大元集合
theorem curve_neighborhood_eq_max_Ad_identity (d : Degree) :
    CurveNeighborhood 1 d = { v | IsMaximalIn v (Ad 1 d) } := by
  rw [CurveNeighborhood]
  congr
  ext v
  constructor
  -- ReachableSet 1 d ⊆ Ad 1 d
  · rintro h_in_Re
    simp only [ReachableSet, ] at h_in_Re
    simp only [Ad, one_mul, length_one, zero_add, true_and]
    have h_deg_le : getDegree v ≤ d := by
      rcases h_in_Re with ⟨h_mem, _⟩
      simp only [Set.mem_setOf_eq] at h_mem
      rcases h_mem with ⟨d', h_chain, h_d'_le_d⟩
      have h_phi_le_d' := lemma_2_5_b 1 v d' h_chain
      simp only [inv_one, one_mul] at h_phi_le_d'
      exact le_trans h_phi_le_d' h_d'_le_d
    rw [IsMaximalIn]
    refine ⟨h_deg_le, ?_⟩
    intro x h_x_deg_le h_v_le_x
    have h_x_in_Re : x ∈ {w | ∃ d', HasChain 1 w d' ∧ d' ≤ d} := by
      use getDegree x
      exact ⟨trivial_chain x, h_x_deg_le⟩
    apply h_in_Re.2 x h_x_in_Re h_v_le_x
  --Ad 1 d ⊆ ReachableSet 1 d
  · intro h_in_Ad
    simp only [Ad, one_mul, length_one, zero_add, true_and] at h_in_Ad
    simp only [ReachableSet]
    constructor
    · use getDegree v
      exact ⟨trivial_chain v, h_in_Ad.1⟩
    · intro x h_in_Re h_v_lt_x
      have h_x_in_Ad : x ∈ {x | getDegree x ≤ d} := by
        change getDegree x ≤ d
        rcases h_in_Re with ⟨d', h_chain, h_d'_le_d⟩
        have h_phi_le_d' := lemma_2_5_b 1 x d' h_chain
        simp only [inv_one, one_mul] at h_phi_le_d'
        exact le_trans h_phi_le_d' h_d'_le_d
      apply h_in_Ad.2 x h_x_in_Ad h_v_lt_x

-- 结论 B: Theorem 3.3 的具体计算公式
theorem theorem_3_3_eq (d : Degree) (p : d.a = d.b) :
  CurveNeighborhood 1 d = { s0s1_pow d.a, s1s0_pow d.a } := by
  rw [curve_neighborhood_eq_max_Ad_identity]
  have h := lemma_3_1_3 d.a ;
  ext v
  specialize h v
  simp_all only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hf : d = { a := d.b, b := d.b } := by
    ext <;> simp[p]
  rw [← hf] at h
  rw [h, s0s1_pow_equiv ,s1s0_pow_equiv]

lemma s_alpha_d_maximal (d : Degree) (p : d.a ≠ d.b) :
  IsMaximalIn (s_alpha_d d) (Ad 1 d) := by
  by_cases h : d.a > d.b
  · simp only [s_alpha_d, s_α, root_from_degree, gt_iff_lt, h, reduceIte, lt_add_iff_pos_right,
    zero_lt_one, Fin.isValue, lemma_3_hl, Degreele_le_def]
    simp only [Fin.isValue, show d.b + 1 + d.b = 2 * d.b + 1 by omega, alternating_prod_odd,
      reduceIte]
    refine ⟨?_, ?_⟩
    · simp[getDegree_sr]
      omega
    · intro v p w
      cases v with
      | r n =>
        have k: sr (-↑d.b) < r n := by
          change (Lt _ _) ∨ _ at w
          simp only [reduceCtorEq, or_false] at w
          exact w
        simp only [lemma_2_3, length_sr, gt_iff_lt, Left.neg_pos_iff, length_r] at k
        simp only [Set.mem_setOf_eq, getDegree_r] at p
        change ℤ at *
        grind
      | sr n =>
        by_contra k
        have k : ℓ (sr (-↑d.b)) < ℓ (sr n) := by
          rw [← lemma_2_3]; exact Std.lt_of_le_of_ne w k
        simp_all only [length_sr']
        simp_all only [ne_eq, gt_iff_lt, Set.mem_setOf_eq, getDegree_sr, sr.injEq, mul_neg]
        change ℤ at *
        omega
  · simp only [s_alpha_d, s_α, root_from_degree, gt_iff_lt, h, reduceIte, add_lt_iff_neg_left,
    _root_.not_lt_zero, Fin.isValue]
    simp only [Fin.isValue, show d.a + (d.a + 1) = 2 * d.a + 1 by omega, alternating_prod_odd,
      one_ne_zero, reduceIte, lemma_3_hl, Degreele_le_def]
    refine ⟨?_, ?_⟩
    · simp[getDegree_sr]
      omega
    · intro v p w
      cases v with
      | r n =>
        have k: sr (d.a + 1 : ℤ) < r n := by
          change (Lt _ _) ∨ _ at w
          simp only [reduceCtorEq, or_false] at w
          exact w
        simp only [lemma_2_3, length_sr, gt_iff_lt, Int.succ_ofNat_pos, reduceIte, length_r] at k
        simp only [Set.mem_setOf_eq, getDegree_r] at p
        change ℤ at *
        grind
      | sr n =>
        by_contra k
        have k : ℓ (sr (d.a + 1 : ℤ)) < ℓ (sr n) := by
          rw [← lemma_2_3]; exact Std.lt_of_le_of_ne w k
        simp_all only [length_sr']
        simp_all only [ne_eq, gt_iff_lt, not_lt, Set.mem_setOf_eq, getDegree_sr, sr.injEq]
        change ℤ at *
        omega

theorem theorem_3_3_neq (d : Degree) (p : d.a ≠ d.b) :
    CurveNeighborhood 1 d = { s_alpha_d d } := by
    rw [curve_neighborhood_eq_max_Ad_identity]
    ext v
    have h := lemma_3_1_2 _ p;
    constructor
    · simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      intro w
      rcases h with ⟨w1,w2,q⟩
      simp at q
      simp [q _ (s_alpha_d_maximal _ p), q _ w]
    · intro w
      simp at *
      simp [w, (s_alpha_d_maximal _ p)]

theorem theorem_3_3 (d : Degree) :
    CurveNeighborhood 1 d =
      if d.a = d.b then
        { s0s1_pow d.a, s1s0_pow d.a }
      else
        { s_alpha_d d } := by
        split_ifs with h
        · exact theorem_3_3_eq d h
        · exact theorem_3_3_neq d h
--这部分是在写example时才发现还没有写statement(thm3.2的第一部分在前面证过了）
--为了example能过临时写的,对应论文中的3.2.2，需要修改
def ends_in_s0 (u : D∞) : Prop := (reducedWord u).getLast? = some 0
def starts_with_s1 (v : D∞) : Prop := (reducedWord v).head? = some 1

-- 辅助引理：alternating 列表非空时的首元素
lemma alternating_head (s : Fin 2) (n : ℕ) (hn : n > 0) :
    (alternating s n).head? = some s := by
  cases n with
  | zero => omega
  | succ k => simp [alternating]


lemma s_alpha_starts_with (α : Root) :
    (reducedWord (s_α α)).head? = some (if α.a > α.b then 0 else 1) := by
  unfold s_α
  split_ifs with h
  · -- 情况 1: α.a > α.b
    rcases α.sub_one with hsub | hsub
    · have h_sum : α.a + α.b = 2 * α.b + 1 := by omega
      rw [h_sum, alternating_prod_odd]
      simp only [Fin.isValue, reduceIte]
      change (reducedWord (sr (-↑α.b))).head? = some 0
      unfold reducedWord
      have h_not_pos : ¬((-↑α.b : ℤ) > 0) := by
        simp only [Left.neg_pos_iff]
        omega
      simp only [h_not_pos, reduceIte]
      exact alternating_head 0 (2 * α.b + 1) (by omega)
    · omega
  · -- 情况 2: α.a ≤ α.b
    rcases α.sub_one with hsub | hsub
    · omega
    · have h_sum : α.a + α.b = 2 * α.a + 1 := by omega
      rw [h_sum, alternating_prod_odd]
      simp only [Fin.isValue, one_ne_zero, reduceIte]
      change (reducedWord (sr (↑α.a + 1))).head? = some 1
      unfold reducedWord
      have h_pos : ((α.a : ℤ) + 1 > 0) := by omega
      simp only [h_pos, reduceIte]
      have h_natAbs : ((α.a : ℤ) + 1).natAbs = α.a + 1 := by omega
      simp only [h_natAbs]
      have h_eq : 2 * (α.a + 1) - 1 = 2 * α.a + 1 := by omega
      rw [h_eq]
      exact alternating_head 1 (2 * α.a + 1) (by omega)


-- 奇数长度的 alternating 列表尾元素是 s
lemma alternating_getLast_odd (s : Fin 2) (k : ℕ) :
    (alternating s (2 * k + 1)).getLast? = some s := by
  induction k generalizing s with
  | zero => simp [alternating]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by omega, alternating_add_two]
    simp only [Fin.isValue, List.getLast?_cons_cons]
    exact ih s

-- 偶数长度（非零）的 alternating 列表尾元素是 s + 1
lemma alternating_getLast_even (s : Fin 2) (k : ℕ) (hk : k > 0) :
    (alternating s (2 * k)).getLast? = some (s + 1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      simp only [alternating, Fin.isValue, List.getLast?_cons_cons,
        List.getLast?_singleton]
    | succ k' =>
      rw [show 2 * (k' + 1 + 1) = 2 * (k' + 1) + 2 by omega, alternating_add_two]
      simp only [Fin.isValue, List.getLast?_cons_cons]
      have hk1 : k' + 1 > 0 := by omega
      exact ih hk1

-- 刻画 ends_in_s0 的具体条件
lemma ends_in_s0_r (k : ℤ) : ends_in_s0 (r k) ↔ k < 0 := by
  unfold ends_in_s0 reducedWord
  simp only [ge_iff_le, Fin.isValue]
  constructor
  · intro h
    split_ifs at h with hk
    · by_cases hk0 : k = 0
      · simp [hk0, alternating] at h
      · have hpos : k.natAbs > 0 := Int.natAbs_pos.mpr hk0
        rw [alternating_getLast_even 0 k.natAbs hpos] at h
        simp at h
    · push_neg at hk; exact hk
  · intro hk
    simp only [not_le.mpr hk, reduceIte]
    have hpos : k.natAbs > 0 := Int.natAbs_pos.mpr (ne_of_lt hk)
    rw [alternating_getLast_even 1 k.natAbs hpos]
    simp [Fin.add_def]

lemma ends_in_s0_sr (k : ℤ) : ends_in_s0 (sr k) ↔ k ≤ 0 := by
  unfold ends_in_s0 reducedWord
  simp only [Fin.isValue]
  constructor
  · intro h
    split_ifs at h with hk
    · have hpos : k.natAbs > 0 := Int.natAbs_pos.mpr (ne_of_gt hk)
      have hlen : 2 * k.natAbs - 1 = 2 * (k.natAbs - 1) + 1 := by omega
      rw [hlen, alternating_getLast_odd] at h
      simp at h
    · push_neg at hk; exact hk
  · intro hk
    simp only [not_lt.mpr hk, reduceIte]
    rw [alternating_getLast_odd]

lemma starts_with_s1_r (k : ℤ) : starts_with_s1 (r k) ↔ k < 0 := by
  unfold starts_with_s1 reducedWord
  simp only [ge_iff_le, Fin.isValue]
  constructor
  · intro h
    split_ifs at h with hk
    · by_cases hk0 : k = 0
      · simp [hk0, alternating] at h
      · have hpos : k.natAbs > 0 := Int.natAbs_pos.mpr hk0
        have hlen : 2 * k.natAbs > 0 := by omega
        rw [alternating_head 0 (2 * k.natAbs) hlen] at h
        simp at h
    · push_neg at hk; exact hk
  · intro hk
    simp only [not_le.mpr hk, reduceIte]
    have hpos : k.natAbs > 0 := Int.natAbs_pos.mpr (ne_of_lt hk)
    have hlen : 2 * k.natAbs > 0 := by omega
    exact alternating_head 1 (2 * k.natAbs) hlen

lemma starts_with_s1_sr (k : ℤ) : starts_with_s1 (sr k) ↔ k > 0 := by
  unfold starts_with_s1 reducedWord
  simp only [Fin.isValue]
  constructor
  · intro h
    split_ifs at h with hk
    · exact hk
    · push_neg at hk
      have hlen : 2 * k.natAbs + 1 > 0 := by omega
      rw [alternating_head 0 (2 * k.natAbs + 1) hlen] at h
      simp at h
  · intro hk
    simp only [hk, reduceIte]
    have hpos : k.natAbs > 0 := Int.natAbs_pos.mpr (ne_of_gt hk)
    have hlen : 2 * k.natAbs - 1 > 0 := by omega
    exact alternating_head 1 (2 * k.natAbs - 1) hlen

lemma length_add_of_ends_s0_starts_s1 (u v : Vertex)
    (hu : ends_in_s0 u) (hv : starts_with_s1 v) : ℓ (u * v) = ℓ u + ℓ v := by
  cases u with
  | r ku =>
    let ku' : ℤ := ku
    have hu' : ku' < 0 := by
      have : ends_in_s0 (r ku') := hu
      exact (ends_in_s0_r ku').mp this
    cases v with
    | r kv =>
      let kv' : ℤ := kv
      have hv' : kv' < 0 := by
        have : starts_with_s1 (r kv') := hv
        exact (starts_with_s1_r kv').mp this
      simp only [r_mul_r, length_r]
      have h : (ku' + kv').natAbs = ku'.natAbs + kv'.natAbs :=
        Int.natAbs_add_of_nonpos (le_of_lt hu') (le_of_lt hv')
      rw [h]; ring
    | sr kv =>
      let kv' : ℤ := kv
      have hv' : kv' > 0 := by
        have : starts_with_s1 (sr kv') := hv
        exact (starts_with_s1_sr kv').mp this
      have h_pos : kv' - ku' > 0 := by linarith
      have h_natAbs : (kv' - ku').natAbs = kv'.natAbs + ku'.natAbs := by
        rw [show kv' - ku' = kv' + (-ku') by ring,
        Int.natAbs_add_of_nonneg (le_of_lt hv') (by linarith : (0 : ℤ) ≤ -ku'), Int.natAbs_neg]
      simp only [r_mul_sr, length_r, length_sr]
      split_ifs with h1
      · rw [h_natAbs]; omega
      · exfalso; exact h1 h_pos
  | sr ku =>
    let ku' : ℤ := ku
    have hu' : ku' ≤ 0 := by
      have : ends_in_s0 (sr ku') := hu
      exact (ends_in_s0_sr ku').mp this
    have h_u_not_pos : ¬(ku' > 0) := not_lt.mpr hu'
    cases v with
    | r kv =>
      let kv' : ℤ := kv
      have hv' : kv' < 0 := by
        have : starts_with_s1 (r kv') := hv
        exact (starts_with_s1_r kv').mp this
      have h_sum_not_pos : ¬(ku' + kv' > 0) := by linarith
      have h_natAbs : (ku' + kv').natAbs = ku'.natAbs + kv'.natAbs :=
        Int.natAbs_add_of_nonpos hu' (le_of_lt hv')
      simp only [sr_mul_r, length_sr, length_r]
      split_ifs with h1
      · exfalso; exact h_sum_not_pos h1
      · rw [h_natAbs]; omega
    | sr kv =>
      let kv' : ℤ := kv
      have hv' : kv' > 0 := by
        have : starts_with_s1 (sr kv') := hv
        exact (starts_with_s1_sr kv').mp this
      have h_natAbs : (kv' - ku').natAbs = kv'.natAbs + ku'.natAbs := by
        rw [show kv' - ku' = kv' + (-ku') by ring,
        Int.natAbs_add_of_nonneg (le_of_lt hv') (by linarith : (0 : ℤ) ≤ -ku'), Int.natAbs_neg]
      simp only [sr_mul_sr, length_r, length_sr]
      split_ifs with h1
      · exfalso; exact h_u_not_pos h1
      · rw [h_natAbs]; omega

lemma degree_of_s_alpha (α : Root) : φ (s_α α) = α.toDegree := φ_s_alpha_eq α

-- 情况 1: d.b > d.a
theorem theorem_3_2_case_b_gt_a (u : Vertex) (d : Degree) (hu : ends_in_s0 u)
    (h : d.b > d.a) : IsMaximalIn (s_alpha_d d) (Ad u d) := by
  set w := s_alpha_d d with hw_def
  -- 计算 root_from_degree d 和 s_alpha_d d 的具体形式
  have hna : ¬(d.a > d.b) := not_lt.mpr (le_of_lt h)
  have h_root : root_from_degree d = ⟨d.a, d.a + 1, Or.inr rfl⟩ := by
    unfold root_from_degree
    simp only [hna, reduceIte]
  have hw_eq : w = listToGroup (alternating 1 (2 * d.a + 1)) := by
    rw [hw_def]
    unfold s_alpha_d s_α
    rw [h_root]
    simp only [gt_iff_lt, add_lt_iff_neg_left, not_lt_zero', reduceIte, Fin.isValue]
    congr 1
    ring_nf
  have hw_sr : w = sr ((d.a : ℤ) + 1) := by
    rw [hw_eq, alternating_prod_odd]
    simp
  -- 证明 w 以 s1 开头
  have hw_starts_s1 : starts_with_s1 w := by
    rw [hw_sr, starts_with_s1_sr]
    omega
  have h_len : ℓ (u * w) = ℓ u + ℓ w :=
    length_add_of_ends_s0_starts_s1 u w hu hw_starts_s1
  have h_deg : φ w ≤ d := by
    rw [hw_def]
    unfold s_alpha_d
    rw [h_root, φ_s_alpha_eq]
    simp only [Root.toDegree, Degreele_le_def, le_refl]
    constructor
    · trivial
    · exact h
  have hw_len : ℓ w = 2 * d.a + 1 := by
    rw [hw_sr, length_sr]
    have hpos : (d.a : ℤ) + 1 > 0 := by linarith
    simp only [hpos, reduceIte]
    rw [show ((d.a : ℤ) + 1).natAbs = d.a + 1 by rfl]
    ring_nf
    exact succ_add_sub_one (d.a * 2) 1
  have hv_len_bound : ∀ v, v ∈ Ad u d → ℓ v ≤ 2 * d.a + 1 := by
    intro v ⟨_, hv_deg⟩
    cases v with
    | r k =>
      simp only [getDegree_r, Degreele_le_def] at hv_deg
      simp only [length_r]
      omega
    | sr k =>
      simp only [getDegree_sr, Degreele_le_def] at hv_deg
      simp only [length_sr]
      split_ifs with hk <;> omega
  constructor
  · exact ⟨h_len, h_deg⟩
  · intro v hv hv_le
    rcases hv_le with hv_lt | hv_eq
    · have hlen_lt : ℓ w < ℓ v := (lemma_2_3 w v).mp hv_lt
      have hlen_bound := hv_len_bound v hv
      rw [hw_len] at hlen_lt
      omega
    · exact hv_eq

-- 情况 2: d.a > d.b
theorem theorem_3_2_case_a_gt_b (u : Vertex) (d : Degree) (hu : ends_in_s0 u)
    (h : d.a > d.b) : IsMaximalIn (s0 * s_alpha_d d) (Ad u d) := by
  set w := s0 * s_alpha_d d with hw_def
  -- 计算 root_from_degree d 的具体形式
  have h_root : root_from_degree d = ⟨d.b + 1, d.b, Or.inl rfl⟩ := by
    unfold root_from_degree
    simp only [h, reduceIte]
  -- s_alpha_d d = sr (-(d.b : ℤ))
  have hs_alpha : s_alpha_d d = sr (-(d.b : ℤ)) := by
    unfold s_alpha_d s_α
    rw [h_root]
    simp only [gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, reduceIte, Fin.isValue]
    have h_sum : d.b + 1 + d.b = 2 * d.b + 1 := by ring
    rw [h_sum, alternating_prod_odd]
    simp
  -- w = s0 * sr (-(d.b)) = r (-(d.b))
  have hw_r : w = r (-(d.b : ℤ)) := by
    rw [hw_def, hs_alpha]
    simp [s0, sr_mul_sr]
  -- 分 d.b > 0 和 d.b = 0 两种情况
  by_cases hb_pos : d.b > 0
  · have hw_starts_s1 : starts_with_s1 w := by
      rw [hw_r, starts_with_s1_r]
      simp only [Left.neg_neg_iff, Nat.cast_pos]
      exact hb_pos
    have h_len : ℓ (u * w) = ℓ u + ℓ w :=
      length_add_of_ends_s0_starts_s1 u w hu hw_starts_s1
    -- φ w ≤ d
    have h_deg : φ w ≤ d := by
      rw [hw_r]
      simp only [getDegree_r, Int.natAbs_neg, Int.natAbs_natCast, Degreele_le_def, le_refl]
      exact ⟨le_of_lt h, trivial⟩
    -- ℓ w = 2 * d.b
    have hw_len : ℓ w = 2 * d.b := by
      rw [hw_r, length_r]
      simp
    -- 任何 v ∈ Ad u d 满足 ℓ v ≤ 2 * d.b
    have hv_len_bound : ∀ v, v ∈ Ad u d → ℓ v ≤ 2 * d.b := by
      intro v ⟨hv_len_eq, hv_deg⟩
      cases v with
      | r k =>
        simp only [getDegree_r, Degreele_le_def] at hv_deg
        simp only [length_r]
        exact Nat.mul_le_mul_left 2 hv_deg.2
      | sr k =>
        simp only [getDegree_sr, Degreele_le_def] at hv_deg
        simp only [length_sr]
        split_ifs with hk
        · rcases hv_deg with ⟨_, h_les⟩
          calc 2 * k.natAbs - 1
            _ ≤ 2 * k.natAbs := Nat.sub_le _ _
            _ ≤ 2 * d.b := Nat.mul_le_mul_left 2 h_les
        · exfalso
          simp only [gt_iff_lt, not_lt] at hk
          let k' : ℤ := k
          have hk' : k' ≤ 0 := hk
          have hlen_v : ℓ (sr k) = 2 * k'.natAbs + 1 := by
            change ℓ (sr k') = 2 * k'.natAbs + 1
            simp only [length_sr, not_lt.mpr hk', reduceIte]
          cases u with
          | r m =>
            let m' : ℤ := m
            have hm : m' < 0 := (ends_in_s0_r m').mp hu
            have hlen_u : ℓ (r m) = 2 * m'.natAbs := length_r m
            have h_prod : (r m) * (sr k) = sr (k' - m') := rfl
            rw [h_prod, hlen_u, hlen_v] at hv_len_eq
            by_cases h_km : k' - m' > 0
            · have hlen_prod : ℓ (sr (k' - m')) = 2 * (k' - m').natAbs - 1 := by
                simp only [length_sr, h_km, reduceIte]
              rw [hlen_prod] at hv_len_eq
              have h_abs : (k' - m').natAbs ≤ k'.natAbs + m'.natAbs := Int.natAbs_sub_le k' m'
              omega
            · push_neg at h_km
              have hlen_prod : ℓ (sr (k' - m')) = 2 * (k' - m').natAbs + 1 := by
                simp only [length_sr, not_lt.mpr h_km, reduceIte]
              rw [hlen_prod] at hv_len_eq
              have h_abs : (k' - m').natAbs ≤ k'.natAbs + m'.natAbs := Int.natAbs_sub_le k' m'
              omega
          | sr m =>
            let m' : ℤ := m
            have hm : m' ≤ 0 := (ends_in_s0_sr m').mp hu
            have hlen_u : ℓ (sr m) = 2 * m'.natAbs + 1 := by
              change ℓ (sr m') = 2 * m'.natAbs + 1
              simp only [length_sr, not_lt.mpr hm, reduceIte]
            have h_prod : (sr m) * (sr k) = r (k' - m') := by rfl
            rw [h_prod, hlen_u, hlen_v] at hv_len_eq
            have hlen_prod : ℓ (r (k' - m')) = 2 * (k' - m').natAbs := by simp only [length_r]
            rw [hlen_prod] at hv_len_eq
            have h_abs : (k' - m').natAbs ≤ k'.natAbs + m'.natAbs := Int.natAbs_sub_le k' m'
            omega
    constructor
    · exact ⟨h_len, h_deg⟩
    · intro v hv hv_le
      rcases hv_le with hv_lt | hv_eq
      · have hlen_lt : ℓ w < ℓ v := (lemma_2_3 w v).mp hv_lt
        have hlen_bound := hv_len_bound v hv
        rw [hw_len] at hlen_lt
        omega
      · exact hv_eq
  · have hb_zero : d.b = 0 := Nat.eq_zero_of_not_pos hb_pos
    have hw_one : w = 1 := by
      rw [hw_r, hb_zero]
      simp
    have hw_len : ℓ w = 0 := by
      rw [hw_one]
      exact cs.length_one
    have hw_deg : φ w = ⟨0, 0⟩ := by
      rw [hw_one]
      exact getDegree_one
    have hv_one : ∀ v, v ∈ Ad u d → v = 1 := by
      intro v ⟨hv_len_eq, hv_deg⟩
      have hv_len_zero : ℓ v = 0 := by
        cases v with
        | r k =>
          simp only [getDegree_r, Degreele_le_def, hb_zero] at hv_deg
          simp only [length_r]
          have : k.natAbs ≤ 0 := hv_deg.2
          have : k.natAbs = 0 := Nat.eq_zero_of_le_zero this
          linarith
        | sr k =>
          exfalso
          simp only [getDegree_sr, Degreele_le_def, hb_zero] at hv_deg
          rcases hv_deg with ⟨_, h⟩
          have hk_zero : k.natAbs = 0 := Nat.eq_zero_of_le_zero h
          have hk_eq : k = 0 := Int.natAbs_eq_zero.mp hk_zero
          subst hk_eq
          have hlen_v : ℓ (sr (0 : ℤ)) = 1 := by simp [length_sr]
          cases u with
          | r m =>
            let m' : ℤ := m
            have hm : m' < 0 := (ends_in_s0_r m').mp hu
            have hlen_u : ℓ (r m) = 2 * m.natAbs := by simp only [length_r]
            simp only [r_mul_sr, length_sr, length_r] at hv_len_eq
            split_ifs at hv_len_eq with h_neg_m_pos <;> omega
          | sr m =>
            let m' : ℤ := m
            have hm : m' ≤ 0 := (ends_in_s0_sr m').mp hu
            have hm_neg : ¬(m' > 0) := not_lt.mpr hm
            simp only [sr_mul_sr, length_r, length_sr] at hv_len_eq
            split_ifs at hv_len_eq with h_m_pos <;> omega
      exact (length_eq_zero_iff cs).mp hv_len_zero
    rw [hw_one]
    constructor
    · constructor
      · simp
      · simp only [Degreele_le_def]
        exact ⟨Nat.zero_le d.a, Nat.zero_le d.b⟩
    · intro v hv hv_le
      specialize hv_one v
      symm
      apply hv_one
      exact hv

-- 情况 3: d.a = d.b
theorem theorem_3_2_case_a_eq_b (u : Vertex) (d : Degree) (hu : ends_in_s0 u)
    (h : d.a = d.b) : IsMaximalIn (s1 * s_alpha_d (d.sub {a := 0, b := 1})) (Ad u d) := by
  set a := d.a with ha_def
  set w := s1 * s_alpha_d (d.sub {a := 0, b := 1}) with hw_def
  by_cases ha_pos : a > 0
  · -- 情况: a > 0
    have h_dsub : d.sub {a := 0, b := 1} = ⟨a, a - 1⟩ := by
      simp only [Degree.sub, h, Nat.sub_zero]
      ext <;>
      simp only
      exact h
    have h_a_gt : a > a - 1 := Nat.sub_lt ha_pos (by omega)
    have h_root : root_from_degree (d.sub {a := 0, b := 1}) = ⟨a, a - 1, Or.inl (by omega)⟩ := by
      unfold root_from_degree
      rw [h_dsub]
      simp only [h_a_gt, reduceIte]
      congr
      exact Nat.sub_add_cancel ha_pos
    -- s_alpha_d (a, a-1) = sr(1-a)
    have hs_alpha : s_alpha_d (d.sub {a := 0, b := 1}) = sr (1 - (a : ℤ)) := by
      unfold s_alpha_d s_α; rw [h_root]
      simp only [gt_iff_lt, h_a_gt, reduceIte, Fin.isValue]
      rw [show a + (a - 1) = 2 * (a - 1) + 1 by omega, alternating_prod_odd]
      simp only [Fin.isValue, reduceIte]
      congr
      have h1 : 1 ≤ a := ha_pos
      rw [Int.ofNat_sub h1]
      ring
    -- w = s1 * sr(1-a) = r(-a)
    have hw_r : w = r (-(a : ℤ)) := by
      rw [hw_def, hs_alpha, s1, sr_mul_sr]; congr; ring
    -- w 以 s1 开头
    have hw_starts_s1 : starts_with_s1 w := by
      rw [hw_r, starts_with_s1_r]
      simp only [Left.neg_neg_iff, Nat.cast_pos]; exact ha_pos
    -- ℓ(u * w) = ℓ u + ℓ w
    have h_len : ℓ (u * w) = ℓ u + ℓ w :=
      length_add_of_ends_s0_starts_s1 u w hu hw_starts_s1
    -- φ(w) ≤ d
    have h_deg : φ w ≤ d := by
      rw [hw_r]
      simp only [getDegree_r, Int.natAbs_neg, Int.natAbs_natCast, Degreele_le_def]
      exact ⟨le_refl a, le_of_eq h⟩
    -- ℓ(w) = 2a
    have hw_len : ℓ w = 2 * a := by rw [hw_r, length_r]; simp
    -- 任何 v ∈ Ad u d 满足 ℓ(v) ≤ 2a
    have hv_len_bound : ∀ v, v ∈ Ad u d → ℓ v ≤ 2 * a := by
      intro v ⟨hv_len_eq, hv_deg⟩
      cases v with
      | r k =>
        let k' : ℤ := k
        by_cases hk_sign : 0 < k'
        · exfalso
          have h_not_starts_s1 : ¬starts_with_s1 (r k) := by
            rw [starts_with_s1_r]; exact not_lt.mpr (le_of_lt hk_sign)
          cases u with
          | r m =>
            let m' : ℤ := m
            have hm : m' < 0 := (ends_in_s0_r m').mp hu
            simp only [r_mul_r, length_r] at hv_len_eq
            omega
          | sr m =>
            let m' : ℤ := m
            have hm : m' ≤ 0 := (ends_in_s0_sr m').mp hu
            have hm_neg : ¬(m' > 0) := not_lt.mpr hm
            simp only [sr_mul_r, length_sr, length_r] at hv_len_eq
            split_ifs at hv_len_eq <;> omega
        · simp only [getDegree_r, Degreele_le_def] at hv_deg
          simp only [length_r]
          exact Nat.mul_le_mul_left 2 hv_deg.1
      | sr k =>
        let k' : ℤ := k
        by_cases hk_pos : k' > 0
        · simp only [length_sr]
          simp only [getDegree_sr, Degreele_le_def] at hv_deg
          have h1 : 2 * k'.natAbs - 1 ≤ 2 * k'.natAbs := Nat.sub_le _ _
          have h2 : 2 * k'.natAbs ≤ 2 * a := by linarith
          split_ifs <;> omega
        · exfalso
          have hk_le : k' ≤ 0 := not_lt.mp hk_pos
          have hlen_v : ℓ (sr k) = 2 * k'.natAbs + 1 := by
            simp only [length_sr, gt_iff_lt]
            split
            · (expose_names; exact False.elim (hk_pos h_1))
            · simp only [Degreele_le_def, length_sr, gt_iff_lt, not_lt, Nat.add_right_cancel_iff,
              mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at *
              rfl
          cases u with
          | r m =>
            let m' : ℤ := m
            have hm : m' < 0 := (ends_in_s0_r m').mp hu
            simp only [r_mul_sr, length_sr, length_r] at hv_len_eq
            rw [← hlen_v] at hv_len_eq
            split_ifs at hv_len_eq <;> omega
          | sr m =>
            let m' : ℤ := m
            have hm : m' ≤ 0 := (ends_in_s0_sr m').mp hu
            simp only [sr_mul_sr, length_r, length_sr] at hv_len_eq
            have hlen_u : ℓ (sr m') = 2 * m'.natAbs + 1 := by
              simp only [length_sr, not_lt.mpr hm, reduceIte]
            have h_abs : (k' - m').natAbs ≤ k'.natAbs + m'.natAbs := Int.natAbs_sub_le k' m'
            split_ifs at hv_len_eq <;> omega
    -- 证明 w 是极大元
    constructor
    · exact ⟨h_len, h_deg⟩
    · intro v hv hv_le
      rcases hv_le with hv_lt | hv_eq
      · have hlen_lt : ℓ w < ℓ v := (lemma_2_3 w v).mp hv_lt
        have hlen_bound := hv_len_bound v hv
        rw [hw_len] at hlen_lt; omega
      · exact hv_eq
  · -- 情况: a = 0
    have ha_zero : a = 0 := Nat.eq_zero_of_not_pos ha_pos
    have hd_zero : d = ⟨0, 0⟩ := by
      ext <;> simp only
      · exact ha_zero
      · rw [← h, ha_zero]
    -- 当 a = 0 时，d.sub {a := 0, b := 1} = (0, 0)
    have h_dsub : d.sub {a := 0, b := 1} = ⟨0, 0⟩ := by
      rw [hd_zero]; rfl
    -- s_alpha_d (0, 0) = s1
    have hs_alpha : s_alpha_d (d.sub {a := 0, b := 1}) = s1 := by
      rw [h_dsub]
      unfold s_alpha_d root_from_degree s_α
      simp only [gt_iff_lt, lt_self_iff_false, reduceIte, Fin.isValue, zero_add,
        alternating, listToGroup, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
      rfl
    -- w = s1 * s1 = 1
    have hw_one : w = 1 := by
      rw [hw_def, hs_alpha, s1]
      simp
    rw [hw_one]
    -- 证明 Ad u (0, 0) = {1}
    have hv_must_be_one : ∀ v, v ∈ Ad u d → v = 1 := by
      intro v ⟨hv_len_eq, hv_deg⟩
      rw [hd_zero] at hv_deg
      simp only [Degreele_le_def] at hv_deg
      have ha_zero' : (φ v).a = 0 := Nat.eq_zero_of_le_zero hv_deg.1
      have hb_zero : (φ v).b = 0 := Nat.eq_zero_of_le_zero hv_deg.2
      cases v with
      | r k =>
        simp only [getDegree_r] at ha_zero'
        have hk_zero : k = 0 := Int.natAbs_eq_zero.mp ha_zero'
        simp [hk_zero]
      | sr k =>
        simp only [getDegree_sr] at hb_zero
        have hk_zero : k = 0 := Int.natAbs_eq_zero.mp hb_zero
        simp only [getDegree_sr, hk_zero] at ha_zero'
        norm_num at ha_zero'
    constructor
    · constructor
      · simp
      · rw [hd_zero]
        simp only [getDegree_one, le_refl]
    · intro v hv hv_le
      symm
      exact hv_must_be_one v hv

-- thm3.2下等式(4)
theorem theorem_3_2_eq_4 (u : Vertex) (d : Degree) (hu : ends_in_s0 u) :
  IsMaximalIn
    (if d.a = d.b then s1 * s_alpha_d (d.sub {a := 0, b := 1})
     else if d.b > d.a then s_alpha_d d
     else s0 * s_alpha_d d)
    (Ad u d) := by
  split_ifs with h1 h2
  · exact theorem_3_2_case_a_eq_b u d hu h1
  · exact theorem_3_2_case_b_gt_a u d hu h2
  · have h3 : d.a > d.b := Nat.lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
    exact theorem_3_2_case_a_gt_b u d hu h3


lemma edge_left_mul (g u v : Vertex) (α : Root) (h : IsEdge u v α) :
    IsEdge (g * u) (g * v) α := by
  dsimp [IsEdge] at *
  rw [h, mul_assoc]

lemma chain_left_mul (g u v : Vertex) (d : Degree) (h : HasChain u v d) :
    HasChain (g * u) (g * v) d := by
  induction h with
  | refl  =>
    exact HasChain.refl (g * u)
  | step h_prev h_edge ih =>
    apply HasChain.step ih (edge_left_mul g _ _ _ h_edge)

lemma CurveNeighborhood_max (h : v ∈ CurveNeighborhood u d) :
     ∀ w ∈ ReachableSet u d, ℓ w ≤ ℓ v := by
  rw [CurveNeighborhood] at h
  intro w hw
  by_contra h_lt
  rw [not_le, ← lemma_2_3] at h_lt
  have h_le : v ≤ w := le_of_lt h_lt
  have h_eq := h.2 w hw h_le
  rw [h_eq] at h_lt
  exact (lt_self_iff_false w).mp h_lt

-- Lemma 3.4: 关于 u, z ∈ Ad(1) 和 v ∈ Γd(u) 的性质
theorem lemma_3_4_a_1 (u : Vertex) (d : Degree) (z : Vertex) (v : Vertex)
    (hz : z ∈ Ad 1 d) (hv : v ∈ CurveNeighborhood u d) :
    ℓ (u * z) ≤ ℓ v := by
  have h_deg_z : φ z ≤ d := by
      simp only [Ad, one_mul, length_one, zero_add, Degreele_le_def, true_and,
        Set.mem_setOf_eq] at hz; exact ⟨hz.1,hz.2⟩
    -- 存在从 1 到 z 的链，度数为 φ(z)
  have h_chain_z : HasChain 1 z (φ z) := trivial_chain z
  have h_chain_uz : HasChain u (u * z) (getDegree z) :=by
    have := chain_left_mul u 1 z _ h_chain_z
    simp only [mul_one] at this
    exact this
  --  u * z 在 u 的 ReachableSet 中 (因为 getDegree z ≤ d)
  have h_uz_in_Re : u * z ∈ ReachableSet u d := by
    use getDegree z
  exact CurveNeighborhood_max hv (u * z) h_uz_in_Re

theorem lemma_3_4_a_2 (u : Vertex) (d : Degree) (v : Vertex)
     (hv : v ∈ CurveNeighborhood u d) :
   φ (u⁻¹ * v) ≤ d := by
  have h_v_reachable : v ∈ ReachableSet u d := by
    rw [CurveNeighborhood] at hv
    exact hv.1
  rcases h_v_reachable with ⟨dv, h_chain_v, h_dv_le_d⟩
  -- 链左乘 u⁻¹
  have h_chain_inv_u_v : HasChain (u⁻¹ * u) (u⁻¹ * v) dv := chain_left_mul u⁻¹ u v dv h_chain_v
  simp only [inv_mul_cancel] at h_chain_inv_u_v
  -- Lemma 2.5 (b)
  have h_phi_le_dv := lemma_2_5_b 1 (u⁻¹ * v) dv h_chain_inv_u_v
  -- 结合 dv ≤ d →  φ(u⁻¹v) ≤ d
  simp only [inv_one, one_mul, Degreele_le_def] at h_phi_le_dv
  exact le_trans h_phi_le_dv h_dv_le_d

theorem lemma_3_4_b (u : Vertex) (d : Degree) (z : Vertex) (v : Vertex)
    (hz : z ∈ CurveNeighborhood 1 d) (hv : v ∈ CurveNeighborhood u d) :
    ℓ (u⁻¹ * v) ≤ ℓ z := by
  rw [CurveNeighborhood] at hv
  rcases hv with ⟨h_v_in_Re, -⟩
  rcases h_v_in_Re with ⟨dv, h_chain_v, h_dv_le_d⟩
  -- 链左乘 u⁻¹
  have h_chain_inv : HasChain (u⁻¹ * u) (u⁻¹ * v) dv := chain_left_mul u⁻¹ u v dv h_chain_v
  simp only [inv_mul_cancel] at h_chain_inv
  --  u⁻¹v ∈ 1 的ReachableSet
  set w := u⁻¹ * v with hw
  have h_w_in_Re : w ∈ ReachableSet 1 d := by use dv
  -- z 的极大性
  apply CurveNeighborhood_max hz w h_w_in_Re

theorem lemma_3_5 (u v : Vertex) (d : Degree) (hv : v ∈ CurveNeighborhood u d) :
    (u⁻¹ * v) ∈ Ad u d := by
  constructor
  · by_cases hu_1 : u = 1
    · simp [hu_1]
    · by_contra h_eq1
      simp only [mul_inv_cancel_left] at h_eq1
      set w := u⁻¹ * v with hw_def
      have h_le : ℓ v ≤ ℓ u + ℓ w := by
        calc ℓ v = ℓ (u * w) := by simp [hw_def]
             _ ≤ ℓ u + ℓ w := lemma_2_1_3 u w
      have h_lt : ℓ v < ℓ u + ℓ w := lt_of_le_of_ne h_le h_eq1
      -- ℓ u ≤ ℓ v
      have h_u_le_v : ℓ u ≤ ℓ v := by
        have h_u_reach : u ∈ ReachableSet u d := ⟨0, HasChain.refl u, by
              simp only [Degreele_le_def]
              constructor <;> exact le_of_ble_eq_true rfl⟩
        exact CurveNeighborhood_max hv u h_u_reach
      -- ℓ(u⁻¹ * v) = ℓ u + ℓ v 或 ℓ(u⁻¹ * v) = ℓ v - ℓ u
      have h_inv_len : ℓ u⁻¹ = ℓ u := (lemma_2_1_1 u).symm
      have h_inv_le : ℓ u⁻¹ ≤ ℓ v := by rw [h_inv_len]; exact h_u_le_v
      have h_dichotomy := lemma_2_1_4 u⁻¹ v h_inv_le
      rcases h_dichotomy with (h_add | h_sub)
      · rw [h_inv_len] at h_add
        -- 取 z ∈ Γ_d(1)
        have h_Gamma_nonempty : (CurveNeighborhood 1 d).Nonempty := by
          rw [theorem_3_3]
          split_ifs with h
          · exact ⟨s0s1_pow d.a, Set.mem_insert _ _⟩
          · exact ⟨s_alpha_d d, Set.mem_singleton _⟩
        obtain ⟨z, hz⟩ := h_Gamma_nonempty
        have hz_Ad : z ∈ Ad 1 d := by
          rw [curve_neighborhood_eq_max_Ad_identity] at hz
          exact hz.1
        have h_uz_le_v : ℓ (u * z) ≤ ℓ v := lemma_3_4_a_1 u d z v hz_Ad hv
        have h_w_le_z : ℓ w ≤ ℓ z := lemma_3_4_b u d z v hz hv
        have h_uv_le_z : ℓ u + ℓ v ≤ ℓ z := by rw [← h_add]; exact h_w_le_z
        -- ℓ(u * z) < ℓ u + ℓ z
        have h_uz_not_reduced : ℓ (u * z) < ℓ u + ℓ z := by
          calc ℓ (u * z) ≤ ℓ v := h_uz_le_v
               _ < ℓ u + ℓ w := h_lt
               _ ≤ ℓ u + ℓ z := by linarith [h_w_le_z]
        -- ℓ u ≥ 1
        have h_u_pos : ℓ u ≥ 1 := by
          by_contra h; push_neg at h
          have : ℓ u = 0 := lt_one_iff.mp h
          exact hu_1 ((length_eq_zero_iff cs).mp this)
        -- z ≠ 1
        have hz_ne : z ≠ 1 := by
          intro h; rw [h, cs.length_one] at h_uv_le_z; linarith
        have h_exists_z' : ∃ z' ∈ Ad 1 d, ℓ z' = ℓ z - 1 ∧ ℓ (u * z') = ℓ u + ℓ z' := by
          obtain ⟨i, hi_left⟩ := cs.exists_leftDescent_of_ne_one hz_ne
          set z' := cs.simple i * z with hz'_def
          use z'
          have hs : cs.simple i = f i := by fin_cases i <;> rfl
          have h_z'_len : ℓ z' = ℓ z - 1 := by
           rw [cs.isLeftDescent_iff] at hi_left
           calc ℓ z' = ℓ (cs.simple i * z) := by rw [hz'_def]
             _ = ℓ z - 1 := Nat.eq_sub_of_add_eq hi_left
          have h_z'_deg : φ z' ≤ d := by
            have hz_deg : φ z ≤ d := hz_Ad.2
            suffices h : φ z' ≤ φ z by exact le_trans h hz_deg
            rw [hz'_def, hs]
            fin_cases i
            · cases z with
              | r k =>
                simp only [f, s0, getDegree_r, Degreele_le_def,Fin.zero_eta,
                    Fin.isValue, Matrix.cons_val_zero, sr_mul_r, zero_add]
                have h_k_pos : (0 : ℤ) < k := by
                  rw [cs.isLeftDescent_iff] at hi_left
                  have hs0 : cs.simple 0 = s0 := rfl
                  simp only [Fin.zero_eta, Fin.isValue, length_r] at hi_left
                  rw [hs0, s0, sr_mul_r, zero_add, length_sr] at hi_left
                  split_ifs at hi_left with hk <;> omega
                constructor
                · simp only [getDegree_sr]
                  omega
                · simp only [getDegree_sr]
                  exact le_refl _
              | sr k =>
                simp only [f, s0, getDegree_sr, Degreele_le_def,Fin.zero_eta, Fin.isValue,
                Matrix.cons_val_zero, sr_mul_sr, sub_zero, getDegree_r, le_refl, and_true]
                have h_k_nonpos : (0 : ℤ) ≥ k:= by
                  rw [cs.isLeftDescent_iff] at hi_left
                  have hs0 : cs.simple 0 = s0 := rfl
                  simp only [Fin.zero_eta, Fin.isValue, length_sr, gt_iff_lt] at hi_left
                  rw [hs0, s0, sr_mul_sr, sub_zero, length_r] at hi_left
                  split_ifs at hi_left with hk <;> omega
                omega
            · cases z with
              | r k =>
                simp only [f, s1, getDegree_r, Degreele_le_def, Fin.mk_one, Fin.isValue,
                  Matrix.cons_val_one, Matrix.cons_val_fin_one, sr_mul_r]
                have h_k_neg : (0 : ℤ) > k := by
                  rw [cs.isLeftDescent_iff] at hi_left
                  have hs1 : cs.simple 1 = s1 := rfl
                  simp only [Fin.mk_one, Fin.isValue, length_r] at hi_left
                  rw [hs1, s1, sr_mul_r, length_sr] at hi_left
                  split_ifs at hi_left with hk <;> omega
                constructor
                · simp only [getDegree_sr]
                  omega
                · simp only [getDegree_sr]
                  omega
              | sr k =>
                simp only [f, s1, getDegree_sr, Degreele_le_def, Fin.mk_one, Fin.isValue,
                Matrix.cons_val_one, Matrix.cons_val_fin_one, sr_mul_sr, getDegree_r,
                le_refl, true_and]
                have h_k_pos : (0 : ℤ) < k := by
                  rw [cs.isLeftDescent_iff] at hi_left
                  have hs1 : cs.simple 1 = s1 := rfl
                  simp only [Fin.mk_one, Fin.isValue, length_sr, gt_iff_lt] at hi_left
                  rw [hs1, s1, sr_mul_sr, length_r] at hi_left
                  split_ifs at hi_left with hk <;> omega
                have h_abs : (k - 1).natAbs = k.natAbs - 1 := by omega
                rw [h_abs]
                omega
          have h_prod : ℓ (u * z') = ℓ u + ℓ z' := by
            by_cases hz'_one : z' = 1
            · simp [hz'_one]
            · rw [hs] at hz'_def
              fin_cases i
              · have h_u_ends : ends_in_s0 u := by
                  cases u with
                  | r ku =>
                    cases z with
                    | r kz =>
                      simp only [r_mul_r, length_r] at h_uz_not_reduced
                      simp only [ends_in_s0_r]
                      have h_kz_neg : (0 : ℤ) < kz := by
                        rw [cs.isLeftDescent_iff] at hi_left
                        have hs1 : cs.simple 0 = s0 := rfl
                        simp only [Fin.zero_eta, Fin.isValue, length_r] at hi_left
                        rw [hs1, s0, sr_mul_r, length_sr] at hi_left
                        split_ifs at hi_left with hkz
                        · exact Int.lt_of_add_lt_add_left hkz
                        · exfalso
                          omega
                      by_contra h_ku_neg
                      push_neg at h_ku_neg
                      omega
                    | sr kz =>
                      simp only [r_mul_sr, length_r, length_sr] at h_uz_not_reduced
                      simp only [ends_in_s0_r]
                      have h_kz_neg : (0 : ℤ) ≥ kz := by
                        rw [cs.isLeftDescent_iff] at hi_left
                        have hs1 : cs.simple 0 = s0 := rfl
                        simp only [Fin.zero_eta, Fin.isValue, length_sr] at hi_left
                        rw [hs1, s0, sr_mul_sr, length_r] at hi_left
                        split_ifs at hi_left with hkz
                        · exfalso
                          omega
                        · exact Int.not_lt.mp hkz
                      by_contra h_ku_neg
                      push_neg at h_ku_neg
                      split_ifs at h_uz_not_reduced <;> omega
                  | sr ku =>
                    cases z with
                    | r kz =>
                      simp only [length_r] at h_uz_not_reduced
                      have h_kz_pos : (0 : ℤ) < kz := by
                        rw [cs.isLeftDescent_iff] at hi_left
                        have hs1 : cs.simple 0 = s0 := rfl
                        simp only [Fin.zero_eta, Fin.isValue, length_r] at hi_left
                        rw [hs1, s0, sr_mul_r, length_sr] at hi_left
                        split_ifs at hi_left with hkz
                        · exact Int.lt_of_add_lt_add_left hkz
                        · exfalso
                          omega
                      rw [ends_in_s0_sr]
                      simp only [sr_mul_r, length_sr] at h_uz_not_reduced
                      by_contra h
                      push_neg at h
                      split_ifs at h_uz_not_reduced with h_sum_pos
                      · omega
                      · push_neg at h_sum_pos
                        omega
                    | sr kz =>
                      simp only [sr_mul_sr, length_r, length_sr] at h_uz_not_reduced
                      simp only [ends_in_s0_sr]
                      have h_kz_nonpos : (0 : ℤ) ≥ kz := by
                        rw [cs.isLeftDescent_iff] at hi_left
                        have hs0 : cs.simple 0 = s0 := rfl
                        simp only [Fin.zero_eta, Fin.isValue, length_sr] at hi_left
                        rw [hs0, s0, sr_mul_sr, sub_zero, length_r] at hi_left
                        split_ifs at hi_left with hkz
                        · omega
                        · push_neg at hkz; exact hkz
                      by_contra h
                      push_neg at h
                      split_ifs at h_uz_not_reduced with h_ku_pos h_kz_pos <;> omega
                have h_z'_starts : starts_with_s1 z' := by
                  rw [hz'_def]
                  cases z with
                  | r kz =>
                    simp only [f, s0, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
                    sr_mul_r, zero_add]
                    rw [cs.isLeftDescent_iff] at hi_left
                    simp only [length_r] at hi_left
                    have hs0 : cs.simple 0 = s0 := rfl
                    simp only [Fin.zero_eta, Fin.isValue] at hi_left
                    rw [hs0, s0, sr_mul_r, length_sr] at hi_left
                    split_ifs at hi_left with h
                    · rw [starts_with_s1_sr]
                      omega
                    · exfalso
                      omega
                  | sr kz =>
                    simp only [f, s0, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
                    sr_mul_sr, sub_zero]
                    rw [cs.isLeftDescent_iff] at hi_left
                    simp only [length_sr] at hi_left
                    have hs0 : cs.simple 0 = s0 := rfl
                    simp only [Fin.zero_eta, Fin.isValue, gt_iff_lt] at hi_left
                    rw [hs0, s0, sr_mul_sr, length_r] at hi_left
                    split_ifs at hi_left with h
                    · exfalso
                      omega
                    · rw [starts_with_s1_r]
                      simp only [not_lt] at h
                      apply lt_of_le_of_ne h
                      by_contra hz0
                      simp_rw [hz0] at hz'_def
                      simp only [Fin.zero_eta, Fin.isValue] at hz'_def
                      contradiction
                exact length_add_of_ends_s0_starts_s1 u z' h_u_ends h_z'_starts
              · have h_u_ends : ¬ends_in_s0 u := by
                  cases u with
                  | r ku =>
                    cases z with
                    | r kz =>
                      simp only [r_mul_r, length_r] at h_uz_not_reduced
                      simp only [ends_in_s0_r, not_lt]
                      have h_kz_neg : (0 : ℤ) > kz := by
                        rw [cs.isLeftDescent_iff] at hi_left
                        have hs1 : cs.simple 1 = s1 := rfl
                        simp only [Fin.mk_one, Fin.isValue, length_r] at hi_left
                        rw [hs1, s1, sr_mul_r, length_sr] at hi_left
                        split_ifs at hi_left with hkz
                        · omega
                        · push_neg at hkz; omega
                      by_contra h_ku_neg
                      push_neg at h_ku_neg
                      have h_eq : (ku + kz).natAbs = ku.natAbs + kz.natAbs :=
                        Int.natAbs_add_of_nonpos (le_of_lt h_ku_neg) (le_of_lt h_kz_neg)
                      omega
                    | sr kz =>
                      simp only [r_mul_sr, length_r, length_sr] at h_uz_not_reduced
                      simp only [ends_in_s0_r, not_lt]
                      have h_kz_pos : (0 : ℤ) < kz := by
                        rw [cs.isLeftDescent_iff] at hi_left
                        have hs1 : cs.simple 1 = s1 := rfl
                        simp only [Fin.mk_one, Fin.isValue, length_sr] at hi_left
                        rw [hs1, s1, sr_mul_sr, length_r] at hi_left
                        split_ifs at hi_left with hkz
                        · exact hkz
                        · omega
                      by_contra h_ku_neg
                      push_neg at h_ku_neg
                      split_ifs at h_uz_not_reduced with h_diff_pos
                      · omega
                      · push_neg at h_diff_pos
                        omega
                  | sr ku =>
                    cases z with
                    | r kz =>
                      simp only [sr_mul_r, length_sr, length_r] at h_uz_not_reduced
                      simp only [ends_in_s0_sr, not_le]
                      have h_kz_neg : (0 : ℤ) > kz := by
                        rw [cs.isLeftDescent_iff] at hi_left
                        have hs1 : cs.simple 1 = s1 := rfl
                        simp only [Fin.mk_one, Fin.isValue, length_r] at hi_left
                        rw [hs1, s1, sr_mul_r, length_sr] at hi_left
                        split_ifs at hi_left with hkz
                        · omega
                        · push_neg at hkz; omega
                      by_contra h_ku_neg
                      push_neg at h_ku_neg
                      have h_eq : (ku + kz).natAbs = ku.natAbs + kz.natAbs :=
                        Int.natAbs_add_of_nonpos (h_ku_neg) (le_of_lt h_kz_neg)
                      split_ifs at h_uz_not_reduced <;> omega
                    | sr kz =>
                      simp only [sr_mul_sr, length_sr, length_r] at h_uz_not_reduced
                      simp only [ends_in_s0_sr, not_le]
                      have h_kz_pos : (0 : ℤ) < kz := by
                        rw [cs.isLeftDescent_iff] at hi_left
                        have hs1 : cs.simple 1 = s1 := rfl
                        simp only [Fin.mk_one, Fin.isValue, length_sr] at hi_left
                        rw [hs1, s1, sr_mul_sr, length_r] at hi_left
                        split_ifs at hi_left with hkz
                        · exact hkz
                        · omega
                      by_contra h_ku_neg
                      push_neg at h_ku_neg
                      split_ifs at h_uz_not_reduced with h_diff_pos
                      · omega
                      · push_neg at h_diff_pos
                        omega
                have h_z'_starts : ¬starts_with_s1 z' := by
                  rw [hz'_def]
                  cases z with
                  | r kz =>
                    simp only [f, s1, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
                      Matrix.cons_val_fin_one, sr_mul_r]
                    rw [cs.isLeftDescent_iff] at hi_left
                    have hs1 : cs.simple 1 = s1 := rfl
                    simp only [Fin.mk_one, Fin.isValue, length_r] at hi_left
                    rw [hs1, s1, sr_mul_r, length_sr] at hi_left
                    split_ifs at hi_left with h
                    · exfalso
                      omega
                    · intro h
                      rw [starts_with_s1_sr] at h
                      omega
                  | sr kz =>
                    simp only [f, s1, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
                      Matrix.cons_val_fin_one, sr_mul_sr]
                    rw [cs.isLeftDescent_iff] at hi_left
                    have hs1 : cs.simple 1 = s1 := rfl
                    simp only [Fin.mk_one, Fin.isValue, length_sr, gt_iff_lt] at hi_left
                    rw [hs1, s1, sr_mul_sr, length_r] at hi_left
                    split_ifs at hi_left with h
                    · intro h
                      rw [starts_with_s1_r] at h
                      omega
                    · exfalso
                      omega
                cases u with
                | r ku =>
                  cases hz'_eq : z' with
                  | r kz' =>
                    simp only [r_mul_r, length_r]
                    simp only [ends_in_s0_r, not_lt] at h_u_ends
                    have hz'_nonneg : (0 : ℤ) ≤ kz' := by
                      by_contra h
                      simp only [not_le] at h
                      have hcontra : starts_with_s1 (r kz') := (starts_with_s1_r kz').mpr h
                      erw [← hz'_eq] at hcontra
                      contradiction
                    rw [Int.natAbs_add_of_nonneg h_u_ends hz'_nonneg]
                    ring
                  | sr kz' =>
                    simp only [r_mul_sr, length_r, length_sr]
                    simp only [ends_in_s0_r, not_lt] at h_u_ends
                    have hz'_nonpos : (0 : ℤ) ≥ kz' := by
                      by_contra h
                      simp only [not_le] at h
                      have hcontra : starts_with_s1 (sr (kz' : ℤ)) :=
                          (starts_with_s1_sr (kz' : ℤ)).mpr h
                      erw [← hz'_eq] at hcontra
                      change starts_with_s1 z' at hcontra
                      exact h_z'_starts hcontra
                    split_ifs <;> omega
                | sr ku =>
                  cases hz'_eq : z' with
                  | r kz' =>
                    simp only [sr_mul_r, length_sr, length_r]
                    simp only [ends_in_s0_sr, not_le] at h_u_ends
                    have hz'_nonneg : (0 : ℤ) ≤ kz' := by
                      by_contra h
                      simp only [not_le] at h
                      have hcontra : starts_with_s1 (r kz') := (starts_with_s1_r kz').mpr h
                      rw [← hz'_eq] at hcontra
                      exact h_z'_starts hcontra
                    split_ifs <;> omega
                  | sr kz' =>
                    simp only [sr_mul_sr, length_sr, length_r]
                    simp only [ends_in_s0_sr, not_le] at h_u_ends
                    have hz'_nonpos : (0 : ℤ) ≥ kz' := by
                      by_contra h
                      simp only [ge_iff_le, not_le] at h
                      have hcontra : starts_with_s1 (sr (kz' : ℤ))
                          := (starts_with_s1_sr (kz' : ℤ)).mpr h
                      erw [← hz'_eq] at hcontra
                      change starts_with_s1 z' at hcontra
                      exact h_z'_starts hcontra
                    simp only [ge_iff_le] at hz'_nonpos
                    split_ifs <;> omega
          refine ⟨?_, h_z'_len, h_prod⟩
          simp only [Ad, one_mul, length_one, zero_add, true_and, Set.mem_setOf_eq]
          exact h_z'_deg
        obtain ⟨z', hz'_Ad, hz'_len, hz'_reduced⟩ := h_exists_z'
        have h_uz'_le_v : ℓ (u * z') ≤ ℓ v := lemma_3_4_a_1 u d z' v hz'_Ad hv
        have h_bound1 : ℓ u + ℓ z - 1 ≤ ℓ v := by
          calc ℓ u + ℓ z - 1 = ℓ u + (ℓ z - 1) := by omega
               _ = ℓ u + ℓ z' := by rw [hz'_len]
               _ = ℓ (u * z') := hz'_reduced.symm
               _ ≤ ℓ v := h_uz'_le_v
        have h_bound2 : ℓ v ≤ ℓ z - ℓ u := Nat.le_sub_of_add_le' h_uv_le_z
        have h_contra : 2 * ℓ u ≤ 1 := by
          have : ℓ u + ℓ z - 1 ≤ ℓ z - ℓ u := le_trans h_bound1 h_bound2
          omega
        linarith
      · rw [h_inv_len, ← hw_def] at h_sub
        have : ℓ v = ℓ u + ℓ w := (Nat.sub_eq_iff_eq_add' h_u_le_v).mp (id (Eq.symm h_sub))
        contradiction
  · exact lemma_3_4_a_2 u d v hv

-- Ad u d 中的元素必然在 Ad 1 d 中
lemma Ad_u_in_Ad_one (u : Vertex) (d : Degree) (v : Vertex) (h : v ∈ Ad u d) : v ∈ Ad 1 d := by
  rw [Ad] at *
  simp only [one_mul, cs.length_one, zero_add, Set.mem_setOf_eq]
  exact And.imp_left (fun a ↦ trivial) h

-- 存在极大元
lemma exists_max_in_Ad (u : Vertex) (d : Degree) (z : Vertex) (hz : z ∈ Ad u d) :
    ∃ w, IsMaximalIn w (Ad u d) ∧ z ≤ w := by
  --  Ad u d 中大于等于 z 的子集
  let S_ge_z := { w ∈ Ad u d | z ≤ w }
  -- 有限
  have h_fin : S_ge_z.Finite := h_finite.subset (Set.sep_subset _ _)
  -- 非空 (z 自身)
  have h_nonempty : S_ge_z.Nonempty := ⟨z, hz, le_refl z⟩
  -- 存在极大元
  obtain ⟨m, ⟨hm_in_Ad, h_z_le_m⟩, hm_max_in_subset⟩ :=
    Set.Finite.exists_maximalFor (id) S_ge_z h_fin h_nonempty
  use m
  constructor
  · rw [IsMaximalIn]
    constructor
    · exact hm_in_Ad
    · intro v' hv' hm_le_v'
      have h_v'_in_subset : v' ∈ S_ge_z := by
        constructor
        · exact hv'
        · exact le_trans h_z_le_m hm_le_v'
      have := hm_max_in_subset h_v'_in_subset hm_le_v'
      simp only [id_eq] at this
      exact le_antisymm hm_le_v' this
  · exact h_z_le_m

-- 如果 w ∈ Ad u d，则 u * w 在 d 范围内Reachable
lemma reachable_of_Ad (u : Vertex) (d : Degree) (w : Vertex) (h : w ∈ Ad u d) :
    u * w ∈ ReachableSet u d := by
  have c1 := trivial_chain w
  -- 左乘 u
  have c2 := chain_left_mul u 1 w (getDegree w) c1
  simp only [mul_one] at c2
  --  u*w in ReachableSet u d
  use getDegree w
  exact ⟨c2, h.2⟩

def lastGen (g : D∞) : Option (Fin 2) := (reducedWord g).getLast?
def firstGen (g : D∞) : Option (Fin 2) := (reducedWord g).head?

--  x, y ∈ Ad u d ，则 x ≤ y ↔ u * x ≤ u * y
lemma mul_le_mul_left_of_length_add (u : Vertex) (x y : Vertex)
    (hx : ℓ (u * x) = ℓ u + ℓ x) (hy : ℓ (u * y) = ℓ u + ℓ y) :
    x ≤ y ↔ u * x ≤ u * y := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, lemma_2_3, lemma_2_3, hx, hy]
  constructor
  · rintro (h | rfl)
    · left; omega
    · right; rfl
  · rintro (h | h)
    · left; omega
    · right; exact mul_left_cancel h

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

-- ReachableSet中的任意元素都受某个极大元支配
-- 有限性
lemma exists_max_ge_in_Reachable (u : Vertex) (d : Degree) (v : Vertex)
    (h : v ∈ ReachableSet u d) :
    ∃ m, m ∈ CurveNeighborhood u d ∧ v ≤ m := by
  -- 定义受控集
  let S_bound := { x : Vertex | φ (u⁻¹ * x) ≤ d }
  --  S_bound 有限
  have h_bound_finite : S_bound.Finite := by
    let pre_image := { y : Vertex | φ y ≤ d }
    have h_pre_finite : pre_image.Finite := by
      have heq : pre_image = Ad 1 d := (lemma_3_hl d).symm
      rw [heq]
      exact h_finite
    have : S_bound = (fun y => u * y) '' pre_image := by
       ext x; simp [S_bound, pre_image]
    rw [this]
    exact Set.Finite.image _ h_pre_finite
  -- 证明 ReachableSet u d ⊆ S_bound
  have h_subset : ReachableSet u d ⊆ S_bound := by
    intro x hx
    rcases hx with ⟨dx, chain, h_dx_le_d⟩
    -- 左乘 u⁻¹
    have chain_inv := chain_left_mul u⁻¹ u x dx chain
    simp only [inv_mul_cancel] at chain_inv
    -- Lemma 2.5(b):  1 -> y 的链，φ(y) ≤ degree
    have h_phi := lemma_2_5_b 1 (u⁻¹ * x) dx
    simp only [inv_one, one_mul] at h_phi
    exact le_trans (h_phi chain_inv) h_dx_le_d
  -- def ReachableSet 中大于等于 v 的子集
  let S_ge_v := { m ∈ ReachableSet u d | v ≤ m }
  -- 有限 非空
  have h_fin_sub : S_ge_v.Finite :=by
    apply Set.Finite.subset h_bound_finite
    intro x ⟨hx_reach, _⟩
    exact h_subset hx_reach
  have h_nonempty : S_ge_v.Nonempty := ⟨v, h, le_refl v⟩
  -- 取极大元
  obtain ⟨m, ⟨hm_reach, h_v_le_m⟩, hm_max⟩ :=
    Set.Finite.exists_maximalFor id S_ge_v h_fin_sub h_nonempty
  use m
  constructor
  · rw [CurveNeighborhood]
    constructor
    · exact hm_reach
    · intro v' hv' hm_le_v'
      have h_v'_in_S : v' ∈ S_ge_v := ⟨hv', le_trans h_v_le_m hm_le_v'⟩
      have := hm_max  h_v'_in_S hm_le_v'
      simp only [id_eq] at this
      exact le_antisymm hm_le_v' this
  · exact h_v_le_m

theorem main_theorem (u : Vertex) (d : Degree) :
    CurveNeighborhood u d = { v | ∃ w, IsMaximalIn w (Ad u d) ∧ v = u * w } := by
  apply Set.ext
  intro v
  constructor
  -- v ∈ Ω_d(u) → v = u * w (w 为极大元)
  · intro hv
    -- 由 Lemma 3.5, z = u⁻¹v ∈ Ad u d
    have h_z_in_Ad : (u⁻¹ * v) ∈ Ad u d := lemma_3_5 u v d hv
    let z := u⁻¹ * v
    have h_v_eq : v = u * z := by simp [z]
    -- 在 Ad u d 中存在极大元 w 使得 z ≤ w
    obtain ⟨w, hw_max, h_z_le_w⟩ := exists_max_in_Ad u d z h_z_in_Ad
    have hw_in_Ad1 : w ∈ Ad 1 d := Ad_u_in_Ad_one u d w hw_max.1
    -- Lemma 3.4(a): ℓ(uw) ≤ ℓ(v)
    have h_len_uw_le_v := lemma_3_4_a_1 u d w v hw_in_Ad1 hv
    -- v = u * z, z ∈ Ad u d =>
    have h_len_v : ℓ v = ℓ u + ℓ z := by
      rw [h_v_eq]
      exact h_z_in_Ad.1
    -- w ∈ Ad u d => ℓ(uw) = ℓ(u) + ℓ(w)
    have h_len_uw : ℓ (u * w) = ℓ u + ℓ w := hw_max.1.1
    -- ℓ(u) + ℓ(w) ≤ ℓ(u) + ℓ(z) => ℓ(w) ≤ ℓ(z)
    rw [h_len_v, h_len_uw] at h_len_uw_le_v
    have h_len_w_le_z : ℓ w ≤ ℓ z := Nat.le_of_add_le_add_left h_len_uw_le_v
    --z ≤ w ∧ ℓ(w) ≤ ℓ(z) => z = w
    have h_z_eq_w : z = w := by
      by_contra h_neq
      have h_lt : z < w := lt_of_le_of_ne h_z_le_w h_neq
      have h_len_lt : ℓ z < ℓ w := by
        rw [← lemma_2_3]
        exact h_lt
      linarith [h_len_lt, h_len_w_le_z]
    use w
    constructor
    · exact hw_max
    · rw [h_v_eq, h_z_eq_w]
  --  (⊇): v = u * w (w maximal) → v ∈ Ω_d(u)
  · rintro ⟨w, hw_max, rfl⟩
    -- reachable
    have h_reach : u * w ∈ ReachableSet u d := reachable_of_Ad u d w hw_max.1
    -- maximal
    rw [CurveNeighborhood]
    refine ⟨h_reach, ?_⟩
    intro v' h_reach_v' h_le_v_v'
    -- 若存在 v' reachable且 u*w ≤ v', v'被某个极大元支配
    obtain ⟨m, hm_max, h_v'_le_m⟩ := exists_max_ge_in_Reachable u d v' h_reach_v'
    have h_m_in_gamma : m ∈ CurveNeighborhood u d := hm_max
    have h_z'_in_Ad : (u⁻¹ * m) ∈ Ad u d := lemma_3_5 u m d h_m_in_gamma
    let w' := u⁻¹ * m
    have h_m_eq : m = u * w' := by simp [w']
    -- u*w ≤ v' ≤ m => u*w ≤ u*w'
    have h_uw_le_uw' : u * w ≤ u * w' :=
        le_trans h_le_v_v' (by rw [h_m_eq] at h_v'_le_m; exact h_v'_le_m)
    --w w' ∈ Ad，左乘保序
    have h_w_le_w' : w ≤ w' := by
      rw [← mul_le_mul_left_of_length_add u w w' hw_max.1.1 h_z'_in_Ad.1] at h_uw_le_uw'
      exact h_uw_le_uw'
    --  w 的极大性
    have h_w_eq_w' : w = w' :=
      hw_max.2 w' h_z'_in_Ad h_w_le_w'
    -- w = w' => u*w = u*w' => v = m
    have h_v_eq_m : u * w = m := by rw [h_m_eq, ←h_w_eq_w']
    -- u*w ≤ v' ≤ m ∧ u*w = m => v' = m = u*w
    have h_v'_eq_v : v' = u * w := by
      have h_m_eq_uw : m = u * w := h_v_eq_m.symm
      rw [h_m_eq_uw] at h_v'_le_m
      exact le_antisymm h_v'_le_m h_le_v_v'
    rw [h_v'_eq_v]

example : CurveNeighborhood 1 {a := 2, b := 2} = { s0s1_pow 2, s1s0_pow 2 } := by
  rw [theorem_3_3_eq {a := 2, b := 2} rfl]
--listToGroup (alternating 0 6) = r 3
example : CurveNeighborhood s0 {a := 2, b := 3} = {listToGroup (alternating 0 6)} := by
  rw [main_theorem s0 {a := 2, b := 3}]
  have h_ends : ends_in_s0 s0 := by
    simp only [ends_in_s0, reducedWord, s0, gt_iff_lt, lt_self_iff_false, reduceIte, alternating,
      Fin.isValue, zero_add, Int.natAbs_zero, mul_zero, List.getLast?_singleton]
  have h_u_ne_1 : s0 ≠ 1 := by
    intro h
    have h_len : ℓ s0 = ℓ 1 := by rw [h]
    simp [length_s0, length_one] at h_len
  have h_max := theorem_3_2_eq_4 s0 {a := 2, b := 3} h_ends
  rw [if_neg (by norm_num), if_pos (by norm_num)] at h_max
  have h_unique := lemma_3_1_1 s0 {a := 2, b := 3} h_u_ne_1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, hw_is_max, rfl⟩
    have h_w_eq : w = s_alpha_d {a := 2, b := 3} := by
      rcases h_unique with ⟨m, hm, h_uniq_eq⟩
      have h1 : w = m :=by exact h_uniq_eq w hw_is_max
      have h2 : s_alpha_d {a := 2, b := 3} = m := h_uniq_eq _ h_max
      rw [h1, h2]
    rw [h_w_eq]
    unfold s_alpha_d s_α
    dsimp only [root_from_degree]
    simp only [Fin.isValue, gt_iff_lt, reduceLT, reduceIte, reduceAdd]
    simp [alternating, listToGroup, f, s0]
  · rintro rfl
    exists s_alpha_d {a := 2, b := 3}
