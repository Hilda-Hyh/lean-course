import Mathlib
import Dihedral.Basic
import Dihedral.Length


open Nat CoxeterSystem DihedralGroup

structure Root where
  a : ℕ
  b : ℕ
  sub_one : (a = b.succ) ∨ (b = a.succ)
deriving DecidableEq

def α0 : Root := ⟨1, 0, Or.inl rfl⟩
def α1 : Root := ⟨0, 1, Or.inr rfl⟩

-- 根的长度定义为 a + b
def Root.length (α : Root) : ℕ := α.a + α.b

lemma lemma_2_1_1 (u : D∞) : ℓ u = ℓ u⁻¹ :=
  (cs.length_inv u).symm

lemma lemma_2_1_3 (u v : D∞) : ℓ (u * v) ≤ ℓ u + ℓ v :=
  cs.length_mul_le u v

def Di_induction_on {P : D∞ → Prop} (g : D∞)
    (r : ∀ k, P (r k)) (sr : ∀ k, P (sr k)) : P g := by
  cases g
  · apply r
  · apply sr

theorem lemma_2_1_4 (u v : D∞) (huv : ℓ u ≤ ℓ v) :
    ℓ (u * v) = ℓ u + ℓ v ∨ ℓ (u * v) = ℓ v - ℓ u := by
  cases u with
  | r u =>
    cases v with
    | r v =>
      simp [r_mul_r, length_r] at *
      omega
    | sr v =>
      simp [r_mul_sr, length_r, length_sr] at *
      split_ifs at * <;> omega
  | sr u =>
    cases v with
    | r v =>
      simp [sr_mul_r, length_r, length_sr] at *
      split_ifs at * <;> omega
    | sr v =>
      simp [sr_mul_sr, length_r, length_sr] at *
      split_ifs at * <;> omega

structure Degree where
  a : ℕ
  b : ℕ
  deriving DecidableEq, Repr

instance : Add Degree where
  add d e := ⟨d.a + e.a, d.b + e.b⟩

instance : Zero Degree where
  zero := ⟨0, 0⟩

-- 定义标量乘法
def Degree.scale (n : ℕ) (d : Degree) : Degree :=
  ⟨n * d.a, n * d.b⟩

instance : HMul ℕ Degree Degree where
  hMul := Degree.scale

def Degree.sub (b d2 : Degree) : Degree :=
  ⟨b.a - d2.a, b.b - d2.b⟩

@[ext]
theorem Degree.ext {d1 d2 : Degree} (h0 : d1.a = d2.a) (h1 : d1.b = d2.b) : d1 = d2 := by
  cases d1; cases d2
  simp only at h0 h1
  rw [h0, h1]

instance : AddCommMonoid Degree where
  add := (· + ·)
  zero := 0
  add_assoc a b c := by
    ext <;> apply Nat.add_assoc
  zero_add a := by
    ext <;> apply Nat.zero_add
  add_zero a := by
    ext <;> apply Nat.add_zero
  add_comm a b := by
    ext <;> apply Nat.add_comm
  nsmul := fun n d => ⟨n * d.a, n * d.b⟩
  nsmul_zero n := by
    ext <;> (simp; rfl)
  nsmul_succ n d := by
    ext; all_goals
      simp only [succ_mul]; rfl

--度数的偏序关系
instance : PartialOrder Degree where
  le d1 d2 := d1.a ≤ d2.a ∧ d1.b ≤ d2.b
  le_refl d := ⟨le_refl _, le_refl _⟩
  le_trans d1 d2 d3 h12 h23 := ⟨le_trans h12.1 h23.1, le_trans h12.2 h23.2⟩
  le_antisymm d1 d2 h12 h21 := by
    cases d1; cases d2
    simp only [Degree.mk.injEq] at *
    exact ⟨Nat.le_antisymm h12.1 h21.1, Nat.le_antisymm h12.2 h21.2⟩

def getDegree : D∞ → Degree
  | .r i =>
    let k := i.natAbs
    ⟨k, k⟩
  | .sr i =>
    let k : ℤ := i
    if k ≥ 0 then
      if i = 0 then ⟨1, 0⟩ else ⟨i.natAbs - 1, i.natAbs⟩
    else
      ⟨i.natAbs + 1, i.natAbs⟩

@[simp]
lemma getDegree_one : getDegree (1 : D∞) = ⟨0, 0⟩ := by
      rfl

def Root.toDegree (α : Root) : Degree :=⟨α.a, α.b⟩

-- 定义顶点 (Vertices)。在 D∞ 的情况下，顶点是群元素
abbrev Vertex := D∞

-- 将根映射到 D∞ 中的反射元素
def s_α (α : Root) : D∞ :=
  if α.a > α.b then
    listToGroup (alternating 0 (α.a + α.b))
  else
    listToGroup (alternating 1 (α.a + α.b))

--  s(1,0) = s0
example : s_α α0 = s0 := by
  simp [α0, s_α, alternating, listToGroup, f]

theorem length_root_reflection (α : Root) :
    ℓ (s_α α) = α.a + α.b := by
  rw [s_α]
  split_ifs with h
  <;>simp [length_alternating]

--顶点 u 和 v 之间存在边，且度为 α。
def IsEdge (u v : Vertex) (α : Root) : Prop :=
  v = u * (s_α α)

notation:50 u " —[" α "]→ " v => IsEdge u v α

theorem edge_exists_iff (u v : Vertex) :
    (∃ α, u —[α]→ v) ↔ ∃ α : Root, v = u * s_α (α) := by
  simp [IsEdge]

--s0 是从 1 到 s0 的边，其度为 (1, 0)
example : (1 : D∞) —[α0]→ (cs.simple 0) := by
  dsimp [IsEdge]
  rw [one_mul]
  have hα : s_α α0 = s0 := by
    simp [α0, s_α, alternating, listToGroup, f]
  have hs : cs.simple 0 = s0 := rfl
  simp [hα, hs]

instance : Zero Degree where
  zero := ⟨0, 0⟩

inductive HasChain : Vertex → Vertex → Degree → Prop where
  | refl (u : Vertex) : HasChain u u 0
  | step {u v w : Vertex} {d : Degree} {α : Root} :
      HasChain u v d → IsEdge v w α → HasChain u w (d + α.toDegree)

-- 递增链：在每一步步进时增加 ℓ w > ℓ v 的判断
inductive HasIncreasingChain : Vertex → Vertex → Degree → Prop where
  | refl (u : Vertex) : HasIncreasingChain u u 0
  | step {u v w : Vertex} {d : Degree} {α : Root} :
      HasIncreasingChain u v d →
      IsEdge v w α →
      (ℓ v < ℓ w) →
      HasIncreasingChain u w (d + α.toDegree)

-- 如果存在任意度数的递增链，则 u < v
def Lt (u v : Vertex) : Prop :=
  ∃ d : Degree, HasIncreasingChain u v d ∧ u ≠ v

lemma chain_length_lt {u v : Vertex} {d : Degree} (h : HasIncreasingChain u v d) :
    ℓ u ≤ ℓ v := by
  induction h with
  | refl => exact le_refl _
  | step _ _ h_lt ih => exact le_of_lt (lt_of_le_of_lt ih h_lt)

lemma chain_length_lt_strict {u v : Vertex} {d : Degree} (h : HasIncreasingChain u v d)
    (hne : u ≠ v) : ℓ u < ℓ v := by
  induction h with
  | refl => contradiction
  | step h_chain h_edge h_lt ih =>
    rename_i v_mid w_final d_mid α
    by_cases heq : u = v_mid
    · subst heq
      exact h_lt
    · have h_u_lt_mid := ih heq
      exact lt_trans h_u_lt_mid h_lt

lemma Lt_trans {u v w} (huv : Lt u v) (hvw : Lt v w) : Lt u w := by
  rcases huv with ⟨d1, huv⟩
  rcases hvw with ⟨d2, hvw⟩
  let rec concat {x y z : Vertex} {d1 d2 : Degree}
      (hc1 : HasIncreasingChain x y d1) (hc2 : HasIncreasingChain y z d2) :
      HasIncreasingChain x z (d1 + d2) := by
    cases hc2 with
    | refl => simp only [add_zero]; exact hc1
    | step hc2_prev edge len_lt =>
      simp only [← add_assoc]
      exact HasIncreasingChain.step (concat hc1 hc2_prev) edge len_lt
  termination_by ℓ z
  use d1 + d2
  constructor
  · exact concat huv.1 hvw.1
  · intro h_eq
    have l1 := chain_length_lt_strict huv.1 huv.2
    have l2 := chain_length_lt_strict hvw.1 hvw.2
    have l3 : ℓ u < ℓ w := lt_trans l1 l2
    rw [h_eq] at l3
    exact lt_irrefl _ l3

lemma Lt_iff_le_not_ge (a b : Vertex) :
    Lt a b ↔ (Lt a b ∨ a = b) ∧ ¬(Lt b a ∨ b = a) := by
  constructor
  · intro h
    constructor
    · left; exact h
    · intro h_ge
      rcases h_ge with (hba | rfl)
      · rcases h with ⟨d1, c1, ne1⟩
        rcases hba with ⟨d2, c2, ne2⟩
        have l1 := chain_length_lt_strict c1 ne1
        have l2 := chain_length_lt_strict c2 ne2
        have contra := lt_trans l1 l2
        exact lt_irrefl _ contra
      · delta Lt at h
        rcases h with ⟨d, chain, ne⟩
        contradiction
  · rintro ⟨(hab | rfl), h_not_ge⟩
    · exact hab
    · exfalso
      apply h_not_ge
      exact Or.inr rfl

instance : PartialOrder D∞ where
  le u v := (Lt u v) ∨ (u = v)
  lt := Lt
  le_refl  u:= Or.inr rfl
  le_trans := by
    rintro a b c (hab|rfl) (hbc|rfl)
    any_goals tauto
    left
    exact Lt_trans hab hbc
  lt_iff_le_not_ge := Lt_iff_le_not_ge
  le_antisymm a b:= by
    rintro (hab|rfl) (hba|h)
    any_goals rfl
    · exfalso
      rcases hab with ⟨d1, c1, ne1⟩
      have l1 := chain_length_lt_strict c1 ne1
      rcases hba with ⟨d2, c2, ne2⟩
      have l2 := chain_length_lt_strict c2 ne2
      have contra := lt_trans l1 l2
      exact lt_irrefl _ contra
    · exact h.symm

lemma exists_root_eq_sr (k : ℤ) : ∃ α : Root, s_α α = sr k := by
  by_cases h : k > 0
  · -- Case k > 0
    let a := k.natAbs - 1
    let b := k.natAbs
    have h_sub : a = b - 1 := rfl
    have h_rel : b = a.succ := by
      dsimp [a, b]
      rw [Nat.sub_add_cancel]
      exact Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr (Int.ne_of_gt h))
    let α : Root := ⟨a, b, Or.inr h_rel⟩
    use α
    simp only [s_α]
    have : ¬ (α.a > α.b) := by
      change ¬ (a > b)
      linarith
    simp only [gt_iff_lt, this, ↓reduceIte, Fin.isValue]
    have h_len : a + b = 2 * k.natAbs - 1 := by
      dsimp [a, b]; omega
    have h_pos : k.natAbs ≥ 1 := by
      exact Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr (Int.ne_of_gt h))
    rw [h_len, show (2 * k.natAbs - 1) = 2 * (k.natAbs - 1) + 1 by omega]
    rw [alternating_prod_odd ( k.natAbs - 1) 1]
    simp only [Fin.isValue, one_ne_zero, ↓reduceIte, sr.injEq]
    have : ((k.natAbs - 1 : ℕ) : ℤ) + 1 = k := by
      calc
          (↑(k.natAbs - 1) : ℤ) + 1
          = ↑(k.natAbs) := by
              norm_cast
              simp [Nat.sub_add_cancel (Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr (Int.ne_of_gt h)))]
      _ = k := by simpa using (le_of_lt h)
    rw [this]
  · -- Case k ≤ 0
    let a := k.natAbs + 1
    let b := k.natAbs
    have h_rel : a = b.succ := rfl
    let α : Root := ⟨a, b, Or.inl h_rel⟩
    use α
    simp only [s_α]
    have : α.a > α.b := by
      change a > b
      linarith
    simp only [gt_iff_lt, this, ↓reduceIte, Fin.isValue]
    have h_len : a + b = 2 * k.natAbs + 1 := by
      dsimp [a, b]; omega
    rw [h_len]
    rw [alternating_prod_odd k.natAbs 0]
    simp
    have : -((k.natAbs) : ℤ) = k := by
      have hk : k ≤ 0 := le_of_not_gt h
      have := Int.ofNat_natAbs_of_nonpos hk
      linarith
    simpa using this

lemma inv_mul_is_sr_of_parity_diff (u v : Vertex)
    (h_parity : (ℓ u) % 2 ≠ (ℓ v) % 2) :
    ∃ k : ℤ, u⁻¹ * v = sr k := by
  -- D∞ 中元素要么是 r k 要么是 sr k
  let g := u⁻¹ * v
  cases hg : g with
  | sr k => use k
  | r k =>
    exfalso
    have h_len_g : ℓ g % 2 = 0 := by
      rw [hg, length_r]
      omega
    have h_hom : ℓ g % 2 = (ℓ u + ℓ v) % 2 := by
      dsimp [g]
      rw [cs.length_mul_mod_two, cs.length_inv]
    rw [h_hom] at h_len_g
    rw [Nat.add_mod] at h_len_g
    have hu_mod : ℓ u % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
    have hv_mod : ℓ v % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
    interval_cases ℓ u % 2 <;> interval_cases ℓ v % 2 <;>
    omega

lemma lt_of_succ_length (u v : Vertex) (h : ℓ v = ℓ u + 1) : u < v := by
  -- 确定 u⁻¹v 是反射 sr k
  have h_parity : (ℓ u) % 2 ≠ (ℓ v) % 2 := by
    rw [h, Nat.add_mod]
    match (ℓ u) % 2 with
    | 0 => simp
    | 1 => simp
    | x =>
      simp only [mod_succ]
      by_contra
      cases Nat.mod_two_eq_zero_or_one x with
      | inl hx =>
          have h1 : (x + 1) % 2 = 1 := Nat.succ_mod_two_eq_one_iff.mpr hx
          rw [h1] at this
          rw [this] at hx
          contradiction
      | inr hx =>
          have h1 : (x + 1) % 2 = 0 := Nat.succ_mod_two_eq_zero_iff.mpr hx
          rw [h1] at this
          rw [this] at hx
          contradiction
  obtain ⟨k, hk⟩ := inv_mul_is_sr_of_parity_diff u v h_parity
  obtain ⟨α, hα⟩ := exists_root_eq_sr k
  have h_edge : IsEdge u v α := by
    dsimp [IsEdge]
    rw [hα, ←hk, mul_inv_cancel_left]
  have h_len_lt : ℓ u < ℓ v := by rw [h]; exact Nat.lt_succ_self _
  let chain := HasIncreasingChain.step (HasIncreasingChain.refl u) h_edge h_len_lt
  have h_ne : u ≠ v := by
    intro eq
    rw [eq] at h_len_lt
    exact lt_irrefl _ h_len_lt
  use (0 + α.toDegree)


theorem lemma_2_3 (u v : Vertex) :
    u < v ↔ ℓ u < ℓ v := by
  constructor
  · intro h
    rcases h with ⟨d, chain, ne⟩
    exact chain_length_lt_strict chain ne
  · intro h_lt
    let k := ℓ v - ℓ u
    have h_diff : ℓ v = ℓ u + k := (Nat.add_sub_of_le (le_of_lt h_lt)).symm
    generalize hn : k = n
    rw [hn] at h_diff
    induction n generalizing v with
    | zero =>
      rw [Nat.add_zero] at h_diff
      rw [h_diff] at h_lt
      exact absurd h_lt (lt_irrefl _)
    | succ n ih =>
      if hn : n = 0 then
        rw [hn, Nat.add_zero] at h_diff
        exact lt_of_succ_length u v h_diff
       else
      -- 递归情况：长度差 > 1
      have h_len_v_pos : ℓ v > 0 := by
        rw [h_diff]
        have : n + 1 ≥ 1 := Nat.le_add_left 1 n
        omega
      have h_ne_one : v ≠ 1 := by
        intro h
        rw [h, cs.length_one] at h_len_v_pos
        exact lt_irrefl 0 h_len_v_pos
      obtain ⟨i, h_descent⟩ := cs.exists_rightDescent_of_ne_one h_ne_one
      let w := v * cs.simple i
      --∃w，使得 ℓ w + 1 = ℓ v，回到归纳
      have hi : ℓ w = ℓ v - 1 := by
        rw [cs.isRightDescent_iff] at h_descent
        exact Nat.eq_sub_of_add_eq h_descent
      have h_len_w : ℓ w = ℓ v - 1 := hi
      -- 证明 u < w
      have h_u_lt_w : ℓ u < ℓ w := by
        rw [h_len_w, h_diff]
        have : n ≥ 1 := Nat.pos_of_ne_zero hn
        omega
      have h_diff_w : ℓ w = ℓ u + n := by
        rw [h_len_w, h_diff]
        simp
      have hk_eq_n : ℓ w - ℓ u = n := by
        rw [h_diff_w]
        simp
      have h_u_le_w : u < w :=ih w h_u_lt_w h_diff_w hk_eq_n
      have h_w_lt_v : w < v := by
        apply lt_of_succ_length
        rw [h_len_w]
        omega
      exact Lt_trans h_u_le_w h_w_lt_v
notation "φ" => getDegree
-- This connects the Root structure to the φ function.
lemma φ_s_alpha_eq (α : Root) : φ (s_α α) = α.toDegree := by
  simp only [s_α, Root.toDegree]
  split_ifs with h_gt
  · -- a = b + 1
    rcases α.sub_one with (h | h)
    · -- a = b + 1
      rw [h, succ_eq_add_one]
      rw [show α.b + 1 + α.b =2 * α.b + 1  by ring, alternating_prod_odd]
      simp only [getDegree, Fin.isValue, ↓reduceIte, Int.neg_nonneg, Int.natCast_nonpos_iff,
        neg_eq_zero, cast_eq_zero, Int.natAbs_neg, Int.natAbs_natCast, ite_eq_right_iff]
      intro h'
      simp [h']
    · -- b = a + 1, contradicts a > b
      linarith
  · --  b = a + 1
    rcases α.sub_one with (h | h)
    · linarith
    · rw [h, succ_eq_add_one, ← add_assoc]
      rw [show α.a + α.a + 1 =2 * α.a + 1  by ring, alternating_prod_odd]
      simp only [one_ne_zero, reduceIte]
      have h_nezero : (α.a : ℤ) + 1 ≠ 0 := by omega
      have h_pos : (α.a : ℤ) + 1 ≥ 0 := by linarith
      simp [h_pos, getDegree, h_nezero]
      omega

lemma getDegree_r (k : ℤ) : φ (r k) = ⟨k.natAbs, k.natAbs⟩ := rfl

lemma getDegree_sr (k : ℤ) :
    φ (sr k) =
    if k ≥ 0 then
      if k = 0 then ⟨1, 0⟩ else ⟨k.natAbs - 1, k.natAbs⟩
    else
      ⟨k.natAbs + 1, k.natAbs⟩ := rfl

-- lemma：度数加法奇偶性
lemma degree_add_parity (g h : D∞) :
    ∃ (r s : ℕ),
      (φ g).a + (φ h).a = (φ (g * h)).a + 2 * r ∧
      (φ g).b + (φ h).b = (φ (g * h)).b + 2 * s := by
--对ZMod2中奇偶进行讨论
  sorry

-- Main Lemma 2.5 Proof
lemma lemma_2_5_a (u v : Vertex) (d : Degree) :
    HasChain u v d →
    ∃ (r s : ℕ), d.a = (φ (u⁻¹ * v)).a + 2 * r ∧
                 d.b = (φ (u⁻¹ * v)).b + 2 * s := by
  intro h
  induction h with
  | refl =>-- u = v, d = 0
    use 0, 0
    rw [inv_mul_cancel u, getDegree_one]
    simp only [mul_zero, add_zero]
    exact eq_zero_of_add_eq_zero rfl
  | step h_chain h_edge ih =>
    rename_i v' w d' α
    rcases ih with ⟨r',s', h0', h1'⟩
    let g := u⁻¹ * v'
    let t := s_α α
    have h_gw : u⁻¹ * w = g * t := by
      simp only [IsEdge] at h_edge
      rw [h_edge, mul_assoc]
    obtain ⟨k, m, hk, hm⟩ := degree_add_parity g t
    have h_deg_t : φ t = α.toDegree := φ_s_alpha_eq α
    use r' + k,s' + m
    constructor
    · -- for component a
      dsimp [Add.add, Root.toDegree]
      change d'.a + α.a = (φ (u⁻¹ * w)).a + 2 * (r' + k)
      rw [h0', h_gw, show α.a = (α.toDegree).a by rfl]
      rw [← h_deg_t]
      linarith [hk]
    · dsimp [Add.add, Root.toDegree]
      change d'.b + α.b = (φ (u⁻¹ * w)).b + 2 * (s' + m)
      rw [h1', h_gw, show α.b = (α.toDegree).b by rfl]
      simp [← h_deg_t]
      linarith [hm]


lemma lemma_2_5_b (u v : Vertex) (d : Degree) (h : HasChain u v d) :
    φ (u⁻¹ * v) ≤ d := by
  obtain ⟨r, s, hr, hs⟩ := lemma_2_5_a u v d h
  constructor
  · rw [hr]; exact Nat.le_add_right _ _
  · rw [hs]; exact Nat.le_add_right _ _
