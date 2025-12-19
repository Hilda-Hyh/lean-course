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
    _ = (s0m * s1m)⁻¹ ^ (n + 1) := by simp [h1, zpow_natCast] at ih ⊢;rw [ih, pow_succ]
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
        dsimp [ψ]; simp_all
      · rfl
      · dsimp [φ] at *
        rw [hφ, f, s1]
        simp only [dvd_refl, ZMod.cast_one, zpow_one, Fin.isValue]
        group
        change M.simple 0 ^2 * M.simple 1 = M.simple 1
        simp
        exact (M.toCoxeterSystem).simple_sq (0 : Fin 2)
    intro g
    exact congrArg (fun m => m.toFun g) h
  map_mul' := by
    exact ψ.map_mul'

noncomputable def cs : CoxeterSystem M (DihedralGroup 0) :=
  { mulEquiv := mulEquiv}

theorem length_s0 : cs.length s0 = 1 := by
  have : cs.simple 0 = s0 := rfl
  simpa [this] using length_simple cs (0 : Fin 2)

notation "ℓ" => cs.length

lemma length_s1 : ℓ s1 = 1 := by
  have : cs.simple 1 = s1 := rfl
  simpa [this] using length_simple cs (1 : Fin 2)

open CoxeterSystem List

def alternating (start : Fin 2) (n : ℕ) : List (Fin 2) :=
  match n with
  | 0 => []
  | k + 1 => start :: alternating (if start = 0 then 1 else 0) k

-- 验证交替列表
lemma alternating_chain (s : Fin 2) (n : ℕ) :
    List.IsChain (· ≠ ·) (alternating s n) := by
  induction n generalizing s with
  | zero => simp [alternating]
  | succ n ih =>
    simp only [ne_eq, alternating, Fin.isValue]
    cases n with
    | zero => simp [alternating]
    | succ n' =>
      simp only [alternating, Fin.isValue, ite_eq_right_iff, one_ne_zero, imp_false, ite_not,
        isChain_cons_cons]
      constructor
      · fin_cases s <;> decide
      · fin_cases s
        <;> simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
        <;> exact ih _

def reducedWord (g : D∞) : List (Fin 2) :=
  --let l : List (Fin 2) :=
    match g with
    | r k =>
      let k_int : ℤ := k
      if k_int ≥ 0 then
        alternating 0 (2 * k_int.natAbs)
      else
        alternating 1 (2 * k_int.natAbs)
    | sr k =>
      let k_int : ℤ := k
      if k_int > 0 then
        alternating 1 (2 * k_int.natAbs - 1)
      else
        alternating 0 (2 * k_int.natAbs + 1)

  --l.map M.toCoxeterSystem.simple

def listToGroup (l : List (Fin 2)) : D∞ :=
  (l.map f).prod

open CoxeterSystem

lemma reducedWord_correct (g : D∞) : cs.wordProd (reducedWord g) = g := by
  -- 计算偶数长度交替列表的乘积
  have h_even : ∀ n : ℕ, cs.wordProd (alternating 0 (2 * n)) = r (n : ℤ) ∧
                         cs.wordProd (alternating 1 (2 * n)) = r (-(n : ℤ)) := by
    intro n
    induction n with
    | zero =>
      simp only [alternating, wordProd_nil, CharP.cast_eq_zero, r_zero, neg_zero, and_self]
    | succ n ih =>
      simp [alternating, Fin.isValue, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg]
      sorry
      --rw [ih.1, ih.2]


  have h_odd : ∀ n : ℕ, cs.wordProd (alternating 0 (2 * n + 1)) = sr (-(n : ℤ)) ∧
                        cs.wordProd (alternating 1 (2 * n + 1)) = sr (n + 1 : ℤ) := by
    intro n
    specialize h_even n
    simp only [alternating, Fin.isValue, ↓reduceIte, cs.wordProd_cons, h_even, one_ne_zero]
    constructor
    · sorry
    · sorry

  cases g with
  | r k =>
    simp [reducedWord]
    split_ifs with h
    · -- k >= 0
      simp [h_even k.natAbs]
      --ZMod上的abs
      sorry
    · -- k < 0
      simp [h_even k.natAbs]
      simp only [not_le] at h
      sorry
  | sr k =>
    simp only [reducedWord, gt_iff_lt, Fin.isValue]
    split_ifs with h
    · -- k > 0
      have h_pos : 0 < k.natAbs := by exact Int.natAbs_pos.mpr (ne_of_gt h)
      let n := k.natAbs - 1
      have hn : k.natAbs = n + 1 := (Nat.succ_pred_eq_of_pos h_pos).symm
      rw [hn, Nat.mul_add]
      simp [h_odd n]
      congr
      simp [n]
      norm_cast
      rw [Nat.sub_add_cancel (by sorry)]
      push_cast
      sorry
    · -- k <= 0
      simp [h_odd k.natAbs]
      simp only [ not_lt] at h
      sorry

theorem length_eq (g : D∞) :
    cs.length g = (reducedWord g).length := by
  have h_prod : cs.wordProd (reducedWord g) = g := reducedWord_correct g
  rw [← h_prod]
  let L := reducedWord g
  have h_chain : List.IsChain (· ≠ ·) L := by
    sorry
  induction L with
  | nil =>
    rw [show reducedWord g = [] by sorry]
    simp only [wordProd_nil, length_one]
    rfl
  | cons head tail ih =>
    exact ih


lemma reducedWord_is_reduced (g : D∞) : cs.IsReduced (reducedWord g) := by
  --   reducedWord g 是一个满足 (· ≠ ·) 链的列表。
  have h_chain_fin : List.IsChain (· ≠ ·) (reducedWord g) := by
    cases g with
    | r k =>
      dsimp only [reducedWord]
      split <;> (apply alternating_chain)
    | sr k =>
      dsimp only [reducedWord]
      split <;> (apply alternating_chain)
  unfold CoxeterSystem.IsReduced
  rw [reducedWord_correct g]
  exact length_eq g

open Nat

structure Root where
  a : ℕ
  b : ℕ
  sub_one : (a = b.succ) ∨ (b = a.succ)
deriving DecidableEq

def α0 : Root := ⟨1, 0, Or.inl rfl⟩
def α1 : Root := ⟨0, 1, Or.inr rfl⟩

/-- 根的长度定义为 a + b -/
def Root.length (α : Root) : ℕ := α.a + α.b

lemma two_p_one_1 (u : D∞) : cs.length u = cs.length u⁻¹ :=
  (cs.length_inv u).symm

lemma length_is_odd_iff_is_reflection (u : D∞) :
    (cs.length (u : DihedralGroup 0)) % 2 = 1 ↔
      match u with | r _ => False | sr _ => True := by
  cases u with
  | r k =>
    -- 证明 r(k) 的长度是偶数
    simp only [iff_false, mod_two_not_eq_one]
    sorry
  | sr k =>
    -- 证明 sr(k) 的长度是奇数
    simp only [iff_true]
    let k_int : ℤ := k
    by_cases h : k_int > 0
    · -- k > 0: length = 2k - 1

      sorry
    · -- k ≤ 0: length = 2|k| + 1
      sorry


lemma two_p_one_3 (u v : D∞) : cs.length (u * v) ≤ cs.length u + cs.length v :=
  cs.length_mul_le u v

lemma two_p_one_4 (i j : ℤ) (h_le : 2 * i.natAbs ≤ 2 * j.natAbs) :
    cs.length (r i * r j) = (cs.length (r i) + cs.length (r j)) ∨
    cs.length (r i * r j) = (cs.length (r j) - cs.length (r i)) := by
  --考虑CoxeterSystem上的Bruhat基
  rw [r_mul_r]
  have h_le : i.natAbs ≤ j.natAbs := by exact Nat.le_of_mul_le_mul_left h_le (by simp)
  obtain hi | hi | hi := lt_trichotomy i 0
  · -- i < 0
    obtain hj | hj | hj := lt_trichotomy j 0
    · -- j < 0: 同号相减
      sorry
    · -- j = 0
      sorry
    · -- j > 0: 异号相加
      sorry
  · -- i = 0
    sorry
  · -- i > 0
    obtain hj | hj | hj := lt_trichotomy j 0
    · -- j < 0: 异号相加
      sorry
    · -- j = 0
      sorry
    · -- j > 0: 同号相减
      sorry

section GraphStructure

/-- 将根映射到 D∞ 中的反射元素 -/
def s_α (α : Root) : D∞ :=
  if α.a > α.b then
    listToGroup (alternating 0 (α.a + α.b))
  else
    listToGroup (alternating 1 (α.a + α.b))

--  s(1,0) = s0
example : s_α α0 = s0 := by
  simp [α0, s_α, alternating, listToGroup, f]

theorem length_root_reflection (α : Root) :
    cs.length (s_α α) = α.a + α.b := by
  rw [s_α]
  split_ifs with h
  · -- a > b
    have h_len : (alternating 0 (α.a + α.b)).length = α.a + α.b := by
      sorry
    rw [← h_len]
    -- 利用之前定义的 length_eq，证明交替序列在 D∞ 中是约简的
    rw [length_eq]
    sorry
  · -- 情况 b > a
    sorry

-- 定义顶点 (Vertices)。在 D∞ 的情况下，顶点是群元素
abbrev Vertex := D∞

--顶点 u 和 v 之间存在边，且度为 α。

def IsEdge (u v : Vertex) (α : Root) : Prop :=
  v = u * (s_α α)

notation:50 u " —[" α "]→ " v => IsEdge u v α

theorem edge_exists_iff (u v : Vertex) :
    (∃ α, u —[α]→ v) ↔ ∃ α : Root, v = u * s_α α := by
  simp [IsEdge]

--若α = (1, 0) 展示 s0 是从 1 到 s0 的边，其度为 (1, 0)
example : (1 : D∞) —[α0]→ (cs.simple 0) := by
  dsimp [IsEdge]
  rw [one_mul]
  sorry

end GraphStructure
