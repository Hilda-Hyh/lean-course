import Mathlib

--无限二面体群由sr0、sr1生成
open DihedralGroup CoxeterSystem List

notation "D∞" => DihedralGroup 0

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

def s0 : D∞ := sr (0 : ZMod 0)
def s1 : D∞ := sr (1 : ZMod 0)

def B : Type := Fin 2
def M : CoxeterMatrix (Fin 2) :={
  M := !![1, 0; 0, 1]
  isSymm := by decide
  diagonal := by decide
  off_diagonal := by decide
}

def f : Fin 2 → D∞ := ![s0, s1]

lemma f_sq_one (i : Fin 2) : (f i) * (f i) = 1 := by
  fin_cases i <;> decide

lemma f_is_liftable : M.IsLiftable f := by
  intro i j
  simp only [M, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  fin_cases i <;> fin_cases j
  all_goals decide

def φ : M.Group →* D∞ := (M.toCoxeterSystem).lift ⟨f, f_is_liftable⟩

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
        · symm; exact inv_eq_of_mul_eq_one_left ss1
        · symm; exact inv_eq_of_mul_eq_one_left ss0
  induction z using Int.induction_on with
  | zero => simp only [zpow_zero, mul_one]; exact ss0
  | succ n ih =>
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

def ψ : D∞ →* M.Group where
  toFun x := match x with
    | DihedralGroup.r i => (s0m * s1m) ^ (i.cast : ℤ)
    | DihedralGroup.sr i => s0m * (s0m * s1m) ^ (i.cast : ℤ)
  map_one' := by
    rw [show (1 : D∞) = r (0 : ZMod 0) by rfl]
    simp only [ZMod.cast_zero, zpow_zero]
  map_mul' := by
    rintro (a | a) (b | b)
    all_goals simp; group
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

def mulEquiv : D∞ ≃* M.Group where
  toFun := ψ.toFun
  invFun := φ.toFun
  left_inv := by
    intro x
    cases x with
    | r i =>
      dsimp [ψ]
      have : φ ((s0m * s1m) ^ (i.cast : ℤ)) = (f 0 * f 1) ^ (i.cast : ℤ) := by simp; congr
      rw [this, f, s0, s1]
      simp
    | sr i =>
      simp only [ψ, OneHom.toFun_eq_coe, OneHom.coe_mk, MonoidHom.toOneHom_coe, map_mul, map_zpow]
      rw [show φ (s0m) = f 0 by rfl, show φ (s1m) = f 1 by rfl]
      dsimp [f]
      rw [show (s0 * s1) = r 1 by rfl, show s0 = sr (0 : ZMod 0) by rfl]
      simp
  right_inv := by
    have h : (ψ.comp φ) = {
        toFun := fun x => x
        map_one' := by simp
        map_mul' := by intros; simp } := by
      apply (M.toCoxeterSystem).ext_simple
      intro i
      simp only [MonoidHom.comp_apply]
      have hφ := (M.toCoxeterSystem).lift_apply_simple (f_is_liftable) i
      fin_cases i
      all_goals
        dsimp [ψ]
        simp_all only [Fin.zero_eta, Fin.isValue, CoxeterMatrix.toCoxeterSystem_simple]
      · rfl
      · dsimp [φ] at *
        rw [hφ, f, s1]
        simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, dvd_refl,
          ZMod.cast_one, zpow_one]
        group
        change M.simple 0 ^2 * M.simple 1 = M.simple 1
        simp only [Fin.isValue, mul_eq_right]
        exact (M.toCoxeterSystem).simple_sq (0 : Fin 2)
    intro g
    exact congrArg (fun m => m.toFun g) h
  map_mul' := by exact ψ.map_mul'

def cs : CoxeterSystem M D∞ := { mulEquiv := mulEquiv}

notation "ℓ" => cs.length

lemma s0' : s0 = cs.simple 0 := rfl
lemma s1' : s1 = cs.simple 1 := rfl

def reducedWord (g : D∞) : List (Fin 2) :=
    match g with
    | r k =>
      let k_int : ℤ := k
      if k_int ≥ 0 then
        CoxeterSystem.alternatingWord 0 1 (2 * k_int.natAbs)
      else
        CoxeterSystem.alternatingWord 1 0 (2 * k_int.natAbs)
    | sr k =>
      let k_int : ℤ := k
      if k_int > 0 then
        CoxeterSystem.alternatingWord 0 1 (2 * k_int.natAbs - 1)
      else
        CoxeterSystem.alternatingWord 1 0 (2 * k_int.natAbs + 1)
-- 辅助函数：定义 D∞ 中元素的预期长度
def explicit_length : D∞ → ℕ
| r k => 2 * k.natAbs
| sr k =>
  let k_int : ℤ := k
  if k_int > 0 then
    2 * k.natAbs - 1
  else
    2 * k.natAbs + 1

lemma explicit_length_mul_le (i : Fin 2) (g : D∞) :
    explicit_length (f i * g) ≤ explicit_length g + 1 := by
  fin_cases i
  · -- multiplying by s0 (f 0)
    simp only [f, s0]
    cases g with
    | r k =>
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, sr_mul_r, zero_add]
      dsimp [explicit_length]
      split_ifs with h
      · apply Nat.le_succ_of_le
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
      · apply le_refl
    | sr k =>
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, sr_mul_sr, sub_zero]
      dsimp [explicit_length]
      split_ifs with h
      · rw [Nat.sub_add_cancel]
        have hk : 1 ≤ Int.natAbs k := by
          have : Int.natAbs k > 0 := Int.natAbs_pos.mpr (ne_of_gt h)
          omega
        nlinarith
      · apply Nat.le_succ_of_le
        apply Nat.le_succ
  · simp only [f, s1]
    cases g with
    | r k =>
      have h_s1 : sr (1 : ZMod 0) = sr 0 * r 1 := by simp [sr_mul_r]
      rw [h_s1, sr_mul_r, zero_add]
      dsimp [explicit_length]
      let k_int : ℤ := k
      by_cases hk : k_int ≥ 0
      · have h_pos : 1 + k_int > 0 := by linarith
        rw [if_pos h_pos]
        have : (1 + k).natAbs = 1 + k.natAbs := by
          rw [Int.natAbs_add_of_nonneg]<;>norm_num; exact hk
        rw [this, Nat.mul_add, mul_one]
        omega
      · push_neg at hk
        by_cases hk1 : k = -1
        · subst hk1; simp
        · have h_nonpos : 1 + k_int ≤ 0 := by linarith
          rw [if_neg (not_lt.mpr h_nonpos)]
          have : (1 + k).natAbs = k.natAbs - 1 := by omega
          rw [this, Nat.mul_sub, mul_one]
          apply Nat.le_trans (m := 2 * k.natAbs - 1)
          · omega
          · apply Nat.le_succ_of_le; apply Nat.sub_le
    | sr k =>
      dsimp [explicit_length]
      split_ifs with h
      · let k_int : ℤ := k
        have : (k - 1).natAbs = k.natAbs - 1 := by
          have h1 : 1 ≤ k_int := Int.add_one_le_iff.mpr h
          rw [Int.natAbs_sub_of_nonneg_of_le (by omega) h1]
          simp only [isUnit_one, Int.natAbs_of_isUnit]
          ring
        rw [this, Nat.mul_sub, mul_one]
        omega
      · let k_int : ℤ := k
        have h_le : k_int ≤ 0 := Int.not_lt.mp h
        have h_abs : (k - 1).natAbs = k.natAbs + 1 := by omega
        rw [h_abs]
        linarith

lemma cs_length_ge_explicit (g : D∞) : explicit_length g ≤ ℓ g := by
  have h_bound (L : List (Fin 2)) : explicit_length (cs.wordProd L) ≤ L.length := by
    induction L with
    | nil => simp [cs.wordProd_nil, explicit_length]; rfl
    | cons i L ih =>
      simp only [List.length_cons, CoxeterSystem.wordProd_cons]
      have h_simple : cs.simple i = f i := by fin_cases i <;> rfl
      rw [h_simple]
      apply le_trans (explicit_length_mul_le i (cs.wordProd L))
      exact Nat.add_le_add_right ih 1
  obtain ⟨L, hL_len, hL_prod⟩ := cs.exists_reduced_word g
  rw [← hL_len, ← hL_prod.symm]
  exact h_bound L

-- 证明 reducedWord生成群元素
lemma reducedWord_correct (g : D∞) : cs.wordProd (reducedWord g) = g := by
  cases g with
  | r k =>
    dsimp [reducedWord]
    split_ifs with h
    · -- k ≥ 0. alternatingWord 0 1 (2k)
      rw [cs.prod_alternatingWord_eq_mul_pow 0 1 (2 * k.natAbs)]
      simp only [even_two, Even.mul_right, ↓reduceIte, Fin.isValue, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_div_cancel_left₀, one_mul]
      change (s0 * s1) ^ Int.natAbs k = r k
      simp only [s0, s1, sr_mul_sr, sub_zero, r_pow,  one_mul, r.injEq]
      exact Int.natAbs_of_nonneg h
    · -- k < 0. alternatingWord 1 0 (2|k|)
      rw [cs.prod_alternatingWord_eq_mul_pow 1 0 (2 * k.natAbs)]
      simp only [even_two, Even.mul_right, ↓reduceIte, Fin.isValue, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_div_cancel_left₀, one_mul]
      change (s1 * s0) ^ Int.natAbs k = r k
      simp only [s1, s0, sr_mul_sr, zero_sub, r_pow, neg_mul, one_mul, r.injEq]
      have : -((k.natAbs) : ℤ) = k := by
        have := Int.ofNat_natAbs_of_nonpos (le_of_not_ge h)
        linarith
      simpa using this
  | sr k =>
    dsimp [reducedWord]
    split_ifs with h
    · -- k > 0. alternatingWord 0 1 (2k - 1). Odd.
      rw [cs.prod_alternatingWord_eq_mul_pow 0 1 (2 * k.natAbs - 1)]
      have h_odd : ¬ Even (2 * k.natAbs - 1) := by
        rw [Nat.not_even_iff_odd]; use (k.natAbs - 1); omega
      simp only [h_odd, ↓reduceIte]
      have h_div : (2 * k.natAbs - 1) / 2 = k.natAbs - 1 := by omega
      rw [h_div, ← s0', ← s1']
      simp only [s1, s0, sr_mul_sr, sub_zero, r_pow, one_mul, sr_mul_r, sr.injEq]
      calc
        1 + ↑(Int.natAbs k - 1)
            = ↑(Int.natAbs k) := by norm_cast; omega
        _   = k := Int.ofNat_natAbs_of_nonneg (le_of_lt h)
    · -- k ≤ 0. alternatingWord 1 0 (2|k| + 1). Odd.
      rw [cs.prod_alternatingWord_eq_mul_pow 1 0 (2 * k.natAbs + 1)]
      have h_odd : ¬ Even (2 * k.natAbs + 1) := by simp only [Nat.not_even_bit1, not_false_eq_true]
      simp only [h_odd, ↓reduceIte]
      have h_div : (2 * k.natAbs + 1) / 2 = k.natAbs := by omega
      rw [h_div, ← s1', ← s0']
      simp only [s0, s1, sr_mul_sr, zero_sub, r_pow, neg_mul, one_mul, sr_mul_r,
        zero_add, sr.injEq]
      rw [Int.ofNat_natAbs_of_nonpos (not_lt.mp h), neg_neg]

-- explicit_length 与 alternatingWord 长度一致，注意alternatingWord定义中没有交替条件
lemma explicit_length_alternatingWord (i j : Fin 2) (n : ℕ) (h_ne : i ≠ j) :
    explicit_length (cs.wordProd (CoxeterSystem.alternatingWord i j n)) = n := by
  -- 利用 wordProd (reducedWord g) = g 的逆向思维
  rw [cs.prod_alternatingWord_eq_mul_pow]
  split_ifs with h_even
  · -- Even n
    simp only [one_mul]
    fin_cases i <;> fin_cases j
    · -- i=0, j=0
      contradiction
    · -- i=0, j=1
      simp [s0, s1, sr_mul_sr, ← s0', ← s1']
      dsimp [explicit_length]
      simpa [Nat.mul_comm] using (Nat.div_mul_cancel (h_even.two_dvd))
    · -- i=1, j=0.
      simp only [explicit_length, Fin.mk_one, Fin.isValue, ← s1', s1, Fin.zero_eta, ← s0', s0,
        sr_mul_sr, zero_sub, r_pow, neg_mul, one_mul]
      rw [Int.natAbs_neg]
      simpa [Nat.mul_comm] using (Nat.div_mul_cancel (h_even.two_dvd))
    · -- i=1, j=1
      contradiction
  · -- Odd n
    rw [Nat.not_even_iff_odd] at h_even
    let m := n / 2
    fin_cases i <;> fin_cases j
    · -- i=0, j=0
      contradiction
    · -- i=0, j=1
      simp only [explicit_length, Fin.mk_one, Fin.isValue, ← s1', s1, Fin.zero_eta, ← s0', s0,
        sr_mul_sr, sub_zero, r_pow, one_mul, sr_mul_r, gt_iff_lt]
      norm_cast
      simp only [add_pos_iff, zero_lt_one, Nat.div_pos_iff, Nat.ofNat_pos, true_and, true_or,
        ↓reduceIte, Nat.cast_add, Nat.cast_one]
      have h : 2 * (n / 2) + 1 = n :=
        Nat.two_mul_div_two_add_one_of_odd h_even
      calc
        2 * Int.natAbs (1 + ↑(n / 2)) - 1
            = 2 * (1 + n / 2) - 1 := by simp;congr
        _   = 2 * (n / 2) + 1 := by omega
        _   = n := h
    · -- i=1, j=0.
      simp only [explicit_length, Fin.zero_eta, Fin.isValue, ← s0', s0, Fin.mk_one, ← s1', s1,
        sr_mul_sr, zero_sub, r_pow, neg_mul, one_mul, sr_mul_r, zero_add, gt_iff_lt,
        Left.neg_pos_iff]
      split_ifs with h_pos
      · have : m = 0 := by linarith
        simp [m, this]
        linarith
      · rw [Int.natAbs_neg]
        simpa using Nat.two_mul_div_two_add_one_of_odd h_even
    · -- i=1, j=1
      contradiction

lemma alternating_reducedWord (i i' : Fin 2) (n : ℕ) (h_ne : i ≠ i') :
    reducedWord (cs.wordProd (alternatingWord i i' n)) = alternatingWord i i' n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · -- n = 2 * k
    fin_cases i <;> fin_cases i'
    · contradiction
    · -- i=0, i'=1. g = (s0 s1)^k = r k.
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, cs.prod_alternatingWord_eq_mul_pow,
        Even.add_self, ↓reduceIte, one_mul]
      simp [s0, s1, sr_mul_sr,←  s0', ← s1', reducedWord]
      congr
      ring_nf
      congr
      simp
      omega
    · -- i=1, i'=0. g = (s1 s0)^k = r (-k).
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, cs.prod_alternatingWord_eq_mul_pow,
        Even.add_self, ↓reduceIte, one_mul]
      simp [s0, s1, sr_mul_sr,←  s0', ← s1', reducedWord]
      split_ifs with h
      · -- k = 0
        have : k = 0 := by omega
        subst this
        simp [alternatingWord]
      · -- k > 0
        congr
        ring_nf
        congr
        simp
        omega
    · contradiction
  · -- n = 2 * k + 1
    fin_cases i <;> fin_cases i'
    · contradiction
    · -- i=0, i'=1.
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, cs.prod_alternatingWord_eq_mul_pow,
        Nat.not_even_bit1, ↓reduceIte]
      have h_div : (2 * k + 1) / 2 = k := by omega
      rw [h_div]
      let k_int : ℤ := k
      simp only [reducedWord, Fin.isValue, ← s1', s1, ← s0', s0, sr_mul_sr, sub_zero, r_pow,
        one_mul, sr_mul_r, gt_iff_lt]
      have : (1 + k_int) > 0 := by norm_cast; omega
      rw [if_pos this]
      congr
      simp
      omega
    · -- i=1, i'=0.
      simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, cs.prod_alternatingWord_eq_mul_pow,
        Nat.not_even_bit1, ↓reduceIte]
      have h_div : (2 * k + 1) / 2 = k := by omega
      rw [h_div]
      simp only [reducedWord, Fin.isValue, ← s0', s0, ← s1', s1, sr_mul_sr, zero_sub, r_pow,
        neg_mul, one_mul, sr_mul_r, zero_add, gt_iff_lt, Left.neg_pos_iff]
      let k_int : ℤ := k
      have : ((k) : ℤ) ≥ 0 := by norm_cast; omega
      rw [if_neg (not_lt.mpr this)]
      congr
      omega
    · contradiction

theorem length_eq (g : D∞) : ℓ g = (reducedWord g).length := by
  have h_prod : cs.wordProd (reducedWord g) = g := reducedWord_correct g
  have h_le : ℓ g ≤ (reducedWord g).length := by
    nth_rewrite 1 [← h_prod]
    exact cs.length_wordProd_le (reducedWord g)
  have h_len_eq : (reducedWord g).length = explicit_length g := by
    cases g with
    | r k =>
      dsimp [reducedWord]
      split_ifs
      <;>
      · rw [CoxeterSystem.length_alternatingWord]
        dsimp [explicit_length]
    | sr k =>
      dsimp [reducedWord]
      split_ifs with h
      <;>
      · rw [CoxeterSystem.length_alternatingWord]
        simp [explicit_length, h]
  rw [h_len_eq] at h_le
  exact le_antisymm h_le (cs_length_ge_explicit g) ▸ h_len_eq.symm

theorem length_sr' (k : ℤ) : ℓ (sr k) = (2 * k - 1).natAbs := by
  sorry

theorem D_induction {P : D∞ → Prop}
    (h1 : P 1)
    (h_s0 : ∀ g, P g → P (g * s0))
    (h_s1 : ∀ g, P g → P (g * s1)) :
    ∀ g, P g := by
  intro g
  rw [← reducedWord_correct g]
  generalize reducedWord g = L
  induction L using List.reverseRecOn with
  | nil =>
    simp only [cs.wordProd_nil]
    exact h1
  | append_singleton xs i ih =>
    -- 归纳步：cs.wordProd (xs ++ [i]) = cs.wordProd xs * s i
    simp only [cs.wordProd_append, cs.wordProd_singleton]
    fin_cases i
    · -- i = 0
      simp only [Fin.zero_eta, Fin.isValue, ← s0']
      apply h_s0
      exact ih
    · -- i = 1
      simp only [Fin.mk_one, Fin.isValue, ← s1']
      apply h_s1
      exact ih

theorem induction_on_alternating {P : D∞ → Prop}
    (h1 : P 1)
    (h_step : ∀ (g : D∞) (s : Fin 2), P g → P (g * cs.simple s)) :
    ∀ g, P g := by
  apply D_induction h1
  · intro g hg; exact h_step g 0 hg
  · intro g hg; exact h_step g 1 hg

-- D∞ 的 Alternating cases
theorem alternating_cases {P : D∞ → Prop}
    (h : ∀ (i j : Fin 2) (n : ℕ), i ≠ j → P (cs.wordProd (alternatingWord i j n))) :
    ∀ g, P g := by
  intro g
  rw [← reducedWord_correct g]
  dsimp [reducedWord]
  cases g with
  | r k =>
    simp only [ge_iff_le, Fin.isValue]
    split_ifs
    · apply h 0 1; decide
    · apply h 1 0; decide
  | sr k =>
    simp only [gt_iff_lt, Fin.isValue]
    split_ifs
    · apply h 0 1; decide
    · apply h 1 0; decide

lemma n_mod_2_induction {P : ℕ → Prop}
  (h0 : ∀ k : ℕ, P (2 * k))
  (h1 : ∀ k : ℕ, P (2 * k + 1)) :
  ∀ n : ℕ, P n := by
  intro n
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← two_mul]
    exact h0 k
  · exact h1 k
