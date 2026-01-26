import Mathlib
import Dihedral.Basic

open DihedralGroup CoxeterSystem List

notation "ℓ" => cs.length

theorem length_s0 : ℓ s0 = 1 := by
  have : cs.simple 0 = s0 := rfl
  simpa [this] using length_simple cs (0 : Fin 2)

lemma length_s1 : ℓ s1 = 1 := by
  have : cs.simple 1 = s1 := rfl
  simpa [this] using length_simple cs (1 : Fin 2)

def alternating (start : Fin 2) (n : ℕ) : List (Fin 2) :=
  match n with
  | .zero => []
  | .succ k => start :: alternating (start + 1) k
--后面发现可用alternatingWord替代
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
      simp only [alternating, Fin.isValue, isChain_cons_cons]
      constructor
      · fin_cases s <;> decide
      · fin_cases s
        <;> simp only [Fin.zero_eta, Fin.isValue]
        <;> exact ih _

def reducedWord (g : D∞) : List (Fin 2) :=
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

def listToGroup (l : List (Fin 2)) : D∞ :=
  (l.map f).prod

lemma alternating_add_two (s : Fin 2) (n : ℕ) :
    alternating s (n + 2) = s :: (s + 1) :: alternating s n := by
  simp only [alternating, Fin.isValue, cons.injEq, true_and]
  congr
  simp [add_assoc]

lemma h_s0s1 : f 0 * f 1 = r (1 : ℤ) := by
  simp [f, s0, s1, sr_mul_sr]

@[simp]
lemma alternating_prod_even (n : ℕ) (s : Fin 2) :
    listToGroup (alternating s (2 * n)) = if s = 0 then r (n : ℤ) else r (-(n : ℤ)) := by
  induction n generalizing s with
  | zero =>
      simp [alternating, listToGroup]
  | succ n ih =>
      rw [Nat.mul_succ, alternating_add_two]
      simp only [listToGroup, Fin.isValue, map_cons, prod_cons, Nat.cast_add, Nat.cast_one,
        neg_add_rev, Int.reduceNeg]
      fin_cases s
      all_goals
        simp only [listToGroup, Fin.isValue, Fin.forall_fin_two, ↓reduceIte, one_ne_zero,
          Fin.mk_one, Int.reduceNeg, Fin.zero_eta] at *
        simp_rw [ih]
        simp [f, s0, s1, add_comm, sub_eq_add_neg]

@[simp]
lemma alternating_prod_odd (n : ℕ) (s : Fin 2) :
    listToGroup (alternating s (2 * n + 1)) =
    if s = 0 then sr (-(n : ℤ)) else sr (n + 1 : ℤ) := by
  induction n generalizing s with
  | zero =>
      fin_cases s <;> simp [alternating, listToGroup, f, s0, s1]
  | succ n ih =>
      rw [Nat.mul_succ, add_comm, ← add_assoc, alternating_add_two, add_comm]
      fin_cases s
      all_goals
        simp only [listToGroup, Fin.isValue, Fin.forall_fin_two, ↓reduceIte, one_ne_zero,
          Fin.zero_eta, map_cons, prod_cons, Nat.cast_add, Nat.cast_one, neg_add_rev,
          Int.reduceNeg, Fin.mk_one, f, s0, s1, Fin.isValue, Matrix.cons_val_zero, add_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.reduceNeg] at *
        rw [add_comm 1 (2*n)]
        simp [ih]
        ring

@[simp]
lemma h_wp : ∀ l, cs.wordProd l = listToGroup l := by
  intro l; induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [wordProd, map_cons, prod_cons, listToGroup]
    have : cs.simple = f :=by
      ext i ; (fin_cases i <;> rfl)
    simp_rw [this]

lemma reducedWord_correct (g : D∞) : cs.wordProd (reducedWord g) = g := by
  -- cs.wordProd 就是 listToGroup
  cases g with
  | r k =>
      dsimp [reducedWord]
      rw [h_wp]
      split_ifs with h
      · -- k ≥ 0
        rw [alternating_prod_even]
        simp only [Fin.isValue, ↓reduceIte, Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, r.injEq]
        rw [abs_of_nonneg]
        exact h.le
      · rw [alternating_prod_even]
        simp only [Fin.isValue, one_ne_zero, ↓reduceIte, Nat.cast_natAbs, Int.cast_abs, Int.cast_eq,
          r.injEq]
        simp only [ge_iff_le, not_le] at h
        rw [abs_of_neg h, neg_neg]
  | sr k =>
      dsimp [reducedWord]
      rw [h_wp]
      split_ifs with h
      · have h_abs : (Int.natAbs k : ℤ) = (k : ℤ) := Int.natAbs_of_nonneg (le_of_lt h)
        let n := Int.natAbs k - 1
        have h_n : 2 * Int.natAbs k - 1 = 2 * n + 1 := by dsimp [n]; omega
        rw [h_n, alternating_prod_odd n 1]
        simp only [Fin.reduceEq, ↓reduceIte]
        have : (n : ℤ) + 1 = Int.natAbs k := by
          dsimp [n];zify
          have : 1 ≤ Int.natAbs k := by zify [h_abs]; exact h
          aesop
        rw [this, h_abs]
      · rw [alternating_prod_odd]
        simp only [Fin.isValue, ↓reduceIte, Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, sr.injEq]
        simp only [gt_iff_lt, not_lt] at h
        rw [abs_of_nonpos h, neg_neg]

lemma alt_inv_even (s : Fin 2) (n : ℕ) : (listToGroup (alternating s (2 * n)))⁻¹ =
    listToGroup (alternating (s + 1) (2 * n)) := by
  induction n generalizing s with
  | zero =>
    simp [alternating, listToGroup]
  | succ n ih =>
    rw [mul_add, mul_one]
    simp only [alternating_add_two, Fin.isValue]
    simp only [listToGroup, map_cons, prod_cons]
    rw [mul_inv_rev, mul_inv_rev]
    rw [fi_inv s, fi_inv (s + 1)]
    change (listToGroup (alternating s (2 * n)))⁻¹ * f (s + 1) * f s =
        f (s + 1) * (f (s + 1 + 1) * listToGroup (alternating (s + 1) (2 * n)))
    rw [ih s]
    fin_cases s
    · simp_all [f, s0, s1, alternating_prod_even]
      ring
    · simp_all [f, s0, s1, alternating_prod_even]


lemma alt_inv_odd (s : Fin 2) (n : ℕ) : (listToGroup (alternating s (2 * n + 1)))⁻¹ =
    listToGroup (alternating s (2 * n + 1)) := by
  induction n generalizing s with
  | zero =>
    simp only [listToGroup, alternating, map_cons, map_nil, prod_cons, prod_nil, mul_one]
    symm
    rw [← mul_eq_one_iff_eq_inv.mp (f_sq_one s)]
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by rfl]
    simp only [alternating_add_two, Fin.isValue]
    simp only [listToGroup, map_cons, prod_cons, mul_inv_rev, fi_inv]
    change (listToGroup (alternating s (2 * n + 1)))⁻¹ * f (s + 1) * f s =
        f s * (f (s + 1) * listToGroup (alternating s (2 * n + 1)))
    rw [ih s]
    fin_cases s
    · simp_all [f, s0, s1, alternating_prod_odd]
      ring
    · simp_all [f, s0, s1, alternating_prod_odd]
      ring

lemma list_length (s : Fin 2) (n : ℕ) : (alternating s n).length = n := by
  induction n generalizing s with
  | zero =>
      simp [alternating]
  | succ k ih =>
      simp [alternating, ih]

-- 辅助函数：定义 D∞ 中元素的预期长度，仅在证明ℓ时使用
def explicit_length : D∞ → ℕ
| r k => 2 * k.natAbs
| sr k =>
  let k_int : ℤ := k
  if k_int > 0 then
    2 * k.natAbs - 1
  else
    2 * k.natAbs + 1

lemma ex_length_one : explicit_length 1 = 0 := by
  rfl

-- 证明 explicit_length 满足三角不等式的一半，也即 Lipschtiz 性质
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
          rw [Int.natAbs_add_of_nonneg]
          all_goals
            norm_num
          exact hk
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
          · apply Nat.le_succ_of_le
            apply Nat.sub_le
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
  set l := ℓ
  have h_bound (L : List (Fin 2)) : explicit_length (cs.wordProd L) ≤ L.length := by
    induction L with
    | nil =>
      simp only [wordProd_nil, length_nil, nonpos_iff_eq_zero, ex_length_one ]
    | cons i L ih =>
      simp only [List.length_cons, CoxeterSystem.wordProd_cons]
      have h_simple : cs.simple i = f i := by
        fin_cases i; all_goals
          simp; rfl
      rw [h_simple]
      apply le_trans (explicit_length_mul_le i (cs.wordProd L))
      exact Nat.add_le_add_right ih 1
  have : ∃ (L : List (Fin 2)), L.length = ℓ g ∧ g = cs.wordProd L :=
    cs.exists_reduced_word g
  obtain ⟨L, hL_len, hL_prod⟩ := this
  dsimp [l]
  rw [← hL_len, ← hL_prod.symm]
  exact h_bound L

lemma explicit_length_alternating (s : Fin 2) (n : ℕ) :
    explicit_length (listToGroup (alternating s n)) = n := by
  match h_mod : n % 2 with
  | 0 =>
    have h_even : ∃ k, n = 2 * k := Nat.dvd_of_mod_eq_zero h_mod
    obtain ⟨k, rfl⟩ := h_even
    rw [alternating_prod_even]
    fin_cases s<;>simp [explicit_length]
  | 1 =>
    have h_odd : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    obtain ⟨k, rfl⟩ := h_odd
    rw [alternating_prod_odd]
    fin_cases s
    · simp [explicit_length]
    · simp [explicit_length]
      omega
  | n + 2 => omega

-- alternating s n 的长度为 n
lemma alternating_isReduced (s : Fin 2) (n : ℕ) :
    cs.IsReduced (alternating s n) := by
  dsimp [CoxeterSystem.IsReduced]
  let g := cs.wordProd (alternating s n)
  have h_le : ℓ g ≤ (alternating s n).length := cs.length_wordProd_le _
  have h_ge : (alternating s n).length ≤ ℓ g := by
    rw [list_length s n]
    have h_calc : explicit_length g = n := by
      simp [g, h_wp, explicit_length_alternating s n]
    rw [← h_calc]
    exact cs_length_ge_explicit g
  exact le_antisymm h_le h_ge

-- alternating Isreduced
lemma length_alternating (s : Fin 2) (n : ℕ) :
    ℓ (listToGroup (alternating s n)) = n := by
  have h_g : listToGroup (alternating s n) = cs.wordProd (alternating s n) := (h_wp _).symm
  rw [h_g]
  have h_red := alternating_isReduced s n
  rw [CoxeterSystem.IsReduced] at h_red
  rw [h_red, list_length]

theorem length_eq (g : D∞) :
   ℓ g = (reducedWord g).length := by
  have h_prod := reducedWord_correct g
  cases g with
  | r k =>
    dsimp [reducedWord]
    split_ifs with h
    · have h_red_eq : reducedWord (r k) = alternating 0 (2 * Int.natAbs k) := by
        simp [reducedWord, h]
      rw [ ← h_prod,h_red_eq, h_wp, length_alternating, list_length]
    · have h_red_eq : reducedWord (r k) = alternating 1 (2 * Int.natAbs k) :=by
        simp [reducedWord, h]
      rw [← h_prod, h_red_eq, h_wp, length_alternating, list_length]
  | sr k =>
    dsimp [reducedWord]
    split_ifs with h
    · have h_red_eq : reducedWord (sr k) = alternating 1 (2 * Int.natAbs k - 1) :=by
        simp [reducedWord, h]
      rw [← h_prod, h_red_eq, h_wp, length_alternating, list_length]
    · have h_red_eq : reducedWord (sr k) = alternating 0 (2 * Int.natAbs k + 1) :=by
        simp [reducedWord, h]
      rw [← h_prod, h_red_eq, h_wp, length_alternating, list_length]


lemma reducedWord_is_reduced (g : D∞) : cs.IsReduced (reducedWord g) := by
  rw [CoxeterSystem.IsReduced]
  rw [reducedWord_correct g]
  rw [length_eq g]

@[simp]
theorem length_r (k : ℤ) : ℓ (r k) = 2*k.natAbs := by
  rw [length_eq (r k)]
  dsimp [reducedWord]
  split_ifs with h <;>
    simp [list_length]

@[simp]
theorem length_sr (k : ℤ) : ℓ (sr k) =
    if k > 0 then 2 * k.natAbs - 1 else 2 * k.natAbs + 1 := by
  rw [length_eq (sr k)]
  dsimp [reducedWord]
  split_ifs with h <;>
    rw [list_length]

theorem length_sr' (k : ℤ) : ℓ (sr k) = (2*k - 1).natAbs := by
  simp [length_sr]; grind

theorem D_induction {P : D∞ → Prop}
    (h1 : P 1)
    (h_s0 : ∀ g, P g → P (g * s0))
    (h_s1 : ∀ g, P g → P (g * s1)) :
    ∀ g, P g := by
  intro g
  rw [← reducedWord_correct g]
  generalize reducedWord g = l
  induction l using List.reverseRecOn with
  | nil =>
    simp only [h_wp, listToGroup, List.map_nil, List.prod_nil]
    exact h1
  | append_singleton xs i ih =>
    -- 归纳：已知 P (listToGroup xs)，求证 P (listToGroup (xs ++ [i]))
    simp only [h_wp, listToGroup, map_append, map_cons, map_nil, prod_append, prod_cons, prod_nil,
      mul_one]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [show f 0 = s0 by rfl]
      apply h_s0
      simp_all only [h_wp]
      exact ih
    · simp only [Fin.mk_one, Fin.isValue]
      rw [show f 1 = s1 by rfl]
      apply h_s1
      simp_all only [h_wp]
      exact ih

--alternating归纳
theorem induction_on_alternating {P : D∞ → Prop}
    (h1 : P 1)
    (h_step : ∀ (s : Fin 2) (n : ℕ),
      P (listToGroup (alternating s n)) →
      P (listToGroup (alternating s (n + 1)))) :
    ∀ g, P g := by
  have h_all : ∀ (n : ℕ) (s : Fin 2), P (listToGroup (alternating s n)) := by
    intro n
    induction n with
    | zero =>
      intro s
      simp only [alternating, listToGroup, List.map_nil, List.prod_nil]
      exact h1
    | succ n ih =>
      intro s
      apply h_step s n
      exact ih s
  intro g
  rw [← reducedWord_correct g]
  cases g with
  | r k =>
    dsimp [reducedWord]
    simp only [h_wp]
    split_ifs
    · exact h_all (2 * Int.natAbs k) 0
    · exact h_all (2 * Int.natAbs k) 1
  | sr k =>
    dsimp [reducedWord]
    simp only [h_wp]
    split_ifs
    · exact h_all _ 1
    · exact h_all _ 0

--D∞ 的 Alternating induction
theorem alternating_cases {P : D∞ → Prop}
    (h : ∀ (s : Fin 2) (n : ℕ), P (listToGroup (alternating s n))) :
    ∀ g, P g := by
  intro g
  rw [← reducedWord_correct g, h_wp]
  dsimp [reducedWord]
  cases g with
  | r k =>
    simp only [ge_iff_le, Fin.isValue]
    split_ifs
    · apply h 0 (2 * k.natAbs)
    · apply h 1 (2 * k.natAbs)
  | sr k =>
    simp only [gt_iff_lt, Fin.isValue]
    split_ifs
    · apply h 1 (2 * k.natAbs - 1)
    · apply h 0 (2 * k.natAbs + 1)

lemma n_mod_2_induction {P : ℕ → Prop}
  (h0 : ∀ k : ℕ, P (2 * k))
  (h1 : ∀ k : ℕ, P (2 * k + 1)) :
  ∀ n : ℕ, P n := by
  intro n
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← two_mul]
    simpa using h0 k
  · simpa using h1 k
