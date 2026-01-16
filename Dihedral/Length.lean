import Mathlib
import Dihedral.Basic

open CoxeterSystem DihedralGroup

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


lemma alternating_add_two (s : Fin 2) (n : ℕ) :
    alternating s (n + 2) = s :: (if s = 0 then 1 else 0) :: alternating s n := by
  simp only [alternating, Fin.isValue, ite_eq_right_iff, one_ne_zero, imp_false, ite_not,
    cons.injEq, true_and]
  split_ifs with h
  · rw [h]
  · have := Fin.eq_one_of_ne_zero s h
    rw [this]


lemma h_s0s1 : f 0 * f 1 = r (1 : ℤ) := by
  simp [f, s0, s1, sr_mul_sr]

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
          Int.reduceNeg, Fin.mk_one] at *
        simp_rw [ih]
        simp only [f, s1, s0, sr_mul_sr, sub_eq_add_neg, neg_zero, add_zero, sr_mul_r, add_comm,
          sr.injEq, zero_add, Int.reduceNeg, add_comm]
      rw [add_comm]

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
    listToGroup (alternating (if s = 0 then (1 : Fin 2) else 0) (2 * n)) := by
  induction n generalizing s with
  | zero =>
    simp [alternating, listToGroup]
  | succ n ih =>
    rw [mul_add, mul_one]
    simp only [alternating_add_two, Fin.isValue, ite_eq_right_iff, one_ne_zero, imp_false, ite_not]
    set s' := if s = 0 then (1 : Fin 2) else 0
    have : s = if s = 0 then 0 else 1 := by fin_cases s <;> decide
    rw [← this]
    simp only [listToGroup, map_cons, prod_cons]
    rw [mul_inv_rev, mul_inv_rev]
    rw [fi_inv s, fi_inv s']
    change (listToGroup (alternating s (2 * n)))⁻¹ * f s' * f s =
        f s' * (f s * listToGroup (alternating s' (2 * n)))
    rw [ih s]
    fin_cases s
    · simp_all [f, s0, s1, alternating_prod_even, s']
      ring
    · simp_all [f, s0, s1, alternating_prod_even, s']

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
    set s' := if s = 0 then (1 : Fin 2) else 0
    simp only [listToGroup, map_cons, prod_cons, mul_inv_rev, fi_inv]
    change (listToGroup (alternating s (2 * n + 1)))⁻¹ * f s' * f s =
        f s * (f s' * listToGroup (alternating s (2 * n + 1)))
    rw [ih s]
    fin_cases s
    · simp_all [f, s0, s1, alternating_prod_odd, s']
      ring
    · simp_all [f, s0, s1, alternating_prod_odd, s']
      ring

lemma list_length (s : Fin 2) (n : ℕ) : (alternating s n).length = n := by
  induction n generalizing s with
  | zero =>
      simp [alternating]
  | succ k ih =>
      simp [alternating, ih]



lemma alternating_isReduced (s : Fin 2) (n : ℕ) :
    cs.IsReduced (alternating s n) := by
  induction n generalizing s with
  | zero =>
    unfold CoxeterSystem.IsReduced
    simp [alternating]
  | succ n ih =>
    rw [alternating]
    set s' := if s = 0 then (1 : Fin 2) else 0
    unfold CoxeterSystem.IsReduced
    simp only [List.length, list_length]
    set L := alternating s' n
    rw [wordProd_cons]
    set g := cs.wordProd L
    -- 目标是证明 cs.length (f s * g) = n + 1
    have h_len_g : cs.length g = n :=by
      have : cs.IsReduced L:= ih s'
      simp at this
      dsimp [g]

      sorry
    rw [← h_len_g]
    rw [← CoxeterSystem.not_isLeftDescent_iff cs]
    --rw [isLeftDescent_iff_not_isLeftDescent_mul, not_not, not_isLeftDescent_iff]
    by_contra h_des
    --rw [isLeftDescent_iff] at h_des
    -- 填充 sorry 的部分
    have h_s_ne_s' : s ≠ s' := by
      fin_cases s <;> simp [s']


    -- 获取 L 的第一个元素。因为 n > 0 (若 n=0 则 g=1, 下降集为空)
    if hn : n = 0 then
      subst hn
      simp only [g, L, wordProd_nil, alternating] at h_des
      rw [isLeftDescent_iff, mul_one, show cs.length 1 = 0 by exact ih s,
        show ℓ (cs.simple s) = 1 by exact length_simple cs s] at h_des
      contradiction
    else
      -- 对于 n > 0, L = s' :: tail
      have h_L_head : L.head (by aesop) = s' := by
        subst s'; fin_cases s <;> simp [L, alternating];sorry;sorry
      sorry


-- 所有交替列表都是最短的
lemma length_alternating (s : Fin 2) (n : ℕ) :
    ℓ (listToGroup (alternating s n)) = n := by
  induction n generalizing s with
  | zero =>
    simp only [listToGroup, alternating, map_nil, prod_nil, length_one]
  | succ n h =>
    rw [← h_wp (alternating s (n + 1)), alternating_isReduced, list_length]

theorem length_eq (g : D∞) :
    cs.length g = (reducedWord g).length := by
  induction reducedWord g with
  | nil => sorry
  | cons head tail ih => sorry



lemma reducedWord_is_reduced (g : D∞) : cs.IsReduced (reducedWord g) := by
  --   reducedWord g 是一个满足 (· ≠ ·) 链的列表。
  have h_chain : List.IsChain (· ≠ ·) (reducedWord g) := by
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
