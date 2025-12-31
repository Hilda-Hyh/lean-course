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

lemma fi_inv (i : Fin 2) : (f i)⁻¹ = f i := by
  exact inv_eq_of_mul_eq_one_left (f_sq_one i)

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
        dsimp [ψ]; simp_all only [Fin.zero_eta, Fin.isValue, CoxeterMatrix.toCoxeterSystem_simple]
      · rfl
      · dsimp [φ] at *
        rw [hφ, f, s1]
        simp only [dvd_refl, ZMod.cast_one, zpow_one, Fin.isValue]
        group
        change M.simple 0 ^2 * M.simple 1 = M.simple 1
        simp only [Fin.isValue, mul_eq_right]
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
      ext i <;> fin_cases i <;> rfl
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
    simp [List.length, list_length]
    apply isReduced_cons_of_reduced_of_not_mem_descents
    · exact ih (if s = 0 then 1 else 0)
    · -- 这里需要证明 f s 不在后续序列的下降集中
      -- 对于 D∞，这等价于证明增加该元素后长度增加
      sorry

-- 所有交替列表都是最短的
lemma length_alternating (s : Fin 2) (n : ℕ) :
    ℓ (listToGroup (alternating s n)) = n := by
  induction n generalizing s with
  | zero =>
    simp only [listToGroup, alternating, map_nil, prod_nil, length_one]
  | succ n h =>
    rw [alternating]
    set s' := if s = 0 then (1 : Fin 2) else 0
    --simp [listToGroup]
    set g := listToGroup (alternating s' n)
    have h_wp_alt : listToGroup (s :: alternating s' n) = f s * listToGroup (alternating s' n) := by
      simp [listToGroup]
    have h_len_g : ℓ g = n := h s'
    rw [h_wp_alt, ← h_wp]
    by_contra h_lt
    have h_inc :
      cs.length (cs.simple s * g) = cs.length g + 1 :=
    by
      apply cs.length_simple_mul_of_not_mem_leftDescent
      -- 这里你证明 s ∉ leftDescent w

    have h_less : ℓ (f s * g) < ℓ g := by
      rw [h_len_g]
      have :=cs.length_simple_mul (f s) s

      linarith [h_lt, this, g]
      exact Nat.lt_of_le_of_ne (cs.length_simple_mul (f s) s) (by
        intro h_eq
        simp_rw [h_wp, g, h_eq] at h_lt
        simp at h_lt)

    -- 如果 ℓ(s * g) < ℓ(g)，则 s ∈ Descents(g)
    -- 在 D∞ 中，这要求 g 的 reduced word 必须以 s 开头
    -- 但 alternating s' n 的开头是 s'，且 s ≠ s'
    have h_chain := alternating_chain s (n + 1)
    sorry

theorem length_eq (g : D∞) :
    cs.length g = (reducedWord g).length := by
  have h_prod : cs.wordProd (reducedWord g) = g := reducedWord_correct g
  rw [← h_prod]
  let L := reducedWord g
  generalize hL : reducedWord g = L
  have h_chain : List.IsChain (· ≠ ·) L := by
    sorry
  induction L with
  | nil =>
    simp only [wordProd_nil, length_one]
    rfl
  | cons head tail ih =>
    simp_all only [wordProd_cons, cons_ne_self, ne_eq, IsEmpty.forall_iff, length_cons]
    rw [← h_prod]

    sorry


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
    simp only [iff_false, mod_two_not_eq_one, ← alternating_prod_even]
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
    cs.length (s_α α) = α.a + α.b := by
  rw [s_α]
  split_ifs with h
  <;>simp [length_alternating]

-- 定义顶点 (Vertices)。在 D∞ 的情况下，顶点是群元素
abbrev Vertex := D∞

--顶点 u 和 v 之间存在边，且度为 α。
def IsEdge (u v : Vertex) (α : Root) : Prop :=
  v = u * (s_α α)

notation:50 u " —[" α "]→ " v => IsEdge u v α

theorem edge_exists_iff (u v : Vertex) :
    (∃ α, u —[α]→ v) ↔ ∃ α : Root, v = u * s_α α := by
  simp [IsEdge]

--s0 是从 1 到 s0 的边，其度为 (1, 0)
example : (1 : D∞) —[α0]→ (cs.simple 0) := by
  dsimp [IsEdge]
  rw [one_mul]
  have hα : s_α α0 = s0 := by
    simp [α0, s_α, alternating, listToGroup, f]
  have hs : cs.simple 0 = s0 := rfl
  simp [hα, hs]

def Root.add (α β : Root) : Root :=
  ⟨α.a + β.a, α.b + β.b, by
    cases α.sub_one with
    | inl h =>
        left
        simp [h, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, ← Nat.add_assoc]
        group
        sorry
    | inr h =>
        right
        -- h : α.b = α.a.succ
        simp [h, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    sorry⟩

lemma s_add (α β : Root) : s_α (α.add β) =s_α α * s_α β := by
  dsimp [s_α, Root.add]

  sorry

lemma IsEdge.trans {u v w} {α β} (huv : u —[α]→ v) (hvw : v —[β]→ w) :
    u —[α.add β]→ w := by
  dsimp [IsEdge] at *
  subst huv hvw

  sorry


inductive _lt_ : D∞ → D∞ → Prop
| edge {u : D∞} {v : D∞} (α : Root) (h : u —[α]→ v) : _lt_ u v

lemma _lt_trans {u v w} (huv : _lt_ u v) (hvw : _lt_ v w) : _lt_ u w := by
  rcases huv with ⟨α_uv, huv⟩
  rcases hvw with ⟨α_vw, hvw⟩
  refine .edge _ (huv.trans hvw)

instance : PartialOrder D∞ where
  le u v := u = v ∨ _lt_ u v
  lt := _lt_
  le_refl := by simp
  le_trans := by
    rintro a b c (rfl|hab) (rfl|hbc)
    any_goals tauto
    right
    exact _lt_trans hab hbc
  lt_iff_le_not_ge := by
    rintro a b
    sorry
  le_antisymm := by
    rintro a b (rfl|hab)
    · simp
    · rintro (rfl|h)
      · simp
      · sorry

lemma two_three (u v : D∞) : u < v ↔ cs.length u < cs.length v:= by
  constructor
  · sorry
  · intro h
    have : ℓ v - ℓ u = 1 := by sorry
    simp_all
    sorry


end GraphStructure

#synth PartialOrder  (DihedralGroup 0)

structure Degree where
  d0 : ℕ
  d1 : ℕ
  deriving DecidableEq, Repr

instance : Add Degree where
  add d e := ⟨d.d0 + e.d0, d.d1 + e.d1⟩

--度数的偏序关系
instance : PartialOrder Degree where
  le d1 d2 := d1.d0 ≤ d2.d0 ∧ d1.d1 ≤ d2.d1
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
    let k := i.natAbs
    if k ≥ 0 then
      -- 当 i=0 时为 s0 (1,0); 当 i=1 时为 s1 (0,1); 当 i=2 时为 s1s0s1 (1,2)
      if i = 0 then ⟨1, 0⟩ else ⟨i.natAbs - 1, i.natAbs⟩
    else
      -- 当 i=-1 时为 s0s1s0 (2,1); 当 i=-2 时为 s0s1s0s1s0 (3,2)
      ⟨i.natAbs + 1, i.natAbs⟩

def Root.toDegree (α : Root) : Degree :=⟨α.a, α.b⟩

instance : Zero Degree where
  zero := ⟨0, 0⟩

inductive HasChain : Vertex → Vertex → Degree → Prop where
  | refl (u : Vertex) : HasChain u u 0
  | step {u v w : Vertex} {d : Degree} {α : Root} :
      HasChain u v d → IsEdge v w α → HasChain u w (d + α.toDegree)

def CanReachWithin (u v : Vertex) (d : Degree) : Prop :=
  exists d', HasChain u v d' ∧ d' ≤ d

--Definition 2.4: 曲线邻域 Gamma_d(u)
def CurveNeighborhood (u : Vertex) (d : Degree) : Set Vertex :=
  { v | CanReachWithin u v d ∧
        ∀ v' : Vertex, CanReachWithin u v' d → v ≤ v' → v = v' }

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
