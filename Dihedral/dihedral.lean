import Mathlib
import Dihedral.Basic
import Dihedral.Length
import Dihedral.Degree

open DihedralGroup CoxeterSystem

example (n : ℕ) (i : ZMod n) : sr i * sr i = 1 := sr_mul_self i
--D_generated_by_sr0_sr1
example : (Subgroup.closure ({sr (0 : ZMod 0), sr (1 : ZMod 0)} : Set (DihedralGroup 0))) = ⊤ := by
  apply eq_top_iff.mpr
  intro g
  cases g with
  | r a => intro g; exact r_zpow_in_D (a : ℤ)
  | sr b => intro g; exact sri_in_D b

#check s0--sr0
#check s1--sr1
#check M
/-M is a CoxeterMatrix of D∞ with
  M = [1 0 ]
      [0 1 ]-/
#eval (M ⟨0, by decide⟩ ⟨1, by decide⟩)
#check B--Fin 2
#check cs--CoxeterSystem M D∞
--Basic.lean后面都在确认D∞是Coxeter群
--define the length ℓ(g) = the total nomber of s0 and s1 in the expression of g
example : ℓ s1 = 1 := by
  have : cs.simple 1 = s1 := rfl
  simpa [this] using length_simple cs (1 : Fin 2)
--用alternating list表示0和1交替出现
#eval alternating 0 5--[0,1,0,1,0]
#check listToGroup-- (l : List (Fin 2)) : D∞ :=(l.map f).prod
#eval listToGroup (alternating 0 5)
example (g : D∞) : ℓ g = (reducedWord g).length:= length_eq g

example (n : ℕ) (s : Fin 2) :
    listToGroup (alternating s (2 * n)) = if s = 0 then r (n : ℤ) else r (-(n : ℤ)) :=
  alternating_prod_even n s
#check ℓ (r 5)
#check length_r
#check length_sr

/-A positive root corresponding to D∞
structure Root where
    a : ℕ; b : ℕ
    sub_one : (a = b.succ) ∨ (b = a.succ)
 deriving DecidableEq
对degree的定义 ℕ * ℕ (可能先定义degree再在degree中根据条件选取root更好？
degree with add, scale, sub(分别计算), AddCommMonoid, PartialOrder
从D∞ → Degree
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
在更新了induction_on_alternating后可用alternating解决
-/
#check getDegree_sr
#check getDegree_r--if needed
#check induction_on_alternating
--以及在开始写的时候没找到关于mod2的比较好用的induction
#check n_mod_2_induction


#check lemma_2_1_1
#check lemma_2_1_3

#check lemma_2_1_4

/- moment graph G associated to D∞
定义顶点 (Vertices)。在 D∞ 的情况下，顶点是群元素
abbrev Vertex := D∞
--顶点 u 和 v 之间存在边，且度为 α。
def IsEdge (u v : Vertex) (α : Root) : Prop :=
  v = u * (s_α α)-/

-- notation:50 u " —[" α "]→ " v => IsEdge u v α
#check  edge_exists_iff

#check HasChain--HasChain u v d → IsEdge v w α → HasChain u w (d + α.toDegree)
#check HasIncreasingChain--w v HasChain∧ ℓ w > ℓ v
#check Lt--∃ d : Degree, HasIncreasingChain u v d ∧ u ≠ v. checkd partial order
#check lemma_2_3--D∞中的偏序

#check lemma_2_5_a
#check lemma_2_5_b
--下接 Neiborhood.lean
