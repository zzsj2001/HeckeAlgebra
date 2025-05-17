import Mathlib.GroupTheory.Coxeter.Inversion
import Mathlib.Algebra.Group.NatPowAssoc
import Init.Data.List.Lemmas

open List

namespace CoxeterSystem
noncomputable section

variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq

instance : DecidableEq W := Classical.typeDecidableEq W

def Reflection : Type := {t : W // IsReflection cs t}

def reflection_mem_leftInvSeq_count (l : List B) (t : cs.Reflection) : ℕ :=
  (cs.leftInvSeq l).count t.1

def reflection_mem_leftInvSeq_parity (l : List B) (t : cs.Reflection) : ZMod 2 :=
  (reflection_mem_leftInvSeq_count cs l t : ZMod 2)

def conj_of_reflection (t : cs.Reflection) (w : W) : cs.Reflection :=
  ⟨w * t.1 * w⁻¹, IsReflection.conj t.2 w⟩

def eta (i : B) (t : cs.Reflection) : ZMod 2 :=
  if (s i = t.1) then 1 else 0

lemma eta_eq_eta_of_simpleConj (i : B) (t : cs.Reflection) :
    cs.eta i t = cs.eta i (cs.conj_of_reflection t (s i)) := by
  simp [eta]
  rcases t with ⟨t, ht⟩
  have : s i = t ↔ s i * t = 1 := by
    constructor
    · intro h'
      rw [h']
      exact IsReflection.mul_self ht
    · intro h'
      apply (mul_left_inj t).mp
      simp [IsReflection.mul_self ht]
      exact h'

  by_cases h : s i = t
  · simp [this, h, conj_of_reflection]
  · simp [this, h, if_neg, conj_of_reflection]

def permutationMap (i : B) : cs.Reflection × ZMod 2 → cs.Reflection × ZMod 2 :=
  fun (t , z) => (cs.conj_of_reflection t (s i), z + cs.eta i t)

theorem permutationMap_orderTwo (i : B) : cs.permutationMap i ∘ cs.permutationMap i = id := by
  funext ⟨t, z⟩
  simp [permutationMap]
  constructor
  · simp[conj_of_reflection, mul_assoc]
  · rw [← cs.eta_eq_eta_of_simpleConj i t]
    ring_nf
    simp
    right
    rfl

lemma Odd.add_one : Odd n → Even (n + 1) := by
  intro h2
  by_contra h3
  simp at h3
  have contra1 : Even ((n + 1) - n) := by
    apply Nat.Odd.sub_odd h3 h2
  simp at contra1

lemma leftInvSeq_repeats : ∀ (k : ℕ) (h : k < M i j),
(cs.leftInvSeq (alternatingWord i j (2 * M i j)))[M i j + k]'(by simp[h]; linarith)   =
(cs.leftInvSeq (alternatingWord i j (2 * M i j)))[k]'(by simp[h]; linarith) := by
  intro k h'
  rw[getElem_leftInvSeq_alternatingWord cs i j (M i j) k]
  rw[getElem_leftInvSeq_alternatingWord cs i j (M i j) ((M i j)+k)]
  rw[cs.prod_alternatingWord_eq_mul_pow]
  rw[cs.prod_alternatingWord_eq_mul_pow]

  have h_odd : Odd (2 * k + 1) := by
    simp

  have h_odd' : Odd (2 * ((M i j) + k) + 1) := by
    simp

  simp[h_odd, h_odd']

  have two_gt_0 : 2 > 0 := by linarith
  have h_exp : (2 * k + 1) / 2 = k := by
    rw[add_comm]
    rw[Nat.add_mul_div_left 1 k two_gt_0]
    simp
  have h_exp' : (2 * ((M i j) + k) + 1) / 2 = (M i j) + k := by
    rw[add_comm]
    rw[Nat.add_mul_div_left 1 ((M i j)+k) two_gt_0]
    simp
  rw[h_exp, h_exp']
  rw[NatPowAssoc.npow_add]
  simp
  linarith
  linarith

lemma leftInvSeq_repeats' : ∀ (k : ℕ) (h : k < M i j),
(cs.leftInvSeq (alternatingWord i j (2 * M i j)))[M i j + k]'(by simp[h]; linarith) =
(cs.leftInvSeq (alternatingWord i j (2 * M i j)))[k]'(by simp[h]; linarith) := by
  intro k h'
  rw[← List.get_eq_getElem (cs.leftInvSeq (alternatingWord i j (2 * M i j))) ⟨M i j + k, by simp[h']; linarith⟩]
  rw[← List.get_eq_getElem (cs.leftInvSeq (alternatingWord i j (2 * M i j))) ⟨k, by simp[h']; linarith⟩]
  exact leftInvSeq_repeats cs k h'

lemma nReflectionOccurrences_even_braidWord (t : cs.Reflection) :
  Even (reflection_mem_leftInvSeq_count cs (alternatingWord i j (2 * M i j)) t) := by

  suffices (reflection_mem_leftInvSeq_count cs (alternatingWord i j (2 * M i j)) t) = 2 * List.count (t.1) (List.take (M.M i j) (cs.leftInvSeq (alternatingWord i j (M.M i j * 2)))) from by
    simp[this]

  simp[reflection_mem_leftInvSeq_count]
  suffices (cs.leftInvSeq (alternatingWord i j (2 * M i j))) = (List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j)))) ++ (List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j)))) from by
    rw[this]
    simp
    ring_nf

  have m_le_two_m : M i j ≤ 2 * M i j := by linarith
  have length_eq : (cs.leftInvSeq (alternatingWord i j (2 * (M i j)))).length =
  (List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j))) ++ (List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j))))).length := by
    simp[m_le_two_m]
    ring

  apply List.ext_getElem length_eq
  intro k hk hk'

  by_cases h : k < M i j
  · have : k < (List.take (M.M i j) (cs.leftInvSeq (alternatingWord i j (2 * M.M i j)))).length := by
      simp[h, m_le_two_m]

    rw[List.getElem_append_left this]
    rw[List.getElem_take']
    exact h
  · have h_k_le : k - M i j < M i j := by
      simp at hk
      apply Nat.sub_lt_left_of_lt_add
      simp at h
      exact h
      linarith
    have : (List.take (M.M i j) (cs.leftInvSeq (alternatingWord i j (2 * M.M i j)))).length ≤ k := by
      simp[h, m_le_two_m]
      linarith

    rw[List.getElem_append_right this]
    rw[List.getElem_take]
    simp[m_le_two_m]

    rw[← leftInvSeq_repeats' cs (k - M i j) h_k_le]

    suffices M.M i j + (k - M.M i j) = k from by
      simp[this]

    rw[← Nat.add_sub_assoc]
    simp
    linarith

lemma parityReflectionOccurrences_braidWord (t : cs.Reflection) :
  reflection_mem_leftInvSeq_parity cs (alternatingWord i j (2 * M i j)) t = 0 := by
  suffices Even (reflection_mem_leftInvSeq_count cs (alternatingWord i j (2 * M i j)) t) from by
    simp[this, reflection_mem_leftInvSeq_parity]
    apply ZMod.eq_zero_iff_even.mpr this
  exact nReflectionOccurrences_even_braidWord cs t

lemma alternatingWord_reverse : (alternatingWord i j (2 * p)).reverse = alternatingWord j i (2 * p) := by
  induction p with
  | zero =>
    simp[alternatingWord]
  | succ p h =>
    simp [mul_add, alternatingWord]
    rw[h]
    have h1 : j :: i :: alternatingWord j i (2 * p) = alternatingWord j i (2 * p + 1 + 1) := by
      rw[alternatingWord_succ']
      rw[alternatingWord_succ']
      simp
    simp[h1, alternatingWord]

instance instMul : Mul (cs.Reflection × ZMod 2 → cs.Reflection × ZMod 2) where
  mul := fun f g => f ∘ g

lemma mulDef (f g : cs.Reflection × ZMod 2 → cs.Reflection × ZMod 2) : f * g = f ∘ g := rfl

instance : Monoid (cs.Reflection × ZMod 2 → cs.Reflection × ZMod 2) where
  one := id
  mul := (instMul cs).mul
  one_mul := by
    intro f
    funext x
    suffices (id ∘ f) x = f x from by
      rw[← this]
      rfl
    simp
  mul_one := by
    intro f
    funext x
    suffices (f ∘ id) x = f x from by
      rw[← this]
      rfl
    simp
  mul_assoc := by
    intro f g h
    funext x
    repeat rw[mulDef]
    rfl

def permutationMap_ofList (l : List B) : cs.Reflection × ZMod 2 → cs.Reflection × ZMod 2 :=
  match l with
  | [] => id
  | a :: t => cs.permutationMap a * permutationMap_ofList t

lemma IsReflection.conj' (ht : cs.IsReflection t) (w : W) :
  cs.IsReflection (w⁻¹ * t * w) := by
  have : w = w⁻¹⁻¹ := by simp
  nth_rewrite 2 [this]
  apply IsReflection.conj ht w⁻¹

lemma permutationMap_ofList_mk_1 (l : List B) :
  (permutationMap_ofList cs l ⟨t,z⟩).1 = cs.conj_of_reflection t (π l) := by
  simp[conj_of_reflection]
  induction l with
  | nil =>
    simp[permutationMap_ofList, permutationMap, reflection_mem_leftInvSeq_count]
  | cons a l h =>
    calc (permutationMap_ofList cs (a :: l) (t, z)).1 = ((cs.permutationMap a * permutationMap_ofList cs l) (t, z)).1 := by simp[permutationMap_ofList]
      _ = (cs.permutationMap a (permutationMap_ofList cs l (t, z))).1 := by rfl

    simp[permutationMap, conj_of_reflection, h]
    simp[cs.wordProd_cons, mul_assoc]

lemma permutationMap_ofList_mk_2 (l : List B) :
 (permutationMap_ofList cs l ⟨t,z⟩).2 = z + reflection_mem_leftInvSeq_parity cs l.reverse t := by
  induction l with
  | nil =>
    simp[permutationMap_ofList, permutationMap, reflection_mem_leftInvSeq_parity, reflection_mem_leftInvSeq_count]
  | cons i l h =>
    rw[permutationMap_ofList, mulDef]
    simp[permutationMap, h]
    simp[reflection_mem_leftInvSeq_parity, reflection_mem_leftInvSeq_count]
    rw[← List.concat_eq_append]
    rw[leftInvSeq_concat]
    simp [List.count_singleton]

    suffices cs.eta i (permutationMap_ofList cs l (t, z)).1 = if (cs.wordProd l)⁻¹ * cs.simple i * cs.wordProd l = t.1 then 1 else 0 from by
      rw[this]
      simp[add_assoc]

    simp[eta, permutationMap_ofList_mk_1, conj_of_reflection]
    by_cases h' : (cs.wordProd l)⁻¹ * cs.simple i * cs.wordProd l = t.1
    · simp[h']
      rw[← h']
      simp[mul_assoc]
    · simp[h']
      by_contra h''
      rw[h''] at h'
      simp[mul_assoc] at h'

lemma permutationMap_ofList_mk (l : List B) (t : cs.Reflection) (z : ZMod 2) :
  (permutationMap_ofList cs l ⟨t,z⟩) = ⟨cs.conj_of_reflection t (π l),
   z + reflection_mem_leftInvSeq_parity cs l.reverse t⟩ := by
  rw[← permutationMap_ofList_mk_1, ← permutationMap_ofList_mk_2]

theorem permutationMap_isLiftable : M.IsLiftable (cs.permutationMap) := by
  intro i j

  have h (p : ℕ) : (cs.permutationMap i * cs.permutationMap j) ^ p = permutationMap_ofList cs (alternatingWord i j (2 * p)) := by
    induction p with
    | zero =>
      simp[permutationMap_ofList, permutationMap, permutationMap_orderTwo]
      rfl
    | succ p h =>
      simp[pow_succ']
      rw[h]
      have : 2 * (p + 1) = 2 * p + 1 + 1 := by ring
      rw[this]
      rw[alternatingWord_succ']
      rw [if_neg (Nat.not_even_bit1 p)]
      rw[permutationMap_ofList]

      rw[alternatingWord_succ']
      rw [if_pos (even_two_mul p)]
      rw[permutationMap_ofList]
      simp[mul_assoc]

  rw[h (M i j)]
  funext ⟨t, z⟩
  convert_to permutationMap_ofList cs (alternatingWord i j (2 * M.M i j)) (t, z) = ⟨t,z⟩

  simp[permutationMap_ofList_mk, conj_of_reflection]
  constructor
  · simp[cs.prod_alternatingWord_eq_mul_pow]
  · rw[alternatingWord_reverse]
    rw[M.symmetric]
    exact parityReflectionOccurrences_braidWord cs t

def permutationMap_lift : W →* cs.Reflection × ZMod 2 → cs.Reflection × ZMod 2 :=
  cs.lift ⟨cs.permutationMap, permutationMap_isLiftable cs⟩

theorem permutationMap_lift_mk_ofList (l : List B) (t : cs.Reflection) (z : ZMod 2) :
  permutationMap_lift cs (cs.wordProd l) ⟨t,z⟩ = permutationMap_ofList cs l ⟨t,z⟩ := by
  induction l with
  | nil =>
    simp[permutationMap_lift, cs.wordProd_nil, permutationMap_ofList]
    rfl
  | cons i l h =>
    rw[cs.wordProd_cons]
    rw[permutationMap_ofList]
    simp[mulDef]
    rw[← h]
    simp[permutationMap_lift]

theorem permutationMap_ext (l l' : List B) (t : cs.Reflection) (z : ZMod 2) (h : π l = π l') :
  permutationMap_ofList cs l ⟨t,z⟩ = permutationMap_ofList cs l' ⟨t,z⟩ := by
  rw[← permutationMap_lift_mk_ofList]
  rw[← permutationMap_lift_mk_ofList]
  simp[h]

def parityReflectionOccurrences_lift (w : W) (t : cs.Reflection) : ZMod 2 :=
  (permutationMap_lift cs w⁻¹ ⟨t,0⟩).2

theorem parityReflectionOccurrences_lift_mk (l : List B) (t : cs.Reflection) :
  parityReflectionOccurrences_lift cs (cs.wordProd l) t = reflection_mem_leftInvSeq_parity cs l t := by
  rw[parityReflectionOccurrences_lift]
  rw[← wordProd_reverse]
  rw[permutationMap_lift_mk_ofList cs l.reverse t 0]
  rw[permutationMap_ofList_mk cs l.reverse t 0]
  simp

theorem permutationMap_lift_mk (w : W) (t : cs.Reflection) (z : ZMod 2) :
  permutationMap_lift cs w ⟨t,z⟩ = ⟨⟨w * t.1 * w⁻¹, IsReflection.conj t.2 w⟩ , z + parityReflectionOccurrences_lift cs w⁻¹ t⟩ := by
  obtain ⟨l, _, rfl⟩ := cs.exists_reduced_word' w
  apply Prod.ext
  · simp[permutationMap_lift_mk_ofList, permutationMap_ofList_mk, conj_of_reflection]
  · simp[parityReflectionOccurrences_lift]
    rw[permutationMap_lift_mk_ofList cs l t 0]
    rw[permutationMap_lift_mk_ofList cs l t z]
    simp[permutationMap_ofList_mk]


theorem parityReflectionOccurrences_ext (l l' : List B) (t : cs.Reflection) (h : π l = π l') :
  reflection_mem_leftInvSeq_parity cs l t = reflection_mem_leftInvSeq_parity cs l' t := by

  calc
    reflection_mem_leftInvSeq_parity cs l t = parityReflectionOccurrences_lift cs (cs.wordProd l) t := by rw[parityReflectionOccurrences_lift_mk]
    _ = parityReflectionOccurrences_lift cs (cs.wordProd l') t := by rw[h]
    _ = reflection_mem_leftInvSeq_parity cs l' t := by rw[parityReflectionOccurrences_lift_mk]

lemma odd_iff_parity_eq_one (n : ℕ) : Odd n ↔ (n : ZMod 2) = 1 := by
  simp [ZMod.eq_one_iff_odd]

lemma gt_one_of_odd (n : ℕ) : Odd n → n > 0 := by
  intro h
  simp[Odd] at h
  rcases h with ⟨m, rfl⟩
  suffices m ≥ 0 from by linarith
  exact Nat.zero_le m

lemma isInLeftInvSeq_of_parityReflectionOccurrences_eq_one (l : List B) (t : cs.Reflection) (h : reflection_mem_leftInvSeq_parity cs l t = 1) :
  t.1 ∈ cs.leftInvSeq l := by
  simp [reflection_mem_leftInvSeq_parity] at h
  rw [← @odd_iff_parity_eq_one (reflection_mem_leftInvSeq_count cs l t)] at h

  apply gt_one_of_odd (reflection_mem_leftInvSeq_count cs l t) at h
  simp[reflection_mem_leftInvSeq_count] at h

  exact h

lemma isLeftInversion_of_parityReflectionOccurrences_eq_one (l : List B) (t : cs.Reflection) :
  reflection_mem_leftInvSeq_parity cs l t = 1 → cs.IsLeftInversion (cs.wordProd l) t.1 := by
  intro h

  rcases cs.exists_reduced_word' (π l) with ⟨u, u_reduced, hu⟩
  rw[hu]
  apply cs.isLeftInversion_of_mem_leftInvSeq u_reduced

  rw[cs.parityReflectionOccurrences_ext l u t hu] at h
  exact isInLeftInvSeq_of_parityReflectionOccurrences_eq_one cs u t h

lemma isLeftInversion_of_parityReflectionOccurrences_lift_eq_one (w : W) (t : cs.Reflection) :
  parityReflectionOccurrences_lift cs w t = 1 → cs.IsLeftInversion w t.1 := by
  intro h
  obtain ⟨l, _, rfl⟩ := cs.exists_reduced_word' w
  simp[parityReflectionOccurrences_lift_mk] at h
  apply isLeftInversion_of_parityReflectionOccurrences_eq_one cs l t h

lemma eraseIdx_of_mul_leftInvSeq (l : List B) (t : cs.Reflection) (h : t.1 ∈ cs.leftInvSeq l) :
  ∃ (k : Fin l.length), t.1 * π l = π (l.eraseIdx k) := by
    have : ∃ (k : Fin (cs.leftInvSeq l).length), (cs.leftInvSeq l).get k = t.1 := List.get_of_mem h
    rcases this with ⟨k, hk⟩
    use ⟨k, by rw[← length_leftInvSeq cs l] ; exact k.2⟩
    rw[← hk]
    rw[← getD_leftInvSeq_mul_wordProd cs l k]
    simp
    rw[← List.get?_eq_getElem?]
    rw [List.get?_eq_get k.2]
    simp

lemma permutationMap_lift_simple (p : B):
  permutationMap_lift cs (cs.simple p) = cs.permutationMap p := by
  simp[permutationMap_lift]

lemma permutationMap_lift_of_reflection (t : cs.Reflection) : ∀ (z : ZMod 2),
  permutationMap_lift cs t.1 (t, z) = ⟨t, z + 1⟩ := by
  rcases t with ⟨t, t_refl⟩
  rcases t_refl with ⟨w, p, rfl⟩
  obtain ⟨l, _, rfl⟩ := cs.wordProd_surjective w
  have : IsReflection cs (cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹) := IsReflection.conj (isReflection_simple cs p) (cs.wordProd l)

  induction l with
  | nil =>
    simp[permutationMap_lift, permutationMap_ofList, permutationMap, reflection_mem_leftInvSeq_count, conj_of_reflection, eta]
  | cons i l h =>
    intro z
    simp_rw[wordProd_cons cs i l]
    simp_rw[mul_inv_rev]
    simp_rw[inv_simple]
    simp[permutationMap_lift_simple, mulDef, ← mul_assoc]
    simp[permutationMap_lift_simple, mulDef] at h
    nth_rewrite 3 [permutationMap]
    simp[conj_of_reflection, ← mul_assoc]
    have : IsReflection cs (cs.simple i * cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ * cs.simple i) := by
      nth_rewrite 3 [← inv_simple]
      have : IsReflection cs (cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹) := IsReflection.conj (isReflection_simple cs p) (cs.wordProd l)
      convert_to IsReflection cs (cs.simple i * (cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹) * (cs.simple i)⁻¹)
      simp[inv_simple, mul_assoc]
      exact IsReflection.conj this (s i)
    rw[h (isReflection_simple cs p) (z + cs.eta i ⟨cs.simple i * cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ * cs.simple i, this⟩)]
    simp[permutationMap, conj_of_reflection]
    constructor
    · simp[mul_assoc]
    · simp[eta, add_assoc]
      by_cases h': cs.simple i * cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ = 1
      · simp[h']
        have : cs.simple i = cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ := by
          apply (mul_right_inj (cs.simple i)).mpr at h'
          simp only[mul_assoc, mul_one] at h'
          rw[← h']
          simp[mul_assoc]
        simp[this]
        simp[ZMod]
      · simp[h']
        by_contra h''
        rw[h''] at h'
        simp[mul_assoc] at h'

lemma isLeftInversion_iff_parityReflectionOccurrences_eq_one (l : List B) (t : cs.Reflection) :
  cs.IsLeftInversion (cs.wordProd l) t.1 ↔ reflection_mem_leftInvSeq_parity cs l t = 1 := by
  constructor
  · intro h
    by_contra h'
    have h'' : reflection_mem_leftInvSeq_parity cs l t = 0 := by
      simp [reflection_mem_leftInvSeq_parity]
      rw [ZMod.eq_zero_iff_even]
      simp[reflection_mem_leftInvSeq_parity] at h'
      rw[ZMod.eq_one_iff_odd] at h'
      exact Nat.not_odd_iff_even.mp h'

    suffices cs.IsLeftInversion (t.1 * π l) t.1 from by
      simp[IsLeftInversion] at this
      rw[← mul_assoc] at this
      rcases this with ⟨_, ht⟩
      rw[IsReflection.mul_self t.2] at ht
      simp at ht
      simp[IsLeftInversion] at h
      linarith

    suffices permutationMap_lift cs (t.1 * π l)⁻¹ ⟨t, 0⟩ = ⟨cs.conj_of_reflection t (π l)⁻¹, 1⟩ from by
      apply isLeftInversion_of_parityReflectionOccurrences_lift_eq_one cs (t.1 * π l) t
      rw[permutationMap_lift_mk cs (t.1 * π l)⁻¹ t 0] at this
      simp at this
      simp[this.2]

    calc
      permutationMap_lift cs (t.1 * π l)⁻¹ ⟨t, 0⟩ = permutationMap_lift cs (π l)⁻¹ (permutationMap_lift cs t.1 ⟨t, 0⟩) := by
          simp[IsReflection.inv t.2]
          rfl
      _ = permutationMap_lift cs (π l)⁻¹ ⟨t, 1⟩ := by
          rw[permutationMap_lift_of_reflection cs t 0]
          simp[permutationMap_lift_mk]
      _ = ⟨cs.conj_of_reflection t (π l)⁻¹, 1 + parityReflectionOccurrences_lift cs (π l) t⟩ := by
        simp[permutationMap_lift_mk, conj_of_reflection]
      _ = (cs.conj_of_reflection t (cs.wordProd l)⁻¹, 1) := by
        simp
        simp[parityReflectionOccurrences_lift_mk, h'']

  · exact isLeftInversion_of_parityReflectionOccurrences_eq_one cs l t

theorem strongExchangeProperty (l : List B) (t : cs.Reflection)
    (h' : cs.IsLeftInversion (cs.wordProd l) t.1) :
    ∃ (k : Fin l.length), t.1 * π l = π (l.eraseIdx k) := by
  suffices t.1 ∈ cs.leftInvSeq l from eraseIdx_of_mul_leftInvSeq cs l t this
  rw [isLeftInversion_iff_parityReflectionOccurrences_eq_one cs l t] at h'
  exact isInLeftInvSeq_of_parityReflectionOccurrences_eq_one cs l t h'

lemma List.eraseIdx_reverse {α} (l : List α) (k : Fin l.length) :
    l.reverse.eraseIdx k = (l.eraseIdx (l.length - 1 - k)).reverse := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h2 : k < l.length
    · simp only [reverse_cons, length_cons, add_tsub_cancel_right]
      rw [show l.length - k = l.length - 1 - k + 1 by omega, List.eraseIdx_cons_succ]
      simp only [length_cons, reverse_cons,
        eraseIdx_append_of_lt_length (length_reverse l ▸ h2), ←ih ⟨k, h2⟩]
    · replace h1 : k = l.length := by
        have := k.2; simp only [length_cons] at this; omega
      have h2 : l.length = (l.reverse ++ [a]).length - 1 := by simp
      simp [h1]
      simp only [h2, List.eraseIdx_length_sub_one]
      simp

theorem strongExchangeProperty' (l : List B) (t : cs.Reflection)
    (h' : cs.IsRightInversion (cs.wordProd l) t.1) :
    ∃ (k : Fin l.length), π l * t.1 = π (l.eraseIdx k) := by
  rw [←cs.isLeftInversion_inv_iff, ←wordProd_reverse] at h'
  obtain ⟨k, hk⟩ := strongExchangeProperty cs l.reverse t h'
  rw [wordProd_reverse, ←IsReflection.inv t.2, ←mul_inv_rev] at hk
  rw [List.eraseIdx_reverse l ⟨k.1, by rw [←length_reverse l]; exact k.2⟩] at hk
  simp only [wordProd_reverse] at hk
  use ⟨l.length - 1 - k, by rw [←length_reverse l]; omega⟩
  exact eq_of_mul_inv_eq_one (mul_eq_one_iff_inv_eq.2 hk)

lemma StrongExchange' {l : List B} {t : W} (ht : cs.IsLeftInversion (π l) t) :
    t ∈ lis l := by
  obtain ⟨k, hk⟩ := strongExchangeProperty cs l ⟨t, ht.1⟩ ht
  simp [←cs.getD_leftInvSeq_mul_wordProd] at hk
  simp only [hk, getElem_mem]

lemma StrongExchange'' {l : List B} {t : W} (ht : cs.IsRightInversion (π l) t) :
    t ∈ ris l := by
  obtain ⟨k, hk⟩ := strongExchangeProperty' cs l ⟨t, ht.1⟩ ht
  simp [←cs.wordProd_mul_getD_rightInvSeq] at hk
  simp only [hk, getElem_mem]

@[simp]
lemma singletonIsReduced (h : l.length = 1) : cs.IsReduced l := by
  simp [IsReduced, h, length_eq_one_iff,List.length_eq_one]
  have := List.length_eq_one.1 h
  obtain ⟨a, ha⟩ := this
  exact ⟨a, by rw [ha]; simp⟩

open Classical in
lemma exists_drop_reduced_of_not_reduced {l : List B} (h : ¬IsReduced cs l) :
    ∃ i, ¬ cs.IsReduced (l.drop i) ∧ (∀ j, i < j → cs.IsReduced (l.drop j)) := by
  have h1 : ∃ i, ¬ cs.IsReduced (drop (l.length - i) l) := ⟨l.length, by simpa⟩
  use l.length - Nat.find h1
  exact ⟨Nat.find_spec h1, by
    intro j hj
    by_cases jge : l.length ≤ j
    · simp [drop_eq_nil_of_le jge, IsReduced]
    · have h2 : l.length - j < Nat.find h1 := by omega
      convert Nat.find_min h1 h2
      simp [show l.length - (l.length - j) = j by omega] ⟩

private lemma DeletionProperty_aux {l : List B} (h : ¬IsReduced cs l) :
    ∃ l', l' <+ l ∧ π l' = π l ∧ l'.length + 2 = l.length := by
  obtain ⟨i, hi⟩ := exists_drop_reduced_of_not_reduced cs h
  have ilt : i < l.length := by
    by_contra!
    simp [ List.drop_eq_nil_of_le this] at hi
    exact hi.1 (by simp [IsReduced])
  rw [←l.getElem_cons_drop _ ilt] at hi
  have h1 : ℓ (π (l[i] :: drop (i + 1) l)) < ℓ (π (drop (i + 1) l)) := by
    simp only [wordProd_cons]
    rcases cs.length_simple_mul (π (drop (i+1) l)) l[i] with hlt | hgt
    · simp [←wordProd_cons] at hlt
      rw [hi.2 (i+1) (by omega), List.length_drop] at hlt
      rw [show l.length - (i + 1) + 1 = l.length - i by omega, ←length_drop] at hlt
      simp at hi
      exact False.elim <| hi.1 hlt
    · omega
  replace h1 : cs.IsLeftInversion (π (drop (i+1) l)) (s l[i]) := by
    simp only [wordProd_cons] at h1
    exact ⟨cs.isReflection_simple l[i], h1⟩
  obtain ⟨k, hk⟩ := cs.strongExchangeProperty _ ⟨s l[i], cs.isReflection_simple l[i]⟩ h1
  simp [←wordProd_cons] at hk
  use take i l ++ (drop (i+1) l).eraseIdx k
  split_ands
  · conv =>
      enter [2]; rw [←List.take_append_drop i l]
    simp only [append_sublist_append_left, ←l.getElem_cons_drop _ ilt]
    exact (eraseIdx_sublist _ k).trans (sublist_cons_self l[i] _)
  · rw [wordProd_append, ←hk, ←wordProd_append, take_append_drop]
  · have h2 : k < l.length - (i + 1) := by convert k.2; simp
    have h3 : i < l.length - 1 := by
      by_contra!
      have : i = l.length - 1 := by omega
      simp [this, List.drop_length_sub_one (show l ≠ [] from List.ne_nil_of_length_pos (by omega))] at hi
    simp [length_append, length_eraseIdx, h2, Nat.min_def, le_of_lt ilt]
    omega

/-- If l is not a reduced word of w but a experssion, there must exist a subword of l which
  is reduced word of w. -/
lemma DeletionProperty {l : List B} (h : ¬IsReduced cs l) :
  ∃ l' : List B, l' <+ l ∧ π l' = π l ∧ IsReduced cs l' := by
  generalize hl : l.length = n
  revert l h
  induction' n using Nat.twoStepInduction with n h1 _ <;> intro l h llsucc
  · have : l = [] := List.eq_nil_of_length_eq_zero llsucc
    rw [this] at h
    exact (h <| (by simp [IsReduced])).elim
  · exact (h (by simp [llsucc])).elim
  · obtain ⟨ll, hll⟩ := DeletionProperty_aux cs h
    have lll : ll.length = n := by linarith
    by_cases hh : IsReduced cs ll
    · exact ⟨ll, ⟨hll.1, ⟨hll.2.1, hh⟩ ⟩⟩
    · obtain ⟨ll', hll'⟩ := h1 hh lll
      exact ⟨ll', ⟨hll'.1.trans hll.1, ⟨hll'.2.1.trans hll.2.1, hll'.2.2⟩ ⟩ ⟩
