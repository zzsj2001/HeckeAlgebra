import Mathlib

variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {l : List B} {t : W}

open CoxeterSystem Multiplicative List

open Classical (choose choose_spec)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq

protected abbrev CoxeterSystem.Group (_ : CoxeterSystem M W) := W

section

abbrev Coxeter.wf : WellFoundedRelation cs.Group := measure cs.length

@[simp]
lemma rel_iff_length_lt (u v : cs.Group) : (Coxeter.wf cs).rel u v ↔ ℓ u < ℓ v := by rfl

theorem CoxeterSystem.induction {p : cs.Group → Prop} {w : cs.Group} (p1 : p 1)
    (pind : ∀ w, p w → ∀ i : B, ℓ w < ℓ (s i * w) → p (s i * w)) : p w := by
  apply WellFounded.induction (Coxeter.wf cs).wf
  simp only [rel_iff_length_lt]
  intro w hy
  by_cases w1 : w = 1
  · simpa [w1]
  · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one w1
    specialize hy (s i * w) hi
    convert pind (s i * w) hy i (by simpa)
    simp

theorem CoxeterSystem.induction' {p : cs.Group → Prop} {w : cs.Group} (p1 : p 1)
    (pind : ∀ w, p w → ∀ i : B, ℓ w < ℓ (w * s i) → p (w * s i)) : p w := by
  apply WellFounded.induction (Coxeter.wf cs).wf
  simp only [rel_iff_length_lt]
  intro w hy
  by_cases w1 : w = 1
  · simpa [w1]
  · obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one w1
    specialize hy (w * s i) hi
    convert pind (w * s i) hy i (by simpa)
    simp

lemma choose_unique_eq {α} {p : α → Prop} {a : α} (he : ∃ a : α, p a)
    (uniq : ∀ b : α, p b → b = a) : choose he = a := uniq _ (choose_spec he)

lemma cons_reduced {l : List B} {i : B} (hl : cs.IsReduced l) (h : ℓ (π l) < ℓ (s i * π l)) :
    cs.IsReduced ([i] ++ l) := by
  simp [CoxeterSystem.IsReduced]
  rcases cs.length_simple_mul (π l) i with hlt | hgt
  · rwa [←hl]
  · omega

lemma concat_reduced {l : List B} {i : B} (hl : cs.IsReduced l) (h : ℓ (π l) < ℓ (π l * s i)) :
    cs.IsReduced (l.concat i) := by
  simp [CoxeterSystem.IsReduced]
  rcases cs.length_mul_simple (π l) i with hlt | hgt
  · rw [←hl]; simpa [wordProd_append]
  · omega

lemma CoxeterSystem.rightInvSeq_cons (i : B) (ω : List B) :
    ris (i :: ω) = ((π ω)⁻¹ * s i * (π ω)) :: ris ω := by
  rw [←reverse_reverse (i :: ω), rightInvSeq_reverse,
    show (i :: ω).reverse = ω.reverse.concat i by simp]
  simp only [cs.leftInvSeq_concat ω.reverse i]
  simp [←cs.rightInvSeq_reverse]

end

noncomputable section permutationRepr

variable [DecidableEq cs.Group]

abbrev reflSet := {w : cs.Group // cs.IsReflection w}

def eta_simple (i : B) (t : reflSet cs) : Multiplicative (ZMod 2) :=
  ite (s i = t) (ofAdd 1) (ofAdd 0)

def pi_simple (i : B) : reflSet cs × Multiplicative (ZMod 2) → reflSet cs × Multiplicative (ZMod 2) :=
  fun (t, ε) => (⟨s i * t * s i, by convert IsReflection.conj t.2 (s i); simp⟩,
  ε * eta_simple cs i t)

lemma pi_simple_involutive (i : B) : (pi_simple cs i).Involutive := by
  intro x
  simp [pi_simple]
  apply Prod.ext (by simp [←Subtype.val_inj]; group; simp)
  simp [←Subtype.val_inj, eta_simple]
  have h1 : x.1.1 * x.1 = 1 := IsReflection.mul_self x.1.2
  by_cases heq : s i = x.1 <;> simp [heq, h1]
  · exact mul_eq_of_eq_mul_inv rfl
  · contrapose! heq
    simpa [←h1] using heq

lemma pi_simple_bij (i : B) : (pi_simple cs i).Bijective := by
  apply Function.Involutive.bijective
  apply pi_simple_involutive

noncomputable def Pi_simple (i : B) :
    reflSet cs × Multiplicative (ZMod 2) ≃ reflSet cs × Multiplicative (ZMod 2) :=
  Equiv.ofBijective _ (pi_simple_bij cs i)

lemma Pi.IsLiftable : M.IsLiftable (Pi_simple cs) := by
  intro i j
  ext x <;> push_cast <;>

  sorry

def Pi := cs.lift ⟨Pi_simple cs, Pi.IsLiftable cs⟩

def eta_aux (l : List B) (t : reflSet cs) : Multiplicative (ZMod 2) :=
  ofAdd <| List.count t.1 (lis l) • 1

def eta (w : cs.Group) (t : reflSet cs) : Multiplicative (ZMod 2) :=
  let l := choose <| cs.exists_reduced_word w
  eta_aux cs l t

lemma eta_apply_one {t : reflSet cs} : eta cs 1 t = ofAdd 0 := by
  have : eta_aux cs [] t = 1 := by simp [eta_aux]
  simp [eta]
  convert this
  apply choose_unique_eq _ (by simp)

lemma eta_refl_apply_self (t : reflSet cs) : eta cs t.1 t = ofAdd 1 := by

  sorry

lemma eta_well_defined {l: List B} {w : cs.Group} (h1 : cs.IsReduced l) (h : w = π l)
    (t : reflSet cs) : eta cs w t = eta_aux cs l t := sorry

lemma Pi_apply (w : cs.Group) (t : reflSet cs) (ε : Multiplicative (ZMod 2)) :
    Pi cs w (t, ε) = (⟨w * t * w⁻¹, IsReflection.conj t.2 w⟩, ε * eta cs w⁻¹ t) := by
  apply CoxeterSystem.induction cs (p := fun w =>
    Pi cs w (t, ε) = (⟨w * t * w⁻¹, IsReflection.conj t.2 w⟩, ε * eta cs w⁻¹ t))
  · simp [eta_apply_one]
  · intro w ih i hi
    simp [map_mul,ih]
    simp [Pi, Pi_simple, pi_simple]
    exact ⟨by group, by
      simp [mul_assoc]
      have hl := choose_spec <| cs.exists_reduced_word w
      set l := choose <| cs.exists_reduced_word w
      have pi_concat : π (i :: l) = s i * w  := by simpa [wordProd_cons] using hl.2.symm
      rw [←cs.inv_simple i, ←mul_inv_rev, ←pi_concat, hl.2]
      have l_red : cs.IsReduced l := by simp [CoxeterSystem.IsReduced, hl]
      have concat_red : cs.IsReduced (i :: l) :=
        cons_reduced cs l_red (by simpa [hl.2] using hi)
      rw [eta_well_defined cs (IsReduced.reverse l_red) (cs.wordProd_reverse l).symm]
      rw [eta_well_defined cs (IsReduced.reverse concat_red) (cs.wordProd_reverse (i :: l)).symm]
      simp only [eta_aux, leftInvSeq_reverse, count_reverse]
      simp [rightInvSeq_cons, count_cons]
      simp [eta_simple]
      split <;> rename_i h1
      · simp [h1]
      · replace h1 : ¬(π l)⁻¹ * cs.simple i * π l = t := by
          contrapose! h1; simp [←h1]
        simp [h1] ⟩

lemma Pi_refl_apply_self (t : reflSet cs) (ε : Multiplicative (ZMod 2)) :
    Pi cs t (t, ε) = (t, ε * ofAdd 1) := by
  simp [Pi_apply]
  simp only [IsReflection.inv t.2, eta_refl_apply_self]

end permutationRepr
