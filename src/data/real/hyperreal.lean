/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir
Construction of the hyperreal numbers as an ultraproduct of real sequences.
-/

import data.real.basic algebra.field order.filter.filter_product analysis.specific_limits
local attribute [instance] classical.prop_decidable

open filter filter.filter_product

/-- Hyperreal numbers on the ultrafilter extending the cofinite filter -/
@[reducible] def hyperreal := filter.filterprod ℝ (@hyperfilter ℕ)

namespace hyperreal

notation `ℝ*` := hyperreal

private def U := is_ultrafilter_hyperfilter set.infinite_univ_nat
noncomputable instance : discrete_linear_ordered_field ℝ* := filter_product.discrete_linear_ordered_field U

/-- A sample infinitesimal hyperreal-/
noncomputable def epsilon : ℝ* := of_seq (λ n, n⁻¹)

/-- A sample infinite hyperreal-/
noncomputable def omega : ℝ* := of_seq (λ n, n)

local notation `ε` := epsilon
local notation `ω` := omega

lemma epsilon_eq_inv_omega : ε = ω⁻¹ := rfl

lemma inv_epsilon_eq_omega : ε⁻¹ = ω := @inv_inv' _ _ ω

lemma epsilon_pos : 0 < ε :=
have h0' : {n : ℕ | ¬ n > 0} = {0} := 
by simp only [not_lt, (set.set_of_eq_eq_singleton).symm]; ext; exact nat.le_zero_iff,
begin
  rw lt_def U,
  show {i : ℕ | (0 : ℝ) < i⁻¹} ∈ hyperfilter.sets,
  simp only [inv_pos', nat.cast_pos],
  exact mem_hyperfilter_of_finite_compl set.infinite_univ_nat (by convert set.finite_singleton _),
end

lemma epsilon_ne_zero : ε ≠ 0 := ne_of_gt epsilon_pos

lemma omega_pos : 0 < ω := by rw ←inv_epsilon_eq_omega; exact inv_pos epsilon_pos

lemma omega_ne_zero : ω ≠ 0 := ne_of_gt omega_pos

theorem epsilon_mul_omega : ε * ω = 1 := @inv_mul_cancel _ _ ω omega_ne_zero

lemma lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : tendsto f at_top (nhds 0)) :
  ∀ {r : ℝ}, r > 0 → of_seq f < (r : ℝ*) :=
begin
  simp only [metric.tendsto_at_top, dist_zero_right, norm, lt_def U] at hf ⊢,
  intros r hr, cases hf r hr with N hf',
  have hs : -{i : ℕ | f i < r} ⊆ {i : ℕ | i ≤ N} :=
    λ i hi1, le_of_lt (by simp only [lt_iff_not_ge];
    exact λ hi2, hi1 (lt_of_le_of_lt (le_abs_self _) (hf' i hi2)) : i < N),
  exact mem_hyperfilter_of_finite_compl set.infinite_univ_nat 
    (set.finite_subset (set.finite_le_nat N) hs)
end

lemma neg_lt_of_tendsto_zero_of_neg {f : ℕ → ℝ} (hf : tendsto f at_top (nhds 0)) :
  ∀ {r : ℝ}, r > 0 → (-r : ℝ*) < of_seq f :=
λ r hr, have hg : _ := tendsto_neg hf,
neg_lt_of_neg_lt (by rw [neg_zero] at hg; exact lt_of_tendsto_zero_of_pos hg hr)

lemma gt_of_tendsto_zero_of_neg {f : ℕ → ℝ} (hf : tendsto f at_top (nhds 0)) :
  ∀ {r : ℝ}, r < 0 → (r : ℝ*) < of_seq f :=
λ r hr, have hn : (r : ℝ*) = -↑(-r) := by rw [←of_eq_coe, ←of_eq_coe, of_neg, neg_neg],
by rw hn; exact neg_lt_of_tendsto_zero_of_neg hf (neg_pos.mpr hr)

lemma epsilon_lt_pos (x : ℝ) : x > 0 → ε < of x := lt_of_tendsto_zero_of_pos tendsto_inverse_at_top_nhds_0_nat

/-- Standard part predicate -/
def is_st (x : ℝ*) (r : ℝ) := ∀ δ : ℝ, δ > 0 → (r - δ : ℝ*) < x ∧ x < r + δ

/-- Standard part function: like a "floor" to ℝ instead of ℤ -/
noncomputable def st : ℝ* → ℝ := 
λ x, dite (∃ r, is_st x r) (classical.some) (λ h, 0)

/-- A hyperreal number is infinitesimal if its standard part is 0 -/
def infinitesimal (x : ℝ*) := is_st x 0

/-- A hyperreal number is positive infinite if it is larger than all real numbers -/
def infinite_pos (x : ℝ*) := ∀ r : ℝ, x > r

/-- A hyperreal number is negative infinite if it is smaller than all real numbers -/
def infinite_neg (x : ℝ*) := ∀ r : ℝ, x < r

/-- A hyperreal number is infinite if it is larger than all real numbers or smaller than all real numbers -/
def infinite (x : ℝ*) := infinite_pos x ∨ infinite_neg x

-- SOME FACTS ABOUT ST THAT MAY (?) TAKE INFINITESIMAL MACHINERY TO PROVE

private lemma is_st_unique_1 (x : ℝ*) (r s : ℝ) (hr : is_st x r) (hs : is_st x s) (hrs : r < s) : false :=
have hrs' : _ := half_pos $ sub_pos_of_lt hrs,
have hr' : _ := (hr _ hrs').2,
have hs' : _ := (hs _ hrs').1,
have h : s + -((s - r) / 2) = r + (s - r) / 2 := by linarith,
by simp only [(of_eq_coe _).symm, sub_eq_add_neg (of s), (of_neg _).symm, (of_add _ _).symm, h] at hr' hs';
  exact not_lt_of_lt hs' hr'

theorem is_st_unique {x : ℝ*} {r s : ℝ} (hr : is_st x r) (hs : is_st x s) : r = s :=
begin
  rcases lt_trichotomy r s with h | h | h,
  { exact false.elim (is_st_unique_1 x r s hr hs h) },
  { exact h },
  { exact false.elim (is_st_unique_1 x s r hs hr h) }
end

lemma st_of_is_st {x : ℝ*} {r : ℝ} (hxr : is_st x r): st x = r :=
begin
  unfold st, split_ifs,
  { exact is_st_unique (classical.some_spec h) hxr },
  { exact false.elim (h ⟨r, hxr⟩) }
end

lemma is_st_of_st {x : ℝ*} (hx : st x ≠ 0) : is_st x (st x) := 
begin
  unfold st, split_ifs,
  { exact classical.some_spec h },
  { exact false.elim (hx (by unfold st; split_ifs; refl)) }
end

lemma is_st_of_st' {x : ℝ*} : ¬ infinite x → is_st x (st x) := sorry

lemma is_st_self (r : ℝ) : is_st r r := sorry

lemma st_self (r : ℝ) : st r = r := st_of_is_st (is_st_self  r)

lemma is_st_of (r : ℝ) : is_st (of r) r := sorry

lemma st_of (r : ℝ) : st (of r) = r := sorry

-- THIS ISN'T RIGHT, BUT I'LL KEEP IT HERE FOR THE TIME BEING
-- Perhaps f needs to be continuous?
/-lemma is_st_function {f : ℝ → ℝ} {x : ℝ*} {r : ℝ} : is_st x r → is_st ((lift f) x) (f r) := sorry

lemma is_st_function₂ {f : ℝ → ℝ → ℝ} {x y : ℝ*} {r s : ℝ} : is_st x r → is_st y s → is_st ((lift₂ f) x y) (f r s) := sorry

lemma st_function {f : ℝ → ℝ} (x : ℝ*) : (st ((lift f) x) : ℝ*) = (lift f) (st x : ℝ*) := sorry

lemma st_function₂ {f : ℝ → ℝ → ℝ} (x y : ℝ*) : (st ((lift₂ f) x y) : ℝ*) = (lift₂ f) (st x : ℝ*) (st y : ℝ*) := sorry-/

lemma is_st_add {x y : ℝ*} {r s : ℝ} : is_st x r → is_st y s → is_st (x + y) (r + s) := sorry

lemma st_add (x y : ℝ*) : st (x + y) = st x + st y := sorry

lemma is_st_neg {x : ℝ*} {r : ℝ} : is_st x r → is_st (-x) (-r) := sorry

lemma st_neg (x : ℝ*) : st x = - st x := sorry

lemma is_st_mul {x y : ℝ*} {r s : ℝ} : is_st x r → is_st y s → is_st (x * y) (r * s) := sorry

lemma st_mul (x y : ℝ*) : st (x * y) = (st x) * (st y) := sorry

lemma is_st_inv {x : ℝ*} {r : ℝ} {hi : ¬ infinitesimal x} : is_st x r → is_st x⁻¹ r⁻¹ := sorry

lemma st_inv (x : ℝ*) : st x⁻¹ = (st x)⁻¹ := sorry

lemma eq_of_is_st_real {r s : ℝ} : is_st r s → r = s := sorry

lemma is_st_real_iff_eq {r s : ℝ} : is_st r s ↔ r = s := ⟨eq_of_is_st_real, λ hrs, by rw [hrs]; exact is_st_self s⟩

/- (st x < st y) → (x < y) → (x ≤ y) → (st x ≤ st y) -/

lemma st_le_of_lt {x y : ℝ*} : x ≤ y → st x ≤ st y := sorry

lemma lt_of_st_lt {x y : ℝ*} : st x < st y → x < y := sorry

theorem not_infinite_of_exist_st {x : ℝ*} : (∃ r : ℝ, is_st x r) → ¬ infinite x := 
λ he hi, Exists.dcases_on he $ λ r hr, hi.elim 
   (λ hip, not_lt_of_lt (hr 2 two_pos).2 (hip $ r + 2))
   (λ hin, not_lt_of_lt (hr 2 two_pos).1 (hin $ r - 2))

theorem exist_st_of_not_infinite {x : ℝ*} (hni : ¬ infinite x) : ∃ r : ℝ, is_st x r := 
have hnile : _ := not_forall.mp (not_or_distrib.mp hni).1, 
have hnige : _ := not_forall.mp (not_or_distrib.mp hni).2,
let S : set ℝ := {y : ℝ | ↑y < x} in
let R : _ := real.Sup S in
Exists.dcases_on hnile (Exists.dcases_on hnige (λ r₁ hr₁ r₂ hr₂,
have HR₁ : ∃ y : ℝ, y ∈ S := ⟨r₁ - 1, lt_of_lt_of_le (of_lt_of_lt U (sub_one_lt _)) (not_lt.mp hr₁)⟩,
have HR₂ : ∃ z : ℝ, ∀ y ∈ S, y ≤ z := ⟨r₂, λ y hy, le_of_lt ((of_lt U).mpr (lt_of_lt_of_le hy (not_lt.mp hr₂)))⟩,
⟨R, λ δ hδ, 
  ⟨lt_of_not_ge' (λ c,
    have hc : ∀ y ∈ S, y ≤ R - δ := λ y hy, (of_le U.1).mpr (le_of_lt (lt_of_lt_of_le hy c)),
    not_lt_of_le ((real.Sup_le _ HR₁ HR₂).mpr hc) (sub_lt_self R hδ)), 
   lt_of_not_ge' (λ c,
    have hc : ↑(R + δ / 2) < x := lt_of_lt_of_le (add_lt_add_left (of_lt_of_lt U (half_lt_self hδ)) ↑R) c,
    not_lt_of_le (real.le_Sup _ HR₂ hc) ((lt_add_iff_pos_right _).mpr (half_pos hδ)))⟩⟩))

theorem exist_st_iff_not_infinite {x : ℝ*} : (∃ r : ℝ, is_st x r) ↔ ¬ infinite x := 
⟨ not_infinite_of_exist_st, exist_st_of_not_infinite ⟩

-- BASIC LEMMAS ABOUT INFINITESIMAL

theorem infinitesimal_def {x : ℝ*} : infinitesimal x ↔ (∀ r : ℝ, r > 0 → -r < x ∧ x < r) := sorry

theorem lt_of_pos_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ r : ℝ, r > 0 → x < r := sorry

theorem lt_neg_of_pos_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ r : ℝ, r > 0 → x < -r := sorry

theorem gt_of_neg_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ r : ℝ, r < 0 → x > r := sorry

theorem lt_and_gt_neg_of_pos_iff_infinitesimal {x : ℝ*} : infinitesimal x ↔ ∀ r : ℝ, r > 0 → x < r ∧ x > -r := sorry

theorem lt_of_pos_and_gt_of_neg_iff_infinitesimal {x : ℝ*} : infinitesimal x ↔ ∀ r : ℝ, ((r > 0 → x < r) ∧ (r < 0 → x > r)) := sorry

theorem abs_lt_real_iff_infinitesimal {x : ℝ*} : infinitesimal x ↔ ∀ r : ℝ, abs x < abs r := sorry

lemma infinitesimal_zero : infinitesimal 0 := is_st_self 0

lemma zero_of_infinitesimal_real {r : ℝ} : infinitesimal r → r = 0 := sorry

lemma zero_iff_infinitesimal_real {r : ℝ} : infinitesimal r ↔ r = 0 := 
⟨zero_of_infinitesimal_real, λ hr, by rw hr; exact infinitesimal_zero⟩

lemma infinitesimal_add (x y : ℝ) : infinitesimal x → infinitesimal y → infinitesimal (x + y) := sorry

lemma infinitesimal_neg (x : ℝ) : infinitesimal x → infinitesimal (-x) := sorry

lemma infinitesimal_mul (x y : ℝ) : infinitesimal x → infinitesimal y → infinitesimal (x * y) := sorry

theorem infinitesimal_of_tendsto_zero {f : ℕ → ℝ} (hf : tendsto f at_top (nhds 0)) :
  infinitesimal (of_seq f) :=
λ d hd, by rw [←of_eq_coe, ←of_eq_coe, sub_eq_add_neg, ←of_neg, ←of_add, ←of_add, zero_add, zero_add, of_eq_coe, of_eq_coe];
exact ⟨neg_lt_of_tendsto_zero_of_neg hf hd, lt_of_tendsto_zero_of_pos hf hd⟩

theorem infinitesimal_epsilon : infinitesimal ε := infinitesimal_of_tendsto_zero tendsto_inverse_at_top_nhds_0_nat

lemma not_real_of_infinitesimal_ne_zero (x : ℝ*) : infinitesimal x → x ≠ 0 → ∀ r : ℝ, x ≠ of r := sorry

-- BASIC LEMMAS ABOUT INFINITE

lemma infinite_pos_def {x : ℝ*} : infinite_pos x ↔ ∀ r : ℝ, x > r := by rw iff_eq_eq; refl

lemma infinite_neg_def {x : ℝ*} : infinite_neg x ↔ ∀ r : ℝ, x < r := by rw iff_eq_eq; refl

lemma infinite_iff_infinite_abs {x : ℝ*} : infinite x ↔ infinite (abs x) := sorry

lemma infinite_abs_iff_infinite_pos_abs {x : ℝ*} : infinite (abs x) ↔ infinite_pos (abs x) := sorry

lemma infinite_iff_infinite_pos_abs {x : ℝ*} : infinite x ↔ infinite_pos (abs x) := sorry

lemma infinite_iff_abs_lt_abs {x : ℝ*} : infinite x ↔ ∀ r : ℝ, (abs r : ℝ*) < abs x := sorry

lemma pos_of_infinite_pos {x : ℝ*} : infinite_pos x → x > 0 := λ hip, hip 0

lemma neg_of_infinite_neg {x : ℝ*} : infinite_neg x → x < 0 := λ hin, hin 0

lemma infinite_pos_iff_infinite_and_pos {x : ℝ*} : infinite_pos x ↔ (infinite x ∧ x > 0) := 
⟨λ hip, ⟨or.inl hip, hip 0⟩, λ ⟨hi, hp⟩, hi.cases_on (λ hip, hip) (λ hin, false.elim (not_lt_of_lt hp (hin 0)))⟩ 

lemma infinite_neg_iff_infinite_and_neg {x : ℝ*} : infinite_neg x ↔ (infinite x ∧ x < 0) := sorry

lemma infinite_pos_add_not_infinite_neg {x y : ℝ*} : infinite_pos x → ¬ infinite_neg y → infinite_pos (x + y) := sorry

lemma not_infinite_neg_add_infinite_pos {x y : ℝ*} : ¬ infinite_neg x → infinite_pos y → infinite_pos (x + y) := sorry

lemma infinite_neg_add_not_infinite_pos {x y : ℝ*} : infinite_neg x → ¬ infinite_pos y → infinite_neg (x + y) := sorry

lemma not_infinite_pos_add_infinite_neg {x y : ℝ*} : ¬ infinite_pos x → infinite_neg y → infinite_neg (x + y) := sorry

lemma infinite_pos_add_infinite_pos {x y : ℝ*} : infinite_pos x → infinite_pos y → infinite_pos (x + y) := sorry

lemma infinite_neg_add_infinite_neg {x y : ℝ*} : infinite_neg x → infinite_neg y → infinite_neg (x + y) := sorry

lemma infinite_pos_add_not_infinite {x y : ℝ*} : infinite_pos x → ¬ infinite y → infinite_pos (x + y) := sorry

lemma infinite_neg_add_not_infinite {x y : ℝ*} : infinite_neg x → ¬ infinite y → infinite_neg (x + y) := sorry

lemma infinite_neg_neg_of_infinite_pos {x : ℝ*} : infinite_pos x → infinite_neg (-x) := sorry

lemma infinite_neg_pos_of_infinite_neg {x : ℝ*} : infinite_neg x → infinite_pos (-x) := sorry

lemma infinite_neg_neg_iff_infinite_pos {x : ℝ*} : infinite_pos x ↔ infinite_neg (-x) := sorry

lemma infinite_neg_pos_iff_infinite_neg {x : ℝ*} : infinite_neg x ↔ infinite_pos (-x) := sorry

lemma not_infinite_of_infinitesimal {x : ℝ*} : infinitesimal x → ¬ infinite x := sorry

lemma not_infinitesimal_of_infinite {x : ℝ*} : infinite x → ¬ infinitesimal x := imp_not_comm.mp not_infinite_of_infinitesimal

lemma infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos {x y : ℝ*} : 
  infinite_pos x → ¬ infinitesimal y → y > 0 → infinite_pos (x * y) := sorry

lemma infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos {x y : ℝ*} : 
  ¬ infinitesimal x → x > 0 → infinite_pos y → infinite_pos (x * y) := sorry

lemma infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg {x y : ℝ*} : 
  infinite_neg x → ¬ infinitesimal y → y < 0 → infinite_pos (x * y) := sorry

lemma infinite_pos_mul_of_notw_infinitesimal_neg_infinite_neg {x y : ℝ*} : 
  ¬ infinitesimal x → x < 0 → infinite_neg y → infinite_pos (x * y) := sorry

lemma infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg {x y : ℝ*} : 
  infinite_pos x → ¬ infinitesimal y → y < 0 → infinite_neg (x * y) := sorry

lemma infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos {x y : ℝ*} : 
  ¬ infinitesimal x → x < 0 → infinite_pos y → infinite_neg (x * y) := sorry
/-    314159265358979323846264338327950288419716939950510582    -/
lemma infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos {x y : ℝ*} : 
  infinite_neg x → ¬ infinitesimal y → y > 0 → infinite_neg (x * y) := sorry

lemma infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg {x y : ℝ*} : 
  ¬ infinitesimal x → x > 0 → infinite_neg y → infinite_neg (x * y) := sorry

lemma infinite_pos_mul_infinite_pos {x y : ℝ*} : infinite_pos x → infinite_pos y → infinite_pos (x * y) := sorry

lemma infinite_neg_mul_infinite_neg {x y : ℝ*} : infinite_neg x → infinite_neg y → infinite_pos (x * y) := sorry

lemma infinite_pos_mul_infinite_neg {x y : ℝ*} : infinite_pos x → infinite_neg y → infinite_neg (x * y) := sorry

lemma infinite_neg_mul_infinite_pos {x y : ℝ*} : infinite_neg x → infinite_pos y → infinite_neg (x * y) := sorry

lemma infinite_mul_of_infinite_not_infinitesimal {x y : ℝ*} : infinite x → ¬ infinitesimal y → infinite (x * y) := sorry

lemma infinite_mul_of_not_infinitesimal_infinite {x y : ℝ*} : ¬ infinitesimal x → infinite y → infinite (x * y) := sorry

lemma infinite_mul_infinite {x y : ℝ*} : infinite x → infinite y → infinite (x * y) := sorry

theorem infinite_pos_of_tendsto_top {f : ℕ → ℝ} (hf : tendsto f at_top at_top) : infinite_pos (of_seq f) := sorry

theorem infinite_neg_of_tendsto_bot {f : ℕ → ℝ} (hf : tendsto f at_top at_bot) : infinite_neg (of_seq f) := sorry

theorem infinite_pos_iff_infinitesimal_inv_pos {x : ℝ*} : infinite_pos x ↔ (infinitesimal x⁻¹ ∧ x⁻¹ > 0) := sorry

theorem infinite_neg_iff_infinitesimal_inv_neg {x : ℝ*} : infinite_neg x ↔ (infinitesimal x⁻¹ ∧ x⁻¹ < 0) := sorry

theorem infinitesimal_pos_iff_infinite_pos_inv {x : ℝ*} : (infinitesimal x ∧ x > 0) ↔ infinite_pos x⁻¹ := sorry

theorem infinitesimal_neg_iff_infinite_neg_inv {x : ℝ*} : (infinitesimal x ∧ x < 0) ↔ infinite_neg x⁻¹ := sorry

theorem infinite_iff_infinitesimal_inv {x : ℝ*} : infinite x ↔ infinitesimal x⁻¹ := sorry

theorem infinitesimal_iff_infinite_inv {x : ℝ*} : infinitesimal x ↔ infinite x⁻¹ := sorry

lemma infinite_pos_omea : infinite_pos ω := sorry

lemma infinite_omega : infinite ω := sorry

theorem not_infinite_iff_exist_lt_gt {x : ℝ*} : ¬ infinite x ↔ ∃ r s : ℝ, ↑r < x ∧ x < s := sorry

theorem not_infinite_real (r : ℝ) : ¬ infinite r := by rw not_infinite_iff_exist_lt_gt; exact
⟨ r - 1, r + 1, 
  by rw [←of_eq_coe, ←of_eq_coe, ←of_lt U]; exact sub_one_lt _, 
  by rw [←of_eq_coe, ←of_eq_coe, ←of_lt U]; exact lt_add_one _⟩

theorem not_real_of_infinite {x : ℝ*} : infinite x → ∀ r : ℝ, x ≠ of r := sorry

theorem infinite_iff_not_exist_st {x : ℝ*} : infinite x ↔ ¬ ∃ r : ℝ, is_st x r := sorry

theorem st_infinite (x : ℝ*) (hi : infinite x) : st x = 0 := 
begin
  unfold st, split_ifs,
  { exact false.elim ((infinite_iff_not_exist_st.mp hi) h) },
  { refl }
end

theorem infinitesimal_sub_is_st {x : ℝ*} {r : ℝ} : is_st x r → infinitesimal (x - r) := sorry

theorem infinitesimal_sub_st {x : ℝ*} (hx : ¬infinite x) : infinitesimal (x - st x) := sorry

/-- Standard part of a cauchy sequence -/
theorem is_st_lim_of_cau_seq {f : ℕ → ℝ} (hf : is_cau_seq abs f) : is_st (of_seq f) (cau_seq.lim ⟨f, hf⟩) := sorry

/-- Standard part of a cauchy sequence (alternative) -/
theorem is_st_cau_seq_lim (f : cau_seq ℝ abs) : is_st (of_seq f.val) (cau_seq.lim f) := is_st_lim_of_cau_seq f.property

end hyperreal
