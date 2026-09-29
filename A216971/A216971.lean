import Mathlib

/-!
# OEIS A216971

`T(n,k)` is the number of functions `f : {1,…,n} → {1,…,n}` that have exactly `k` nonrecurrent
elements mapped to a recurrent element. An element `x` is *recurrent* if `f^j(x) = x` for some
`j ≥ 1`, i.e. it lies on a cycle of the functional digraph.

J. Perry conjectured (2012): every entry in row `n` is divisible by `n`.

We prove it (`A216971.dvd_T`). Group the functions by their set `R` of recurrent elements.
* The symmetric group of `R` acts freely on the functions with recurrent set `R`, by
  post-composing on `R`, and this preserves the statistic. So `|R|!` divides their number
  (`A216971.factorial_dvd_card_N`).
* Conjugating by a permutation of `{1,…,n}` shows that this number depends only on `|R|`
  (`A216971.card_N_eq`).
* Hence `T(n,k) = ∑ₘ C(n,m)·N_m` with `m! ∣ N_m`, and `n ∣ C(n,m)·m! = n(n−1)⋯(n−m+1)` for
  `m ≥ 1`. The term `m = 0` vanishes, since every function on a nonempty finite set has a
  cycle.
-/

open Finset Function

namespace A216971

variable {n : ℕ}

/-- `x` is recurrent for `f`: `f^[j] x = x` for some `j ≥ 1`. -/
def IsRec (f : Fin n → Fin n) (x : Fin n) : Prop := ∃ j, 0 < j ∧ f^[j] x = x

lemma isRec_iff_mem (f : Fin n → Fin n) (x : Fin n) : IsRec f x ↔ x ∈ periodicPts f :=
  Iff.rfl

/-- Recurrence can be decided by looking at `j ≤ n` only. -/
lemma isRec_iff_bounded (f : Fin n → Fin n) (x : Fin n) :
    IsRec f x ↔ ∃ j ∈ Icc 1 n, f^[j] x = x := by
  constructor
  · rintro ⟨j, hj, hx⟩
    have hper : x ∈ periodicPts f := mk_mem_periodicPts hj hx
    have hp : 0 < minimalPeriod f x := minimalPeriod_pos_of_mem_periodicPts hper
    refine ⟨minimalPeriod f x, mem_Icc.2 ⟨hp, ?_⟩, isPeriodicPt_minimalPeriod f x⟩
    have := card_le_card_of_injOn (fun i => f^[i] x) (s := range (minimalPeriod f x))
      (t := (univ : Finset (Fin n))) (fun _ _ => mem_coe.2 (mem_univ _))
      (fun a ha b hb h => iterate_injOn_Iio_minimalPeriod (by simpa using ha)
        (by simpa using hb) h)
    simpa using this
  · rintro ⟨j, hj, hx⟩
    exact ⟨j, (mem_Icc.1 hj).1, hx⟩

instance (f : Fin n → Fin n) (x : Fin n) : Decidable (IsRec f x) :=
  decidable_of_iff _ (isRec_iff_bounded f x).symm

/-- The number of nonrecurrent elements mapped to a recurrent element. -/
def stat (f : Fin n → Fin n) : ℕ := #{x | ¬ IsRec f x ∧ IsRec f (f x)}

/-- The triangle `T(n,k)`. -/
def T (n k : ℕ) : ℕ := #{f : Fin n → Fin n | stat f = k}

-- Sanity check against the OEIS rows `n = 1, …, 4`.
example : (List.range 4).map (T 4) = [24, 156, 72, 4] ∧ (List.range 3).map (T 3) = [6, 18, 3] ∧
    (List.range 2).map (T 2) = [2, 2] ∧ T 1 0 = 1 := by
  decide +kernel

/-! ### Basic facts about recurrent points -/

lemma IsRec.apply {f : Fin n → Fin n} {x : Fin n} (h : IsRec f x) : IsRec f (f x) := by
  obtain ⟨j, hj, hx⟩ := h
  exact ⟨j, hj, by rw [← iterate_succ_apply, iterate_succ_apply', hx]⟩

lemma IsRec.iterate {f : Fin n → Fin n} {x : Fin n} (h : IsRec f x) (i : ℕ) :
    IsRec f (f^[i] x) := by
  induction i with
  | zero => exact h
  | succ i ih => rw [iterate_succ_apply']; exact ih.apply

/-- Every function on a nonempty finite set has a recurrent point. -/
lemma exists_isRec (f : Fin n → Fin n) (x : Fin n) : ∃ y, IsRec f y := by
  obtain ⟨a, b, hab, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => f^[i] x)
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · refine ⟨f^[a] x, b - a, by omega, ?_⟩
    rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le]; exact h.symm
  · refine ⟨f^[b] x, a - b, by omega, ?_⟩
    rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le]; exact h

/-- **Gluing.** Let `h` agree with `f` off the recurrent points of `f`, and let `h` map the
recurrent points of `f` injectively into themselves. Then `h` and `f` have the same recurrent
points. -/
lemma isRec_glue {f h : Fin n → Fin n} (hout : ∀ x, ¬ IsRec f x → h x = f x)
    (hmaps : ∀ x, IsRec f x → IsRec f (h x))
    (hinj : ∀ x y, IsRec f x → IsRec f y → h x = h y → x = y) (x : Fin n) :
    IsRec h x ↔ IsRec f x := by
  have hit : ∀ i y, IsRec f y → IsRec f (h^[i] y) := by
    intro i
    induction i with
    | zero => intro y hy; exact hy
    | succ i ih => intro y hy; rw [iterate_succ_apply']; exact hmaps _ (ih y hy)
  constructor
  · rintro ⟨p, hp, hx⟩
    by_contra hnx
    -- the `h`-orbit of `x` never enters the recurrent set of `f`
    have hnot : ∀ i, ¬ IsRec f (h^[i] x) := by
      intro i hi
      have := hit (p * (i + 1) - i) _ hi
      rw [← iterate_add_apply, Nat.sub_add_cancel (by nlinarith),
        (show IsPeriodicPt h p x from hx).mul_const (i + 1)] at this
      exact hnx this
    -- so it is also the `f`-orbit
    have heq : ∀ i, h^[i] x = f^[i] x := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [iterate_succ_apply', iterate_succ_apply', ← ih, hout _ (hnot i)]
    exact hnx ⟨p, hp, by rw [← heq]; exact hx⟩
  · intro hx
    obtain ⟨a, b, hab, hEq⟩ := Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => h^[i] x)
    -- cancel the common prefix using injectivity of `h` on the recurrent points of `f`
    have cancel : ∀ i y z, IsRec f y → IsRec f z → h^[i] y = h^[i] z → y = z := by
      intro i
      induction i with
      | zero => intro y z _ _ e; exact e
      | succ i ih =>
        intro y z hy hz e
        rw [iterate_succ_apply, iterate_succ_apply] at e
        exact hinj _ _ hy hz (ih _ _ (hmaps _ hy) (hmaps _ hz) e)
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · refine ⟨b - a, by omega, (cancel a _ _ (hit _ _ hx) hx ?_)⟩
      rw [← iterate_add_apply, Nat.add_sub_cancel' hlt.le]; exact hEq.symm
    · refine ⟨a - b, by omega, (cancel b _ _ (hit _ _ hx) hx ?_)⟩
      rw [← iterate_add_apply, Nat.add_sub_cancel' hlt.le]; exact hEq

lemma stat_eq_of {f h : Fin n → Fin n} (hrec : ∀ x, IsRec h x ↔ IsRec f x)
    (hout : ∀ x, ¬ IsRec f x → h x = f x) : stat h = stat f := by
  unfold stat
  congr 1
  apply filter_congr
  intro x _
  rw [hrec, hrec]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [← hout x h1]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hout x h1]⟩

/-! ### Conjugation -/

/-- Relabelling a function by a permutation `π`. -/
def conj (π : Equiv.Perm (Fin n)) (f : Fin n → Fin n) : Fin n → Fin n := fun x => π (f (π.symm x))

lemma conj_iterate (π : Equiv.Perm (Fin n)) (f : Fin n → Fin n) (j : ℕ) (x : Fin n) :
    (conj π f)^[j] x = π (f^[j] (π.symm x)) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih => rw [iterate_succ_apply, ih, iterate_succ_apply]; simp [conj]

lemma isRec_conj (π : Equiv.Perm (Fin n)) (f : Fin n → Fin n) (x : Fin n) :
    IsRec (conj π f) x ↔ IsRec f (π.symm x) := by
  simp only [IsRec, conj_iterate]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, by rw [← π.symm_apply_apply (f^[j] _), h]⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, by rw [h]; simp⟩

lemma stat_conj (π : Equiv.Perm (Fin n)) (f : Fin n → Fin n) : stat (conj π f) = stat f := by
  unfold stat
  refine card_nbij' (fun x => π.symm x) (fun y => π y) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, isRec_conj] at hx ⊢
    simpa [conj] using hx
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, isRec_conj] at hy ⊢
    simpa [conj] using hy
  · intro x _; simp
  · intro y _; simp

/-! ### Functions with a prescribed recurrent set -/

/-- The recurrent set of `f`. -/
def recSet (f : Fin n → Fin n) : Finset (Fin n) := {x | IsRec f x}

/-- Functions with statistic `k` and recurrent set `S`. -/
def N (k : ℕ) (S : Finset (Fin n)) : Finset (Fin n → Fin n) :=
  {f ∈ ({f | stat f = k} : Finset (Fin n → Fin n)) | recSet f = S}

lemma recSet_conj (π : Equiv.Perm (Fin n)) (f : Fin n → Fin n) :
    recSet (conj π f) = (recSet f).map π.toEmbedding := by
  ext x
  simp only [recSet, mem_filter, mem_univ, true_and, isRec_conj, mem_map_equiv]

lemma card_N_map (k : ℕ) (S : Finset (Fin n)) (π : Equiv.Perm (Fin n)) :
    #(N k (S.map π.toEmbedding)) = #(N k S) := by
  refine card_nbij' (conj π.symm) (conj π) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [N, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
    refine ⟨by rw [stat_conj]; exact hf.1, ?_⟩
    rw [recSet_conj, hf.2]
    ext x; simp
  · intro f hf
    simp only [N, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
    exact ⟨by rw [stat_conj]; exact hf.1, by rw [recSet_conj, hf.2]⟩
  · intro f _; funext x; simp [conj]
  · intro f _; funext x; simp [conj]

/-- The number of functions with recurrent set `S` depends only on `|S|`. -/
lemma card_N_eq (k : ℕ) {S S' : Finset (Fin n)} (h : #S = #S') : #(N k S) = #(N k S') := by
  have e1 : {x // x ∈ S} ≃ {x // x ∈ S'} :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_coe, h])
  have e2 : {x // ¬ x ∈ S} ≃ {x // ¬ x ∈ S'} :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
      simp only [Fintype.card_coe, h])
  set π : Equiv.Perm (Fin n) := Equiv.subtypeCongr e1 e2
  have hpos : ∀ x (hx : x ∈ S), π x = e1 ⟨x, hx⟩ := by
    intro x hx; simp [π, Equiv.subtypeCongr, hx]
  have hπ : S.map π.toEmbedding = S' := by
    ext y
    simp only [mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hpos a ha]; exact (e1 _).2
    · intro hy
      refine ⟨e1.symm ⟨y, hy⟩, (e1.symm ⟨y, hy⟩).2, ?_⟩
      rw [hpos _ (e1.symm ⟨y, hy⟩).2]
      simp
  rw [← hπ, card_N_map]

/-! ### The free action of the symmetric group of the recurrent set -/

lemma mem_recSet {f : Fin n → Fin n} {x : Fin n} : x ∈ recSet f ↔ IsRec f x := by
  simp [recSet]

/-- Replace `f` by the identity on `S`. -/
def normal (S : Finset (Fin n)) (f : Fin n → Fin n) : Fin n → Fin n :=
  fun x => if x ∈ S then x else f x

/-- Glue a permutation `e` of `S` with `g` outside `S`. -/
def glue (S : Finset (Fin n)) (e : Equiv.Perm S) (g : Fin n → Fin n) : Fin n → Fin n :=
  fun x => if hx : x ∈ S then (e ⟨x, hx⟩ : Fin n) else g x

lemma glue_mem_N {k : ℕ} {S : Finset (Fin n)} {f : Fin n → Fin n} (hf : f ∈ N k S)
    (e : Equiv.Perm S) : glue S e (normal S f) ∈ N k S := by
  simp only [N, mem_filter, mem_univ, true_and] at hf ⊢
  obtain ⟨hstat, hR⟩ := hf
  have hS : ∀ x, IsRec f x ↔ x ∈ S := fun x => by rw [← hR, mem_recSet]
  have hout : ∀ x, ¬ IsRec f x → glue S e (normal S f) x = f x := by
    intro x hx
    have hxS : x ∉ S := by rwa [← hS]
    simp [glue, normal, hxS]
  have hrec := isRec_glue hout
    (by
      intro x hx
      rw [hS] at hx ⊢
      simp only [glue, hx, dite_true]
      exact (e _).2)
    (by
      intro x y hx hy hxy
      rw [hS] at hx hy
      simp only [glue, hx, hy, dite_true] at hxy
      have := e.injective (Subtype.ext hxy)
      simpa using this)
  refine ⟨by rw [stat_eq_of hrec hout, hstat], ?_⟩
  ext x
  rw [mem_recSet, hrec, hS]

lemma normal_glue {S : Finset (Fin n)} (e : Equiv.Perm S) (f : Fin n → Fin n) :
    normal S (glue S e (normal S f)) = normal S f := by
  funext x
  by_cases hx : x ∈ S <;> simp [normal, glue, hx]

/-- `|S|!` divides the number of functions with recurrent set `S`. -/
lemma factorial_dvd_card_N (k : ℕ) (S : Finset (Fin n)) : (#S).factorial ∣ #(N k S) := by
  rw [card_eq_sum_card_image (normal S) (N k S)]
  rw [sum_const_nat (m := (#S).factorial)]
  · exact dvd_mul_left _ _
  intro g hg
  obtain ⟨f₀, hf₀, rfl⟩ := mem_image.1 hg
  have hfib : {f ∈ N k S | normal S f = normal S f₀} =
      (univ : Finset (Equiv.Perm S)).image (fun e => glue S e (normal S f₀)) := by
    ext f
    simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨hf, hnf⟩
      have hf' := hf
      simp only [N, mem_filter, mem_univ, true_and] at hf'
      have hS : ∀ x, IsRec f x ↔ x ∈ S := fun x => by rw [← hf'.2, mem_recSet]
      have hmaps : ∀ x : S, f x ∈ S := fun x => (hS _).1 ((hS _).2 x.2).apply
      have hinj : Injective (fun x : S => (⟨f x, hmaps x⟩ : S)) := by
        intro x y hxy
        have h1 : f x = f y := congrArg Subtype.val hxy
        exact Subtype.ext ((bijOn_periodicPts (f := f)).injOn ((hS _).2 x.2) ((hS _).2 y.2) h1)
      refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj), ?_⟩
      funext x
      by_cases hx : x ∈ S
      · simp [glue, hx]
      · have := congrFun hnf x
        simp only [normal, hx, ite_false] at this
        simp [glue, hx, normal, this]
    · rintro ⟨e, rfl⟩
      exact ⟨glue_mem_N hf₀ e, normal_glue e f₀⟩
  rw [hfib, card_image_of_injective]
  · rw [card_univ, Fintype.card_perm, Fintype.card_coe]
  · intro e e' h
    ext x
    have := congrFun h x
    simp only [glue, coe_mem, dite_true, Subtype.coe_eta] at this
    rw [this]

/-! ### Assembly -/

lemma N_empty (hn : 1 ≤ n) (k : ℕ) : N k (∅ : Finset (Fin n)) = ∅ := by
  ext f
  simp only [N, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and]
  intro _ h
  obtain ⟨y, hy⟩ := exists_isRec f ⟨0, hn⟩
  have : y ∈ recSet f := mem_recSet.2 hy
  rw [h] at this
  exact notMem_empty _ this

/-- `#(N k S)` as a function of `|S|`. -/
noncomputable def F (n k m : ℕ) : ℕ :=
  if h : m ≤ n then
    #(N k (exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using h)).choose)
  else 0

lemma card_N_eq_F (k : ℕ) (S : Finset (Fin n)) : #(N k S) = F n k #S := by
  have hS : #S ≤ n := by simpa using card_le_univ S
  rw [F, dite_eq_left_of_eq_true (eq_true hS)]
  exact card_N_eq k (exists_subset_card_eq (s := (univ : Finset (Fin n)))
    (by simpa using hS)).choose_spec.2.symm

lemma dvd_descFactorial (n m : ℕ) : n ∣ n.descFactorial (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.descFactorial_succ]; exact dvd_mul_of_dvd_right ih _

/-- **Perry's conjecture.** Every entry in row `n ≥ 1` of A216971 is divisible by `n`. -/
theorem dvd_T (hn : 1 ≤ n) (k : ℕ) : n ∣ T n k := by
  have hsum : T n k = ∑ S : Finset (Fin n), #(N k S) :=
    card_eq_sum_card_fiberwise (f := recSet) (fun _ _ => mem_univ _)
  rw [hsum]
  simp_rw [card_N_eq_F k]
  rw [← powerset_univ, sum_powerset_apply_card, card_univ, Fintype.card_fin]
  apply dvd_sum
  intro m hm
  rw [smul_eq_mul]
  have hmn : m ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hm)
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := m)
    (by simpa using hmn)
  rw [← hS, ← card_N_eq_F k S]
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · rw [card_eq_zero.1 hS, N_empty hn]; simp
  · obtain ⟨q, hq⟩ := factorial_dvd_card_N k S
    rw [hq, hS, ← mul_assoc, mul_comm (n.choose m), ← Nat.descFactorial_eq_factorial_mul_choose]
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact dvd_mul_of_dvd_left (dvd_descFactorial n m') _

end A216971

#print axioms A216971.dvd_T
