import Mathlib

/-!
# OEIS A326250

`a(n)` is the number of weakly nesting simple graphs with vertices `{1,…,n}`. Two edges
`{a,b}`, `{c,d}` are weakly nesting if `a ≤ c < d ≤ b` or `c ≤ a < b ≤ d`.

G. Wiseman conjectured (2019): `A006125(n) = a(n) + A000108(n)`, i.e. `2^C(n,2) = a(n) + Cₙ`.
Equivalently, the graphs on `{1,…,n}` with no two weakly nesting edges are counted by the
Catalan number `Cₙ`.

We prove it (`A326250.wiseman`). Such a graph has distinct left endpoints and distinct right
endpoints, and its edges ordered by left endpoint are also ordered by right endpoint.

Delete the vertices `n, n-1, …` one at a time, and remember the left endpoints of the edges
whose right endpoint was deleted ("pending" left endpoints).
* Let `S(m,h)` count the pairs (non-nesting graph on `{1,…,m}`, set `P` of `h` pending left
  endpoints), where every element of `P` exceeds every left endpoint of the graph.
* Deleting vertex `m+1` gives `S(m+1,h) = S(m,h) + S(m,h+1) + [h ≥ 1]·(S(m,h-1) + S(m,h))`
  (`A326250.S_succ_zero`, `A326250.S_succ_succ`).
* This is the recursion for Dyck paths read two steps at a time. Its solution is the ballot
  number `S(m,h) = C(2m, m+h) − C(2m, m+h+1)` (`A326250.S_eq_B`).
* In particular `S(n,0) = C(2n,n) − C(2n,n+1) = Cₙ`.
-/

open Finset

namespace A326250

/-- The possible edges `{a, b}` of a simple graph on `{1,…,n}`, written as pairs `a < b`. -/
def edgeSet (n : ℕ) : Finset (ℕ × ℕ) := (Icc 1 n ×ˢ Icc 1 n).filter fun e => e.1 < e.2

/-- Two distinct edges of `G` are weakly nesting: `e = {a,b}`, `f = {c,d}` with `a ≤ c < d ≤ b`. -/
def WeaklyNesting (G : Finset (ℕ × ℕ)) : Prop :=
  ∃ e ∈ G, ∃ f ∈ G, e ≠ f ∧ e.1 ≤ f.1 ∧ f.2 ≤ e.2

instance : DecidablePred WeaklyNesting := fun G => by unfold WeaklyNesting; infer_instance

/-- The sequence: weakly nesting simple graphs on `{1,…,n}`. -/
def a (n : ℕ) : ℕ := #{G ∈ (edgeSet n).powerset | WeaklyNesting G}

-- Sanity check against the OEIS data `0, 0, 0, 3, 50`.
example : (List.range 5).map a = [0, 0, 0, 3, 50] := by decide +kernel

lemma mem_edgeSet {n : ℕ} {e : ℕ × ℕ} : e ∈ edgeSet n ↔ 1 ≤ e.1 ∧ e.2 ≤ n ∧ e.1 < e.2 := by
  simp only [edgeSet, mem_filter, mem_product, mem_Icc]
  omega

lemma card_edgeSet (n : ℕ) : #(edgeSet n) = n.choose 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : edgeSet (n + 1) = edgeSet n ∪ (Icc 1 n).image (fun a => (a, n + 1)) := by
      ext e
      simp only [mem_union, mem_edgeSet, mem_image, mem_Icc]
      constructor
      · intro h
        rcases Nat.lt_or_ge e.2 (n + 1) with h2 | h2
        · left; omega
        · right; exact ⟨e.1, by omega, Prod.ext rfl (by simp; omega)⟩
      · rintro (h | ⟨a, ha, rfl⟩)
        · omega
        · simp; omega
    have hc : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
    rw [h, card_union_of_disjoint, ih, card_image_of_injective _ (fun a b h => by simpa using h),
      Nat.card_Icc, hc, Nat.choose_one_right]
    · omega
    · rw [disjoint_left]
      intro e he he'
      obtain ⟨a, -, rfl⟩ := mem_image.1 he'
      rw [mem_edgeSet] at he
      simp at he

/-! ### Graphs with pending left endpoints -/

/-- Pairs `(G, P)`: a non-nesting graph on `{1,…,m}` and a set `P ⊆ {1,…,m}` of `h` pending
left endpoints, each larger than every left endpoint of `G`. -/
def Obj (m h : ℕ) : Finset (Finset (ℕ × ℕ) × Finset ℕ) :=
  ((edgeSet m).powerset ×ˢ (Icc 1 m).powerset).filter fun X =>
    ¬ WeaklyNesting X.1 ∧ #X.2 = h ∧ ∀ p ∈ X.2, ∀ e ∈ X.1, e.1 < p

/-- The number of such pairs. -/
def S (m h : ℕ) : ℕ := #(Obj m h)

lemma mem_Obj {m h : ℕ} {X : Finset (ℕ × ℕ) × Finset ℕ} :
    X ∈ Obj m h ↔ X.1 ⊆ edgeSet m ∧ X.2 ⊆ Icc 1 m ∧ ¬ WeaklyNesting X.1 ∧ #X.2 = h ∧
      ∀ p ∈ X.2, ∀ e ∈ X.1, e.1 < p := by
  simp only [Obj, mem_filter, mem_product, mem_powerset, and_assoc]

lemma not_wn_iff {G : Finset (ℕ × ℕ)} :
    ¬ WeaklyNesting G ↔ ∀ e ∈ G, ∀ f ∈ G, e ≠ f → ¬ (e.1 ≤ f.1 ∧ f.2 ≤ e.2) := by
  simp only [WeaklyNesting, not_exists, not_and]

lemma not_wn_mono {G G' : Finset (ℕ × ℕ)} (h : G' ⊆ G) (hG : ¬ WeaklyNesting G) :
    ¬ WeaklyNesting G' := by
  rw [not_wn_iff] at hG ⊢
  exact fun e he f hf => hG e (h he) f (h hf)

/-- `S(n, 0)` counts the graphs without weakly nesting edges. -/
lemma S_zero_eq (n : ℕ) : S n 0 = #{G ∈ (edgeSet n).powerset | ¬ WeaklyNesting G} := by
  unfold S
  refine card_nbij' (fun X => X.1) (fun G => (G, ∅)) ?_ ?_ ?_ ?_
  · intro X hX
    rw [mem_coe, mem_Obj] at hX
    simp only [coe_filter, mem_powerset, Set.mem_ofPred_eq]
    exact ⟨hX.1, hX.2.2.1⟩
  · intro G hG
    simp only [coe_filter, mem_powerset, Set.mem_ofPred_eq] at hG
    rw [mem_coe, mem_Obj]
    simp [hG.1, hG.2]
  · intro X hX
    rw [mem_coe, mem_Obj] at hX
    have : X.2 = ∅ := card_eq_zero.1 hX.2.2.2.1
    ext <;> simp [this]
  · intro G _; rfl

section Step

variable (m : ℕ)

/-- Vertex `m+1` is the right endpoint of an edge of `X.1`. -/
def R (X : Finset (ℕ × ℕ) × Finset ℕ) : Prop := ∃ e ∈ X.1, e.2 = m + 1

instance (X : Finset (ℕ × ℕ) × Finset ℕ) : Decidable (R m X) := by unfold R; infer_instance

/-- Part (i): if vertex `m+1` is unused, the pair lives on `{1,…,m}`. -/
lemma filter_notR_notP (h : ℕ) :
    (Obj (m + 1) h).filter (fun X => ¬ R m X ∧ m + 1 ∉ X.2) = Obj m h := by
  ext X
  simp only [mem_filter, mem_Obj, R, not_exists, not_and]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩
    refine ⟨fun e he => ?_, fun p hp => ?_, h3, h4, h5⟩
    · have := mem_edgeSet.1 (h1 he)
      have := h6 e he
      exact mem_edgeSet.2 (by omega)
    · have := mem_Icc.1 (h2 hp)
      have : p ≠ m + 1 := fun h => h7 (h ▸ hp)
      exact mem_Icc.2 (by omega)
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨⟨fun e he => ?_, fun p hp => ?_, h3, h4, h5⟩, fun e he => ?_, fun hp => ?_⟩
    · have := mem_edgeSet.1 (h1 he); exact mem_edgeSet.2 (by omega)
    · have := mem_Icc.1 (h2 hp); exact mem_Icc.2 (by omega)
    · have := mem_edgeSet.1 (h1 he); omega
    · have := mem_Icc.1 (h2 hp); omega

/-- The left endpoint of the edge ending at `m+1`. -/
def la (X : Finset (ℕ × ℕ) × Finset ℕ) : ℕ := (X.1.filter fun f => f.2 = m + 1).sup Prod.fst

/-- The minimum of a finite set (`0` if empty). -/
def mn (s : Finset ℕ) : ℕ := if h : s.Nonempty then s.min' h else 0

/-- In a pair containing an edge `e` ending at `m+1`, every other edge ends before `m+1` and
starts before `e`. -/
lemma other_edges {h : ℕ} {X : Finset (ℕ × ℕ) × Finset ℕ} (hX : X ∈ Obj (m + 1) h)
    {e : ℕ × ℕ} (he : e ∈ X.1) (he2 : e.2 = m + 1) {f : ℕ × ℕ} (hf : f ∈ X.1) (hfe : f ≠ e) :
    f.2 ≤ m ∧ f.1 < e.1 := by
  rw [mem_Obj] at hX
  have hnn := not_wn_iff.1 hX.2.2.1
  have hf' := mem_edgeSet.1 (hX.1 hf)
  have h1 : f.1 < e.1 := by
    by_contra hc
    exact hnn e he f hf hfe.symm ⟨by omega, by omega⟩
  refine ⟨?_, h1⟩
  by_contra hc
  exact hnn f hf e he hfe ⟨h1.le, by omega⟩

lemma la_eq {h : ℕ} {X : Finset (ℕ × ℕ) × Finset ℕ} (hX : X ∈ Obj (m + 1) h)
    {e : ℕ × ℕ} (he : e ∈ X.1) (he2 : e.2 = m + 1) : la m X = e.1 := by
  have : X.1.filter (fun f => f.2 = m + 1) = {e} := by
    ext f
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hf, hf2⟩
      by_contra hfe
      have := other_edges m hX he he2 hf hfe
      omega
    · rintro rfl; exact ⟨he, he2⟩
  rw [la, this, sup_singleton]

/-- Part (ii): removing the edge ending at `m+1` makes its left endpoint pending. -/
lemma card_filter_R_notP (h : ℕ) :
    #((Obj (m + 1) h).filter (fun X => R m X ∧ m + 1 ∉ X.2)) = S m (h + 1) := by
  unfold S
  refine card_nbij' (fun X => (X.1.filter fun f => f.2 ≠ m + 1, insert (la m X) X.2))
    (fun Y => (insert (mn Y.2, m + 1) Y.1, Y.2.erase (mn Y.2))) ?_ ?_ ?_ ?_
  · intro X hX
    simp only [coe_filter, Set.mem_ofPred_eq] at hX
    obtain ⟨hX, ⟨e, he, he2⟩, hv⟩ := hX
    have hla := la_eq m hX he he2
    have hX' := mem_Obj.1 hX
    have he' := mem_edgeSet.1 (hX'.1 he)
    have hnot : e.1 ∉ X.2 := fun hp => lt_irrefl _ (hX'.2.2.2.2 _ hp e he)
    rw [mem_coe, mem_Obj]
    dsimp only
    rw [hla]
    refine ⟨fun f hf => ?_, fun p hp => ?_, not_wn_mono (filter_subset _ _) hX'.2.2.1, ?_, ?_⟩
    · rw [mem_filter] at hf
      have := mem_edgeSet.1 (hX'.1 hf.1)
      exact mem_edgeSet.2 (by omega)
    · rw [mem_insert] at hp
      rcases hp with rfl | hp
      · exact mem_Icc.2 (by omega)
      · have := mem_Icc.1 (hX'.2.1 hp)
        have : p ≠ m + 1 := fun h => hv (h ▸ hp)
        exact mem_Icc.2 (by omega)
    · rw [card_insert_of_notMem hnot, hX'.2.2.2.1]
    · intro p hp f hf
      rw [mem_filter] at hf
      rw [mem_insert] at hp
      rcases hp with rfl | hp
      · exact (other_edges m hX he he2 hf.1 (fun h => hf.2 (h ▸ he2))).2
      · exact hX'.2.2.2.2 p hp f hf.1
  · intro Y hY
    rw [mem_coe, mem_Obj] at hY
    obtain ⟨h1, h2, h3, h4, h5⟩ := hY
    have hne : Y.2.Nonempty := card_pos.1 (by omega)
    have hmn : mn Y.2 = Y.2.min' hne := dite_eq_left_of_eq_true (eq_true hne)
    set a := mn Y.2
    have ha : a ∈ Y.2 := hmn ▸ min'_mem _ _
    have hamin : ∀ p ∈ Y.2, a ≤ p := fun p hp => hmn ▸ min'_le _ _ hp
    have ha' := mem_Icc.1 (h2 ha)
    simp only [coe_filter, Set.mem_ofPred_eq]
    refine ⟨?_, ⟨(a, m + 1), mem_insert_self _ _, rfl⟩, fun hv => ?_⟩
    · rw [mem_Obj]
      refine ⟨fun f hf => ?_, fun p hp => ?_, ?_, ?_, ?_⟩
      · rw [mem_insert] at hf
        rcases hf with rfl | hf
        · exact mem_edgeSet.2 ⟨by simp; omega, le_rfl, by simp; omega⟩
        · have := mem_edgeSet.1 (h1 hf); exact mem_edgeSet.2 (by omega)
      · have := mem_Icc.1 (h2 (mem_of_mem_erase hp)); exact mem_Icc.2 (by omega)
      · rw [not_wn_iff]
        intro e he f hf hef
        rw [mem_insert] at he hf
        rcases he with rfl | he <;> rcases hf with rfl | hf
        · exact absurd rfl hef
        · have := h5 a ha f hf; simp; omega
        · have := mem_edgeSet.1 (h1 he); simp; omega
        · exact not_wn_iff.1 h3 e he f hf hef
      · rw [card_erase_of_mem ha, h4]; rfl
      · intro p hp f hf
        have hpa : p ≠ a := ne_of_mem_erase hp
        have hp' := mem_of_mem_erase hp
        rw [mem_insert] at hf
        rcases hf with rfl | hf
        · have := hamin p hp'; simp; omega
        · exact h5 p hp' f hf
    · have := mem_Icc.1 (h2 (mem_of_mem_erase hv)); omega
  · intro X hX
    simp only [coe_filter, Set.mem_ofPred_eq] at hX
    obtain ⟨hX, ⟨e, he, he2⟩, hv⟩ := hX
    have hla := la_eq m hX he he2
    have hX' := mem_Obj.1 hX
    have hnot : e.1 ∉ X.2 := fun hp => lt_irrefl _ (hX'.2.2.2.2 _ hp e he)
    have hmn : mn (insert e.1 X.2) = e.1 := by
      have hne : (insert e.1 X.2).Nonempty := insert_nonempty _ _
      rw [mn, dite_eq_left_of_eq_true (eq_true hne)]
      apply le_antisymm (min'_le _ _ (mem_insert_self _ _))
      apply le_min'
      intro p hp
      rw [mem_insert] at hp
      rcases hp with rfl | hp
      · exact le_rfl
      · exact (hX'.2.2.2.2 p hp e he).le
    simp only [hla, hmn]
    ext x
    · simp only [mem_insert, mem_filter]
      constructor
      · rintro (rfl | ⟨hx, -⟩)
        · rw [← he2]; exact he
        · exact hx
      · intro hx
        by_cases hx2 : x.2 = m + 1
        · left
          by_contra hxe
          have hee : e = (e.1, m + 1) := Prod.ext rfl he2
          have := other_edges m hX he he2 hx (fun h => hxe (h.trans hee))
          omega
        · exact Or.inr ⟨hx, hx2⟩
    · simp only [mem_erase, mem_insert]
      constructor
      · rintro ⟨hx, rfl | hx'⟩
        · exact absurd rfl hx
        · exact hx'
      · intro hx
        exact ⟨fun h => hnot (h ▸ hx), Or.inr hx⟩
  · intro Y hY
    dsimp only
    rw [mem_coe, mem_Obj] at hY
    obtain ⟨h1, h2, h3, h4, h5⟩ := hY
    have hne : Y.2.Nonempty := card_pos.1 (by omega)
    have hmn : mn Y.2 = Y.2.min' hne := dite_eq_left_of_eq_true (eq_true hne)
    set a := mn Y.2
    have ha : a ∈ Y.2 := hmn ▸ min'_mem _ _
    have hfilt : (insert (a, m + 1) Y.1).filter (fun f => f.2 ≠ m + 1) = Y.1 := by
      ext f
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hf, hf2⟩
        · exact absurd rfl hf2
        · exact hf
      · intro hf
        have := mem_edgeSet.1 (h1 hf)
        exact ⟨Or.inr hf, by omega⟩
    -- the left endpoint of the new edge is `a`
    have hla : la m (insert (a, m + 1) Y.1, Y.2.erase a) = a := by
      unfold la
      have : (insert (a, m + 1) Y.1).filter (fun f => f.2 = m + 1) = {(a, m + 1)} := by
        ext f
        simp only [mem_filter, mem_insert, mem_singleton]
        constructor
        · rintro ⟨rfl | hf, hf2⟩
          · rfl
          · have := mem_edgeSet.1 (h1 hf); omega
        · rintro rfl; exact ⟨Or.inl rfl, rfl⟩
      rw [this, sup_singleton]
    rw [hfilt, hla, insert_erase ha]

/-- Part (iii): a pending vertex `m+1` can be removed from `P`. -/
lemma card_filter_P (h : ℕ) :
    #((Obj (m + 1) (h + 1)).filter (fun X => m + 1 ∈ X.2)) =
      #((Obj (m + 1) h).filter (fun X => m + 1 ∉ X.2)) := by
  refine card_nbij' (fun X => (X.1, X.2.erase (m + 1))) (fun Y => (Y.1, insert (m + 1) Y.2))
    ?_ ?_ ?_ ?_
  · intro X hX
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Obj] at hX ⊢
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, hv⟩ := hX
    refine ⟨⟨h1, fun p hp => h2 (mem_of_mem_erase hp), h3, ?_,
      fun p hp => h5 p (mem_of_mem_erase hp)⟩, fun h => (ne_of_mem_erase h) rfl⟩
    rw [card_erase_of_mem hv, h4]; rfl
  · intro Y hY
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Obj] at hY ⊢
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, hv⟩ := hY
    refine ⟨⟨h1, fun p hp => ?_, h3, ?_, fun p hp e he => ?_⟩, mem_insert_self _ _⟩
    · rw [mem_insert] at hp
      rcases hp with rfl | hp
      · exact mem_Icc.2 (by omega)
      · exact h2 hp
    · rw [card_insert_of_notMem hv, h4]
    · rw [mem_insert] at hp
      rcases hp with rfl | hp
      · have := mem_edgeSet.1 (h1 he); omega
      · exact h5 p hp e he
  · intro X hX
    simp only [coe_filter, Set.mem_ofPred_eq] at hX
    simp [insert_erase hX.2]
  · intro Y hY
    simp only [coe_filter, Set.mem_ofPred_eq] at hY
    simp [erase_insert hY.2]

lemma card_notP (h : ℕ) :
    #((Obj (m + 1) h).filter (fun X => m + 1 ∉ X.2)) = S m h + S m (h + 1) := by
  have h1 := card_filter_add_card_filter_not (s := (Obj (m + 1) h).filter (fun X => m + 1 ∉ X.2))
    (R m)
  rw [filter_filter, filter_filter] at h1
  have e1 : (Obj (m + 1) h).filter (fun X => m + 1 ∉ X.2 ∧ R m X) =
      (Obj (m + 1) h).filter (fun X => R m X ∧ m + 1 ∉ X.2) :=
    filter_congr (fun _ _ => and_comm)
  have e2 : (Obj (m + 1) h).filter (fun X => m + 1 ∉ X.2 ∧ ¬ R m X) =
      (Obj (m + 1) h).filter (fun X => ¬ R m X ∧ m + 1 ∉ X.2) :=
    filter_congr (fun _ _ => and_comm)
  rw [← h1, e1, e2, card_filter_R_notP, filter_notR_notP, add_comm]; rfl

lemma S_succ_zero : S (m + 1) 0 = S m 0 + S m 1 := by
  rw [S, ← card_filter_add_card_filter_not (fun X => m + 1 ∈ X.2), card_notP]
  have : (Obj (m + 1) 0).filter (fun X => m + 1 ∈ X.2) = ∅ := by
    ext X
    simp only [mem_filter, mem_Obj, notMem_empty, iff_false, not_and]
    intro hX hv
    have h4 := hX.2.2.2.1
    rw [card_eq_zero] at h4
    rw [h4] at hv
    exact notMem_empty _ hv
  rw [this, card_empty, zero_add]

lemma S_succ_succ (h : ℕ) :
    S (m + 1) (h + 1) = S m h + S m (h + 1) + (S m (h + 1) + S m (h + 2)) := by
  rw [S, ← card_filter_add_card_filter_not (fun X => m + 1 ∈ X.2), card_notP,
    card_filter_P, card_notP]

end Step

/-! ### Solving the recursion -/

/-- The ballot numbers `C(2m, m+h) − C(2m, m+h+1)`. -/
def B (m h : ℕ) : ℤ := ((2 * m).choose (m + h) : ℤ) - (2 * m).choose (m + h + 1)

lemma choose_two_step (n k : ℕ) :
    ((n + 2).choose (k + 2) : ℤ) = n.choose k + 2 * n.choose (k + 1) + n.choose (k + 2) := by
  rw [Nat.choose_succ_succ, Nat.choose_succ_succ, Nat.choose_succ_succ (n := n) (k := k + 1)]
  push_cast; ring

lemma B_succ_succ (m h : ℕ) : B (m + 1) (h + 1) = B m h + 2 * B m (h + 1) + B m (h + 2) := by
  unfold B
  rw [show 2 * (m + 1) = 2 * m + 2 by ring, show m + 1 + (h + 1) + 1 = (m + h + 1) + 2 by ring,
    show m + 1 + (h + 1) = (m + h) + 2 by ring, choose_two_step, choose_two_step,
    show m + (h + 1) = m + h + 1 by ring, show m + (h + 2) = m + h + 2 by ring]
  ring

lemma B_succ_zero (m : ℕ) : B (m + 1) 0 = B m 0 + B m 1 := by
  rcases m with _ | m
  · decide
  unfold B
  rw [show 2 * (m + 1 + 1) = 2 * (m + 1) + 2 by ring, show m + 1 + 1 + 0 = m + 2 by ring,
    show m + 1 + 1 + 0 + 1 = (m + 1) + 2 by ring, choose_two_step, choose_two_step]
  have hsym : (2 * (m + 1)).choose m = (2 * (m + 1)).choose (m + 2) :=
    Nat.choose_symm_of_eq_add (by ring)
  simp only [add_zero, show m + 1 + 1 = m + 2 by ring, show m + 1 + 1 + 1 = m + 3 by ring,
    hsym]
  ring

lemma S_zero_left (h : ℕ) : S 0 h = if h = 0 then 1 else 0 := by
  unfold S
  have : Obj 0 h = if h = 0 then {(∅, ∅)} else ∅ := by
    ext X
    rw [mem_Obj]
    have he : edgeSet 0 = ∅ := rfl
    simp only [he, subset_empty, show Icc 1 0 = ∅ from rfl]
    split_ifs with hh
    · subst hh
      simp only [mem_singleton]
      constructor
      · rintro ⟨h1, h2, -, -, -⟩; exact Prod.ext h1 h2
      · rintro rfl; simp [WeaklyNesting]
    · simp only [notMem_empty, iff_false, not_and]
      intro _ h2 _ h4
      rw [h2, card_empty] at h4
      exact absurd h4.symm hh
  rw [this]
  split_ifs <;> simp

/-- `S(m, h)` is the ballot number `C(2m, m+h) − C(2m, m+h+1)`. -/
theorem S_eq_B (m h : ℕ) : (S m h : ℤ) = B m h := by
  induction m generalizing h with
  | zero =>
    rw [S_zero_left, B]
    rcases h with _ | h <;> simp
  | succ m ih =>
    rcases h with _ | h
    · rw [S_succ_zero, B_succ_zero]; push_cast; simp only [ih]
    · rw [S_succ_succ, B_succ_succ]; push_cast; simp only [ih]; ring

lemma B_zero_eq_catalan (n : ℕ) : B n 0 = catalan n := by
  unfold B
  have h1 := succ_mul_catalan_eq_centralBinom n
  rw [Nat.centralBinom_eq_two_mul_choose] at h1
  have h2 := Nat.choose_succ_right_eq (2 * n) n
  rw [show 2 * n - n = n by omega] at h2
  have h1' : ((n + 1 : ℕ) : ℤ) * catalan n = (2 * n).choose n := by exact_mod_cast h1
  have h2' : ((2 * n).choose (n + 1) : ℤ) * (n + 1) = (2 * n).choose n * n := by
    exact_mod_cast h2
  have hpos : ((n + 1 : ℕ) : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hpos
  simp only [add_zero]
  push_cast at h1' ⊢
  linear_combination -h1' - h2'

/-- The graphs on `{1,…,n}` without weakly nesting edges are counted by the Catalan number. -/
theorem card_not_weaklyNesting (n : ℕ) :
    #{G ∈ (edgeSet n).powerset | ¬ WeaklyNesting G} = catalan n := by
  rw [← S_zero_eq]
  exact_mod_cast (S_eq_B n 0).trans (B_zero_eq_catalan n)

/-- **Wiseman's conjecture.** `A006125(n) = a(n) + A000108(n)`, i.e. `2^C(n,2) = a(n) + Cₙ`. -/
theorem wiseman (n : ℕ) : 2 ^ n.choose 2 = a n + catalan n := by
  rw [a, ← card_not_weaklyNesting, card_filter_add_card_filter_not, card_powerset,
    card_edgeSet]

end A326250

#print axioms A326250.wiseman
