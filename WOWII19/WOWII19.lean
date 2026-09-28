import Mathlib

/-!
# Written on the Wall II, Conjecture 19

DeLaViña's Graffiti.pc conjecture WOWII #19: for every connected graph `G`,

  `⌊(Σ_v ecc(v)) / |V| + max_v α(N(v))⌋ ≤ b(G)`,

where `α(N(v))` is the independence number of the neighbourhood of `v` and `b(G)` is the
order of a largest induced bipartite subgraph.

The statement `conjecture19` is copied verbatim from Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/WrittenOnTheWallII/GraphConjecture19.lean`), together with the
definitions it uses (`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Induced.lean`
and `Independence.lean`).

## Proof

Let `w` maximise `L = α(N(w))` and take BFS layers from `w`. Any vertex set whose
intersection with every layer is independent induces a bipartite graph, via the colouring
`dist(w, ·) mod 2` (`card_le_of_layers`).

* `w`, a maximum independent set of `N(w)` and one vertex in each layer `2, …, dist(w, a)`
  of a shortest path to `a` form such a set, so `dist(w, a) + L ≤ b(G)` (`one_path`).
* Adding a second shortest path, from `w` to `c`, gives `dist(a, c) + L ≤ b(G) + 1`
  (`two_path`). Deep enough layers contain two distinct, non-adjacent path vertices.
  Otherwise the paths would give a shortcut from `a` to `c`.

If `ecc(w)` equals the diameter `D`, the first bound gives `D + L ≤ b(G)`. Otherwise the
average eccentricity is `< D`, so the floor is at most `D + L - 1`. Take `a, c` at distance
`D`; the second bound finishes the proof.
-/

open SimpleGraph Finset

namespace WOWII19

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Definitions (as in formal-conjectures) -/

/-- `largestInducedBipartiteSubgraphSize G` is the size of a largest induced
bipartite subgraph of `G`. -/
noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

/-- `b G` is the number of vertices of a largest induced bipartite subgraph of `G`. -/
noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)

/-- Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

/-- The same quantity as a real number. -/
noncomputable def indepNeighbors (G : SimpleGraph α) (v : α) : ℝ :=
  (indepNeighborsCard G v : ℝ)

variable {G : SimpleGraph α}

/-! ### Distance layers give induced bipartite subgraphs -/

omit [DecidableEq α] in
/-- If no edge of `s` joins two vertices at the same distance from `u`, then `s` induces a
bipartite subgraph (colour by the parity of the distance). -/
lemma card_le_of_layers (u : α) (s : Finset α)
    (hs : ∀ x ∈ s, ∀ y ∈ s, G.Adj x y → G.dist u x ≠ G.dist u y) :
    s.card ≤ largestInducedBipartiteSubgraphSize G := by
  apply le_csSup
  · refine ⟨Fintype.card α, ?_⟩
    rintro n ⟨t, -, rfl⟩
    exact t.card_le_univ
  · refine ⟨s, ⟨Coloring.mk (fun x => (⟨G.dist u x.1 % 2, Nat.mod_lt _ two_pos⟩ : Fin 2)) ?_⟩, rfl⟩
    intro x y hxy
    have hadj : G.Adj x.1 y.1 := by simpa using hxy
    have hne := hs x.1 (by simp) y.1 (by simp) hadj
    have h3 := hadj.diff_dist_adj (u := u)
    simp only [ne_eq, Fin.mk.injEq]
    omega

/-! ### Distances, shortest paths and eccentricities -/

omit [Fintype α] [DecidableEq α] in
/-- A vertex splitting a shortest `u`–`w` path at distance `j` from `u`. -/
lemma exists_split (hc : G.Connected) (u w : α) (j : ℕ) (hj : j ≤ G.dist u w) :
    ∃ x, G.dist u x = j ∧ G.dist x w = G.dist u w - j := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u w
  have h1 := dist_le (p.take j)
  have h2 := dist_le (p.drop j)
  rw [Walk.take_length, min_eq_left (hp ▸ hj)] at h1
  rw [Walk.drop_length] at h2
  have h3 := hc.dist_triangle (u := u) (v := p.getVert j) (w := w)
  exact ⟨p.getVert j, by omega, by omega⟩

/-- The eccentricity as a natural number. -/
noncomputable def ecc (G : SimpleGraph α) (u : α) : ℕ := (G.eccent u).toNat

omit [DecidableEq α] in
lemma dist_le_ecc (hc : G.Connected) (u v : α) : G.dist u v ≤ ecc G u := by
  obtain ⟨w, hw⟩ := exists_edist_eq_eccent_of_finite (G := G) u
  have hne : G.eccent u ≠ ⊤ := by
    rw [← hw]; exact edist_ne_top_iff_reachable.mpr (hc u w)
  exact ENat.toNat_le_toNat edist_le_eccent hne

omit [DecidableEq α] in
lemma exists_dist_eq_ecc (u : α) : ∃ v, G.dist u v = ecc G u := by
  obtain ⟨w, hw⟩ := exists_edist_eq_eccent_of_finite (G := G) u
  exact ⟨w, by rw [ecc, ← hw]; rfl⟩

omit [Fintype α] [DecidableEq α] in
/-- A maximum independent set of the neighbourhood of `v`, as a `Finset α`. -/
lemma exists_indep_nbhd (v : α) : ∃ I : Finset α, I.card = indepNeighborsCard G v ∧
    (∀ x ∈ I, G.Adj v x) ∧ (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) := by
  classical
  obtain ⟨s, hs⟩ := (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum
  refine ⟨s.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · rw [Finset.card_map]; exact hs.card_eq
  · intro x hx
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  · intro x hx y hy hadj
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hne : x' ≠ y' := fun h => hadj.ne (by rw [h])
    exact hs.isIndepSet (Finset.mem_coe.mpr hx') (Finset.mem_coe.mpr hy') hne (by simpa using hadj)

/-! ### The core construction -/

/-- `w`, a maximum independent set `I` of `N(w)`, the vertices of a shortest `w`–`a` path in
layers `2, …, p` and the vertices of a shortest `w`–`c` path in layers `m, …, q` induce a
bipartite subgraph. Here `p = dist(w,a)`, `q = dist(w,c)` and `m = max 2 (t+1)` with
`t = ⌊(p + q + 1 - dist(a,c)) / 2⌋`. -/
lemma core (hc : G.Connected) (w a c : α) :
    1 + indepNeighborsCard G w + (G.dist w a - 1) +
      (G.dist w c + 1 - max 2 ((G.dist w a + G.dist w c + 1 - G.dist a c) / 2 + 1))
      ≤ largestInducedBipartiteSubgraphSize G := by
  classical
  obtain ⟨I, hIcard, hIadj, hIind⟩ := exists_indep_nbhd (G := G) w
  set p := G.dist w a with hp
  set q := G.dist w c with hq
  set D := G.dist a c with hD
  set t := (p + q + 1 - D) / 2 with ht
  set m := max 2 (t + 1) with hm
  have hm2 : 2 ≤ m := le_max_left _ _
  have hmt : t + 1 ≤ m := le_max_right _ _
  -- choice of path vertices
  have hf : ∀ j : ℕ, ∃ x, j ≤ p → G.dist w x = j ∧ G.dist x a = p - j := fun j => by
    by_cases hj : j ≤ p
    · obtain ⟨x, hx⟩ := exists_split hc w a j hj; exact ⟨x, fun _ => hx⟩
    · exact ⟨w, fun h => absurd h hj⟩
  have hg : ∀ j : ℕ, ∃ x, j ≤ q → G.dist w x = j ∧ G.dist x c = q - j := fun j => by
    by_cases hj : j ≤ q
    · obtain ⟨x, hx⟩ := exists_split hc w c j hj; exact ⟨x, fun _ => hx⟩
    · exact ⟨w, fun h => absurd h hj⟩
  choose f hf using hf
  choose g hg using hg
  -- deep layers: the two path vertices are distinct and non-adjacent
  have key : ∀ j, t + 1 ≤ j → j ≤ p → j ≤ q → f j ≠ g j ∧ ¬ G.Adj (f j) (g j) := by
    intro j hj1 hjp hjq
    have hfa := (hf j hjp).2
    have hgc := (hg j hjq).2
    have tri : D ≤ G.dist a (f j) + G.dist (f j) (g j) + G.dist (g j) c := by
      have h1 := hc.dist_triangle (u := a) (v := f j) (w := c)
      have h2 := hc.dist_triangle (u := f j) (v := g j) (w := c)
      omega
    rw [dist_comm] at tri
    have hlt : ¬ G.dist (f j) (g j) ≤ 1 := by omega
    refine ⟨fun h => hlt (by rw [h, dist_self]; omega), fun h => hlt ?_⟩
    rw [dist_eq_one_iff_adj.mpr h]
  set A := (Finset.Icc 2 p).image f with hA
  set C := (Finset.Icc m q).image g with hC
  have hmemA : ∀ x ∈ A, ∃ j, 2 ≤ j ∧ j ≤ p ∧ x = f j ∧ G.dist w x = j := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_Icc] at hj
    exact ⟨j, hj.1, hj.2, rfl, (hf j hj.2).1⟩
  have hmemC : ∀ x ∈ C, ∃ j, m ≤ j ∧ j ≤ q ∧ x = g j ∧ G.dist w x = j := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_Icc] at hj
    exact ⟨j, hj.1, hj.2, rfl, (hg j hj.2).1⟩
  have hdistI : ∀ x ∈ I, G.dist w x = 1 := fun x hx => dist_eq_one_iff_adj.mpr (hIadj x hx)
  have hcardA : A.card = p - 1 := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro i hi j hj hij
      simp only [Finset.coe_Icc, Set.mem_Icc] at hi hj
      have := (hf i hi.2).1; have := (hf j hj.2).1
      have hij' : G.dist w (f i) = G.dist w (f j) := by rw [hij]
      omega
  have hcardC : C.card = q + 1 - m := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    intro i hi j hj hij
    simp only [Finset.coe_Icc, Set.mem_Icc] at hi hj
    have := (hg i hi.2).1; have := (hg j hj.2).1
    have hij' : G.dist w (g i) = G.dist w (g j) := by rw [hij]
    omega
  -- disjointness
  have hIA : Disjoint I A := by
    rw [Finset.disjoint_left]
    intro x hxI hxA
    obtain ⟨j, hj2, -, -, hjd⟩ := hmemA x hxA
    have := hdistI x hxI; omega
  have hIC : Disjoint I C := by
    rw [Finset.disjoint_left]
    intro x hxI hxC
    obtain ⟨j, hj2, -, -, hjd⟩ := hmemC x hxC
    have := hdistI x hxI; omega
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro x hxA hxC
    obtain ⟨i, hi2, hip, rfl, hid⟩ := hmemA x hxA
    obtain ⟨j, hjm, hjq, hij, hjd⟩ := hmemC (f i) hxC
    have hij' : i = j := by omega
    subst hij'
    exact (key i (by omega) hip hjq).1 hij
  have hw : w ∉ I ∪ A ∪ C := by
    simp only [Finset.mem_union, not_or]
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
    · have := hdistI w h; simp at this
    · obtain ⟨j, hj2, -, -, hjd⟩ := hmemA w h; simp at hjd; omega
    · obtain ⟨j, hj2, -, -, hjd⟩ := hmemC w h; simp at hjd; omega
  have hcard : (insert w (I ∪ A ∪ C)).card = 1 + indepNeighborsCard G w + (p - 1) + (q + 1 - m) := by
    rw [Finset.card_insert_of_notMem hw, Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨hIC, hAC⟩), Finset.card_union_of_disjoint hIA,
      hcardA, hcardC, hIcard]
    ring
  rw [← hcard]
  -- the layer condition
  apply card_le_of_layers w
  intro x hx y hy hadj heq
  have hxy : x ≠ y := hadj.ne
  simp only [Finset.mem_insert, Finset.mem_union] at hx hy
  have d0 : ∀ z, z = w → G.dist w z = 0 := fun z hz => by rw [hz, dist_self]
  rcases hx with hx | (hx | hx) | hx <;> rcases hy with hy | (hy | hy) | hy
  · exact hxy (hx.trans hy.symm)
  · have := d0 x hx; have := hdistI y hy; omega
  · have := d0 x hx; obtain ⟨j, hj2, -, -, hjd⟩ := hmemA y hy; omega
  · have := d0 x hx; obtain ⟨j, hj2, -, -, hjd⟩ := hmemC y hy; omega
  · have := d0 y hy; have := hdistI x hx; omega
  · exact hIind x hx y hy hadj
  · have := hdistI x hx; obtain ⟨j, hj2, -, -, hjd⟩ := hmemA y hy; omega
  · have := hdistI x hx; obtain ⟨j, hj2, -, -, hjd⟩ := hmemC y hy; omega
  · have := d0 y hy; obtain ⟨j, hj2, -, -, hjd⟩ := hmemA x hx; omega
  · have := hdistI y hy; obtain ⟨j, hj2, -, -, hjd⟩ := hmemA x hx; omega
  · obtain ⟨i, -, -, hxi, hid⟩ := hmemA x hx
    obtain ⟨j, -, -, hyj, hjd⟩ := hmemA y hy
    have hij : i = j := by omega
    exact hxy (by rw [hxi, hyj, hij])
  · obtain ⟨i, hi2, hip, hxi, hid⟩ := hmemA x hx
    obtain ⟨j, hjm, hjq, hyj, hjd⟩ := hmemC y hy
    have hij : i = j := by omega
    rw [hxi, hyj, ← hij] at hadj
    exact (key i (by omega) hip (by omega)).2 hadj
  · have := d0 y hy; obtain ⟨j, hj2, -, -, hjd⟩ := hmemC x hx; omega
  · have := hdistI y hy; obtain ⟨j, hj2, -, -, hjd⟩ := hmemC x hx; omega
  · obtain ⟨i, him, hiq, hxi, hid⟩ := hmemC x hx
    obtain ⟨j, hj2, hjp, hyj, hjd⟩ := hmemA y hy
    have hij : i = j := by omega
    rw [hxi, hyj, ← hij] at hadj
    exact (key i (by omega) (by omega) hiq).2 hadj.symm
  · obtain ⟨i, -, -, hxi, hid⟩ := hmemC x hx
    obtain ⟨j, -, -, hyj, hjd⟩ := hmemC y hy
    have hij : i = j := by omega
    exact hxy (by rw [hxi, hyj, hij])

/-- One shortest path: `dist(w, a) + α(N(w)) ≤ b(G)`. -/
lemma one_path (hc : G.Connected) (w a : α) :
    G.dist w a + indepNeighborsCard G w ≤ largestInducedBipartiteSubgraphSize G := by
  have h := core hc w a a
  rw [dist_self] at h
  have hm : G.dist w a + 1 ≤ max 2 ((G.dist w a + G.dist w a + 1 - 0) / 2 + 1) :=
    le_trans (by omega) (le_max_right _ _)
  omega

/-- Two shortest paths: `dist(a, c) + α(N(w)) ≤ b(G) + 1`. -/
lemma two_path (hc : G.Connected) (w a c : α) :
    G.dist a c + indepNeighborsCard G w ≤ largestInducedBipartiteSubgraphSize G + 1 := by
  have h := core hc w a c
  have htri := hc.dist_triangle (u := a) (v := w) (w := c)
  rw [dist_comm (u := a) (v := w)] at htri
  set p := G.dist w a
  set q := G.dist w c
  set D := G.dist a c
  set t := (p + q + 1 - D) / 2
  have hm := max_choice 2 (t + 1)
  have hm2 : 2 ≤ max 2 (t + 1) := le_max_left _ _
  have hmt : t + 1 ≤ max 2 (t + 1) := le_max_right _ _
  rcases hm with hm | hm <;> rw [hm] at h hm2 hmt <;> omega

/-! ### The conjecture -/

/--
WOWII [Conjecture 19](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

If `G` is connected then the size `b(G)` of a largest induced bipartite subgraph
satisfies
`b(G) ≥ FLOOR((∑ ecc(v))/(|V|) + sSup (range (l G)))`, where `ecc(v)` denotes
eccentricity and `l(G)` is the independence number of neighbourhoods.
-/
theorem conjecture19 (G : SimpleGraph α) [Nontrivial α] (h_conn : G.Connected) :
    ⌊(∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) +
      sSup (Set.range (indepNeighbors G))⌋ ≤ b G := by
  classical
  -- a vertex `w` with the largest neighbourhood independence number
  obtain ⟨w, -, hw⟩ :=
    Finset.exists_max_image Finset.univ (indepNeighborsCard G) Finset.univ_nonempty
  have hsup : sSup (Set.range (indepNeighbors G)) = (indepNeighborsCard G w : ℝ) := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨w, rfl⟩, ?_⟩
    rintro _ ⟨x, rfl⟩
    simp only [indepNeighbors]
    exact_mod_cast hw x (Finset.mem_univ x)
  -- the diameter `D` and a pair `a, c` realising it
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ (ecc G) Finset.univ_nonempty
  obtain ⟨c, hc⟩ := exists_dist_eq_ecc (G := G) a
  set D := ecc G a with hD
  set L := indepNeighborsCard G w with hL
  set N := largestInducedBipartiteSubgraphSize G with hN
  set n := Fintype.card α with hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) = ((∑ v, ecc G v : ℕ) : ℝ) := by
    push_cast; rfl
  have hle : ∑ v, ecc G v ≤ n * D := by
    calc ∑ v, ecc G v ≤ ∑ _v : α, D := Finset.sum_le_sum fun v _ => ha v (Finset.mem_univ v)
      _ = n * D := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hsup, hsum, b]
  set S := ∑ v, ecc G v with hS
  suffices h : ⌊(S : ℝ) / n + L⌋ ≤ (N : ℤ) by exact_mod_cast h
  by_cases he : ecc G w = D
  · -- `ecc(w) = D`: one path from `w` to a farthest vertex
    obtain ⟨z, hz⟩ := exists_dist_eq_ecc (G := G) w
    have h1 := one_path h_conn w z
    rw [hz, he] at h1
    have havg : (S : ℝ) / n ≤ D := by
      rw [div_le_iff₀ hn0]; exact_mod_cast (by linarith [hle] : S ≤ D * n)
    have : ⌊(S : ℝ) / n + L⌋ ≤ ((D + L : ℕ) : ℤ) := by
      rw [Int.floor_le_iff]; push_cast; linarith
    have h1' : ((D + L : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast h1
    linarith
  · -- `ecc(w) < D`: the average eccentricity is `< D`
    have hwD : ecc G w < D := lt_of_le_of_ne (ha w (Finset.mem_univ w)) he
    have hlt : ∑ v, ecc G v < n * D := by
      calc ∑ v, ecc G v < ∑ _v : α, D :=
            Finset.sum_lt_sum (fun v _ => ha v (Finset.mem_univ v)) ⟨w, Finset.mem_univ _, hwD⟩
        _ = n * D := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    have h2 := two_path h_conn w a c
    rw [hc] at h2
    have havg : (S : ℝ) / n < D := by
      rw [div_lt_iff₀ hn0]; exact_mod_cast (by linarith [hlt] : S < D * n)
    have : ⌊(S : ℝ) / n + L⌋ ≤ ((D + L : ℕ) : ℤ) - 1 := by
      rw [Int.floor_le_iff]; push_cast; linarith
    have h2' : ((D + L : ℕ) : ℤ) ≤ (N : ℤ) + 1 := by exact_mod_cast h2
    linarith

end WOWII19
