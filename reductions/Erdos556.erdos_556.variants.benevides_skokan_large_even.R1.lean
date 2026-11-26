import FormalConjectures.ErdosProblems.«556»
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import Mathlib.Combinatorics.Pigeonhole

/-! A four-block lower bound and cycle-embedding lemmas for large even cycles. -/

open SimpleGraph Filter

namespace OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1

-- Below 2n vertices, use three exceptional vertices and four equal blocks.
-- The two low bits distinguish the four blocks. After removing the exceptional
-- vertex of a colour, ordinary edges of that colour stay in pairs of blocks.
def H1 : Prop :=
  let colour (x y : ℕ) : Fin 3 :=
    if min x y < 3 then ⟨min x y % 3, Nat.mod_lt _ (by decide)⟩
    else if x % 2 = y % 2 then 0
    else if (x / 2) % 2 = (y / 2) % 2 then 1 else 2
  ∀ n : ℕ, 4 ≤ n → Even n → ∀ f : Fin n → ℕ, Function.Injective f →
    (∀ u, f u < 2 * n - 1) → ∀ i : Fin 3,
      ∃ u v, (cycleGraph n).Adj u v ∧ colour (f u) (f v) ≠ i

-- The forcing direction is a statement about a single host size for each n.
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, Even n →
    ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)),
      (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
        ∃ i, (cycleGraph n).IsContained (c i)


-- Deleting a single index from a cyclic order leaves the other indices
-- in path order. Rotate so that the omitted index is immediately before it.
lemma lowerColouringAvoidsCycle : H1 := by
  classical
  intro n hn he f hf hsize i
  let colour (x y : ℕ) : Fin 3 :=
    if min x y < 3 then ⟨min x y % 3, Nat.mod_lt _ (by decide)⟩
    else if x % 2 = y % 2 then 0
    else if x / 2 % 2 = y / 2 % 2 then 1 else 2
  change ∃ u v, (cycleGraph n).Adj u v ∧ colour (f u) (f v) ≠ i
  by_contra! hmono
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  obtain ⟨k, hk⟩ := he
  obtain ⟨a, ha⟩ : ∃ a : Fin (m + 4), ∀ u, f u = i.val → u = a := by
    by_cases hit : ∃ u, f u = i.val
    · obtain ⟨a, ha⟩ := hit
      exact ⟨a, fun _ hu => hf (hu.trans ha.symm)⟩
    · exact ⟨0, fun u hu => (hit ⟨u, hu⟩).elim⟩
  let pos (j : Fin (m + 3)) : Fin (m + 4) := a + j.succ
  have pos_inj : Function.Injective pos := by
    intro u v h
    exact Fin.succ_inj.mp (add_left_cancel (show a + u.succ = a + v.succ from h))
  let g (j : Fin (m + 3)) := f (pos j)
  have avoid (j) : g j ≠ i.val := by
    intro h
    have hpos := ha (pos j) h
    exact Fin.succ_ne_zero j (add_left_cancel
      (show a + j.succ = a + 0 from hpos.trans (add_zero a).symm))
  have edge (j : Fin (m + 2)) : colour (g j.castSucc) (g j.succ) = i := by
    apply hmono
    apply cycleGraph_adj.mpr
    right
    apply sub_eq_iff_eq_add.mpr
    change a + j.succ.succ = 1 + (a + j.castSucc.succ)
    rw [← Fin.coeSucc_eq_succ (a := j.succ), Fin.castSucc_succ]
    ac_rfl
  -- Within one colour, fixing the component leaves two ordinary
  -- residues per group of four. The second coordinate selects one of them.
  let key (c : Fin 3) (x : ℕ) : ℕ :=
    if c = 0 then x % 2 else if c = 1 then x / 2 % 2
    else if x % 2 = x / 2 % 2 then 0 else 1
  let bit (c : Fin 3) (x : ℕ) := if c = 0 then x / 2 % 2 else x % 2
  have pair {x y : ℕ} (hx : x ≠ i.val) (hy : y ≠ i.val)
      (hc : colour x y = i) : 3 ≤ x ∧ 3 ≤ y ∧ key i x = key i y := by
    by_cases hs : min x y < 3
    · have hv := congrArg Fin.val hc
      simp only [colour, if_pos hs, Nat.mod_eq_of_lt hs] at hv
      rw [min_def] at hv
      split at hv <;> contradiction
    · have hx3 : 3 ≤ x := le_trans (Nat.le_of_not_lt hs) (min_le_left _ _)
      have hy3 : 3 ≤ y := le_trans (Nat.le_of_not_lt hs) (min_le_right _ _)
      refine ⟨hx3, hy3, ?_⟩
      by_cases hp : x % 2 = y % 2
      · have hi : (0 : Fin 3) = i := by simpa only [colour, if_neg hs, if_pos hp] using hc
        simpa [← hi, key] using hp
      · by_cases hb : x / 2 % 2 = y / 2 % 2
        · have hi : (1 : Fin 3) = i := by simpa only [colour, if_neg hs, if_neg hp, if_pos hb] using hc
          simpa [← hi, key] using hb
        · have hi : (2 : Fin 3) = i := by simpa only [colour, if_neg hs, if_neg hp, if_neg hb] using hc
          rw [← hi]
          simp only [key, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, if_false]
          split_ifs <;> omega
  have links (j : Fin (m + 2)) := pair (avoid j.castSucc) (avoid j.succ) (edge j)
  have same (j : Fin (m + 3)) : 3 ≤ g j ∧ key i (g j) = key i (g 0) := by
    induction j using Fin.induction with
    | zero => exact ⟨(links 0).1, rfl⟩
    | succ j ih => exact ⟨(links j).2.1, (links j).2.2.symm.trans ih.2⟩
  let code (j : Fin (m + 3)) : Fin (m + 2) :=
    ⟨2 * ((g j - 3) / 4) + bit i (g j), by
      have := hsize (pos j)
      change g j < 2 * (m + 4) - 1 at this
      have := (same j).1
      dsimp [bit]
      split <;> omega⟩
  have inj : Function.Injective code := by
    intro u v huv
    apply pos_inj
    apply hf
    change g u = g v
    have hc := congrArg Fin.val huv
    change 2 * ((g u - 3) / 4) + bit i (g u) = 2 * ((g v - 3) / 4) + bit i (g v) at hc
    have heq := (same u).2.trans (same v).2.symm
    have hu := (same u).1
    have hv := (same v).1
    have bit_lt (x : ℕ) : bit i x < 2 := by dsimp [bit]; split <;> omega
    have bu := bit_lt (g u)
    have bv := bit_lt (g v)
    have row : (g u - 3) / 4 = (g v - 3) / 4 := by omega
    have lastBit : bit i (g u) = bit i (g v) := by omega
    have digits (x : ℕ) : x % 4 = x % 2 + 2 * (x / 2 % 2) := by
      have hd : x / 2 / 2 = x / 4 := Nat.div_div_eq_div_mul _ _ _
      omega
    have low : g u % 4 = g v % 4 := by
      rw [digits (g u), digits (g v)]
      fin_cases i <;> simp [key, bit] at heq lastBit <;> (try split_ifs at heq) <;> omega
    have xu := Nat.mod_add_div (g u) 4
    have xv := Nat.mod_add_div (g v) 4
    omega
  have impossible := Fintype.card_le_of_injective code inj
  simp only [Fintype.card_fin] at impossible
  omega

-- A sufficient embedding condition for an even cycle in one colour:
-- alternate two disjoint sets of k vertices across a complete bipartite pair.
lemma cycle_of_complete_pair {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (left right : Fin k ↪ V) (apart : ∀ a b, left a ≠ right b)
    (cross : ∀ a b, G.Adj (left a) (right b)) :
    (cycleGraph (2 * k)).IsContained G := by
  let half (u : Fin (2 * k)) : Fin k := ⟨u.val / 2, by have := u.isLt; omega⟩
  let place (u : Fin (2 * k)) := if u.val % 2 = 0 then left (half u) else right (half u)
  have opposite {a b : Fin (2 * k)} (h : (a - b).val = 1) : a.val % 2 ≠ b.val % 2 := by
    by_cases hle : b ≤ a
    · rw [Fin.sub_val_of_le hle] at h
      omega
    · rw [Fin.coe_sub_iff_lt.mpr (lt_of_not_ge hle)] at h
      have := b.isLt
      omega
  refine ⟨⟨⟨place, ?_⟩, ?_⟩⟩
  · intro a b hab
    have hop : a.val % 2 ≠ b.val % 2 := by
      rcases cycleGraph_adj'.mp hab with h | h
      · exact opposite h
      · exact Ne.symm (opposite h)
    dsimp only [place]
    split_ifs <;> first | exact cross _ _ | exact (cross _ _).symm | exfalso; omega
  · intro a b h
    change place a = place b at h
    dsimp only [place] at h
    split_ifs at h
    · have hh := congrArg Fin.val (left.injective h)
      change a.val / 2 = b.val / 2 at hh
      exact Fin.ext (by omega)
    · exact (apart _ _ h).elim
    · exact (apart _ _ h.symm).elim
    · have hh := congrArg Fin.val (right.injective h)
      change a.val / 2 = b.val / 2 at hh
      exact Fin.ext (by omega)

-- The right vertices are candidates for the gaps between successive left
-- vertices. Half-degree on both sides of this auxiliary graph gives Hall.
lemma matching_of_half_degrees {k : ℕ} (cand : Fin k → Finset (Fin k))
    (rows : ∀ j, k ≤ 2 * (cand j).card)
    (cols : ∀ v, k ≤ 2 * (Finset.univ.filter (fun j => v ∈ cand j)).card) :
    ∃ pick : Fin k → Fin k, Function.Injective pick ∧ ∀ j, pick j ∈ cand j := by
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' cand).mp
  intro s
  by_cases small : 2 * s.card ≤ k
  · by_cases hs : s.Nonempty
    · obtain ⟨j, hj⟩ := hs
      have hsub : cand j ⊆ s.biUnion cand :=
        fun v hv => Finset.mem_biUnion.mpr ⟨j, hj, hv⟩
      have := Finset.card_le_card hsub
      have := rows j
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
  · have hall : s.biUnion cand = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro v
      by_contra hv
      have hsub : Finset.univ.filter (fun j => v ∈ cand j) ⊆ sᶜ := by
        intro j hj
        apply Finset.mem_compl.mpr
        intro hjs
        exact hv (Finset.mem_biUnion.mpr ⟨j, hjs, (Finset.mem_filter.mp hj).2⟩)
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_compl, Fintype.card_fin] at hcard
      have := cols v
      have hsk : s.card ≤ k := by simpa using Finset.card_le_univ s
      omega
    rw [hall]
    exact Finset.card_le_univ s

-- A candidate for an odd cycle position must join each of its two even
-- neighbours. The relation allows unrelated cross-edges to be absent.
lemma cycle_from_gap_matching {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (left right : Fin k ↪ V) (apart : ∀ a b, left a ≠ right b)
    (pick : Fin k → Fin k) (hinj : Function.Injective pick)
    (fits : ∀ (a b : Fin (2 * k)) (u v : Fin k),
      a.val % 2 = 0 → b.val % 2 ≠ 0 → (cycleGraph (2 * k)).Adj a b →
      u.val = a.val / 2 → v.val = b.val / 2 → G.Adj (left u) (right (pick v))) :
    (cycleGraph (2 * k)).IsContained G := by
  let half (u : Fin (2 * k)) : Fin k := ⟨u.val / 2, by have := u.isLt; omega⟩
  let place (u : Fin (2 * k)) :=
    if u.val % 2 = 0 then left (half u) else right (pick (half u))
  have flip {a b : Fin (2 * k)} (h : (a - b).val = 1) : a.val % 2 ≠ b.val % 2 := by
    by_cases hle : b ≤ a
    · rw [Fin.sub_val_of_le hle] at h
      omega
    · rw [Fin.coe_sub_iff_lt.mpr (lt_of_not_ge hle)] at h
      have := b.isLt
      omega
  refine ⟨⟨⟨place, ?_⟩, ?_⟩⟩
  · intro a b hab
    have hop : a.val % 2 ≠ b.val % 2 :=
      (cycleGraph_adj'.mp hab).elim flip (fun h => Ne.symm (flip h))
    dsimp only [place]
    by_cases ha : a.val % 2 = 0
    · have hb : b.val % 2 ≠ 0 := by omega
      rw [if_pos ha, if_neg hb]
      exact fits a b (half a) (half b) ha hb hab rfl rfl
    · have hb : b.val % 2 = 0 := by omega
      rw [if_neg ha, if_pos hb]
      exact (fits b a (half b) (half a) hb ha hab.symm rfl rfl).symm
  · intro a b h
    change place a = place b at h
    dsimp only [place] at h
    split_ifs at h
    · have hh := congrArg Fin.val (left.injective h)
      change a.val / 2 = b.val / 2 at hh
      exact Fin.ext (by omega)
    · exact (apart _ _ h).elim
    · exact (apart _ _ h.symm).elim
    · have hh := congrArg Fin.val (hinj (right.injective h))
      change a.val / 2 = b.val / 2 at hh
      exact Fin.ext (by omega)

-- Consecutive rows with at least three quarters of the opposite vertices
-- in each neighbourhood have at least half in common. Applying the same
-- count to each column verifies the other side of Hall's condition.
lemma consecutive_common_representatives {k : ℕ} (next : Equiv.Perm (Fin k))
    (nb : Fin k → Finset (Fin k))
    (rows : ∀ j, 3 * k ≤ 4 * (nb j).card)
    (cols : ∀ v, 3 * k ≤ 4 * (Finset.univ.filter (fun j => v ∈ nb j)).card) :
    ∃ pick : Fin k → Fin k, Function.Injective pick ∧
      ∀ j, pick j ∈ nb j ∧ pick j ∈ nb (next j) := by
  classical
  have half {s t : Finset (Fin k)} (hs : 3 * k ≤ 4 * s.card) (ht : 3 * k ≤ 4 * t.card) :
      k ≤ 2 * (s ∩ t).card := by
    have h := Finset.card_union_add_card_inter s t
    have hmax : (s ∪ t).card ≤ k := by simpa using Finset.card_le_univ (s ∪ t)
    omega
  let cand (j : Fin k) := nb j ∩ nb (next j)
  have col (v : Fin k) : k ≤ 2 * (Finset.univ.filter (fun j => v ∈ cand j)).card := by
    let s := Finset.univ.filter (fun j => v ∈ nb j)
    let t := s.map next.symm.toEmbedding
    have ht (j : Fin k) : j ∈ t ↔ v ∈ nb (next j) := by
      change j ∈ s.map next.symm.toEmbedding ↔ _
      constructor
      · intro hj
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hj
        simpa [s] using hx
      · intro hj
        exact Finset.mem_map.mpr ⟨next j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩,
          next.symm_apply_apply j⟩
    have heq : Finset.univ.filter (fun j => v ∈ cand j) = s ∩ t := by
      ext j
      simp [s, cand, ht]
    rw [heq]
    apply half (cols v)
    simpa [t] using cols v
  obtain ⟨p, hp, hmem⟩ := matching_of_half_degrees cand
    (fun j => half (rows j) (rows (next j))) col
  exact ⟨p, hp, fun j => Finset.mem_inter.mp (hmem j)⟩

-- With at most one quarter of the cross-edges missing at each vertex,
-- use distinct common neighbours to close the prescribed cyclic left order.
lemma cycle_of_three_quarter_pair {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (left right : Fin (k + 1) ↪ V) (apart : ∀ a b, left a ≠ right b)
    (nb : Fin (k + 1) → Finset (Fin (k + 1)))
    (sound : ∀ a b, b ∈ nb a → G.Adj (left a) (right b))
    (rows : ∀ j, 3 * (k + 1) ≤ 4 * (nb j).card)
    (cols : ∀ v, 3 * (k + 1) ≤ 4 * (Finset.univ.filter (fun j => v ∈ nb j)).card) :
    (cycleGraph (2 * (k + 1))).IsContained G := by
  let next := Equiv.addRight (1 : Fin (k + 1))
  obtain ⟨pick, hinj, sides⟩ := consecutive_common_representatives next nb rows cols
  apply cycle_from_gap_matching G (k + 1) left right apart pick hinj
  intro a b u v ha hb hab hu hv
  have adjacent : u = v ∨ u = next v := by
    have ha' := a.isLt
    have hb' := b.isLt
    have hv' := v.isLt
    have hn : (next v).val = if v.val = k then 0 else v.val + 1 := by
      change (v + 1).val = _
      rw [Fin.val_add_one]
      simp only [Fin.ext_iff, Fin.val_last]
    simp only [Fin.ext_iff]
    rw [hn]
    rcases cycleGraph_adj'.mp hab with h | h
    · by_cases hle : b ≤ a
      · rw [Fin.sub_val_of_le hle] at h
        split_ifs <;> omega
      · rw [Fin.coe_sub_iff_lt.mpr (lt_of_not_ge hle)] at h
        split_ifs <;> omega
    · by_cases hle : a ≤ b
      · rw [Fin.sub_val_of_le hle] at h
        split_ifs <;> omega
      · rw [Fin.coe_sub_iff_lt.mpr (lt_of_not_ge hle)] at h
        split_ifs <;> omega
  rcases adjacent with h | h
  · rw [h]; exact sound _ _ (sides v).1
  · rw [h]; exact sound _ _ (sides v).2

-- From a budget of missing cross-edges, choose q rows each with at most
-- t missing edges. This can be applied on the two sides independently.
lemma select_low_defect (q r t : ℕ) (defect : Fin (q + r) → ℕ)
    (budget : ∑ x, defect x < (r + 1) * (t + 1)) :
    ∃ e : Fin q ↪ Fin (q + r), ∀ a, defect (e a) ≤ t := by
  classical
  let bad := Finset.univ.filter fun x => t < defect x
  have total : bad.card * (t + 1) ≤ ∑ x, defect x := by
    calc
      bad.card * (t + 1) = ∑ _x ∈ bad, (t + 1) := by simp
      _ ≤ ∑ x ∈ bad, defect x := Finset.sum_le_sum fun x hx =>
        Nat.succ_le_of_lt (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x, defect x := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have few : bad.card ≤ r := by
    by_contra! hr
    have hmul : (r + 1) * (t + 1) ≤ bad.card * (t + 1) := Nat.mul_le_mul_right _ hr
    exact (not_lt_of_ge (hmul.trans total)) budget
  have hc : q ≤ Fintype.card ↥(badᶜ : Finset (Fin (q+r))) := by
    simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨f⟩ : Nonempty (Fin q ↪ ↥(badᶜ : Finset (Fin (q+r)))) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hc)
  refine ⟨⟨fun a => (f a).val, Subtype.val_injective.comp f.injective⟩, ?_⟩
  intro a
  have ha := (f a).property
  simpa [bad] using ha

-- Each missing cross-edge contributes once to the row total and once to
-- the column total. With r spare vertices on either side, discard rows
-- and columns of excessive defect, then apply the three-quarter lemma.
lemma cycle_of_sparse_missing_edges {V : Type*} (G : SimpleGraph V) (k r : ℕ)
    (left right : Fin (k + 1 + r) ↪ V) (apart : ∀ a b, left a ≠ right b)
    (miss : Fin (k + 1 + r) → Finset (Fin (k + 1 + r)))
    (sound : ∀ a b, b ∉ miss a → G.Adj (left a) (right b))
    (budget : ∑ a, (miss a).card < (r + 1) * ((k + 1) / 4 + 1)) :
    (cycleGraph (2 * (k + 1))).IsContained G := by
  classical
  let col (b : Fin (k + 1 + r)) := Finset.univ.filter fun a => b ∈ miss a
  have eqtotal : ∑ b, (col b).card = ∑ a, (miss a).card := by
    calc
      _ = ∑ b, ∑ a : Fin (k + 1 + r), if b ∈ miss a then 1 else 0 := by
        simp [col, Finset.sum_boole]
      _ = ∑ a, ∑ b : Fin (k + 1 + r), if b ∈ miss a then 1 else 0 := Finset.sum_comm
      _ = _ := by simp
  obtain ⟨L, hL⟩ := select_low_defect (k + 1) r ((k + 1) / 4) (fun a => (miss a).card) budget
  obtain ⟨R, hR⟩ := select_low_defect (k + 1) r ((k + 1) / 4) (fun b => (col b).card)
    (by rw [eqtotal]; exact budget)
  let nb (a : Fin (k + 1)) := Finset.univ.filter fun b : Fin (k + 1) => R b ∉ miss (L a)
  apply cycle_of_three_quarter_pair G k (L.trans left) (R.trans right)
    (fun a b => apart (L a) (R b)) nb
  · intro a b hb
    exact sound _ _ (Finset.mem_filter.mp hb).2
  · intro a
    have sub : ((nb a)ᶜ).card ≤ (miss (L a)).card := by
      apply Finset.card_le_card_of_injOn R _ R.injective.injOn
      intro b hb
      simpa [nb] using hb
    rw [Finset.card_compl, Fintype.card_fin] at sub
    have := hL a
    omega
  · intro b
    let neighbours := Finset.univ.filter (fun a => b ∈ nb a)
    have sub : (neighboursᶜ).card ≤ (col (R b)).card := by
      apply Finset.card_le_card_of_injOn L _ L.injective.injOn
      intro a ha
      simpa [col, neighbours, nb] using ha
    rw [Finset.card_compl, Fintype.card_fin] at sub
    have := hR b
    change 3 * (k + 1) ≤ 4 * neighbours.card
    omega

-- An unconditional, coarse host bound. Group the right vertices by
-- their entire colour pattern towards 3q left vertices. Two applications
-- of pigeonhole yield a monochromatic complete q-by-q bipartite graph.
lemma constant_subsequence {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (f : A → B) (q : ℕ) (hsize : Fintype.card B * q ≤ Fintype.card A) :
    ∃ b : B, ∃ e : Fin q ↪ A, ∀ j, f (e j) = b := by
  classical
  obtain ⟨b, hb⟩ := Fintype.exists_le_card_fiber_of_mul_le_card f hsize
  let s := Finset.univ.filter fun a => f a = b
  obtain ⟨e⟩ : Nonempty (Fin q ↪ ↥s) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin, Fintype.card_coe]; exact hb)
  exact ⟨b, ⟨fun j => (e j).val, Subtype.val_injective.comp e.injective⟩,
    fun j => (Finset.mem_filter.mp (e j).property).2⟩

lemma even_cycle_forcing_host (q : ℕ) :
    ∀ c : Fin 3 → SimpleGraph (Fin (3 * q + 3 ^ (3 * q) * q)),
      (⊤ : SimpleGraph _).IsEdgeColouring c → ∃ i, (cycleGraph (2 * q)).IsContained (c i) := by
  classical
  let l := 3 * q
  let r := 3 ^ l * q
  intro c hc
  let L : Fin l ↪ Fin (l + r) :=
    ⟨fun a => ⟨a.val, by have := a.isLt; omega⟩,
      fun a b h => Fin.ext (congrArg (fun z : Fin (l + r) => z.val) h)⟩
  let R : Fin r ↪ Fin (l + r) :=
    ⟨fun b => ⟨l + b.val, by have := b.isLt; omega⟩, by
      intro a b h
      apply Fin.ext
      exact Nat.add_left_cancel (congrArg Fin.val h)⟩
  have apart (a : Fin l) (b : Fin r) : L a ≠ R b := by
    intro h
    have heq := congrArg Fin.val h
    change a.val = l + b.val at heq
    have := a.isLt
    omega
  have covered (b : Fin r) (a : Fin l) : ∃ i, (c i).Adj (L a) (R b) := by
    apply iSup_adj.mp
    rw [← hc.1]
    exact (top_adj _ _).mpr (apart _ _)
  let pattern (b : Fin r) (a : Fin l) : Fin 3 := (covered b a).choose
  obtain ⟨word, cols, hcols⟩ := constant_subsequence pattern q
    (by simp [r])
  obtain ⟨i, rows, hrows⟩ := constant_subsequence word q (by simp [l])
  refine ⟨i, cycle_of_complete_pair (c i) q (rows.trans L) (cols.trans R)
    (fun a b => apart _ _) ?_⟩
  intro a b
  have he := (covered (cols b) (rows a)).choose_spec
  change (c (pattern (cols b) (rows a))).Adj (L (rows a)) (R (cols b)) at he
  rw [hcols b, hrows a] at he
  exact he

lemma even_cycle_global_upper (q : ℕ) :
    multicolourRamsey (cycleGraph (2 * q)) 3 ≤ 3 * q + 3 ^ (3 * q) * q := by
  apply Nat.sInf_le
  exact even_cycle_forcing_host q

lemma even_cycle_lower_bound (n : ℕ) (hfour : 4 ≤ n) (heven : Even n) :
    2 * n ≤ multicolourRamsey (cycleGraph n) 3 := by
  classical
  have hbad := lowerColouringAvoidsCycle
  let S : Set ℕ := {N | ∀ c : Fin 3 → SimpleGraph (Fin N),
    (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c → ∃ i, (cycleGraph n).IsContained (c i)}
  change 2 * n ≤ sInf S
  have hne : S.Nonempty := by
    obtain ⟨q, hq⟩ := heven
    have h : n = 2 * q := by omega
    refine ⟨3 * q + 3 ^ (3 * q) * q, ?_⟩
    dsimp only [S, Set.mem_setOf_eq]
    rw [h]
    exact even_cycle_forcing_host q
  refine le_csInf hne ?_
  intro N hN
  by_contra! hsmall
  let colour (x y : ℕ) : Fin 3 :=
    if min x y < 3 then ⟨min x y % 3, Nat.mod_lt _ (by decide)⟩
    else if x % 2 = y % 2 then 0
    else if (x / 2) % 2 = (y / 2) % 2 then 1 else 2
  have sym (x y : ℕ) : colour x y = colour y x := by
    unfold colour
    rw [min_comm y x]
    by_cases hp : x % 2 = y % 2
    · simp only [if_pos hp, if_pos hp.symm]
    · by_cases hb : x / 2 % 2 = y / 2 % 2
      · simp only [if_neg hp, if_neg (Ne.symm hp), if_pos hb, if_pos hb.symm]
      · simp only [if_neg hp, if_neg (Ne.symm hp), if_neg hb, if_neg (Ne.symm hb)]
  let c (i : Fin 3) : SimpleGraph (Fin N) :=
    { Adj := fun x y => x ≠ y ∧ colour x.val y.val = i
      symm := ⟨fun x y h => ⟨h.1.symm, (sym x.val y.val).symm.trans h.2⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  have hc : (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c := by
    constructor
    · ext x y
      rw [top_adj, iSup_adj]
      exact ⟨fun h => ⟨colour x.val y.val, h, rfl⟩, fun ⟨_, h⟩ => h.1⟩
    · intro i j hij
      apply disjoint_iff_inf_le.mpr
      intro x y h
      exact (hij (h.1.2.symm.trans h.2.2)).elim
  obtain ⟨i, ⟨copy⟩⟩ := hN c hc
  obtain ⟨u, v, huv, hdiff⟩ := hbad n hfour heven (fun u => (copy u).val)
    (Fin.val_injective.comp copy.injective) (fun u => by have := (copy u).isLt; omega) i
  exact hdiff (copy.toHom.map_adj huv).2

section RegularPairs

open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  {S T : Finset V} {ε : ℚ}

/-- In any two sufficiently large subclusters of a regular pair, one can choose
a vertex in the first with the expected number of neighbours in the second. -/
lemma regular_pair_choose {A B : Finset V} (hreg : G.IsUniform ε S T)
    (hd : ε ≤ G.edgeDensity S T) (hA : A ⊆ S) (hB : B ⊆ T)
    (hsizeA : (S.card : ℚ) * ε ≤ A.card) (hsizeB : (T.card : ℚ) * ε ≤ B.card) :
    ∃ a ∈ A, (G.edgeDensity S T - ε) * B.card < ((B.filter (G.Adj a)).card : ℚ) := by
  classical
  by_contra! hall
  have hu := (abs_lt.mp (hreg hA hB hsizeA hsizeB)).1
  have hsum : ((G.interedges A B).card : ℚ) ≤
      (A.card : ℚ) * ((G.edgeDensity S T - ε) * B.card) := by
    calc
      ((G.interedges A B).card : ℚ) ≤ ∑ a ∈ A, ((B.filter (G.Adj a)).card : ℚ) := by
        change ((Rel.interedges G.Adj A B).card : ℚ) ≤ _
        rw [Rel.interedges_eq_biUnion]
        exact_mod_cast (show _ ≤ ∑ a ∈ A, (B.filter (G.Adj a)).card from
          (card_biUnion_le).trans_eq (by simp))
      _ ≤ _ := by simpa using (sum_le_sum hall)
  have hden : G.edgeDensity A B ≤ G.edgeDensity S T - ε := by
    rw [edgeDensity_def]
    apply div_le_of_le_mul₀ (by positivity) (sub_nonneg.mpr hd)
    linarith only [hsum, show (A.card : ℚ) * ((G.edgeDensity S T - ε) * B.card) =
        (G.edgeDensity S T - ε) * (A.card * B.card) by ring]
  linarith

/-- A regular pair joins any two eligible subclusters by an edge. -/
lemma regular_pair_edge {A B : Finset V} (hreg : G.IsUniform ε S T)
    (hd : ε ≤ G.edgeDensity S T) (hA : A ⊆ S) (hB : B ⊆ T)
    (hsizeA : (S.card : ℚ) * ε ≤ A.card) (hsizeB : (T.card : ℚ) * ε ≤ B.card) :
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a b := by
  obtain ⟨a, ha, h⟩ := regular_pair_choose G hreg hd hA hB hsizeA hsizeB
  have hpos : (0 : ℚ) < (B.filter (G.Adj a)).card :=
    lt_of_le_of_lt (mul_nonneg (sub_nonneg.mpr hd) (Nat.cast_nonneg _)) h
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < (B.filter (G.Adj a)).card by exact_mod_cast hpos)
  exact ⟨a, ha, b, (mem_filter.mp hb).1, (mem_filter.mp hb).2⟩

end RegularPairs

theorem main : H1 → H2 → type_of% @Erdos556.erdos_556.variants.benevides_skokan_large_even := by
  intro _ hforce
  unfold H2 at hforce
  filter_upwards [hforce, eventually_ge_atTop 4] with n hn hfour
  intro heven
  refine le_antisymm ?_ (even_cycle_lower_bound n hfour heven)
  apply Nat.sInf_le
  exact hn heven

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1
