import FormalConjectures.ErdosProblems.«556»
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
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
  have hu : -ε < G.edgeDensity A B - G.edgeDensity S T := by
    simpa using (abs_lt.mp (hreg hA hB hsizeA hsizeB)).1
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

section RegularPaths

open Finset

/-- Grow a path two vertices at a time in a regular pair, leaving a set of
neighbours of the far endpoint untouched for the closing edge. The internal
vertices stay in the supplied pools, so vertices of an existing embedding
can be excluded in advance. -/
lemma regular_pair_odd_path {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {S T : Finset V} {ε : ℚ}
    (hreg : G.IsUniform ε S T) (hd : ε ≤ G.edgeDensity S T) (hst : Disjoint S T)
    (k m : ℕ) (hs : (S.card : ℚ) * ε ≤ k) (ht : (T.card : ℚ) * ε ≤ k)
    (hkm : k ≤ m) (hdegree : (k : ℚ) ≤ (G.edgeDensity S T - ε) * m)
    {R : Finset V} {y : V} (hR : R ⊆ S) (hrsize : k ≤ R.card) (hy : y ∈ T)
    (hRy : ∀ z ∈ R, G.Adj z y)
    (r : ℕ) (A B : Finset V) (x : V) (ha : A ⊆ S) (hb : B ⊆ T)
    (har : Disjoint A R) (hx : x ∈ S) (hxa : x ∉ A) (hxr : x ∉ R) (hyb : y ∉ B)
    (hA : m + r ≤ A.card) (hB : m + r ≤ B.card)
    (hxB : k ≤ (B.filter (G.Adj x)).card) :
    ∃ l : List V, l.length = 2 * r + 2 ∧
      (x :: (l ++ [y])).Nodup ∧ (x :: (l ++ [y])).IsChain G.Adj ∧
      ∀ z ∈ l, z ∈ A ∨ z ∈ B ∨ z ∈ R := by
  classical
  have separate : ∀ {u v}, u ∈ S → v ∈ T → u ≠ v := by
    rintro u v hu hv rfl
    exact Finset.disjoint_left.mp hst hu hv
  induction r generalizing A B x with
  | zero =>
    obtain ⟨a, haR, b, hbN, hab⟩ := regular_pair_edge G hreg hd hR
      ((filter_subset _ _).trans hb) (hs.trans (by exact_mod_cast hrsize))
      (ht.trans (by exact_mod_cast hxB))
    obtain ⟨hbin, hxb⟩ := mem_filter.mp hbN
    have hxb' := separate hx (hb hbin)
    have hxy := separate hx hy
    have hab' := separate (hR haR) (hb hbin)
    have hay := separate (hR haR) hy
    have hxa' : x ≠ a := fun e => hxr (e ▸ haR)
    have hby : b ≠ y := fun e => hyb (e ▸ hbin)
    refine ⟨[b, a], by simp, ?_, ?_, ?_⟩
    · simp [hxb', hxa', hxy, hab'.symm, hby, hay]
    · simp [List.isChain_cons_cons, hxb, hab.symm, hRy a haR]
    · intro z hz
      simp at hz
      rcases hz with rfl | rfl <;> tauto
  | succ r ih =>
    have size {U : Finset V} (hu : m ≤ U.card) :
        (k : ℚ) ≤ (G.edgeDensity S T - ε) * U.card :=
      hdegree.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hu) (sub_nonneg.mpr hd))
    have hswap : ε ≤ G.edgeDensity T S := by rwa [G.edgeDensity_comm T S]
    obtain ⟨b, hbN, hbn⟩ := regular_pair_choose G hreg.symm hswap
      ((filter_subset _ _).trans hb) ha (ht.trans (by exact_mod_cast hxB))
      (hs.trans (by exact_mod_cast (show k ≤ A.card by omega)))
    obtain ⟨hbin, hxb⟩ := mem_filter.mp hbN
    rw [G.edgeDensity_comm T S] at hbn
    have hbA : (k : ℚ) ≤ (A.filter (G.Adj b)).card :=
      (size (by omega : m ≤ A.card)).trans hbn.le
    have hBerase : m + r ≤ (B.erase b).card := by rw [card_erase_of_mem hbin]; omega
    obtain ⟨a, haN, han⟩ := regular_pair_choose G hreg hd
      ((filter_subset _ _).trans ha) ((erase_subset _ _).trans hb)
      (hs.trans hbA) (ht.trans (by exact_mod_cast (show k ≤ (B.erase b).card by omega)))
    obtain ⟨hain, hba⟩ := mem_filter.mp haN
    have hax : k ≤ ((B.erase b).filter (G.Adj a)).card := by
      exact_mod_cast (size (by omega : m ≤ (B.erase b).card)).trans han.le
    have hAerase : m + r ≤ (A.erase a).card := by rw [card_erase_of_mem hain]; omega
    have haR := Finset.disjoint_left.mp har hain
    obtain ⟨l, hl, hsimple, hchain, hpool⟩ := ih (A.erase a) (B.erase b) a
      ((erase_subset _ _).trans ha) ((erase_subset _ _).trans hb)
      (har.mono_left (erase_subset _ _)) (ha hain) (notMem_erase _ _) haR
      (fun h => hyb (erase_subset _ _ h)) hAerase hBerase hax
    have hxl : x ∉ l := by
      intro h
      rcases hpool x h with h | h | h
      · exact hxa (erase_subset _ _ h)
      · exact separate hx (hb (erase_subset _ _ h)) rfl
      · exact hxr h
    have hbl : b ∉ l := by
      intro h
      rcases hpool b h with h | h | h
      · exact separate (ha (erase_subset _ _ h)) (hb hbin) rfl
      · exact notMem_erase _ _ h
      · exact separate (hR h) (hb hbin) rfl
    have hxa' : x ≠ a := fun e => hxa (e ▸ hain)
    have hby : b ≠ y := fun e => hyb (e ▸ hbin)
    have hxb' := separate hx (hb hbin)
    have hba' := (separate (ha hain) (hb hbin)).symm
    have hxy := separate hx hy
    refine ⟨b :: a :: l, by simp [hl]; omega, ?_, ?_, ?_⟩
    · change (x :: b :: a :: (l ++ [y])).Nodup
      exact List.nodup_cons.mpr ⟨by simp [hxb', hxa', hxl, hxy],
        List.nodup_cons.mpr ⟨by simp [hba', hbl, hby], hsimple⟩⟩
    · exact List.isChain_cons_cons.mpr ⟨hxb, List.isChain_cons_cons.mpr ⟨hba, hchain⟩⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inr (Or.inl hbin)
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inl hain
      rcases hpool z hz with h | h | h
      · exact Or.inl (erase_subset _ _ h)
      · exact Or.inr (Or.inl (erase_subset _ _ h))
      · exact Or.inr (Or.inr h)

end RegularPaths

/-- Close an embedded simple path with an edge between its endpoints. -/
lemma cycle_of_closed_chain {V : Type*} (G : SimpleGraph V) {x y : V} {l : List V}
    (hlen : 0 < l.length) (hpath : (x :: (l ++ [y])).Nodup)
    (hchain : (x :: (l ++ [y])).IsChain G.Adj) (hclose : G.Adj y x) :
    (cycleGraph (l.length + 2)).IsContained G := by
  let L := (x :: l) ++ [y]
  have hn : L ≠ [] := by simp [L]
  let p := Walk.ofSupport L hn hchain
  have hlast : L.getLast hn = y := by simp [L]
  have hedge : G.Adj (L.getLast hn) (L.head hn) := hlast ▸ hclose
  have hp : p.IsPath := Walk.IsPath.mk' ((Walk.support_ofSupport hn hchain).symm ▸ (show L.Nodup from hpath))
  have hlen' : p.length = l.length + 1 := by
    calc
      p.length = L.length - 1 := Walk.length_ofSupport hn hchain
      _ = _ := by simp [L]
  apply (cycleGraph_isContained_iff (by omega)).mpr
  refine ⟨_, Walk.cons hedge p, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, ?_⟩, ?_⟩
  · simpa using hp
  · rw [Walk.length_cons, hlen']; omega
  · rw [Walk.length_cons, hlen']


/-- The endpoint form of the regular-pair path lemma. Either endpoint may be
prescribed, even when the endpoints have no edge between them. -/
lemma regular_pair_path_between {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T : Finset V} {ε : ℚ}
    (hreg : G.IsUniform ε S T) (hd : ε ≤ G.edgeDensity S T) (hst : Disjoint S T)
    (k m r : ℕ) (hs : (S.card : ℚ) * ε ≤ k) (ht : (T.card : ℚ) * ε ≤ k)
    (hkm : k ≤ m) (hdegree : (k : ℚ) ≤ (G.edgeDensity S T - ε) * m)
    (hA : m + r + k + 1 ≤ S.card) (hB : m + r + 1 ≤ T.card)
    {x y : V} (hx : x ∈ S) (hy : y ∈ T)
    (hxdeg : k < (T.filter (G.Adj x)).card) (hycard : k < (S.filter (G.Adj y)).card) :
    ∃ l : List V, l.length = 2 * r + 2 ∧ (x :: (l ++ [y])).Nodup ∧
      (x :: (l ++ [y])).IsChain G.Adj ∧ ∀ z ∈ l, z ∈ S ∨ z ∈ T := by
  classical
  have herase : k ≤ ((S.filter (G.Adj y)).erase x).card := by
    exact (show k ≤ (S.filter (G.Adj y)).card - 1 by omega).trans Finset.pred_card_le_card_erase
  obtain ⟨R, hR, hRcard⟩ := Finset.exists_subset_card_eq herase
  have hRS : R ⊆ S := hR.trans ((Finset.erase_subset _ _).trans (Finset.filter_subset _ _))
  have hxR : x ∉ R := fun h => Finset.notMem_erase _ _ (hR h)
  have hRy : ∀ z ∈ R, G.Adj z y := fun z hz =>
    (Finset.mem_filter.mp (Finset.erase_subset _ _ (hR hz))).2.symm
  let A := (S.erase x) \ R
  let B := T.erase y
  have hAsub : A ⊆ S.erase x := Finset.sdiff_subset
  have hAsize : m + r ≤ A.card := by
    have h := Finset.le_card_sdiff R (S.erase x)
    rw [Finset.card_erase_of_mem hx, hRcard] at h
    change m + r ≤ ((S.erase x) \ R).card
    omega
  have hBsize : m + r ≤ B.card := by
    dsimp [B]; rw [Finset.card_erase_of_mem hy]; omega
  have hNB : k ≤ (B.filter (G.Adj x)).card := by
    have heq : B.filter (G.Adj x) = (T.filter (G.Adj x)).erase y := by
      ext z; simp [B, and_assoc]
    rw [heq]
    exact (show k ≤ (T.filter (G.Adj x)).card - 1 by omega).trans Finset.pred_card_le_card_erase
  obtain ⟨l, hl, hsimple, hchain, hpool⟩ := regular_pair_odd_path G hreg hd hst k m hs ht hkm hdegree
    hRS hRcard.ge hy hRy r A B x (hAsub.trans (Finset.erase_subset _ _)) (Finset.erase_subset _ _)
    (Finset.disjoint_left.mpr (fun _ ha hr => (Finset.mem_sdiff.mp ha).2 hr))
    hx (fun h => Finset.notMem_erase _ _ (hAsub h)) hxR (Finset.notMem_erase _ _) hAsize hBsize hNB
  refine ⟨l, hl, hsimple, hchain, ?_⟩
  intro z hz
  rcases hpool z hz with h | h | h
  · exact Or.inl (Finset.erase_subset _ _ (hAsub h))
  · exact Or.inr (Finset.erase_subset _ _ h)
  · exact Or.inl (hRS h)

/-- A single regular dense pair contains every even cycle length allowed by
the unused-vertex budget. Both endpoints and the reserved neighbourhood are
chosen inside the pair. -/
lemma cycle_of_regular_pair {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T : Finset V} {ε : ℚ}
    (hreg : G.IsUniform ε S T) (hd : ε ≤ G.edgeDensity S T) (hst : Disjoint S T)
    (k m r : ℕ) (hs : (S.card : ℚ) * ε ≤ k) (ht : (T.card : ℚ) * ε ≤ k)
    (hkm : k ≤ m) (hdegree : (k : ℚ) ≤ (G.edgeDensity S T - ε) * m)
    (hA : m + r + k + 1 ≤ S.card) (hB : m + r + 1 ≤ T.card) :
    (cycleGraph (2 * r + 4)).IsContained G := by
  classical
  have size {U : Finset V} (hu : m ≤ U.card) :
      (k : ℚ) ≤ (G.edgeDensity S T - ε) * U.card :=
    hdegree.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hu) (sub_nonneg.mpr hd))
  obtain ⟨x, hx, hxN⟩ := regular_pair_choose G hreg hd (Finset.Subset.refl S) (Finset.Subset.refl T)
    (hs.trans (by exact_mod_cast (show k ≤ S.card by omega)))
    (ht.trans (by exact_mod_cast (show k ≤ T.card by omega)))
  have hxdeg : k < (T.filter (G.Adj x)).card := by
    exact_mod_cast (size (by omega : m ≤ T.card)).trans_lt hxN
  have hswap : ε ≤ G.edgeDensity T S := by rwa [G.edgeDensity_comm T S]
  obtain ⟨y, hyN, hydeg⟩ := regular_pair_choose G hreg.symm hswap
    (Finset.filter_subset _ _) (Finset.Subset.refl S) (ht.trans (by exact_mod_cast hxdeg.le))
    (hs.trans (by exact_mod_cast (show k ≤ S.card by omega)))
  rw [G.edgeDensity_comm T S] at hydeg
  obtain ⟨hy, hxy⟩ := Finset.mem_filter.mp hyN
  have hycard : k < (S.filter (G.Adj y)).card := by
    exact_mod_cast (size (by omega : m ≤ S.card)).trans_lt hydeg
  obtain ⟨l, hl, hsimple, hchain, _⟩ := regular_pair_path_between G hreg hd hst k m r hs ht hkm hdegree
    hA hB hx hy hxdeg hycard
  rw [← (show l.length + 2 = 2 * r + 4 by omega)]
  exact cycle_of_closed_chain G (by omega : 0 < l.length) hsimple hchain hxy.symm

/-- Quantitative fixed-endpoint path embedding (Benevides, thesis, Lemma 3.3,
in the small-density range used for the reduced graph). The largeness
condition is explicit. Here length counts edges. -/
lemma regular_pair_path_length_range {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T : Finset V} {ε α : ℚ} {n l : ℕ}
    (hS : S.card = n) (hT : T.card = n) (hst : Disjoint S T)
    (hreg : G.IsUniform ε S T) (hd : α / 4 ≤ G.edgeDensity S T)
    (ha : 0 < α) (ha' : α ≤ 1/2) (he : 0 < ε) (he' : ε ≤ α / 100)
    (hlarge : 100 ≤ (n : ℚ) * ε)
    {x y : V} (hx : x ∈ S) (hy : y ∈ T)
    (hxdeg : α * n / 5 ≤ ((T.filter (G.Adj x)).card : ℚ))
    (hydeg : α * n / 5 ≤ ((S.filter (G.Adj y)).card : ℚ))
    (hl : 1 ≤ l) (hrange : (l : ℚ) + 5 * ((n : ℚ) * ε / α) ≤ n) :
    ∃ p : G.Walk x y, p.IsPath ∧ p.length = 2 * l + 1 ∧
      ∀ z ∈ p.support, z ∈ S ∨ z ∈ T := by
  let t : ℚ := n * ε / α
  let k : ℕ := ⌈(n : ℚ) * ε⌉₊
  let m : ℕ := ⌈43 / 10 * t⌉₊
  have ht0 : 0 ≤ t := div_nonneg (mul_nonneg (Nat.cast_nonneg _) he.le) ha.le
  have ht : t * α = n * ε := div_mul_cancel₀ _ ha.ne'
  have hhalf : t * α ≤ t / 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha') ht0]
  have htlarge : 100 ≤ t := by linarith
  have hklo : n * ε ≤ (k : ℚ) := Nat.le_ceil _
  have hkhi : (k : ℚ) < n * ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmlo : 43 / 10 * t ≤ (m : ℚ) := Nat.le_ceil _
  have hmhi : (m : ℚ) < 43 / 10 * t + 1 := Nat.ceil_lt_add_one (by positivity)
  have hkm : k ≤ m := by exact_mod_cast (show (k : ℚ) ≤ m by linarith)
  have hd' : ε ≤ G.edgeDensity S T := by linarith
  have hdegree : (k : ℚ) ≤ (G.edgeDensity S T - ε) * m := by
    have hd0 : 6 / 25 * α ≤ G.edgeDensity S T - ε := by linarith
    have hmul := mul_le_mul hd0 hmlo (show 0 ≤ 43 / 10 * t by positivity)
      (by linarith : 0 ≤ G.edgeDensity S T - ε)
    nlinarith [hmul]
  have hbudget : k + m + l ≤ n := by
    exact_mod_cast (show (k : ℚ) + m + l ≤ n by change (l : ℚ) + 5 * t ≤ n at hrange; linarith)
  have hend : (k : ℚ) < α * n / 5 := by
    nlinarith [mul_le_mul_of_nonneg_left he' (show 0 ≤ (n : ℚ) by positivity)]
  let r := l - 1
  have hrl : r + 1 = l := by dsimp [r]; omega
  obtain ⟨L, hlen, hnodup, hchain, hpool⟩ := regular_pair_path_between G hreg hd' hst k m r
    (hS ▸ hklo) (hT ▸ hklo) hkm hdegree (by omega) (by omega) hx hy
    (by exact_mod_cast hend.trans_le hxdeg) (by exact_mod_cast hend.trans_le hydeg)
  let W := (x :: L) ++ [y]
  have hn : W ≠ [] := by simp [W]
  let w := Walk.ofSupport W hn hchain
  have hw : w.support = W := Walk.support_ofSupport hn hchain
  have hwlen : w.length = W.length - 1 := Walk.length_ofSupport hn hchain
  have hend' : W.getLast hn = y := by simp [W]
  have hstart : W.head hn = x := rfl
  refine ⟨w.copy hstart hend', ?_, ?_, ?_⟩
  · apply Walk.IsPath.mk'
    rw [Walk.support_copy, hw]
    exact hnodup
  · rw [Walk.length_copy, hwlen]
    simp [W, hlen]; omega
  · rw [Walk.support_copy, hw]
    intro z hz
    simp [W] at hz
    rcases hz with rfl | h | rfl
    · exact Or.inl hx
    · exact hpool _ h
    · exact Or.inr hy

/-- Benevides, Proposition 3.2, with an arbitrary eligible target subset.
The forbidden set may therefore be recomputed after vertices have been used. -/
lemma regular_pair_few_bad {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T B : Finset V} {ε : ℚ} (hreg : G.IsUniform ε S T)
    (hd : ε ≤ G.edgeDensity S T) (hB : B ⊆ T) (hsize : (T.card : ℚ) * ε ≤ B.card) :
    ((S.filter fun x => ((B.filter (G.Adj x)).card : ℚ) ≤
      (G.edgeDensity S T - ε) * B.card).card : ℚ) < S.card * ε := by
  by_contra! h
  obtain ⟨a, ha, hdeg⟩ := regular_pair_choose G hreg hd (Finset.filter_subset _ _) hB h hsize
  exact (not_lt_of_ge (Finset.mem_filter.mp ha).2) hdeg

/-- Choose a single attachment vertex typical toward two different clusters
in the same colour. The candidate pool may already exclude used vertices. -/
lemma regular_pair_two_targets {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T U B C X : Finset V} {ε : ℚ}
    (ht : G.IsUniform ε S T) (hu : G.IsUniform ε S U)
    (hdt : ε ≤ G.edgeDensity S T) (hdu : ε ≤ G.edgeDensity S U)
    (hB : B ⊆ T) (hC : C ⊆ U) (hsizeB : (T.card : ℚ) * ε ≤ B.card)
    (hsizeC : (U.card : ℚ) * ε ≤ C.card) (hX : X ⊆ S) (hsizeX : 2 * S.card * ε ≤ X.card) :
    ∃ x ∈ X, (G.edgeDensity S T - ε) * B.card < ((B.filter (G.Adj x)).card : ℚ) ∧
      (G.edgeDensity S U - ε) * C.card < ((C.filter (G.Adj x)).card : ℚ) := by
  classical
  let badT := S.filter fun x => ((B.filter (G.Adj x)).card : ℚ) ≤ (G.edgeDensity S T - ε) * B.card
  let badU := S.filter fun x => ((C.filter (G.Adj x)).card : ℚ) ≤ (G.edgeDensity S U - ε) * C.card
  have ht' : (badT.card : ℚ) < S.card * ε := regular_pair_few_bad G ht hdt hB hsizeB
  have hu' : (badU.card : ℚ) < S.card * ε := regular_pair_few_bad G hu hdu hC hsizeC
  by_contra! hnone
  have hsub : X ⊆ badT ∪ badU := by
    intro x hx
    by_cases h : ((B.filter (G.Adj x)).card : ℚ) ≤ (G.edgeDensity S T - ε) * B.card
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hX hx, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hX hx, hnone x hx (lt_of_not_ge h)⟩)
  have htot : (X.card : ℚ) ≤ badT.card + badU.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  linarith

/-- Lift a finite walk through regular pairs to a simple path. The same cluster
may occur several times. Each step deletes its chosen vertex from all future
pools, and the output records the pool used at every position. -/
lemma lift_regular_chain {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {ε d : ℚ} (hd : ε ≤ d) (k m : ℕ) (hk : 0 < k) (hkm : k ≤ m)
    (hdegree : (k : ℚ) ≤ (d - ε) * m) (r : ℕ) (C P : ℕ → Finset V) (A : Finset V)
    (hA : A ⊆ C 0) (hstart : k ≤ A.card)
    (hthreshold : ∀ i ≤ r, ((C i).card : ℚ) * ε ≤ k)
    (hpools : ∀ i < r, P i ⊆ C (i+1) ∧ m + r ≤ (P i).card)
    (hpairs : ∀ i < r, G.IsUniform ε (C i) (C (i+1)) ∧ d ≤ G.edgeDensity (C i) (C (i+1))) :
    ∃ x ∈ A, ∃ L : List V, L.length = r ∧ (x :: L).Nodup ∧ (x :: L).IsChain G.Adj ∧
      ∀ i (hi : i < L.length), L[i] ∈ P i := by
  classical
  induction r generalizing C P A with
  | zero =>
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (hk.trans_le hstart)
    exact ⟨x, hx, [], rfl, by simp, .singleton _, fun i hi => by simp at hi⟩
  | succ r ih =>
    obtain ⟨hreg, hden⟩ := hpairs 0 (by omega)
    obtain ⟨hsub, hcard⟩ := hpools 0 (by omega)
    obtain ⟨x, hx, hdeg⟩ := regular_pair_choose G hreg (hd.trans hden) hA hsub
      ((hthreshold 0 (by omega)).trans (by exact_mod_cast hstart))
      ((hthreshold 1 (by omega)).trans (by exact_mod_cast (show k ≤ (P 0).card by omega)))
    let A' := (P 0).filter (G.Adj x)
    have hA' : k ≤ A'.card := by
      have low : (k : ℚ) ≤ (G.edgeDensity (C 0) (C 1) - ε) * (P 0).card :=
        hdegree.trans (mul_le_mul (sub_le_sub_right hden ε)
          (by exact_mod_cast (show m ≤ (P 0).card by omega)) (Nat.cast_nonneg _) (by linarith))
      exact_mod_cast low.trans hdeg.le
    let P' (i : ℕ) := (P (i+1)).erase x
    have hpools' (i) (hi : i < r) : P' i ⊆ C (i+1+1) ∧ m + r ≤ (P' i).card := by
      obtain ⟨hsi, hci⟩ := hpools (i+1) (by omega)
      refine ⟨(Finset.erase_subset _ _).trans hsi, ?_⟩
      have h : (P (i+1)).card - 1 ≤ (P' i).card := Finset.pred_card_le_card_erase
      omega
    obtain ⟨y, hy, L, hlen, hs, hc, hpos⟩ := ih (fun i => C (i+1)) P' A'
      ((Finset.filter_subset _ _).trans hsub) hA' (fun i hi => hthreshold _ (by omega)) hpools'
      (fun i hi => hpairs _ (by omega))
    obtain ⟨hyP, hxy⟩ := Finset.mem_filter.mp hy
    have hxL : x ∉ L := by
      intro hit
      obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hit
      have h := hpos i hi
      rw [hix] at h
      exact Finset.notMem_erase _ _ h
    refine ⟨x, hx, y :: L, by simp [hlen], ?_, List.isChain_cons_cons.mpr ⟨hxy,hc⟩, ?_⟩
    · exact List.nodup_cons.mpr ⟨by simp [hxy.ne, hxL], hs⟩
    · intro i hi
      cases i with
      | zero => exact hyP
      | succ j =>
        exact Finset.erase_subset _ _ (hpos j (by simpa using hi))

/-- Embed one reduced connector with separately prescribed pools for its
two ends, avoiding all vertices already used by other connectors. -/
lemma route_regular_chain {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {ε d : ℚ} (hd : ε ≤ d) (k m : ℕ) (hk : 0 < k) (hkm : k ≤ m)
    (hdegree : (k : ℚ) ≤ (d-ε)*m) (r : ℕ) (C : ℕ → Finset V) (A Z F : Finset V)
    (hA : A ⊆ C 0) (hZ : Z ⊆ C (r+1))
    (hstart : k + F.card ≤ A.card) (hend : m + (r+1) + F.card ≤ Z.card)
    (hth : ∀ i ≤ r+1, ((C i).card : ℚ)*ε ≤ k)
    (hsize : ∀ i < r, m + (r+1) + F.card ≤ (C (i+1)).card)
    (hpair : ∀ i < r+1, G.IsUniform ε (C i) (C (i+1)) ∧ d ≤ G.edgeDensity (C i) (C (i+1))) :
    ∃ x ∈ A, ∃ y ∈ Z, ∃ J : List V, J.length = r ∧
      (x :: (J ++ [y])).Nodup ∧ (x :: (J ++ [y])).IsChain G.Adj ∧
      ∀ z ∈ x :: (J ++ [y]), z ∉ F := by
  classical
  let P (i : ℕ) := (if i = r then Z else C (i+1)) \ F
  have hcard (U : Finset V) (n : ℕ) (hn : n + F.card ≤ U.card) : n ≤ (U \ F).card :=
    (show n ≤ U.card - F.card by omega).trans (Finset.le_card_sdiff F U)
  have hp (i) (hi : i < r+1) : P i ⊆ C (i+1) ∧ m+(r+1) ≤ (P i).card := by
    by_cases h : i = r
    · subst i
      simpa [P] using And.intro (Finset.sdiff_subset.trans hZ : Z \ F ⊆ C (r+1)) (hcard _ _ hend)
    · simpa [P,h] using And.intro (Finset.sdiff_subset : C (i+1) \ F ⊆ C (i+1))
          (hcard _ _ (hsize i (by omega)))
  obtain ⟨x,hx,L,hL,hs,hc,hpos⟩ := lift_regular_chain G hd k m hk hkm hdegree (r+1)
    C P (A \ F) (Finset.sdiff_subset.trans hA) (hcard _ _ hstart) hth hp hpair
  have hne : L ≠ [] := by intro e; simp [e] at hL
  obtain ⟨J,y,heq⟩ : ∃ J y, L = J ++ [y] :=
    ⟨L.dropLast,L.getLast hne,(List.dropLast_concat_getLast hne).symm⟩
  subst L
  have hlen : J.length = r := by simpa using hL
  have hy := hpos J.length (by simp)
  have hyZ : y ∈ Z \ F := by simpa [P,hlen] using hy
  refine ⟨x,(Finset.mem_sdiff.mp hx).1,y,(Finset.mem_sdiff.mp hyZ).1,J,hlen,hs,hc,?_⟩
  intro z hz
  rcases List.mem_cons.mp hz with rfl | h
  · exact (Finset.mem_sdiff.mp hx).2
  obtain ⟨i,hi,heq⟩ := List.mem_iff_getElem.mp h
  have hz' := hpos i hi
  rw [heq] at hz'
  exact (Finset.mem_sdiff.mp hz').2

/-- Greedily realize a finite family of bounded routes. At stage i the
earlier routes have used at most iM vertices. The witness set records
the whole reservation for later expansion of the matching. -/
lemma disjoint_routes_of_avoidance {V : Type*} [DecidableEq V] (q M : ℕ)
    (P : ℕ → List V → Prop)
    (step : ∀ i < q, ∀ F : Finset V, F.card ≤ i*M →
      ∃ L : List V, P i L ∧ L.length ≤ M ∧ ∀ v ∈ L, v ∉ F) :
    ∃ f : ℕ → List V, ∃ used : Finset V, used.card ≤ q*M ∧
      (∀ i < q, P i (f i) ∧ ∀ z ∈ f i, z ∈ used) ∧
      ∀ i j, i < j → j < q → (f i).Disjoint (f j) := by
  classical
  induction q with
  | zero => exact ⟨fun _ => [],∅,by simp,by simp,by simp⟩
  | succ q ih =>
    obtain ⟨f,F,hcard,hf,hdis⟩ := ih (fun i hi => step i (by omega))
    obtain ⟨L,hL,hlen,havoid⟩ := step q (by omega) F hcard
    let new (i : ℕ) := if i = q then L else f i
    let U := F ∪ L.toFinset
    have hU : U.card ≤ (q+1)*M := by
      have hc := Finset.card_union_le F L.toFinset
      have hlen' := List.toFinset_card_le L
      dsimp [U]; rw [Nat.succ_mul]; omega
    refine ⟨new,U,hU,?_,?_⟩
    · intro i hi
      by_cases e : i = q
      · subst i
        exact ⟨by simpa [new] using hL, fun z hz => Finset.mem_union_right _ (by simpa [new] using hz)⟩
      · obtain ⟨hprop,hin⟩ := hf i (by omega)
        exact ⟨by simpa [new,e] using hprop, fun z hz => Finset.mem_union_left _
          (hin z (by simpa [new,e] using hz))⟩
    · intro i j hij hj
      have hi : i < q := by omega
      by_cases eq : j = q
      · subst j
        simp only [new, if_neg hi.ne, if_pos rfl]
        exact fun z hz hz' => havoid z hz' ((hf i hi).2 z hz)
      · simpa [new,hi.ne,eq] using hdis i j hij (by omega)

/-- Select disjoint connectors along any specified family of reduced paths.
The start and end pools can impose the degree requirements of the matched
edges without requiring the reduced paths themselves to be disjoint. -/
lemma disjoint_regular_routes {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {ε d : ℚ} (hd : ε ≤ d) (k m : ℕ) (hk : 0 < k) (hkm : k ≤ m)
    (hdegree : (k : ℚ) ≤ (d-ε)*m) (q M : ℕ) (r : ℕ → ℕ)
    (C : ℕ → ℕ → Finset V) (A Z : ℕ → Finset V)
    (hbound : ∀ i < q, r i + 2 ≤ M)
    (hends : ∀ i < q, A i ⊆ C i 0 ∧ Z i ⊆ C i (r i+1))
    (hstart : ∀ i < q, k + i*M ≤ (A i).card)
    (hend : ∀ i < q, m + (r i+1) + i*M ≤ (Z i).card)
    (hth : ∀ i < q, ∀ j ≤ r i+1, ((C i j).card : ℚ)*ε ≤ k)
    (hsize : ∀ i < q, ∀ j < r i, m + (r i+1) + i*M ≤ (C i (j+1)).card)
    (hpairs : ∀ i < q, ∀ j < r i+1, G.IsUniform ε (C i j) (C i (j+1)) ∧
      d ≤ G.edgeDensity (C i j) (C i (j+1))) :
    ∃ f : ℕ → List V, ∃ used : Finset V, used.card ≤ q*M ∧
      (∀ i < q, (∃ x ∈ A i, ∃ y ∈ Z i, ∃ J : List V,
        f i = x :: (J ++ [y]) ∧ J.length = r i ∧ (f i).Nodup ∧ (f i).IsChain G.Adj) ∧
        ∀ z ∈ f i, z ∈ used) ∧ ∀ i j, i < j → j < q → (f i).Disjoint (f j) := by
  apply disjoint_routes_of_avoidance q M (fun i L => ∃ x ∈ A i, ∃ y ∈ Z i, ∃ J : List V,
    L = x :: (J ++ [y]) ∧ J.length = r i ∧ L.Nodup ∧ L.IsChain G.Adj)
  intro i hi F hF
  have hA := hstart i hi
  have hZ := hend i hi
  obtain ⟨x,hx,y,hy,J,hlen,hs,hc,ha⟩ := route_regular_chain G hd k m hk hkm hdegree (r i)
    (C i) (A i) (Z i) F (hends i hi).1 (hends i hi).2 (by omega) (by omega)
    (hth i hi) (fun j hj => by have h := hsize i hi j hj; omega) (hpairs i hi)
  exact ⟨x :: (J ++ [y]),⟨x,hx,y,hy,J,rfl,hlen,hs,hc⟩,by have h := hbound i hi; simp [hlen]; omega,ha⟩

/-- Reserve exactly the interiors of disjoint connector paths. Their
endpoints remain available to start and end the paths in matched pairs. -/
lemma reserve_route_interiors {V I : Type*} [DecidableEq V] (used : Finset V)
    (x y : I → V) (J : I → List V) (hs : ∀ i, (x i :: (J i ++ [y i])).Nodup)
    (hdis : ∀ i j, i ≠ j → (x i :: (J i ++ [y i])).Disjoint (x j :: (J j ++ [y j])))
    (hu : ∀ i z, z ∈ J i → z ∈ used) :
    ∃ F ⊆ used, (∀ z, z ∈ F ↔ ∃ i, z ∈ J i) ∧ ∀ i, x i ∉ F ∧ y i ∉ F := by
  classical
  let F := used.filter fun z => ∃ i, z ∈ J i
  have hf (z) : z ∈ F ↔ ∃ i, z ∈ J i := by
    constructor
    · exact fun h => (Finset.mem_filter.mp h).2
    · rintro ⟨i,hi⟩
      exact Finset.mem_filter.mpr ⟨hu i z hi, i, hi⟩
  refine ⟨F,Finset.filter_subset _ _,hf,?_⟩
  intro i
  constructor
  · intro hit
    obtain ⟨j,hj⟩ := (hf _).mp hit
    by_cases e : i = j
    · subst j
      exact (List.nodup_cons.mp (hs i)).1 (List.mem_append_left _ hj)
    · exact hdis i j e (by simp) (List.mem_cons_of_mem _ (List.mem_append_left _ hj))
  · intro hit
    obtain ⟨j,hj⟩ := (hf _).mp hit
    by_cases e : i = j
    · subst j
      exact (List.nodup_append'.mp (List.nodup_cons.mp (hs i)).2).2.2 hj (by simp)
    · exact hdis i j e (by simp) (List.mem_cons_of_mem _ (List.mem_append_left _ hj))

/-- Turn disjoint connector routes into the endpoint and reservation data
for the matched pairs. Route i ends at the entry to pair i+1, with the last
route returning to pair zero. -/
lemma organize_matching_connectors {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (t : ℕ) (A B : ℕ → Finset V) (r : ℕ → ℕ) (f : ℕ → List V) (used : Finset V)
    (hf : ∀ i ≤ t, (∃ x ∈ B i, ∃ y ∈ A (if i < t then i+1 else 0), ∃ J : List V,
      f i = x :: (J ++ [y]) ∧ J.length = r i ∧ (f i).Nodup ∧ (f i).IsChain G.Adj) ∧
      ∀ z ∈ f i, z ∈ used)
    (hdis : ∀ i j, i < j → j ≤ t → (f i).Disjoint (f j)) :
    ∃ a b : ℕ → V, ∃ J : ℕ → List V, ∃ F ⊆ used,
      (∀ i ≤ t, a i ∈ A i ∧ b i ∈ B i ∧ a i ∉ F ∧ b i ∉ F) ∧
      (∀ i ≤ t, (J i).length = r i ∧ (J i).Nodup ∧ (b i :: J i).IsChain G.Adj ∧
        ∀ z ∈ J i, z ∈ F) ∧
      (∀ i j, i < j → j ≤ t → (J i).Disjoint (J j)) ∧
      (∀ i < t, G.Adj ((b i :: J i).getLast (by simp)) (a (i+1))) ∧
      G.Adj ((b t :: J t).getLast (by simp)) (a 0) := by
  classical
  have spec (i : Fin (t+1)) := (hf i (by omega)).1
  choose x hx y hy K eqn hlen hsimple hchain using spec
  have whole (i : Fin (t+1)) : (x i :: (K i ++ [y i])).Nodup := eqn i ▸ hsimple i
  have chain (i : Fin (t+1)) : (x i :: (K i ++ [y i])).IsChain G.Adj := eqn i ▸ hchain i
  have sep (i j : Fin (t+1)) (hne : i ≠ j) :
      (x i :: (K i ++ [y i])).Disjoint (x j :: (K j ++ [y j])) := by
    rw [← eqn i, ← eqn j]
    rcases lt_or_gt_of_ne hne with lt | gt
    · exact hdis _ _ lt (by omega)
    · exact (hdis _ _ gt (by omega)).symm
  have inused (i : Fin (t+1)) (z) (hz : z ∈ K i) : z ∈ used :=
    (hf i (by omega)).2 z (by rw [eqn i]; simp [hz])
  obtain ⟨F,hF,hin,hends⟩ := reserve_route_interiors used x y K whole sep inused
  let idx (i : ℕ) : Fin (t+1) := ⟨min i t,by omega⟩
  have idxval (i) (hi : i ≤ t) : (idx i).val = i := Nat.min_eq_left hi
  let a : ℕ → V
    | 0 => y (idx t)
    | j+1 => y (idx j)
  let b (i : ℕ) := x (idx i)
  let J (i : ℕ) := K (idx i)
  have endlink (i : Fin (t+1)) : G.Adj ((x i :: K i).getLast (by simp)) (y i) := by
    have hc : ((x i :: K i) ++ [y i]).IsChain G.Adj := chain i
    exact hc.rel_getLast_head_of_append (by simp) (by simp)
  refine ⟨a,b,J,F,hF,?_,?_,?_,?_,endlink (idx t)⟩
  · intro i hi
    have hbi : b i ∈ B i := by simpa [b,idxval i hi] using hx (idx i)
    have ha : a i ∈ A i ∧ a i ∉ F := by
      cases i with
      | zero => exact ⟨by simpa [a,idxval t le_rfl] using hy (idx t), (hends _).2⟩
      | succ j =>
        have hj : j < t := by omega
        exact ⟨by simpa [a,idxval j hj.le,hj] using hy (idx j), (hends _).2⟩
    exact ⟨ha.1,hbi,ha.2,(hends _).1⟩
  · intro i hi
    have nd := (List.nodup_cons.mp (whole (idx i))).2
    have cc : ((x (idx i) :: K (idx i)) ++ [y (idx i)]).IsChain G.Adj := chain _
    exact ⟨by simpa [J,idxval i hi] using hlen (idx i), (List.nodup_append'.mp nd).1,
      cc.left_of_append, fun z hz => (hin z).mpr ⟨idx i,hz⟩⟩
  · intro i j hij hj z hz hz'
    have e : idx i ≠ idx j := fun h => by
      have hh := congrArg Fin.val h
      rw [idxval i (by omega),idxval j hj] at hh
      omega
    exact sep _ _ e (List.mem_cons_of_mem _ (List.mem_append_left _ hz))
      (List.mem_cons_of_mem _ (List.mem_append_left _ hz'))
  · intro i _
    exact endlink (idx i)

/-- Close a lifted chain at a vertex reserved outside its pools. The first
and last pools lie in the neighbourhood of that vertex. Intermediate
clusters may repeat along the reduced walk. -/
lemma lift_regular_circuit {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {ε d : ℚ} (hd : ε ≤ d) (k m : ℕ) (hk : 0 < k) (hkm : k ≤ m)
    (hdegree : (k : ℚ) ≤ (d - ε) * m) (r : ℕ) (C P : ℕ → Finset V) (A : Finset V)
    (hA : A ⊆ C 0) (hstart : k ≤ A.card)
    (hthreshold : ∀ i ≤ r + 1, ((C i).card : ℚ) * ε ≤ k)
    (hpools : ∀ i < r + 1, P i ⊆ C (i+1) ∧ m + (r+1) ≤ (P i).card)
    (hpairs : ∀ i < r + 1, G.IsUniform ε (C i) (C (i+1)) ∧ d ≤ G.edgeDensity (C i) (C (i+1)))
    (a : V) (havoid : ∀ i < r + 1, a ∉ P i)
    (hfirst : ∀ x ∈ A, G.Adj a x) (hlast : ∀ y ∈ P r, G.Adj y a) :
    (cycleGraph (r+3)).IsContained G := by
  obtain ⟨x, hx, L, hlen, hs, hc, hpos⟩ := lift_regular_chain G hd k m hk hkm hdegree (r+1)
    C P A hA hstart hthreshold hpools hpairs
  have hax := hfirst x hx
  have haL : a ∉ L := by
    intro ha
    obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
    have h := hpos i hi
    rw [hia] at h
    exact havoid _ (by omega) h
  have hne : L ≠ [] := by intro e; simp [e] at hlen
  obtain ⟨L', y, heq⟩ : ∃ L' y, L = L' ++ [y] :=
    ⟨L.dropLast, L.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  subst L
  have hlen' : L'.length = r := by simpa using hlen
  have hlastmem := hpos L'.length (by simp)
  have hy : y ∈ P r := by simpa [hlen'] using hlastmem
  have hsimple : (a :: x :: (L' ++ [y])).Nodup :=
    List.nodup_cons.mpr ⟨by simp only [List.mem_cons, not_or]; exact ⟨hax.ne,haL⟩,hs⟩
  have hchain : (a :: x :: (L' ++ [y])).IsChain G.Adj := List.isChain_cons_cons.mpr ⟨hax,hc⟩
  have hcopy := cycle_of_closed_chain (l := x :: L') G (by simp) hsimple hchain (hlast y hy)
  rw [← (show (x :: L').length + 2 = r + 3 by simp; omega)]
  exact hcopy

/-- Every sufficiently well populated closed walk through dense regular
pairs lifts to a cycle of the same length in the original colour. No
distinctness of the cluster visits is required. -/
lemma cycle_of_regular_closed_walk {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {ε d : ℚ} (hd : ε ≤ d) (k m r : ℕ) (hk : 0 < k) (hkm : k ≤ m)
    (hdegree : (k : ℚ) ≤ (d - ε) * m) (C : ℕ → Finset V)
    (hthreshold : ∀ i ≤ r+2, ((C i).card : ℚ) * ε ≤ k)
    (hroot : 2*k ≤ (C 0).card)
    (hsize : ∀ i ≤ r+2, m+r+2 ≤ (C i).card)
    (hattach : ∀ i ≤ r+2, ((m+r+1 : ℕ) : ℚ) ≤ (d-ε) * (C i).card)
    (hpairs : ∀ i < r+2, G.IsUniform ε (C i) (C (i+1)) ∧ d ≤ G.edgeDensity (C i) (C (i+1)))
    (hclose : G.IsUniform ε (C 0) (C (r+2)) ∧ d ≤ G.edgeDensity (C 0) (C (r+2))) :
    (cycleGraph (r+3)).IsContained G := by
  classical
  obtain ⟨hreg, hden⟩ := hpairs 0 (by omega)
  have hth (i) (hi : i ≤ r+2) : ((C i).card : ℚ) * ε ≤ (C i).card :=
    (hthreshold i hi).trans (by exact_mod_cast (show k ≤ (C i).card by have := hsize i hi; omega))
  have h0 : 2 * ((C 0).card : ℚ) * ε ≤ (C 0).card := by
    have h := hthreshold 0 (by omega)
    have h' : (2 : ℚ) * k ≤ (C 0).card := by exact_mod_cast hroot
    linarith
  obtain ⟨a, _, hn1, hn2⟩ := regular_pair_two_targets G hreg hclose.1 (hd.trans hden) (hd.trans hclose.2)
    (Finset.Subset.refl _) (Finset.Subset.refl _) (hth 1 (by omega)) (hth _ le_rfl)
    (Finset.Subset.refl _) h0
  have degree {T : Finset V} (h : d ≤ G.edgeDensity (C 0) T)
      (hlo : ((m+r+1 : ℕ) : ℚ) ≤ (d-ε) * T.card)
      (hn : (G.edgeDensity (C 0) T - ε) * T.card < ((T.filter (G.Adj a)).card : ℚ)) :
      m+r+1 ≤ (T.filter (G.Adj a)).card := by
    exact_mod_cast (hlo.trans (mul_le_mul_of_nonneg_right (sub_le_sub_right h ε) (Nat.cast_nonneg _))).trans hn.le
  have h1 : m+r+1 ≤ ((C 1).filter (G.Adj a)).card := degree hden (hattach 1 (by omega)) hn1
  have h2 := degree hclose.2 (hattach _ le_rfl) hn2
  let P (i : ℕ) := if i = r then (C (r+2)).filter (G.Adj a) else (C (i+2)).erase a
  refine lift_regular_circuit G hd k m hk hkm hdegree r (fun i => C (i+1)) P
    ((C 1).filter (G.Adj a)) (Finset.filter_subset _ _) (by omega) (fun i hi => hthreshold _ (by omega))
    ?_ (fun i hi => hpairs _ (by omega)) a ?_ ?_ ?_
  · intro i hi
    by_cases eq : i = r
    · subst i
      exact ⟨by simpa [P] using (Finset.filter_subset (G.Adj a) (C (r+2))),
        by simpa [P, Nat.add_assoc] using h2⟩
    · have hb := hsize (i+2) (by omega)
      have hc : (C (i+2)).card - 1 ≤ ((C (i+2)).erase a).card := Finset.pred_card_le_card_erase
      simp only [P, if_neg eq]
      exact ⟨Finset.erase_subset _ _, by omega⟩
  · intro i hi
    by_cases eq : i = r <;> simp [P, eq]
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro y hy
    have hy' : y ∈ (C (r+2)).filter (G.Adj a) := by simpa [P] using hy
    exact (Finset.mem_filter.mp hy').2.symm

/-- Concatenate path segments lying in disjoint vertex pools, with one
connecting edge between successive segments. The order is exactly the sum
of the segment orders. -/
lemma join_disjoint_path_segments {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (a b : ℕ → V) (pool : ℕ → Finset V) (len : ℕ → ℕ) (t : ℕ)
    (hseg : ∀ i ≤ t, ∃ l : List V, l.length = len i ∧
      (a i :: (l ++ [b i])).Nodup ∧ (a i :: (l ++ [b i])).IsChain G.Adj ∧
      ∀ z ∈ a i :: (l ++ [b i]), z ∈ pool i)
    (hlinks : ∀ i < t, G.Adj (b i) (a (i+1)))
    (hdis : ∀ i j, i < j → j ≤ t → Disjoint (pool i) (pool j)) :
    ∃ L : List V, L.length + 2 = ∑ i ∈ Finset.range (t+1), (len i + 2) ∧
      (a 0 :: (L ++ [b t])).Nodup ∧ (a 0 :: (L ++ [b t])).IsChain G.Adj ∧
      ∀ z ∈ a 0 :: (L ++ [b t]), ∃ i ≤ t, z ∈ pool i := by
  induction t with
  | zero =>
    obtain ⟨l, hl, hs, hc, hp⟩ := hseg 0 le_rfl
    exact ⟨l, by simp [hl], hs, hc, fun z hz => ⟨0, le_rfl, hp z hz⟩⟩
  | succ t ih =>
    obtain ⟨l, hl, hs, hc, hp⟩ := ih (fun i hi => hseg i (by omega))
      (fun i hi => hlinks i (by omega)) (fun i j hij hj => hdis i j hij (by omega))
    obtain ⟨l', hl', hs', hc', hp'⟩ := hseg (t+1) le_rfl
    let X := a 0 :: (l ++ [b t])
    let Y := a (t+1) :: (l' ++ [b (t+1)])
    have hsep : X.Disjoint Y := by
      intro z hz hz'
      obtain ⟨i, hi, h⟩ := hp z hz
      exact Finset.disjoint_left.mp (hdis i (t+1) (by omega) le_rfl) h (hp' z hz')
    have hsimple : (X ++ Y).Nodup := List.nodup_append'.mpr ⟨hs,hs',hsep⟩
    have hchain : (X ++ Y).IsChain G.Adj := by
      apply hc.append hc'
      intro u hu v hv
      have hu' : b t = u := by
        change u ∈ ((a 0 :: l) ++ [b t]).getLast? at hu
        rw [List.getLast?_append_of_ne_nil _ (by simp)] at hu
        simpa using hu
      have hv' : a (t+1) = v := by simpa using hv
      exact hu' ▸ hv' ▸ hlinks t (by omega)
    let L := l ++ [b t, a (t+1)] ++ l'
    have heq : a 0 :: (L ++ [b (t+1)]) = X ++ Y := by simp [L,X,Y,List.append_assoc]
    refine ⟨L, ?_, heq ▸ hsimple, heq ▸ hchain, ?_⟩
    · rw [Finset.sum_range_succ, ← hl]
      simp [L,hl']; omega
    · rw [heq]
      intro z hz
      rcases List.mem_append.mp hz with h | h
      · obtain ⟨i, hi, h⟩ := hp z h
        exact ⟨i, by omega, h⟩
      · exact ⟨_, le_rfl, hp' z h⟩

/-- Distribute any requested even increment among the matched pairs, up to
their combined capacity. -/
lemma allocate_cycle_length (t : ℕ) (cap : ℕ → ℕ) (q : ℕ)
    (h : q ≤ ∑ i ∈ Finset.range t, cap i) :
    ∃ use : ℕ → ℕ, (∀ i < t, use i ≤ cap i) ∧ ∑ i ∈ Finset.range t, use i = q := by
  induction t generalizing q with
  | zero =>
    simp at h
    exact ⟨fun _ => 0, by simp, by simp [h]⟩
  | succ t ih =>
    rw [Finset.sum_range_succ] at h
    obtain ⟨f, hf, hsum⟩ := ih (q - cap t) (by omega)
    let use (i : ℕ) := if i = t then min q (cap t) else f i
    refine ⟨use, ?_, ?_⟩
    · intro i hi
      by_cases e : i = t
      · simp [use,e]
      · simpa [use,e] using hf i (by omega)
    · have hold : ∑ i ∈ Finset.range t, use i = ∑ i ∈ Finset.range t, f i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [use, (Finset.mem_range.mp hi).ne]
      rw [Finset.sum_range_succ, hold, hsum]
      simp [use]

/-- In a cyclic arrangement of disjoint path segments, independently
extensible segments realize every admissible total order of the correct
parity. Segments of zero capacity serve as fixed connectors. -/
lemma cycle_of_flexible_segments {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (t : ℕ) (a b : ℕ → V) (pool : ℕ → Finset V) (base cap : ℕ → ℕ)
    (hseg : ∀ i ≤ t, ∀ j ≤ cap i, ∃ l : List V, l.length = base i + 2*j ∧
      (a i :: (l ++ [b i])).Nodup ∧ (a i :: (l ++ [b i])).IsChain G.Adj ∧
      ∀ z ∈ a i :: (l ++ [b i]), z ∈ pool i)
    (hlinks : ∀ i < t, G.Adj (b i) (a (i+1))) (hclose : G.Adj (b t) (a 0))
    (hdis : ∀ i j, i < j → j ≤ t → Disjoint (pool i) (pool j))
    (n q : ℕ) (hn : 3 ≤ n) (hcap : q ≤ ∑ i ∈ Finset.range (t+1), cap i)
    (horder : n = (∑ i ∈ Finset.range (t+1), (base i + 2)) + 2*q) :
    (cycleGraph n).IsContained G := by
  obtain ⟨f,hf,hsum⟩ := allocate_cycle_length (t+1) cap q hcap
  obtain ⟨L,hL,hs,hc,_⟩ := join_disjoint_path_segments G a b pool (fun i => base i + 2*f i) t
    (fun i hi => hseg i hi (f i) (hf i (by omega))) hlinks hdis
  have hlen : L.length + 2 = n := by
    rw [hL, horder, ← hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    omega
  rw [← hlen]
  exact cycle_of_closed_chain G (by omega) hs hc hclose

/-- Replace every distinguished edge of a cyclic arrangement of regular
pairs by a path. Disjointness of the pairs allows independent choices of
the path lengths. The edges between successive pairs are fixed. -/
lemma cycle_from_regular_pairs {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : ℕ) (S T : ℕ → Finset V) (a b : ℕ → V)
    (ε : ℚ) (k m : ℕ) (hkm : k ≤ m) (cap : ℕ → ℕ)
    (hreg : ∀ i ≤ t, G.IsUniform ε (S i) (T i))
    (hd : ∀ i ≤ t, ε ≤ G.edgeDensity (S i) (T i))
    (hst : ∀ i ≤ t, Disjoint (S i) (T i))
    (hsep : ∀ i j, i < j → j ≤ t → Disjoint (S i ∪ T i) (S j ∪ T j))
    (hthS : ∀ i ≤ t, ((S i).card : ℚ) * ε ≤ k)
    (hthT : ∀ i ≤ t, ((T i).card : ℚ) * ε ≤ k)
    (hden : ∀ i ≤ t, (k : ℚ) ≤ (G.edgeDensity (S i) (T i) - ε) * m)
    (hS : ∀ i ≤ t, m + cap i + k + 1 ≤ (S i).card)
    (hT : ∀ i ≤ t, m + cap i + 1 ≤ (T i).card)
    (ha : ∀ i ≤ t, a i ∈ S i) (hb : ∀ i ≤ t, b i ∈ T i)
    (hdegA : ∀ i ≤ t, k < ((T i).filter (G.Adj (a i))).card)
    (hdegB : ∀ i ≤ t, k < ((S i).filter (G.Adj (b i))).card)
    (hlink : ∀ i < t, G.Adj (b i) (a (i+1))) (hclose : G.Adj (b t) (a 0))
    (q : ℕ) (hq : q ≤ ∑ i ∈ Finset.range (t+1), cap i) :
    (cycleGraph (4*(t+1) + 2*q)).IsContained G := by
  refine cycle_of_flexible_segments G t a b (fun i => S i ∪ T i) (fun _ => 2) cap
    ?_ hlink hclose hsep _ q (by omega) hq ?_
  · intro i hi j hj
    have hs := hS i hi
    have ht := hT i hi
    obtain ⟨L,hL,hsimp,hchain,hpool⟩ := regular_pair_path_between G (hreg i hi) (hd i hi)
      (hst i hi) k m j (hthS i hi) (hthT i hi) hkm (hden i hi) (by omega) (by omega)
      (ha i hi) (hb i hi) (hdegA i hi) (hdegB i hi)
    refine ⟨L, by omega, hsimp, hchain, ?_⟩
    intro z hz
    simp at hz
    rcases hz with rfl | h | rfl
    · exact Finset.mem_union_left _ (ha _ hi)
    · exact Finset.mem_union.mpr (hpool z h)
    · exact Finset.mem_union_right _ (hb _ hi)
  · simp [Nat.mul_comm]

/-- Typical endpoints in a matched cluster pair occupy enough of the cluster
to apply regularity on a neighbouring pair. -/
lemma regular_pair_eligible_endpoints {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T : Finset V} {ε : ℚ} (hreg : G.IsUniform ε S T)
    (hd : ε ≤ G.edgeDensity S T) (k : ℕ)
    (hs : (S.card : ℚ) * ε ≤ k) (ht : (T.card : ℚ) * ε ≤ T.card)
    (hden : (k : ℚ) ≤ (G.edgeDensity S T - ε) * T.card) (hsize : 2*k ≤ S.card) :
    k ≤ (S.filter fun x => k < (T.filter (G.Adj x)).card).card := by
  classical
  let N (x : V) := (T.filter (G.Adj x)).card
  let bad := S.filter fun x => (N x : ℚ) ≤ (G.edgeDensity S T - ε) * T.card
  have hbad : (bad.card : ℚ) < S.card * ε :=
    regular_pair_few_bad G hreg hd (Finset.Subset.refl _) ht
  have sub : S.filter (fun x => ¬ k < N x) ⊆ bad := by
    intro x hx
    obtain ⟨hS, h⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hS,(show (N x : ℚ) ≤ k by exact_mod_cast le_of_not_gt h).trans hden⟩
  have hc : (S.filter (fun x => ¬ k < N x)).card < k := by
    have hsmall : bad.card < k := by exact_mod_cast hbad.trans_le hs
    exact (Finset.card_le_card sub).trans_lt hsmall
  have hsum := Finset.card_filter_add_card_filter_not (s := S) (fun x => k < N x)
  change k ≤ (S.filter fun x => k < N x).card
  omega

/-- An exact range of even cycles forced by a monochromatic cyclic sequence
of regular pairs in the reduced graph. The connecting edges and endpoints
in the host graph are chosen as part of the proof. -/
lemma cycle_from_regular_cluster_ring {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : ℕ) (S T : ℕ → Finset V)
    (ε : ℚ) (k m : ℕ) (hkm : k ≤ m) (cap : ℕ → ℕ)
    (hreg : ∀ i ≤ t, G.IsUniform ε (S i) (T i))
    (hd : ∀ i ≤ t, ε ≤ G.edgeDensity (S i) (T i))
    (hst : ∀ i ≤ t, Disjoint (S i) (T i))
    (hsep : ∀ i j, i < j → j ≤ t → Disjoint (S i ∪ T i) (S j ∪ T j))
    (hthS : ∀ i ≤ t, ((S i).card : ℚ) * ε ≤ k)
    (hthT : ∀ i ≤ t, ((T i).card : ℚ) * ε ≤ k)
    (hden : ∀ i ≤ t, (k : ℚ) ≤ (G.edgeDensity (S i) (T i) - ε) * m)
    (hS : ∀ i ≤ t, m + cap i + k + 1 ≤ (S i).card)
    (hT : ∀ i ≤ t, max (2*k) (m + cap i + 1) ≤ (T i).card)
    (hlink : ∀ i < t, G.IsUniform ε (T i) (S (i+1)) ∧ ε ≤ G.edgeDensity (T i) (S (i+1)))
    (hwrap : G.IsUniform ε (T t) (S 0) ∧ ε ≤ G.edgeDensity (T t) (S 0))
    (q : ℕ) (hq : q ≤ ∑ i ∈ Finset.range (t+1), cap i) :
    (cycleGraph (4*(t+1) + 2*q)).IsContained G := by
  classical
  let A (i : ℕ) := (S i).filter fun x => k < ((T i).filter (G.Adj x)).card
  let B (i : ℕ) := (T i).filter fun y => k < ((S i).filter (G.Adj y)).card
  have good (i) (hi : i ≤ t) : k ≤ (A i).card ∧ k ≤ (B i).card := by
    have hs := hS i hi
    have ht₁ := (le_max_left _ _).trans (hT i hi)
    have ht₂ := (le_max_right _ _).trans (hT i hi)
    have hdpos := sub_nonneg.mpr (hd i hi)
    constructor
    · apply regular_pair_eligible_endpoints G (hreg i hi) (hd i hi) k (hthS i hi)
      · exact (hthT i hi).trans (by exact_mod_cast (show k ≤ (T i).card by omega))
      · exact (hden i hi).trans (mul_le_mul_of_nonneg_left
          (by exact_mod_cast (show m ≤ (T i).card by omega)) hdpos)
      · omega
    · apply regular_pair_eligible_endpoints G (hreg i hi).symm
        (by rw [G.edgeDensity_comm (T i)]; exact hd i hi) k (hthT i hi)
      · exact (hthS i hi).trans (by exact_mod_cast (show k ≤ (S i).card by omega))
      · rw [G.edgeDensity_comm (T i)]
        exact (hden i hi).trans (mul_le_mul_of_nonneg_left
          (by exact_mod_cast (show m ≤ (S i).card by omega)) hdpos)
      · exact ht₁
  have connector (i j) (hi : i ≤ t) (hj : j ≤ t)
      (h : G.IsUniform ε (T i) (S j) ∧ ε ≤ G.edgeDensity (T i) (S j)) :
      ∃ x ∈ B i, ∃ y ∈ A j, G.Adj x y :=
    regular_pair_edge G h.1 h.2 (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      ((hthT i hi).trans (by exact_mod_cast (good i hi).2))
      ((hthS j hj).trans (by exact_mod_cast (good j hj).1))
  obtain ⟨last, hlast, first, hfirst, hclose⟩ := connector t 0 le_rfl (Nat.zero_le _) hwrap
  have internal (i : Fin t) := connector i.val (i.val+1) i.isLt.le i.isLt (hlink i i.isLt)
  choose left hleft right hright hed using internal
  let a : ℕ → V
    | 0 => first
    | i+1 => if h : i < t then right ⟨i,h⟩ else first
  let b (i : ℕ) := if h : i < t then left ⟨i,h⟩ else last
  have ha (i) (hi : i ≤ t) : a i ∈ A i := by
    cases i with
    | zero => exact hfirst
    | succ j => simpa [a, show j < t by omega] using hright ⟨j,by omega⟩
  have hb (i) (hi : i ≤ t) : b i ∈ B i := by
    rcases lt_or_eq_of_le hi with hl | rfl
    · simpa [b, hl] using hleft ⟨i,hl⟩
    · simpa [b] using hlast
  exact cycle_from_regular_pairs G t S T a b ε k m hkm cap hreg hd hst hsep hthS hthT hden hS
    (fun i hi => (le_max_right _ _).trans (hT i hi))
    (fun i hi => (Finset.mem_filter.mp (ha i hi)).1) (fun i hi => (Finset.mem_filter.mp (hb i hi)).1)
    (fun i hi => (Finset.mem_filter.mp (ha i hi)).2) (fun i hi => (Finset.mem_filter.mp (hb i hi)).2)
    (fun i hi => by simpa [a,b,hi] using hed ⟨i,hi⟩) (by simpa [a,b] using hclose) q hq

section ReducedColours

open Finset

variable {V : Type*} [DecidableEq V] (c : Fin 3 → SimpleGraph V)
  [∀ i, DecidableRel (c i).Adj] (hc : (⊤ : SimpleGraph V).IsEdgeColouring c)

include hc

/-- The three densities of a cluster pair in a complete edge-colouring sum to one. -/
lemma cluster_colour_densities {S T : Finset V} (hst : Disjoint S T)
    (hs : S.Nonempty) (ht : T.Nonempty) : ∑ i, (c i).edgeDensity S T = 1 := by
  classical
  let E (i : Fin 3) := (c i).interedges S T
  have cover : (univ.biUnion E) = S ×ˢ T := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp
      exact mem_product.mpr ⟨(((c i).mem_interedges_iff).mp hi).1, (((c i).mem_interedges_iff).mp hi).2.1⟩
    · intro hp
      obtain ⟨ha, hb⟩ := mem_product.mp hp
      have hne : p.1 ≠ p.2 := fun h => Finset.disjoint_left.mp hst (h ▸ ha) hb
      have hed : (⨆ i, c i).Adj p.1 p.2 := by rw [← hc.1]; exact (top_adj _ _).mpr hne
      obtain ⟨i, hi⟩ := iSup_adj.mp hed
      exact mem_biUnion.mpr ⟨i, mem_univ _, ((c i).mem_interedges_iff).mpr ⟨ha, hb, hi⟩⟩
  have hcount : ∑ i, (E i).card = S.card * T.card := by
    rw [← card_product, ← cover, card_biUnion]
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hi hj
    exact (disjoint_iff_inf_le.mp (hc.2 i j hij) (show (c i ⊓ c j).Adj p.1 p.2 from
      ⟨(((c i).mem_interedges_iff).mp hi).2.2, (((c j).mem_interedges_iff).mp hj).2.2⟩)).elim
  simp_rw [edgeDensity_def]
  rw [← Finset.sum_div, div_eq_one_iff_eq]
  · exact_mod_cast hcount
  · exact (mul_pos (by exact_mod_cast hs.card_pos) (by exact_mod_cast ht.card_pos)).ne'

/-- Use every sufficiently dense colour of a simultaneously regular pair.
A uniquely labelled pair is almost monochromatic in the original graph. -/
lemma reduced_colour_graphs {I : Type*} (C : I → Finset V)
    (hne : ∀ u, (C u).Nonempty) (hdis : ∀ u v, u ≠ v → Disjoint (C u) (C v))
    (ε δ : ℚ) (hδ : δ ≤ 1/3) :
    ∃ red : Fin 3 → SimpleGraph I,
      (∀ i u v, (red i).Adj u v ↔ u ≠ v ∧
        (∀ j, (c j).IsUniform ε (C u) (C v)) ∧ δ ≤ (c i).edgeDensity (C u) (C v)) ∧
      (∀ u v, u ≠ v → (∀ j, (c j).IsUniform ε (C u) (C v)) → ∃ i, (red i).Adj u v) ∧
      ∀ i u v, (red i).Adj u v → (∀ j, j ≠ i → ¬ (red j).Adj u v) →
        1 - 2 * δ < (c i).edgeDensity (C u) (C v) := by
  classical
  let red (i : Fin 3) : SimpleGraph I :=
    { Adj := fun u v => u ≠ v ∧ (∀ j, (c j).IsUniform ε (C u) (C v)) ∧
          δ ≤ (c i).edgeDensity (C u) (C v)
      symm := ⟨fun u v h => ⟨h.1.symm, fun j => (h.2.1 j).symm,
        ((c i).edgeDensity_comm (C u) (C v)) ▸ h.2.2⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  refine ⟨red, fun _ _ _ => Iff.rfl, ?_, ?_⟩
  · intro u v huv hreg
    have htotal := cluster_colour_densities c hc (hdis u v huv) (hne u) (hne v)
    rw [Fin.sum_univ_three] at htotal
    by_contra! h
    have small (i : Fin 3) : (c i).edgeDensity (C u) (C v) < δ :=
      lt_of_not_ge fun hi => h i ⟨huv, hreg, hi⟩
    linarith [small 0, small 1, small 2]
  · intro i u v hi honly
    obtain ⟨huv, hreg, _⟩ := hi
    have htotal := cluster_colour_densities c hc (hdis u v huv) (hne u) (hne v)
    rw [Fin.sum_univ_three] at htotal
    have small (j : Fin 3) (hj : j ≠ i) : (c j).edgeDensity (C u) (C v) < δ :=
      lt_of_not_ge fun hd => honly j hj ⟨huv, hreg, hd⟩
    fin_cases i
    · change 1 - 2 * δ < (c 0).edgeDensity (C u) (C v)
      linarith [small 1 (by decide), small 2 (by decide)]
    · change 1 - 2 * δ < (c 1).edgeDensity (C u) (C v)
      linarith [small 0 (by decide), small 2 (by decide)]
    · change 1 - 2 * δ < (c 2).edgeDensity (C u) (C v)
      linarith [small 0 (by decide), small 1 (by decide)]

end ReducedColours

/-- The pairs discarded by simultaneous three-colour regularity occupy at
most three times the one-colour error budget. Pairs are counted in both orders. -/
lemma simultaneously_irregular_count {V : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U) (c : Fin 3 → SimpleGraph V)
    [∀ i, DecidableRel (c i).Adj] (ε : ℚ) (h : ∀ i, P.IsUniform (c i) ε) :
    ∃ bad : Finset (Finset V × Finset V),
      (∀ S T, (S,T) ∈ bad ↔ S ∈ P.parts ∧ T ∈ P.parts ∧ S ≠ T ∧
          ¬ ∀ i, (c i).IsUniform ε S T) ∧
      (bad.card : ℚ) ≤ (P.parts.card * (P.parts.card - 1) : ℕ) * (3 * ε) := by
  classical
  let bad := Finset.univ.biUnion (fun i => P.nonUniforms (c i) ε)
  refine ⟨bad, ?_, ?_⟩
  · intro S T
    simp only [bad, Finset.mem_biUnion, Finset.mem_univ, true_and, Finpartition.mk_mem_nonUniforms]
    push Not
    aesop
  · calc
      (bad.card : ℚ) ≤ ∑ i : Fin 3, ((P.nonUniforms (c i) ε).card : ℚ) := by
        exact_mod_cast (Finset.card_biUnion_le : bad.card ≤ ∑ i : Fin 3, (P.nonUniforms (c i) ε).card)
      _ ≤ _ := by
        rw [Fin.sum_univ_three]
        have h' (i : Fin 3) : ((P.nonUniforms (c i) ε).card : ℚ) ≤
            ((P.parts.card * (P.parts.card - 1) : ℕ) : ℚ) * ε := h i
        linarith [h' 0, h' 1, h' 2]

/-- Delete high-defect clusters before the stability argument (the counting
step in Benevides, Lemma 4.4). Within the remaining cluster set every row
has at most k missing ordered pairs. -/
lemma clean_reduced_pairs {I : Type*} [DecidableEq I] (U : Finset I)
    (bad : Finset (I × I)) (hoff : bad ⊆ U.offDiag)
    (b k : ℕ) (hbudget : bad.card < (b + 1) * (k + 1)) :
    ∃ good ⊆ U, U.card ≤ good.card + b ∧
      ∀ x ∈ good, (good.filter fun y => (x,y) ∈ bad).card ≤ k := by
  classical
  let deg (x : I) := (bad.filter (fun p => p.1 = x)).card
  let high := U.filter fun x => k < deg x
  have hsum : bad.card = ∑ x ∈ U, deg x :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (fun p hp => (Finset.mem_offDiag.mp (hoff hp)).1)
  have hcount : high.card * (k + 1) ≤ bad.card := by
    calc
      _ = ∑ _x ∈ high, (k + 1) := by simp
      _ ≤ ∑ x ∈ high, deg x := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x ∈ U, deg x := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = _ := hsum.symm
  have hfew : high.card ≤ b := by
    by_contra! h
    exact (not_le_of_gt hbudget) ((Nat.mul_le_mul_right (k+1) h).trans hcount)
  let good := U \ high
  have hhigh : high ⊆ U := Finset.filter_subset _ _
  refine ⟨good, Finset.sdiff_subset, ?_, ?_⟩
  · have h : good.card + high.card = U.card := Finset.card_sdiff_add_card_eq_card hhigh
    omega
  · intro x hx
    obtain ⟨hxU, hxH⟩ := Finset.mem_sdiff.mp hx
    have hd : deg x ≤ k := le_of_not_gt (fun h => hxH (Finset.mem_filter.mpr ⟨hxU,h⟩))
    apply le_trans _ hd
    apply Finset.card_le_card_of_injOn (fun y => (x,y))
    · intro y hy
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).2,rfl⟩
    · intro y _ z _ h
      exact congrArg Prod.snd h

section Stability

open Finset

/-- The common-neighbour step of Benevides's thesis, Lemma 4.5. Every
left vertex is in one component as soon as twice the missing-degree bound
is smaller than the right side. -/
lemma dense_pair_left_reachable {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (k : ℕ)
    (hmiss : ∀ x ∈ A, B.card ≤ (B.filter (G.Adj x)).card + k) (hB : 2 * k < B.card)
    {x z : V} (hx : x ∈ A) (hz : z ∈ A) : G.Reachable x z := by
  let X := B.filter (G.Adj x)
  let Z := B.filter (G.Adj z)
  have hU : X ∪ Z ⊆ B := union_subset (filter_subset _ _) (filter_subset _ _)
  have hcard := card_le_card hU
  have hsum := card_union_add_card_inter X Z
  have hx' : B.card ≤ X.card + k := hmiss x hx
  have hz' : B.card ≤ Z.card + k := hmiss z hz
  obtain ⟨b, hb⟩ := card_pos.mp (by omega : 0 < (X ∩ Z).card)
  obtain ⟨hbX, hbZ⟩ := mem_inter.mp hb
  exact (mem_filter.mp hbX).2.reachable.trans (mem_filter.mp hbZ).2.symm.reachable

/-- The connected matching conclusion of Lemma 4.5. A and B can have
different sizes. The edges indexed by D have distinct endpoints on each
side and every vertex in the pair belongs to their component. -/
lemma dense_pair_connected_matching {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (k : ℕ)
    (hab : Disjoint A B) (hsize : A.card ≤ B.card) (hA : k < A.card) (hB : 2 * k < B.card)
    (hl : ∀ x ∈ A, B.card ≤ (B.filter (G.Adj x)).card + k)
    (hr : ∀ y ∈ B, A.card ≤ (A.filter (G.Adj y)).card + k) :
    ∃ a ∈ A, (∀ v ∈ A ∪ B, G.Reachable a v) ∧
      ∃ D ⊆ A, D.card = A.card - k ∧ ∃ f : D ↪ V,
        (∀ x, f x ∈ B ∧ G.Adj x.val (f x)) ∧ Disjoint D (univ.image f) := by
  classical
  obtain ⟨a, ha⟩ := card_pos.mp (by omega : 0 < A.card)
  refine ⟨a, ha, ?_, ?_⟩
  · intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact dense_pair_left_reachable G A B k hl hB ha hv
    · have hd := hr v hv
      obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < (A.filter (G.Adj v)).card)
      obtain ⟨huA, hvu⟩ := mem_filter.mp hu
      exact (dense_pair_left_reachable G A B k hl hB ha huA).trans hvu.symm.reachable
  · obtain ⟨D, hD, hcard⟩ := exists_subset_card_eq (Nat.sub_le A.card k)
    let cand (x : D) := B.filter (G.Adj x.val)
    obtain ⟨f, hfinj, hf⟩ : ∃ f : D → V, Function.Injective f ∧ ∀ x, f x ∈ cand x := by
      apply (all_card_le_biUnion_card_iff_existsInjective' cand).mp
      intro s
      by_cases h : s.Nonempty
      · obtain ⟨x, hx⟩ := h
        have hsub : cand x ⊆ s.biUnion cand := fun z hz => mem_biUnion.mpr ⟨x, hx, hz⟩
        have hc := card_le_card hsub
        have hs : s.card ≤ D.card := by simpa using card_le_univ s
        have hv : B.card ≤ (cand x).card + k := hl _ (hD x.property)
        omega
      · simp [not_nonempty_iff_eq_empty.mp h]
    let emb : D ↪ V := ⟨f, hfinj⟩
    refine ⟨D, hD, hcard, emb, fun x => mem_filter.mp (hf x), ?_⟩
    exact hab.mono hD (by
      intro z hz
      obtain ⟨x, _, rfl⟩ := mem_image.mp hz
      exact (mem_filter.mp (hf x)).1)

end Stability

/-- Benevides, Lemma 4.8. If each vertex misses at most k pairs in a
two-coloured graph on U, a monochromatic component covers all but 2k
vertices. The large component can be chosen to contain a prescribed root. -/
lemma two_colour_large_component {V : Type*} [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    [DecidableRel G.Reachable] [DecidableRel H.Reachable]
    (U : Finset V) (k : ℕ) (hm : ∀ x ∈ U,
      (U.filter fun y => y ≠ x ∧ ¬ G.Adj x y ∧ ¬ H.Adj x y).card ≤ k)
    (a : V) (ha : a ∈ U) :
    U.card ≤ (U.filter (G.Reachable a)).card + 2 * k ∨
    U.card ≤ (U.filter (H.Reachable a)).card + k := by
  classical
  let A := U.filter (G.Reachable a)
  let B := U \ A
  have hAU : A ⊆ U := Finset.filter_subset _ _
  have hBU : B ⊆ U := Finset.sdiff_subset
  have haA : a ∈ A := Finset.mem_filter.mpr ⟨ha, Reachable.refl _⟩
  have hAB : Disjoint A B := Finset.disjoint_left.mpr fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx
  have hcount : B.card + A.card = U.card := Finset.card_sdiff_add_card_eq_card hAU
  by_cases hB : B.card ≤ 2 * k
  · left; change U.card ≤ A.card + 2 * k; omega
  right
  have blue (x) (hx : x ∈ A) : B.card ≤ (B.filter (H.Adj x)).card + k := by
    have hsub : B.filter (fun y => ¬ H.Adj x y) ⊆
        U.filter (fun y => y ≠ x ∧ ¬ G.Adj x y ∧ ¬ H.Adj x y) := by
      intro y hy
      obtain ⟨hyB, hxy⟩ := Finset.mem_filter.mp hy
      have hyU := hBU hyB
      have hyA := (Finset.mem_sdiff.mp hyB).2
      refine Finset.mem_filter.mpr ⟨hyU, (fun e => hyA (e ▸ hx)), ?_, hxy⟩
      intro hg
      exact hyA (Finset.mem_filter.mpr ⟨hyU, (Finset.mem_filter.mp hx).2.trans hg.reachable⟩)
    have small := (Finset.card_le_card hsub).trans (hm x (hAU hx))
    have add := Finset.card_filter_add_card_filter_not (s := B) (H.Adj x)
    omega
  have hleft (x) (hx : x ∈ A) := dense_pair_left_reachable H A B k blue (by omega) haA hx
  let D := B.filter (H.Adj a)
  have hdB : D ⊆ B := Finset.filter_subset _ _
  have sub : A ∪ D ⊆ U.filter (H.Reachable a) := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_filter.mpr ⟨hAU h, hleft x h⟩
    · exact Finset.mem_filter.mpr ⟨hBU (hdB h), (Finset.mem_filter.mp h).2.reachable⟩
  have hc := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint (hAB.mono_right hdB)] at hc
  have hD : B.card ≤ D.card + k := blue _ haA
  omega

/-- A connected matching in a finite reduced graph admits an even closed
walk through every marked edge. The bound counts the cost of visiting the
edges one at a time and is independent of the cluster sizes. -/
lemma bounded_tour_of_reachable_edges {I : Type*} [Fintype I] (H : SimpleGraph I)
    (root : I) (u v : ℕ → I) (q : ℕ) (hr : ∀ i < q, H.Reachable root (u i))
    (he : ∀ i < q, H.Adj (u i) (v i)) :
    ∃ p : H.Walk root root, Even p.length ∧ p.length ≤ 2 * q * Fintype.card I ∧
      ∀ i < q, s(u i, v i) ∈ p.edges := by
  classical
  induction q with
  | zero => exact ⟨.nil, by simp, by simp, by simp⟩
  | succ q ih =>
    obtain ⟨p, hp, hlen, hseen⟩ := ih (fun i hi => hr i (by omega)) (fun i hi => he i (by omega))
    obtain ⟨w⟩ := hr q (by omega)
    let e : H.Walk (u q) (v q) := .cons (he q (by omega)) .nil
    let leg := w.bypass.append e
    have hl : leg.length ≤ Fintype.card I := by
      have hshort := w.bypass_isPath.length_lt
      change (w.bypass.append e).length ≤ _
      rw [Walk.length_append]
      have he1 : e.length = 1 := rfl
      omega
    refine ⟨p.append (leg.append leg.reverse), ?_, ?_, ?_⟩
    · rw [Walk.length_append, Walk.length_append, Walk.length_reverse]
      exact hp.add ⟨leg.length, rfl⟩
    · rw [Walk.length_append, Walk.length_append, Walk.length_reverse]
      rw [Nat.mul_succ, Nat.add_mul]
      omega
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [Walk.edges_append]
        exact List.mem_append_left _ (hseen i hi)
      · have hmem : s(u i,v i) ∈ leg.edges := by simp [leg,e,Walk.edges_append,Walk.edges_cons]
        simp only [Walk.edges_append, List.mem_append]
        exact Or.inr (Or.inl hmem)

/-- Routes from the exit of one matched edge to the entry of the next.
The closed tour obtained by inserting the marked edges has even length.
Each connector has at least one edge even if a shortest route passes back
over the marked edge. -/
lemma connected_matching_routes {I D : Type*} [Fintype I] [Fintype D] (H : SimpleGraph I)
    (root : I) (a b : D → I) (next : Equiv.Perm D)
    (hr : ∀ i, H.Reachable root (a i)) (he : ∀ i, H.Adj (a i) (b i)) :
    ∃ w : ∀ i, H.Walk (b i) (a (next i)),
      (∀ i, 0 < (w i).length ∧ (w i).length < 2*Fintype.card I) ∧
      Even (Fintype.card D + ∑ i, (w i).length) := by
  classical
  let walk (i : D) : H.Walk root (a i) := Classical.choice (hr i)
  let p (i : D) := (walk i).bypass
  let w (i : D) : H.Walk (b i) (a (next i)) := .cons (he i).symm ((p i).reverse.append (p (next i)))
  have len (i) : (w i).length = (p i).length + (p (next i)).length + 1 := by
    simp [w,Walk.length_append]
  refine ⟨w,?_,?_⟩
  · intro i
    have hi : (p i).length < Fintype.card I := (walk i).bypass_isPath.length_lt
    have hj : (p (next i)).length < Fintype.card I := (walk (next i)).bypass_isPath.length_lt
    rw [len]; omega
  · have perm : (∑ i, (p (next i)).length) = ∑ i, (p i).length :=
      Equiv.sum_comp next (fun i => (p i).length)
    refine ⟨Fintype.card D + ∑ i, (p i).length, ?_⟩
    simp_rw [len, Finset.sum_add_distrib, perm]
    simp; omega

/-- Construct the alternating path in the proof of Benevides, Lemma 5.7(a).
Its vertices on the first side may be specified in any simple order. Only
degrees on that side are needed. -/
lemma dense_pair_prescribed_left_order {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) (k : ℕ) (y : V) (hy : y ∈ A)
    (middle : List V) (B : Finset V) (x : V) (hx : x ∈ A) (hm : ∀ z ∈ middle, z ∈ A)
    (hsimple : (x :: (middle ++ [y])).Nodup) (hdis : Disjoint A B)
    (hmiss : ∀ z ∈ A, (B.filter fun w => ¬G.Adj z w).card ≤ k)
    (hsize : 2*k + middle.length + 1 ≤ B.card) :
    ∃ l : List V, l.length = 2*middle.length+1 ∧ (x :: (l ++ [y])).Nodup ∧
      (x :: (l ++ [y])).IsChain G.Adj ∧ l.filter (fun z => z ∈ A) = middle ∧ ∀ z ∈ l, z ∈ middle ∨ z ∈ B := by
  classical
  have common (B : Finset V) (u v : V) (hu : u ∈ A) (hv : v ∈ A)
      (hmiss : ∀ z ∈ A, (B.filter fun w => ¬G.Adj z w).card ≤ k)
      (hB : 2*k < B.card) : ∃ b ∈ B, G.Adj u b ∧ G.Adj v b := by
    let U := B.filter (G.Adj u)
    let W := B.filter (G.Adj v)
    have h1 := Finset.card_filter_add_card_filter_not (s := B) (G.Adj u)
    have h2 := Finset.card_filter_add_card_filter_not (s := B) (G.Adj v)
    have hU : B.card ≤ U.card + k := by dsimp [U]; have := hmiss u hu; omega
    have hW : B.card ≤ W.card + k := by dsimp [W]; have := hmiss v hv; omega
    have hsub : U ∪ W ⊆ B := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hc := Finset.card_union_add_card_inter U W
    have hc' := Finset.card_le_card hsub
    obtain ⟨b,hb⟩ := Finset.card_pos.mp (by omega : 0 < (U ∩ W).card)
    obtain ⟨hbu,hbw⟩ := Finset.mem_inter.mp hb
    exact ⟨b,(Finset.mem_filter.mp hbu).1,(Finset.mem_filter.mp hbu).2,(Finset.mem_filter.mp hbw).2⟩
  induction middle generalizing B x with
  | nil =>
    obtain ⟨b,hb,hxb,hyb⟩ := common B x y hx hy hmiss (by simpa using hsize)
    have hxy : x ≠ y := by simpa using hsimple
    have hbA : b ∉ A := fun h => Finset.disjoint_left.mp hdis h hb
    refine ⟨[b], by simp, ?_, ?_, by simp [hbA], ?_⟩
    · simp [hxb.ne,hxy,hyb.ne.symm]
    · simp [List.isChain_cons_cons,hxb,hyb.symm]
    · intro z hz
      simpa using (show z ∈ B from (List.mem_singleton.mp hz) ▸ hb)
  | cons u rest ih =>
    have hu := hm u (by simp)
    obtain ⟨b,hb,hxb,hub⟩ := common B x u hx hu hmiss (by simp at hsize; omega)
    have hB' : 2*k + rest.length + 1 ≤ (B.erase b).card := by
      rw [Finset.card_erase_of_mem hb]; simp at hsize; omega
    have less (z : V) (hz : z ∈ A) :
        ((B.erase b).filter fun w => ¬G.Adj z w).card ≤ k := by
      apply le_trans _ (hmiss z hz)
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
    obtain ⟨l,hlen,hs,hc,hord,hp⟩ := ih (B.erase b) u hu (fun z hz => hm z (by simp [hz]))
      (List.nodup_cons.mp hsimple).2 (hdis.mono_right (Finset.erase_subset _ _)) less hB'
    have nox := (List.nodup_cons.mp hsimple).1
    have hxrest : x ∉ rest := fun h => nox (by simp [h])
    have hxu : x ≠ u := fun e => nox (by simp [e])
    have hxy : x ≠ y := fun e => nox (by simp [e])
    have hxl : x ∉ l := by
      intro hit
      rcases hp x hit with h | h
      · exact hxrest h
      · exact Finset.disjoint_left.mp hdis hx (Finset.erase_subset _ _ h)
    have hbl : b ∉ l := by
      intro hit
      rcases hp b hit with h | h
      · exact Finset.disjoint_left.mp hdis (hm b (by simp [h])) hb
      · exact Finset.notMem_erase _ _ h
    have hby : b ≠ y := fun e => Finset.disjoint_left.mp hdis hy (e ▸ hb)
    have hbA : b ∉ A := fun h => Finset.disjoint_left.mp hdis h hb
    refine ⟨b :: u :: l, by simp [hlen]; omega, ?_, ?_, by simp [hbA,hu,hord], ?_⟩
    · exact List.nodup_cons.mpr ⟨by simp [hxb.ne,hxu,hxl,hxy],
        List.nodup_cons.mpr ⟨by simp [hub.ne.symm,hbl,hby],hs⟩⟩
    · exact List.isChain_cons_cons.mpr ⟨hxb,List.isChain_cons_cons.mpr ⟨hub.symm,hc⟩⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inr hb
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inl (by simp)
      rcases hp z hz with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (Finset.erase_subset _ _ h)

/-- Removing up to half the vertices on either side preserves regularity
with parameter 2ε and costs less than ε in density. In particular the
vertices of previously embedded connectors may be deleted before a
matched pair is expanded. -/
lemma regular_pair_after_deletions {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T A B : Finset V} {ε : ℚ} (hreg : G.IsUniform ε S T)
    (he : ε ≤ 1/2) (ha : A ⊆ S) (hb : B ⊆ T) (hA : S.card ≤ 2*A.card)
    (hB : T.card ≤ 2*B.card) :
    G.IsUniform (2*ε) A B ∧ G.edgeDensity S T - ε < G.edgeDensity A B := by
  have hpos := hreg.pos.le
  have half (a n : ℕ) (h : n ≤ 2*a) : (n : ℚ)*ε ≤ a := by
    have h' : (n : ℚ) ≤ 2*a := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ (n : ℚ) by positivity)]
  have big (a n : ℕ) (h : n ≤ 2*a) : (n : ℚ)*ε ≤ a*(2*ε) := by
    have h' : (n : ℚ) ≤ 2*a := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_right h' hpos]
  have hab : |G.edgeDensity A B - G.edgeDensity S T| < ε := by
    simpa using hreg ha hb (half _ _ hA) (half _ _ hB)
  constructor
  · intro X hX Y hY hx hy
    have hxy : |G.edgeDensity X Y - G.edgeDensity S T| < ε := by
      simpa using hreg (hX.trans ha) (hY.trans hb) ((big _ _ hA).trans hx) ((big _ _ hB).trans hy)
    have htri := abs_sub_le (G.edgeDensity X Y) (G.edgeDensity S T) (G.edgeDensity A B)
    rw [abs_sub_comm (G.edgeDensity S T) (G.edgeDensity A B)] at htri
    have h : |G.edgeDensity X Y - G.edgeDensity A B| < 2*ε := by linarith
    simpa using h
  · linarith [(abs_lt.mp hab).1]

/-- Expand a matched pair while avoiding the vertices already assigned to
other connectors. The input degree and size conditions are measured before
deletion, and the forbidden budget is charged explicitly. -/
lemma regular_pair_path_avoiding {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T F : Finset V} {ε : ℚ} (hreg : G.IsUniform ε S T)
    (he : ε ≤ 1/2) (hd : 3*ε ≤ G.edgeDensity S T) (hst : Disjoint S T)
    (k m r : ℕ) (hkm : k ≤ m) (hS : 2*F.card ≤ S.card) (hT : 2*F.card ≤ T.card)
    (hthS : (S.card : ℚ)*(2*ε) ≤ k) (hthT : (T.card : ℚ)*(2*ε) ≤ k)
    (hden : (k : ℚ) ≤ (G.edgeDensity S T - 3*ε)*m)
    (hcapS : m + r + k + 1 + F.card ≤ S.card) (hcapT : m + r + 1 + F.card ≤ T.card)
    {x y : V} (hx : x ∈ S) (hy : y ∈ T) (hxF : x ∉ F) (hyF : y ∉ F)
    (hxdeg : k + F.card < (T.filter (G.Adj x)).card)
    (hydeg : k + F.card < (S.filter (G.Adj y)).card) :
    ∃ l : List V, l.length = 2*r+2 ∧ (x :: (l ++ [y])).Nodup ∧
      (x :: (l ++ [y])).IsChain G.Adj ∧ ∀ z ∈ l, (z ∈ S ∨ z ∈ T) ∧ z ∉ F := by
  classical
  let A := S \ F
  let B := T \ F
  have hAS : A ⊆ S := Finset.sdiff_subset
  have hBT : B ⊆ T := Finset.sdiff_subset
  have hca : S.card - F.card ≤ A.card := Finset.le_card_sdiff F S
  have hcb : T.card - F.card ≤ B.card := Finset.le_card_sdiff F T
  obtain ⟨hreg',hd'⟩ := regular_pair_after_deletions G hreg he hAS hBT (by omega) (by omega)
  have deg (v : V) (U : Finset V) (hu : k + F.card < (U.filter (G.Adj v)).card) :
      k < ((U \ F).filter (G.Adj v)).card := by
    have heq : (U \ F).filter (G.Adj v) = (U.filter (G.Adj v)) \ F := by
      ext w
      simp [and_assoc, and_comm, and_left_comm]
    rw [heq]
    have h := Finset.le_card_sdiff F (U.filter (G.Adj v))
    omega
  have h2ε : 0 ≤ 2*ε := by linarith [hreg.pos]
  have threshold {P Q : Finset V} (hp : P ⊆ Q) (h : (Q.card : ℚ)*(2*ε) ≤ k) :
      (P.card : ℚ)*(2*ε) ≤ k :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hp) h2ε).trans h
  have hden' : (k : ℚ) ≤ (G.edgeDensity A B - 2*ε)*m :=
    hden.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
  obtain ⟨l,hl,hs,hc,hpool⟩ := regular_pair_path_between G hreg' (by linarith) (hst.mono hAS hBT)
    k m r (threshold hAS hthS) (threshold hBT hthT) hkm hden' (by omega) (by omega)
    (Finset.mem_sdiff.mpr ⟨hx,hxF⟩) (Finset.mem_sdiff.mpr ⟨hy,hyF⟩) (deg x T hxdeg) (deg y S hydeg)
  refine ⟨l,hl,hs,hc,?_⟩
  intro z hz
  rcases hpool z hz with h | h
  · exact ⟨Or.inl (hAS h),(Finset.mem_sdiff.mp h).2⟩
  · exact ⟨Or.inr (hBT h),(Finset.mem_sdiff.mp h).2⟩

/-- Append a reserved connector to a simple path without shifting its
starting endpoint. The connector may have no internal vertices. -/
lemma append_reserved_connector {V : Type*} (G : SimpleGraph V) {a b : V} (L J : List V)
    (hpath : (a :: (L ++ [b])).Nodup) (hchain : (a :: (L ++ [b])).IsChain G.Adj)
    (hJ : J.Nodup) (hcJ : (b :: J).IsChain G.Adj)
    (hdis : (a :: (L ++ [b])).Disjoint J) :
    let e := (b :: J).getLast (by simp)
    ∃ M : List V, M.length = L.length + J.length ∧ (a :: (M ++ [e])).Nodup ∧
      (a :: (M ++ [e])).IsChain G.Adj ∧
      ∀ z ∈ a :: (M ++ [e]), z ∈ a :: (L ++ [b]) ∨ z ∈ J := by
  let Q := b :: J
  have hQ : Q ≠ [] := by simp [Q]
  let e := Q.getLast hQ
  have heq : Q.dropLast ++ [e] = b :: J := List.dropLast_concat_getLast hQ
  let M := L ++ Q.dropLast
  have hjoin : a :: (M ++ [e]) = (a :: (L ++ [b])) ++ J := by
    simp only [M,List.append_assoc,heq,List.cons_append,List.nil_append]
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · simp [M,Q]
  · rw [hjoin]
    exact List.nodup_append'.mpr ⟨hpath,hJ,hdis⟩
  · rw [hjoin]
    change (a :: ((L ++ [b]) ++ J)).IsChain G.Adj
    rw [List.append_assoc]
    exact List.isChain_cons_split.mpr ⟨hchain,hcJ⟩
  · rw [hjoin]
    exact fun _ hz => List.mem_append.mp hz

/-- Expand a matching of regular pairs linked by concrete connector paths.
Connector interiors may visit other matched clusters. All their vertices
are charged to F once and reserved throughout the expansion. -/
lemma cycle_from_routed_regular_matching {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : ℕ) (S T : ℕ → Finset V) (a b : ℕ → V) (J : ℕ → List V)
    (F : Finset V) (ε : ℚ) (he : ε ≤ 1/2) (k m : ℕ) (hkm : k ≤ m) (cap : ℕ → ℕ)
    (hreg : ∀ i ≤ t, G.IsUniform ε (S i) (T i))
    (hd : ∀ i ≤ t, 3*ε ≤ G.edgeDensity (S i) (T i))
    (hst : ∀ i ≤ t, Disjoint (S i) (T i))
    (hsep : ∀ i j, i < j → j ≤ t → Disjoint (S i ∪ T i) (S j ∪ T j))
    (hsmall : ∀ i ≤ t, 2*F.card ≤ (S i).card ∧ 2*F.card ≤ (T i).card)
    (hth : ∀ i ≤ t, ((S i).card : ℚ)*(2*ε) ≤ k ∧ ((T i).card : ℚ)*(2*ε) ≤ k)
    (hden : ∀ i ≤ t, (k : ℚ) ≤ (G.edgeDensity (S i) (T i) - 3*ε)*m)
    (hcap : ∀ i ≤ t, m + cap i + k + 1 + F.card ≤ (S i).card ∧
        m + cap i + 1 + F.card ≤ (T i).card)
    (hab : ∀ i ≤ t, a i ∈ S i ∧ b i ∈ T i ∧ a i ∉ F ∧ b i ∉ F)
    (hdeg : ∀ i ≤ t, k + F.card < ((T i).filter (G.Adj (a i))).card ∧
        k + F.card < ((S i).filter (G.Adj (b i))).card)
    (hJ : ∀ i ≤ t, (J i).Nodup ∧ (b i :: J i).IsChain G.Adj ∧ ∀ z ∈ J i, z ∈ F)
    (hJJ : ∀ i j, i < j → j ≤ t → (J i).Disjoint (J j))
    (hlink : ∀ i < t, G.Adj ((b i :: J i).getLast (by simp)) (a (i+1)))
    (hclose : G.Adj ((b t :: J t).getLast (by simp)) (a 0))
    (n q : ℕ) (hn : 3 ≤ n) (hq : q ≤ ∑ i ∈ Finset.range (t+1), cap i)
    (horder : n = (∑ i ∈ Finset.range (t+1), (4 + (J i).length)) + 2*q) :
    (cycleGraph n).IsContained G := by
  classical
  let pair (i : ℕ) := (S i ∪ T i) \ F
  let pool (i : ℕ) := pair i ∪ (J i).toFinset
  let e (i : ℕ) := (b i :: J i).getLast (by simp)
  refine cycle_of_flexible_segments G t a e pool (fun i => 2 + (J i).length) cap ?_ hlink hclose ?_
    n q hn hq ?_
  · intro i hi j hj
    obtain ⟨hx,hy,hxF,hyF⟩ := hab i hi
    obtain ⟨hS,hT⟩ := hcap i hi
    obtain ⟨L,hL,hs,hc,hpool⟩ := regular_pair_path_avoiding G (hreg i hi) he (hd i hi) (hst i hi)
      k m j hkm (hsmall i hi).1 (hsmall i hi).2 (hth i hi).1 (hth i hi).2 (hden i hi)
      (by omega) (by omega) hx hy hxF hyF (hdeg i hi).1 (hdeg i hi).2
    have inPair (z) (hz : z ∈ a i :: (L ++ [b i])) : z ∈ pair i := by
      apply Finset.mem_sdiff.mpr
      simp at hz
      rcases hz with rfl | h | rfl
      · exact ⟨Finset.mem_union_left _ hx,hxF⟩
      · exact ⟨Finset.mem_union.mpr (hpool z h).1,(hpool z h).2⟩
      · exact ⟨Finset.mem_union_right _ hy,hyF⟩
    have sep : (a i :: (L ++ [b i])).Disjoint (J i) := fun z h h' =>
      (Finset.mem_sdiff.mp (inPair z h)).2 ((hJ i hi).2.2 z h')
    obtain ⟨M,hM,hs',hc',hverts⟩ := append_reserved_connector G L (J i) hs hc
      (hJ i hi).1 (hJ i hi).2.1 sep
    refine ⟨M,by omega,hs',hc',?_⟩
    intro z hz
    rcases hverts z hz with h | h
    · exact Finset.mem_union_left _ (inPair z h)
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr h)
  · intro i j hij hj
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    rcases Finset.mem_union.mp hz with h | h <;> rcases Finset.mem_union.mp hz' with h' | h'
    · exact Finset.disjoint_left.mp (hsep i j hij hj) (Finset.mem_sdiff.mp h).1 (Finset.mem_sdiff.mp h').1
    · exact (Finset.mem_sdiff.mp h).2 ((hJ j hj).2.2 z (List.mem_toFinset.mp h'))
    · exact (Finset.mem_sdiff.mp h').2 ((hJ i (by omega)).2.2 z (List.mem_toFinset.mp h))
    · exact hJJ i j hij hj (List.mem_toFinset.mp h) (List.mem_toFinset.mp h')
  · simpa only [show ∀ i, 2 + (J i).length + 2 = 4 + (J i).length by intro; omega] using horder

/-- Exact-length lifting from a system of reduced routes. Only the matched
cluster pairs must be disjoint. Intermediate visits can repeat arbitrarily,
both within one connector and between different connectors. -/
lemma cycle_from_reduced_routes {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t N : ℕ) (S T : ℕ → Finset V) (r : ℕ → ℕ)
    (C : ℕ → ℕ → Finset V) (cap : ℕ → ℕ) (ε d : ℚ)
    (he : ε ≤ 1/2) (hd : 3*ε ≤ d) (k m M s : ℕ) (hk : 0 < k) (hkm : k ≤ m)
    (hth : (N : ℚ)*(2*ε) ≤ k) (hden : (k : ℚ) ≤ (d-3*ε)*m)
    (hs : m + M + (t+1)*M ≤ s) (h2s : 2*s ≤ N) (htyp : (s : ℚ) ≤ (d-ε)*N)
    (hsize : ∀ i ≤ t, (S i).card = N ∧ (T i).card = N)
    (hcap : ∀ i ≤ t, m + cap i + k + 1 + (t+1)*M ≤ N)
    (hpair : ∀ i ≤ t, G.IsUniform ε (S i) (T i) ∧ d ≤ G.edgeDensity (S i) (T i))
    (hst : ∀ i ≤ t, Disjoint (S i) (T i))
    (hsep : ∀ i j, i < j → j ≤ t → Disjoint (S i ∪ T i) (S j ∪ T j))
    (hbound : ∀ i ≤ t, r i + 2 ≤ M)
    (hends : ∀ i ≤ t, C i 0 = T i ∧ C i (r i+1) = S (if i < t then i+1 else 0))
    (hcount : ∀ i ≤ t, ∀ j ≤ r i+1, (C i j).card = N)
    (hroute : ∀ i ≤ t, ∀ j < r i+1, G.IsUniform ε (C i j) (C i (j+1)) ∧
      d ≤ G.edgeDensity (C i j) (C i (j+1)))
    (n q : ℕ) (hn : 3 ≤ n) (hq : q ≤ ∑ i ∈ Finset.range (t+1), cap i)
    (hlen : n = (∑ i ∈ Finset.range (t+1), (4+r i)) + 2*q) :
    (cycleGraph n).IsContained G := by
  classical
  let next (i : ℕ) := if i < t then i+1 else 0
  have hnext (i) : next i ≤ t := by dsimp [next]; split <;> omega
  let A (i : ℕ) := (S i).filter fun x => s < ((T i).filter (G.Adj x)).card
  let B (i : ℕ) := (T i).filter fun x => s < ((S i).filter (G.Adj x)).card
  have he0 : 0 ≤ ε := (hpair 0 (by omega)).1.pos.le
  have hδ : ε ≤ d := by linarith
  have hs' : k ≤ s := by omega
  have hN : (N : ℚ)*ε ≤ k := by nlinarith [mul_nonneg (show 0 ≤ (N : ℚ) by positivity) he0]
  have typ (i) (hi : i ≤ t) : s ≤ (A i).card ∧ s ≤ (B i).card := by
    obtain ⟨hS,hT⟩ := hsize i hi
    obtain ⟨reg,den⟩ := hpair i hi
    have hmono := mul_le_mul_of_nonneg_right (sub_le_sub_right den ε) (show 0 ≤ (N : ℚ) by positivity)
    have th' : (N : ℚ)*ε ≤ s := hN.trans (by exact_mod_cast hs')
    have hbig : (N : ℚ)*ε ≤ N := hN.trans (by exact_mod_cast (show k ≤ N by omega))
    constructor
    · apply regular_pair_eligible_endpoints G reg (hδ.trans den) s
      · simpa [hS] using th'
      · simpa [hT] using hbig
      · simpa [hT] using htyp.trans hmono
      · simpa [hS] using h2s
    · apply regular_pair_eligible_endpoints G reg.symm (by rw [G.edgeDensity_comm (T i)]; exact hδ.trans den) s
      · simpa [hT] using th'
      · simpa [hS] using hbig
      · rw [G.edgeDensity_comm (T i),hS]; exact htyp.trans hmono
      · simpa [hT] using h2s
  have mulbound (i : ℕ) (hi : i < t+1) : i*M ≤ (t+1)*M := Nat.mul_le_mul_right M hi.le
  have hdeg' : (k : ℚ) ≤ (d-ε)*m := hden.trans
    (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
  obtain ⟨f,used,hused,hf,hsepF⟩ := disjoint_regular_routes G hδ k m hk hkm hdeg' (t+1) M r C B
    (fun i => A (next i)) (fun i hi => hbound i (by omega))
    (fun i hi => by
      obtain ⟨h0,h1⟩ := hends i (by omega)
      rw [h0,h1]
      exact ⟨Finset.filter_subset _ _,Finset.filter_subset _ _⟩)
    (fun i hi => by have h := (typ i (by omega)).2; have := mulbound i hi; omega)
    (fun i hi => by have h := (typ (next i) (hnext i)).1; have := hbound i (by omega); have := mulbound i hi; omega)
    (fun i hi j hj => by rw [hcount i (by omega) j hj]; exact hN)
    (fun i hi j hj => by rw [hcount i (by omega) (j+1) (by omega)]; have := hbound i (by omega); have := mulbound i hi; omega)
    (fun i hi => hroute i (by omega))
  obtain ⟨a,b,J,F,hFu,hab,hJ,hJJ,hlink,hclose⟩ := organize_matching_connectors G t A B r f used
    (fun i hi => hf i (by omega)) (fun i j hij hj => hsepF i j hij (by omega))
  have hF := (Finset.card_le_card hFu).trans hused
  refine cycle_from_routed_regular_matching G t S T a b J F ε he k m hkm cap
    (fun i hi => (hpair i hi).1) (fun i hi => hd.trans (hpair i hi).2) hst hsep ?_ ?_ ?_ ?_ ?_ ?_
    (fun i hi => (hJ i hi).2) hJJ hlink hclose n q hn hq ?_
  · intro i hi
    rw [(hsize i hi).1,(hsize i hi).2]; omega
  · intro i hi
    rw [(hsize i hi).1,(hsize i hi).2]; exact ⟨hth,hth⟩
  · intro i hi
    exact hden.trans (mul_le_mul_of_nonneg_right (sub_le_sub_right (hpair i hi).2 _) (Nat.cast_nonneg _))
  · intro i hi
    rw [(hsize i hi).1,(hsize i hi).2]; have := hcap i hi; omega
  · intro i hi
    obtain ⟨ha,hb,haF,hbF⟩ := hab i hi
    exact ⟨(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp hb).1,haF,hbF⟩
  · intro i hi
    obtain ⟨ha,hb,_,_⟩ := hab i hi
    exact ⟨lt_of_le_of_lt (by omega : k+F.card ≤ s) (Finset.mem_filter.mp ha).2,
      lt_of_le_of_lt (by omega : k+F.card ≤ s) (Finset.mem_filter.mp hb).2⟩
  · rw [hlen]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [(hJ i (by have := Finset.mem_range.mp hi; omega)).1]

/-- Lift a monochromatic connected matching from a finite reduced graph.
Every even order between the stated bounds is realized. The lower bound
allows for the connector tour and the upper bound uses the combined
capacity of the matched pairs. -/
lemma cycle_of_reduced_connected_matching {V I : Type*} [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph I)
    (C : I → Finset V) (N : ℕ) (hN : ∀ i, (C i).card = N)
    (ε d : ℚ) (he : ε ≤ 1/2) (hd : 3*ε ≤ d)
    (hred : ∀ i j, H.Adj i j → G.IsUniform ε (C i) (C j) ∧ d ≤ G.edgeDensity (C i) (C j))
    (root : I) (t : ℕ) (u v : Fin (t+1) → I)
    (hr : ∀ i, H.Reachable root (u i)) (hed : ∀ i, H.Adj (u i) (v i))
    (hpair : ∀ i, Disjoint (C (u i)) (C (v i)))
    (hsep : ∀ i j, i < j → Disjoint (C (u i) ∪ C (v i)) (C (u j) ∪ C (v j)))
    (k m s cap : ℕ) (hk : 0 < k) (hkm : k ≤ m)
    (hth : (N : ℚ)*(2*ε) ≤ k) (hden : (k : ℚ) ≤ (d-3*ε)*m)
    (hs : m + 2*Fintype.card I + (t+1)*(2*Fintype.card I) ≤ s)
    (h2s : 2*s ≤ N) (htyp : (s : ℚ) ≤ (d-ε)*N)
    (hcap : m + cap + k + 1 + (t+1)*(2*Fintype.card I) ≤ N)
    (n : ℕ) (hn : 3 ≤ n) (heven : Even n)
    (hmin : (t+1)*(2*Fintype.card I + 2) ≤ n)
    (hmax : n ≤ 4*(t+1) + 2*((t+1)*cap)) :
    (cycleGraph n).IsContained G := by
  classical
  let p := t+1
  let M := 2*Fintype.card I
  let next : Equiv.Perm (Fin (t+1)) := Equiv.addRight 1
  obtain ⟨w,hw,hpar⟩ := connected_matching_routes H root u v next hr hed
  let idx (i : ℕ) : Fin (t+1) := ⟨i % (t+1), Nat.mod_lt _ (by omega)⟩
  have valid (i : Fin (t+1)) : idx i = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have idxval (i) (hi : i ≤ t) : (idx i).val = i := Nat.mod_eq_of_lt (by omega)
  have cyclic (i) (hi : i ≤ t) : next (idx i) = idx (if i < t then i+1 else 0) := by
    change idx i + 1 = _
    by_cases h : i < t
    · apply Fin.ext
      rw [Fin.val_add_one_of_lt (show idx i < Fin.last t by change (idx i).val < t; rwa [idxval i hi])]
      simp only [if_pos h, idxval i hi, idxval (i+1) (by omega)]
    · have e : idx i = Fin.last t := Fin.ext (by rw [idxval i hi]; simp; omega)
      rw [e,Fin.last_add_one,if_neg h]
      exact Fin.ext (by simp [idx])
  let r (i : ℕ) := (w (idx i)).length - 1
  let route (i j : ℕ) := C ((w (idx i)).getVert j)
  have hrlen (i) : r i + 1 = (w (idx i)).length := by dsimp [r]; have := (hw (idx i)).1; omega
  have hbound (i) : r i + 2 ≤ M := by have := (hw (idx i)).2; have := hrlen i; dsimp [M]; omega
  let base := ∑ i ∈ Finset.range p, (4+r i)
  have hsum : (∑ i ∈ Finset.range p, (r i + 1)) = ∑ i, (w i).length := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    exact (hrlen i.val).trans (congrArg (fun j => (w j).length) (valid i))
  have bval : base = 4*p + ∑ i ∈ Finset.range p, r i := by simp [base,Finset.sum_add_distrib,Nat.mul_comm]
  have low : base ≤ n := by
    have small : base ≤ ∑ _i ∈ Finset.range p, (M+2) :=
      Finset.sum_le_sum fun i _ => by have := hbound i; omega
    have h : base ≤ p*(M+2) := by simpa using small
    exact h.trans hmin
  have big : 4*p ≤ base := by omega
  have parity : Even base := by
    obtain ⟨b,hb⟩ := hpar
    rw [← hsum, Finset.sum_add_distrib] at hb
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Fintype.card_fin] at hb
    change p + ((∑ i ∈ Finset.range p, r i) + p) = b + b at hb
    exact ⟨b+p,by omega⟩
  let q := (n-base)/2
  have exactlen : n = base + 2*q := by
    obtain ⟨j,hj⟩ := heven
    obtain ⟨b,hb⟩ := parity
    dsimp [q]; omega
  have lim : q ≤ p*cap := by change n ≤ 4*p+2*(p*cap) at hmax; omega
  refine cycle_from_reduced_routes G t N (fun i => C (u (idx i))) (fun i => C (v (idx i)))
    r route (fun _ => cap) ε d he hd k m M s hk hkm hth hden hs h2s htyp
    (fun _ _ => ⟨hN _,hN _⟩) (fun _ _ => hcap) (fun _ _ => hred _ _ (hed _))
    (fun _ _ => hpair _) (fun i j hij hj => hsep _ _ (by change (idx i).val < (idx j).val; rwa [idxval i (by omega),idxval j hj]))
    (fun i _ => hbound i) ?_ (fun _ _ _ _ => hN _) ?_ n q hn (by simpa [p] using lim) exactlen
  · intro i hi
    constructor
    · simp [route]
    · dsimp [route]
      rw [hrlen,Walk.getVert_length,cyclic i hi]
  · intro i hi j hj
    apply hred
    exact (w (idx i)).adj_getVert_succ (by rwa [← hrlen])

/-- At a host of exactly 2n vertices, the excess of four times the
matching size over the number of clusters pays for discarded vertices
and the unused capacity of each matched pair. -/
lemma matching_capacity_at_sharp_host (n N c p exc loss : ℕ)
    (hhost : 2*n ≤ c*N + exc) (hmatch : c ≤ 4*p) (hfit : loss ≤ N)
    (hslack : 4*p*loss + exc ≤ (4*p-c)*N) :
    n ≤ 4*p + 2*(p*(N-loss)) := by
  have hfull : (4*p-c)*N + c*N = 4*p*N := by rw [← Nat.add_mul, Nat.sub_add_cancel hmatch]
  have hcap : 4*p*(N-loss) + 4*p*loss = 4*p*N := by rw [← Nat.mul_add, Nat.sub_add_cancel hfit]
  have hdouble : 4*p*(N-loss) = 2*(2*(p*(N-loss))) := by ring
  omega

/-- The connected-matching case at the sharp host size. The counting
hypotheses allow an exceptional set of size exc outside the equal clusters.
All reduced edges in H have the indicated density in the same colour. -/
lemma sharp_host_of_connected_matching {I : Type*} [Fintype I] (n : ℕ)
    (col : Fin 3 → SimpleGraph (Fin (2*n))) (i : Fin 3) [DecidableRel (col i).Adj]
    (H : SimpleGraph I) (C : I → Finset (Fin (2*n))) (N : ℕ) (hN : ∀ j, (C j).card = N)
    (ε d : ℚ) (he : ε ≤ 1/2) (hd : 3*ε ≤ d)
    (hred : ∀ x y, H.Adj x y → (col i).IsUniform ε (C x) (C y) ∧ d ≤ (col i).edgeDensity (C x) (C y))
    (root : I) (t : ℕ) (u v : Fin (t+1) → I)
    (hr : ∀ j, H.Reachable root (u j)) (hed : ∀ j, H.Adj (u j) (v j))
    (hpair : ∀ j, Disjoint (C (u j)) (C (v j)))
    (hsep : ∀ j l, j < l → Disjoint (C (u j) ∪ C (v j)) (C (u l) ∪ C (v l)))
    (k m s exc : ℕ) (hk : 0 < k) (hkm : k ≤ m)
    (hth : (N : ℚ)*(2*ε) ≤ k) (hden : (k : ℚ) ≤ (d-3*ε)*m)
    (hs : m + 2*Fintype.card I + (t+1)*(2*Fintype.card I) ≤ s)
    (h2s : 2*s ≤ N) (htyp : (s : ℚ) ≤ (d-ε)*N)
    (hn : 3 ≤ n) (heven : Even n) (hmin : (t+1)*(2*Fintype.card I+2) ≤ n)
    (hhost : 2*n ≤ Fintype.card I*N + exc) (hmatch : Fintype.card I ≤ 4*(t+1))
    (hfit : m+k+1+(t+1)*(2*Fintype.card I) ≤ N)
    (hslack : 4*(t+1)*(m+k+1+(t+1)*(2*Fintype.card I)) + exc ≤
      (4*(t+1)-Fintype.card I)*N) :
    ∃ j, (cycleGraph n).IsContained (col j) := by
  let loss := m+k+1+(t+1)*(2*Fintype.card I)
  have hbudget : m + (N-loss) + k + 1 + (t+1)*(2*Fintype.card I) ≤ N := by dsimp [loss]; omega
  refine ⟨i,cycle_of_reduced_connected_matching (col i) H C N hN ε d he hd hred root t u v
    hr hed hpair hsep k m s (N-loss) hk hkm hth hden hs h2s htyp hbudget n hn heven hmin ?_⟩
  exact matching_capacity_at_sharp_host n N _ (t+1) exc loss hhost hmatch hfit hslack

/-- Splitting both sides of a pair increases its size-weighted mean square
density by exactly the variance of the subpair densities. In particular a
refinement chosen to repair one colour cannot cost energy in another. -/
lemma cluster_refinement_variance {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T : Finset V} (hS : S.Nonempty) (hT : T.Nonempty)
    (P : Finpartition S) (Q : Finpartition T) :
    let blocks := P.parts ×ˢ Q.parts
    let weight := fun z : Finset V × Finset V => (z.1.card : ℚ) * z.2.card
    let d := fun z : Finset V × Finset V => G.edgeDensity z.1 z.2
    (∑ z ∈ blocks, weight z * (d z)^2) =
      (S.card : ℚ) * T.card * (G.edgeDensity S T)^2 +
      ∑ z ∈ blocks, weight z * (d z - G.edgeDensity S T)^2 := by
  classical
  let blocks := P.parts ×ˢ Q.parts
  let w (z : Finset V × Finset V) : ℚ := z.1.card * z.2.card
  let f (z : Finset V × Finset V) := G.edgeDensity z.1 z.2
  let D := G.edgeDensity S T
  change (∑ z ∈ blocks, w z * (f z)^2) =
    (S.card : ℚ) * T.card * D^2 + ∑ z ∈ blocks, w z * (f z-D)^2
  have hweight : ∑ z ∈ blocks, w z = (S.card : ℚ) * T.card := by
    change (∑ z ∈ P.parts ×ˢ Q.parts, (z.1.card : ℚ) * z.2.card) = _
    rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    exact_mod_cast congrArg₂ (· * ·) P.sum_card_parts Q.sum_card_parts
  have hmass {A B : Finset V} (ha : A.Nonempty) (hb : B.Nonempty) :
      ((A.card : ℚ) * B.card) * G.edgeDensity A B = (G.interedges A B).card := by
    rw [G.edgeDensity_def]
    field_simp [show (A.card : ℚ) ≠ 0 by exact_mod_cast ha.card_pos.ne',
      show (B.card : ℚ) ≠ 0 by exact_mod_cast hb.card_pos.ne']
  have hmean : ∑ z ∈ blocks, w z * f z = ((S.card : ℚ) * T.card) * D := by
    rw [show (S.card : ℚ) * T.card * D = (G.interedges S T).card from hmass hS hT]
    calc
      _ = ∑ z ∈ blocks, ((G.interedges z.1 z.2).card : ℚ) := by
        apply Finset.sum_congr rfl
        intro z hz
        obtain ⟨ha,hb⟩ := Finset.mem_product.mp hz
        exact hmass (P.nonempty_of_mem_parts ha) (Q.nonempty_of_mem_parts hb)
      _ = _ := by exact_mod_cast (Rel.card_interedges_finpartition G.Adj P Q).symm
  have expand (z) : w z * (f z - D)^2 = w z * (f z)^2 - (w z * f z) * (2*D) + w z * D^2 := by ring
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hmean, hweight]
  ring

/-- A rectangle witnessing non-regularity forces a fourth-power energy
gain when the refinement has that rectangle as one of its cells. -/
lemma irregular_rectangle_energy_gain {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T : Finset V} (hS : S.Nonempty) (hT : T.Nonempty)
    (P : Finpartition S) (Q : Finpartition T) {A B : Finset V} (hA : A ∈ P.parts)
    (hB : B ∈ Q.parts) {ε : ℚ} (he : 0 ≤ ε)
    (hs : (S.card : ℚ)*ε ≤ A.card) (ht : (T.card : ℚ)*ε ≤ B.card)
    (hgap : ε ≤ |G.edgeDensity A B - G.edgeDensity S T|) :
    (S.card : ℚ) * T.card * ((G.edgeDensity S T)^2 + ε^4) ≤
      ∑ z ∈ P.parts ×ˢ Q.parts, (z.1.card : ℚ) * z.2.card * (G.edgeDensity z.1 z.2)^2 := by
  classical
  let D := G.edgeDensity S T
  let term (z : Finset V × Finset V) :=
    (z.1.card : ℚ) * z.2.card * (G.edgeDensity z.1 z.2 - D)^2
  have hvar := cluster_refinement_variance G hS hT P Q
  change _ = (S.card : ℚ) * T.card * D^2 + ∑ z ∈ P.parts ×ˢ Q.parts, term z at hvar
  have hw := mul_le_mul hs ht (mul_nonneg (Nat.cast_nonneg _) he) (Nat.cast_nonneg _)
  have hsq : ε^2 ≤ (G.edgeDensity A B - D)^2 := by
    have h := pow_le_pow_left₀ he hgap 2
    simpa [D, sq_abs] using h
  have hpart : (S.card : ℚ)*T.card*ε^4 ≤ term (A,B) := by
    have h := mul_le_mul hw hsq (sq_nonneg ε)
      (mul_nonneg (Nat.cast_nonneg A.card) (Nat.cast_nonneg B.card))
    dsimp [term]
    nlinarith only [h]
  have hsum : term (A,B) ≤ ∑ z ∈ P.parts ×ˢ Q.parts, term z :=
    Finset.single_le_sum (fun z _ => by dsimp [term]; positivity) (Finset.mem_product.mpr ⟨hA,hB⟩)
  rw [hvar, mul_add]
  exact add_le_add (le_refl _) (hpart.trans hsum)

/-- Size-weighted squared density is monotone under a common partition
refinement. This applies independently to all three colours, including
colours that did not determine the refinement. -/
lemma weighted_energy_mono_bind {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {U : Finset V} (P : Finpartition U)
    (Q : ∀ A ∈ P.parts, Finpartition A) :
    let F := fun A B : Finset V => (A.card : ℚ)*B.card*(G.edgeDensity A B)^2
    ∑ A ∈ P.parts, ∑ B ∈ P.parts, F A B ≤
      ∑ A ∈ (P.bind Q).parts, ∑ B ∈ (P.bind Q).parts, F A B := by
  classical
  let F (A B : Finset V) := (A.card : ℚ)*B.card*(G.edgeDensity A B)^2
  let child (A : P.parts) := (Q A.val A.property).parts
  have bind_sum (f : Finset V → ℚ) :
      ∑ X ∈ (P.bind Q).parts, f X = ∑ A ∈ P.parts.attach, ∑ X ∈ child A, f X :=
    Finpartition.sum_combine (fun A : P.parts => Q A.val A.property) P.supIndep.attach f
  have cell (A B : P.parts) :
      F A.val B.val ≤ ∑ X ∈ child A, ∑ Y ∈ child B, F X Y := by
    have h := cluster_refinement_variance G (P.nonempty_of_mem_parts A.property)
      (P.nonempty_of_mem_parts B.property) (Q _ A.property) (Q _ B.property)
    dsimp only at h
    have hvar : 0 ≤ ∑ z ∈ (child A) ×ˢ (child B),
        (z.1.card : ℚ) * z.2.card * (G.edgeDensity z.1 z.2 - G.edgeDensity A B)^2 :=
      Finset.sum_nonneg (fun z _ => by positivity)
    rw [Finset.sum_product] at h
    exact (le_add_of_nonneg_right hvar).trans_eq h.symm
  change ∑ A ∈ P.parts, ∑ B ∈ P.parts, F A B ≤ _
  calc
    _ = ∑ A ∈ P.parts.attach, ∑ B ∈ P.parts.attach, F A.val B.val := by
      calc
        _ = ∑ A ∈ P.parts.attach, (fun X => ∑ B ∈ P.parts, F X B) A.val :=
          (Finset.sum_attach _ _).symm
        _ = _ := Finset.sum_congr rfl fun A _ => (Finset.sum_attach _ (F A.val)).symm
    _ ≤ ∑ A ∈ P.parts.attach, ∑ B ∈ P.parts.attach, ∑ X ∈ child A, ∑ Y ∈ child B, F X Y :=
      Finset.sum_le_sum (fun A _ => Finset.sum_le_sum (fun B _ => cell A B))
    _ = ∑ A ∈ P.parts.attach, ∑ X ∈ child A, ∑ B ∈ P.parts.attach, ∑ Y ∈ child B, F X Y := by
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.sum_comm]
    _ = ∑ X ∈ (P.bind Q).parts, ∑ Y ∈ (P.bind Q).parts, F X Y := by
      rw [bind_sum (fun X => ∑ Y ∈ (P.bind Q).parts, F X Y)]
      simp_rw [bind_sum (F _)]

/-- Compare the refinement-monotone weighted energy with Mathlib's
off-diagonal energy on an equipartition. This includes the contribution of
the diagonal cells and the rounding in the part sizes. -/
lemma equipartition_weighted_energy_bounds {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {U : Finset V} (P : Finpartition U) (hP : P.IsEquipartition)
    (hne : P.parts.Nonempty) :
    let p : ℚ := P.parts.card
    let m : ℚ := (U.card / P.parts.card : ℕ)
    let W := ∑ z ∈ P.parts ×ˢ P.parts, (z.1.card : ℚ)*z.2.card*(G.edgeDensity z.1 z.2)^2
    m^2*(p^2 * P.energy G) ≤ W ∧ W ≤ (m+1)^2*(p^2 * P.energy G + p) := by
  classical
  let p : ℚ := P.parts.card
  let m : ℚ := (U.card / P.parts.card : ℕ)
  let f (z : Finset V × Finset V) := (G.edgeDensity z.1 z.2)^2
  let w (z : Finset V × Finset V) := (z.1.card : ℚ)*z.2.card
  let Z := P.parts ×ˢ P.parts
  have hpow : (∑ z ∈ P.parts.offDiag, f z) = p^2 * P.energy G := by
    have hp : p ≠ 0 := by dsimp [p]; exact_mod_cast hne.card_pos.ne'
    unfold Finpartition.energy
    change _ = p^2 * ((∑ z ∈ P.parts.offDiag, f z) / p^2)
    field_simp
  have hsize (A) (hA : A ∈ P.parts) : m ≤ A.card ∧ (A.card : ℚ) ≤ m+1 := by
    rcases hP.card_parts_eq_average hA with h | h
    · simp [h,m]
    · simp [h,m]
  have limits (z) (hz : z ∈ Z) : m^2 ≤ w z ∧ w z ≤ (m+1)^2 := by
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hz
    obtain ⟨h1,h2⟩ := hsize _ ha
    obtain ⟨h3,h4⟩ := hsize _ hb
    have hm : 0 ≤ m := Nat.cast_nonneg _
    exact ⟨by simpa [w,pow_two] using mul_le_mul h1 h3 hm (Nat.cast_nonneg z.1.card),
      by simpa [w,pow_two] using mul_le_mul h2 h4 (Nat.cast_nonneg z.2.card) (by linarith : 0 ≤ m+1)⟩
  have spl : ∑ z ∈ Z, f z = ∑ z ∈ P.parts.diag, f z + ∑ z ∈ P.parts.offDiag, f z := by
    dsimp [Z]; rw [← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  have diaglo : 0 ≤ ∑ z ∈ P.parts.diag, f z := Finset.sum_nonneg (fun z _ => sq_nonneg _)
  have diaghi : ∑ z ∈ P.parts.diag, f z ≤ p := by
    calc
      _ ≤ ∑ _z ∈ P.parts.diag, (1 : ℚ) := Finset.sum_le_sum fun z _ =>
        (sq_le_one_iff₀ (G.edgeDensity_nonneg _ _)).mpr (G.edgeDensity_le_one _ _)
      _ = _ := by simp [p,Finset.diag_card]
  change (m^2*(p^2 * P.energy G) ≤ ∑ z ∈ Z, w z * f z) ∧ _
  constructor
  · calc
      _ ≤ m^2*(∑ z ∈ Z, f z) := by rw [spl,← hpow]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left diaglo) (sq_nonneg _)
      _ = ∑ z ∈ Z, m^2*f z := Finset.mul_sum ..
      _ ≤ _ := Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_right (limits z hz).1 (sq_nonneg _)
  · calc
      (∑ z ∈ Z, w z * f z) ≤ ∑ z ∈ Z, (m+1)^2*f z :=
        Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_right (limits z hz).2 (sq_nonneg _)
      _ = (m+1)^2*(∑ z ∈ Z, f z) := (Finset.mul_sum ..).symm
      _ ≤ (m+1)^2*(p^2 * P.energy G + p) := by rw [spl,← hpow]; exact mul_le_mul_of_nonneg_left (by linarith only [diaghi]) (sq_nonneg _)

/-- Convert the integral equipartition bounds into a uniform additive
error for the normalized index. The size conditions apply both to the
number of clusters and to the minimum cluster size. -/
lemma normalized_weighted_index_error (m p N W E x : ℚ)
    (hm : 1 ≤ m) (hp : 1 ≤ p) (hNlo : m*p ≤ N) (hNhi : N ≤ (m+1)*p)
    (hE : 0 ≤ E) (hE1 : E ≤ 1) (hx : 0 ≤ x)
    (hmx : 128 ≤ m*x) (hpx : 128 ≤ p*x)
    (hlo : m^2*(p^2*E) ≤ W) (hhi : W ≤ (m+1)^2*(p^2*E+p)) :
    N^2*(E - x/16) ≤ W ∧ W ≤ N^2*(E + x/16) := by
  have hm0 : 0 ≤ m := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hN0 := (mul_nonneg hm0 hp0).trans hNlo
  have nsq := pow_le_pow_left₀ (mul_nonneg hm0 hp0) hNlo 2
  have nupper := pow_le_pow_left₀ hN0 hNhi 2
  have loss1 : (2*m+1)*p^2*E ≤ 3*m*p^2 := by
    calc
      _ ≤ (2*m+1)*p^2*1 := mul_le_mul_of_nonneg_left hE1 (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg p)]
  have loss2 : (m+1)^2*p ≤ 4*m^2*p := by
    have h := pow_le_pow_left₀ (show 0 ≤ m+1 by linarith) (show m+1 ≤ 2*m by linarith) 2
    nlinarith [mul_le_mul_of_nonneg_right h hp0]
  have err1 : 128*(m*p^2) ≤ (m*p)^2*x := by
    nlinarith only [mul_le_mul_of_nonneg_right hmx (mul_nonneg hm0 (sq_nonneg p))]
  have err2 : 128*(m^2*p) ≤ (m*p)^2*x := by
    nlinarith only [mul_le_mul_of_nonneg_right hpx (mul_nonneg (sq_nonneg m) hp0)]
  have err := mul_le_mul_of_nonneg_right nsq hx
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_right nupper hE, loss1, hlo, err1, err,
      mul_nonneg (sq_nonneg N) hx]
  · nlinarith only [mul_le_mul_of_nonneg_right nsq hE, loss1, loss2, hhi, err1, err2, err,
      mul_nonneg (sq_nonneg N) hx]

/-- On a sufficiently fine equipartition with sufficiently large parts,
the size-weighted index and Mathlib's index agree up to x/16. -/
lemma equipartition_index_approximation {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {U : Finset V} (P : Finpartition U) (hP : P.IsEquipartition)
    (hne : P.parts.Nonempty) (x : ℚ) (hx : 0 ≤ x)
    (hm : 1 ≤ U.card / P.parts.card)
    (hmx : 128 ≤ ((U.card / P.parts.card : ℕ) : ℚ)*x)
    (hpx : 128 ≤ (P.parts.card : ℚ)*x) :
    let W := ∑ z ∈ P.parts ×ˢ P.parts, (z.1.card : ℚ)*z.2.card*(G.edgeDensity z.1 z.2)^2
    (U.card : ℚ)^2*(P.energy G-x/16) ≤ W ∧ W ≤ (U.card : ℚ)^2*(P.energy G+x/16) := by
  let p := P.parts.card
  let m := U.card / p
  have hpos : 0 < p := hne.card_pos
  have hlo : m*p ≤ U.card := Nat.div_mul_le_self _ _
  have hhi : U.card ≤ (m+1)*p := by
    have h := Nat.mod_add_div U.card p
    rw [Nat.mul_comm p _] at h
    have hmod := Nat.mod_lt U.card hpos
    change U.card % p + m*p = U.card at h
    rw [Nat.add_mul]; omega
  obtain ⟨hl,hh⟩ := equipartition_weighted_energy_bounds G P hP hne
  exact normalized_weighted_index_error (m : ℚ) (p : ℚ) U.card _ (P.energy G) x
    (by exact_mod_cast hm) (by exact_mod_cast (show 1 ≤ p from hpos)) (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    (P.energy_nonneg G) (P.energy_le_one G) hx hmx hpx hl hh

/-- Changing a partition to repair a different colour costs at most x/8 in
this colour's unweighted index. The underlying weighted index is monotone. -/
lemma equipartition_refinement_energy_loss {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {U : Finset V} (hU : U.Nonempty)
    (P : Finpartition U) (Q : ∀ A ∈ P.parts, Finpartition A)
    (hP : P.IsEquipartition) (hQ : (P.bind Q).IsEquipartition)
    (x : ℚ) (hx : 0 ≤ x)
    (hgood : ∀ R ∈ ({P, P.bind Q} : Finset (Finpartition U)), R.parts.Nonempty ∧
      1 ≤ U.card / R.parts.card ∧ 128 ≤ ((U.card / R.parts.card : ℕ) : ℚ)*x ∧
      128 ≤ (R.parts.card : ℚ)*x) :
    P.energy G ≤ (P.bind Q).energy G + x/8 := by
  classical
  obtain ⟨hp0,hm0,hmx0,hpx0⟩ := hgood P (by simp)
  obtain ⟨hp1,hm1,hmx1,hpx1⟩ := hgood (P.bind Q) (by simp)
  have hlo := (equipartition_index_approximation G P hP hp0 x hx hm0 hmx0 hpx0).1
  have hhi := (equipartition_index_approximation G (P.bind Q) hQ hp1 x hx hm1 hmx1 hpx1).2
  simp only [Finset.sum_product] at hlo hhi
  have comp := hlo.trans ((weighted_energy_mono_bind G P Q).trans hhi)
  have hpos : 0 < (U.card : ℚ)^2 := pow_pos (by exact_mod_cast hU.card_pos) _
  have := le_of_mul_le_mul_left comp hpos
  linarith

/-- A partition irregular for one colour has an equitable refinement that
increases the sum of all three energies. The error allowed in the other two
colours is covered by the gain in the irregular colour. -/
lemma three_colour_energy_increment {V : Type*} [DecidableEq V] [Fintype V] [Nonempty V]
    (c : Fin 3 → SimpleGraph V) [∀ j, DecidableRel (c j).Adj]
    {P : Finpartition (Finset.univ : Finset V)} (hP : P.IsEquipartition) {ε : ℚ}
    (he : 0 < ε) (he1 : ε ≤ 1) (i : Fin 3) (hirr : ¬P.IsUniform (c i) (ε : ℝ))
    (h7 : 7 ≤ P.parts.card) (hpow : 100 ≤ (4 : ℝ)^P.parts.card * (ε : ℝ)^5)
    (hbig : P.parts.card * 16^P.parts.card ≤ Fintype.card V)
    (b : ℕ) (hb : 0 < b) (hbε : 256 ≤ (b : ℚ)*ε^5) (hbp : b ≤ P.parts.card)
    (hbn : b*SzemerediRegularity.stepBound P.parts.card ≤ Fintype.card V) :
    ∃ R : Finpartition (Finset.univ : Finset V), R.IsEquipartition ∧
      R.parts.card = SzemerediRegularity.stepBound P.parts.card ∧
      (∑ j, P.energy (c j)) + ε^5/8 ≤ ∑ j, R.energy (c j) := by
  classical
  let R := SzemerediRegularity.increment hP (c i) (ε : ℝ)
  have hR : R.IsEquipartition := SzemerediRegularity.increment_isEquipartition ..
  have hcard : R.parts.card = SzemerediRegularity.stepBound P.parts.card :=
    SzemerediRegularity.card_increment hbig hirr
  have gain : P.energy (c i) + ε^5/4 ≤ R.energy (c i) := by
    exact_mod_cast SzemerediRegularity.energy_increment hP h7 hpow hbig hirr
      (by exact_mod_cast he.le) (by exact_mod_cast he1)
  have hstep : P.parts.card ≤ SzemerediRegularity.stepBound P.parts.card :=
    SzemerediRegularity.le_stepBound _
  have hx0 : 0 ≤ ε^5/2 := by positivity
  have hsize (S : Finpartition (Finset.univ : Finset V)) (h : S ∈ ({P,R} : Finset _)) :
      S.parts.Nonempty ∧ 1 ≤ (Finset.univ : Finset V).card / S.parts.card ∧
      128 ≤ (((Finset.univ : Finset V).card / S.parts.card : ℕ) : ℚ)*(ε^5/2) ∧
      128 ≤ (S.parts.card : ℚ)*(ε^5/2) := by
    have hp : b ≤ S.parts.card ∧ S.parts.card ≤ SzemerediRegularity.stepBound P.parts.card := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl
      · exact ⟨hbp,hstep⟩
      · rw [hcard]; exact ⟨hbp.trans hstep,le_rfl⟩
    have hs : 0 < S.parts.card := hb.trans_le hp.1
    have hdiv : b ≤ Fintype.card V / S.parts.card :=
      (Nat.le_div_iff_mul_le hs).mpr ((Nat.mul_le_mul_left b hp.2).trans hbn)
    have threshold (z : ℕ) (hz : b ≤ z) : 128 ≤ (z : ℚ)*(ε^5/2) := by
      have h := mul_le_mul_of_nonneg_right (show (b : ℚ) ≤ z by exact_mod_cast hz) (pow_nonneg he.le 5)
      linarith
    rw [Finset.card_univ]
    exact ⟨Finset.card_pos.mp hs,hb.trans_le hdiv,threshold _ hdiv,threshold _ hp.1⟩
  have loss (j : Fin 3) : P.energy (c j) ≤ R.energy (c j) + ε^5/16 := by
    have h := equipartition_refinement_energy_loss (c j) Finset.univ_nonempty P
      (fun _ => SzemerediRegularity.chunk hP (c i) (ε : ℝ)) hP hR (ε^5/2) hx0 hsize
    change P.energy (c j) ≤ R.energy (c j) + ε^5/2/8 at h
    linarith
  refine ⟨R,hR,hcard,?_⟩
  rw [Fin.sum_univ_three,Fin.sum_univ_three]
  have cases3 : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  rcases cases3 i with rfl | rfl | rfl <;> linarith [loss 0,loss 1,loss 2]

/-- Transport rational regularity thresholds to Mathlib's real-valued
regularity lemma without changing the exceptional cluster pairs. -/
lemma regular_pair_rat_iff_real {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T : Finset V} (ε : ℚ) : G.IsUniform ε S T ↔ G.IsUniform (ε : ℝ) S T := by
  constructor
  · intro h A hA B hB hs ht
    have hu : |G.edgeDensity A B - G.edgeDensity S T| < ε := by
      simpa using h hA hB (by exact_mod_cast hs) (by exact_mod_cast ht)
    exact_mod_cast hu
  · intro h A hA B hB hs ht
    have hu := h hA hB (by exact_mod_cast hs) (by exact_mod_cast ht)
    have hh : |G.edgeDensity A B - G.edgeDensity S T| < ε := by exact_mod_cast hu
    simpa using hh

lemma uniform_partition_rat_of_real {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {U : Finset V} (P : Finpartition U) (ε : ℚ)
    (h : P.IsUniform G (ε : ℝ)) : P.IsUniform G ε := by
  classical
  have eqn : P.nonUniforms G ε = P.nonUniforms G (ε : ℝ) := by
    ext ⟨A,B⟩
    simp only [Finpartition.mk_mem_nonUniforms,regular_pair_rat_iff_real G ε]
  unfold Finpartition.IsUniform at h ⊢
  rw [eqn]
  exact_mod_cast h

/-- A single equitable partition simultaneously regular for all three
graphs, with a number of clusters bounded independently of the host order. -/
lemma simultaneous_three_colour_regularity (ε : ℚ) (he : 0 < ε) (he1 : ε ≤ 1) (l : ℕ) :
    ∃ B N₀ : ℕ, ∀ N ≥ N₀, ∀ c : Fin 3 → SimpleGraph (Fin N), ∀ [inst : ∀ i, DecidableRel (c i).Adj],
      ∃ P : Finpartition (Finset.univ : Finset (Fin N)), P.IsEquipartition ∧ l ≤ P.parts.card ∧
        P.parts.card ≤ B ∧ ∀ i, P.IsUniform (c i) ε := by
  classical
  let b := ⌈256/ε^5⌉₊ + 1
  let start := SzemerediRegularity.initialBound (ε : ℝ) (max l b)
  let rounds := ⌈24/ε^5⌉₊ + 1
  let bound (j : ℕ) := (SzemerediRegularity.stepBound^[j]) start
  let B := bound rounds
  have grow (j) : bound j ≤ bound (j+1) := by
    change bound j ≤ (SzemerediRegularity.stepBound^[j+1]) start
    rw [Function.iterate_succ_apply']; exact SzemerediRegularity.le_stepBound _
  have mono : Monotone bound := monotone_nat_of_le_succ grow
  have startle : start ≤ B := mono (Nat.zero_le rounds)
  have hb : 0 < b := Nat.succ_pos _
  have hε5 : 0 < ε^5 := pow_pos he _
  have largeb : 256 ≤ (b : ℚ)*ε^5 := by
    apply (div_le_iff₀ hε5).mp
    exact (Nat.le_ceil _).trans (by dsimp [b]; push_cast; linarith)
  have largel : 3 < ε^5/8*(rounds : ℚ) := by
    have h : 24/ε^5 < (rounds : ℚ) := (Nat.le_ceil _).trans_lt (by dsimp [rounds]; push_cast; linarith)
    have := (div_lt_iff₀ hε5).mp h
    linarith
  have hstart : max l b ≤ start := SzemerediRegularity.le_initialBound ..
  refine ⟨B, B*16^B + b*SzemerediRegularity.stepBound B + B + 1,?_⟩
  intro N hN c inst
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨P₀,heq₀,hcnt₀⟩ := Finpartition.exists_equipartition_card_eq (Finset.univ : Finset (Fin N))
    (show start ≠ 0 by dsimp [start]; exact (SzemerediRegularity.initialBound_pos ..).ne')
    (show start ≤ (Finset.univ : Finset (Fin N)).card by simp; omega)
  have loop (j : ℕ) (hj : j ≤ rounds) :
      ∃ P : Finpartition (Finset.univ : Finset (Fin N)), P.IsEquipartition ∧ start ≤ P.parts.card ∧
        P.parts.card ≤ bound j ∧ ((∀ i, P.IsUniform (c i) (ε : ℝ)) ∨ ε^5/8*j ≤ ∑ i, P.energy (c i)) := by
    induction j with
    | zero =>
      refine ⟨P₀,heq₀,hcnt₀.ge,hcnt₀.le,Or.inr ?_⟩
      rw [Nat.cast_zero,mul_zero]
      exact Finset.sum_nonneg (fun i _ => P₀.energy_nonneg (c i))
    | succ j ih =>
      obtain ⟨P,heq,hlo,hhi,halt⟩ := ih (by omega)
      by_cases uniform : ∀ i, P.IsUniform (c i) (ε : ℝ)
      · exact ⟨P,heq,hlo,hhi.trans (grow j),Or.inl uniform⟩
      have base := halt.resolve_left uniform
      push Not at uniform
      obtain ⟨i,hi⟩ := uniform
      have hprev : P.parts.card ≤ B := hhi.trans (mono (by omega : j ≤ rounds))
      have hn₁ : P.parts.card*16^P.parts.card ≤ Fintype.card (Fin N) := by
        rw [Fintype.card_fin]
        exact (Nat.mul_le_mul hprev (Nat.pow_le_pow_right (by decide) hprev)).trans (by omega)
      have hn₂ : b*SzemerediRegularity.stepBound P.parts.card ≤ Fintype.card (Fin N) := by
        rw [Fintype.card_fin]
        exact (Nat.mul_le_mul_left b (SzemerediRegularity.stepBound_mono hprev)).trans (by omega)
      have hpow : 100 ≤ (4 : ℝ)^P.parts.card * (ε : ℝ)^5 := by
        have h0 := SzemerediRegularity.hundred_lt_pow_initialBound_mul
          (by exact_mod_cast he : 0 < (ε : ℝ)) (max l b)
        exact h0.le.trans (mul_le_mul_of_nonneg_right (pow_right_mono₀ (by norm_num) hlo) (by positivity))
      obtain ⟨R,hR,hr,gain⟩ := three_colour_energy_increment c heq he he1 i hi
        ((SzemerediRegularity.seven_le_initialBound ..).trans hlo) hpow hn₁ b hb largeb
        ((le_max_right l b).trans (hstart.trans hlo)) hn₂
      refine ⟨R,hR,?_,?_,Or.inr ?_⟩
      · rw [hr]; exact hlo.trans (SzemerediRegularity.le_stepBound _)
      · rw [hr]; change _ ≤ (SzemerediRegularity.stepBound^[j+1]) start
        rw [Function.iterate_succ_apply']; exact SzemerediRegularity.stepBound_mono hhi
      · push_cast; linarith
  obtain ⟨P,hP,hlo,hhi,hend⟩ := loop rounds le_rfl
  have maxE : (∑ i, P.energy (c i)) ≤ 3 := by
    rw [Fin.sum_univ_three]; linarith [P.energy_le_one (c 0),P.energy_le_one (c 1),P.energy_le_one (c 2)]
  have uniform := hend.resolve_right (fun h => (not_le_of_gt largel) (h.trans maxE))
  exact ⟨P,hP,(le_max_left l b).trans (hstart.trans hlo),hhi,
    fun i => uniform_partition_rat_of_real (c i) P ε (uniform i)⟩

/-- The reduced multigraph supplied to the stability argument. At most
floor(ηp) clusters are removed and every surviving cluster has at most
floor(ηp) other surviving clusters with no colour, where p is the original
cluster count. A unique reduced colour has density greater than 1−2δ. -/
lemma three_colour_reduced_partition (η δ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hδ : δ ≤ 1/3) (l : ℕ) :
    ∃ B N₀ : ℕ, ∀ N ≥ N₀, ∀ c : Fin 3 → SimpleGraph (Fin N), ∀ [inst : ∀ i, DecidableRel (c i).Adj],
      (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c →
      ∃ P : Finpartition (Finset.univ : Finset (Fin N)), P.IsEquipartition ∧ l ≤ P.parts.card ∧
        P.parts.card ≤ B ∧ ∃ good ⊆ P.parts, P.parts.card ≤ good.card + ⌊η * P.parts.card⌋₊ ∧
        ∃ red : Fin 3 → SimpleGraph good,
          (∀ i u v, (red i).Adj u v ↔ u ≠ v ∧
            (∀ j, (c j).IsUniform (η^2/3) u.val v.val) ∧ δ ≤ (c i).edgeDensity u.val v.val) ∧
          (∀ u : good, ∀ X : Finset good, (∀ v ∈ X, u ≠ v ∧ ∀ i, ¬(red i).Adj u v) →
            X.card ≤ ⌊η * P.parts.card⌋₊) ∧
          ∀ i u v, (red i).Adj u v → (∀ j, j ≠ i → ¬(red j).Adj u v) →
            1 - 2*δ < (c i).edgeDensity u.val v.val := by
  classical
  let ε := η^2/3
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by dsimp [ε]; nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hη1)]
  obtain ⟨B,N₀,h⟩ := simultaneous_three_colour_regularity ε hε hε1 l
  refine ⟨B,N₀,?_⟩
  intro N hN c inst hc
  obtain ⟨P,hP,hl,hB,hu⟩ := h N hN c
  obtain ⟨bad,hbad,hcnt⟩ := simultaneously_irregular_count P c ε hu
  let p := P.parts.card
  let d := ⌊η * p⌋₊
  have hoff : bad ⊆ P.parts.offDiag := by
    intro ⟨u,v⟩ hv
    obtain ⟨hu,hv,hne,_⟩ := (hbad _ _).mp hv
    exact Finset.mem_offDiag.mpr ⟨hu,hv,hne⟩
  have hbudget : bad.card < (d+1)*(d+1) := by
    have hbase : (p*(p-1) : ℕ) ≤ p*p := Nat.mul_le_mul_left _ (Nat.sub_le ..)
    have hc' : (bad.card : ℚ) ≤ (η * p)^2 := by
      calc
        _ ≤ ((p*(p-1) : ℕ) : ℚ)*(3*ε) := hcnt
        _ ≤ ((p*p : ℕ) : ℚ)*(3*ε) := mul_le_mul_of_nonneg_right (by exact_mod_cast hbase) (by positivity)
        _ = _ := by push_cast; dsimp [ε]; ring
    have hlt : η*(p : ℚ) < (d : ℚ)+1 := Nat.lt_floor_add_one _
    have hs := mul_self_lt_mul_self (by positivity : 0 ≤ η*(p : ℚ)) hlt
    rw [sq] at hc'
    exact_mod_cast hc'.trans_lt hs
  obtain ⟨good,hsub,hcount,hdeg⟩ := clean_reduced_pairs P.parts bad hoff d d hbudget
  obtain ⟨red,hred,hcover,hunique⟩ := reduced_colour_graphs c hc (fun u : good => u.val)
    (fun u => P.nonempty_of_mem_parts (hsub u.property))
    (fun u v huv => P.disjoint (hsub u.property) (hsub v.property) (fun e => huv (Subtype.ext e))) ε δ hδ
  refine ⟨P,hP,hl,hB,good,hsub,hcount,red,hred,?_,hunique⟩
  intro u X hX
  apply le_trans _ (hdeg u.val u.property)
  apply Finset.card_le_card_of_injOn (fun v : good => v.val)
  · intro v hv
    obtain ⟨hne,habs⟩ := hX v hv
    refine Finset.mem_filter.mpr ⟨v.property,(hbad _ _).mpr
      ⟨hsub u.property,hsub v.property,fun e => hne (Subtype.ext e),?_⟩⟩
    intro hreg
    obtain ⟨i,hi⟩ := hcover u v hne hreg
    exact habs i hi
  · exact fun _ _ _ _ eqn => Subtype.ext eqn

/-- Benevides's strong endpoints lemma (4.3). The uncovered vertices of a
maximum matching are independent, and each matched edge has an endpoint
with at most one neighbour among the uncovered vertices. -/
lemma maximum_matching_strong_endpoints {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) :
    let matching (T : Finset (Finset V)) := (∀ e ∈ T, ∃ a b, G.Adj a b ∧ e = {a,b}) ∧
      ∀ e ∈ T, ∀ f ∈ T, e ≠ f → Disjoint e f
    let U := Finset.univ \ M.biUnion id
    matching M → (∀ T, matching T → T.card ≤ M.card) →
      (∀ a ∈ U, ∀ b ∈ U, ¬G.Adj a b) ∧
      (∀ e ∈ M, ∃ a ∈ e, (U.filter (G.Adj a)).card ≤ 1) := by
  classical
  intro matching U hM hmax
  have free (a) (ha : a ∈ U) (e) (he : e ∈ M) : a ∉ e := by
    intro hae
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_biUnion.mpr ⟨e,he,hae⟩)
  have addEdge (T : Finset (Finset V)) (hT : matching T) (a b : V) (hab : G.Adj a b)
      (hf : ∀ e ∈ T, a ∉ e ∧ b ∉ e) : matching (insert {a,b} T) ∧ ({a,b} : Finset V) ∉ T := by
    have hd (e) (he : e ∈ T) : Disjoint ({a,b} : Finset V) e := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (hf e he).1
      · exact (hf e he).2
    refine ⟨⟨?_,?_⟩,fun h => (hf _ h).1 (by simp)⟩
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact ⟨a,b,hab,rfl⟩
      · exact hT.1 e he
    · intro e he f hf' hne
      rcases Finset.mem_insert.mp he with rfl | he <;> rcases Finset.mem_insert.mp hf' with rfl | hf'
      · exact (hne rfl).elim
      · exact hd _ hf'
      · exact (hd _ he).symm
      · exact hT.2 _ he _ hf' hne
  constructor
  · intro a ha b hb hab
    obtain ⟨ok,hn⟩ := addEdge M hM a b hab (fun e he => ⟨free _ ha _ he, free _ hb _ he⟩)
    have hc := hmax _ ok
    rw [Finset.card_insert_of_notMem hn] at hc
    omega
  intro e he
  obtain ⟨a,b,hab,rfl⟩ := hM.1 e he
  by_cases small : (U.filter (G.Adj a)).card ≤ 1
  · exact ⟨a,by simp,small⟩
  refine ⟨b,by simp,?_⟩
  by_contra! many
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (by omega : 0 < (U.filter (G.Adj b)).card)
  obtain ⟨hyU,hby⟩ := Finset.mem_filter.mp hy
  obtain ⟨x,hx,hxy⟩ : ∃ x ∈ U.filter (G.Adj a), x ≠ y := by
    by_contra! h
    have sub : U.filter (G.Adj a) ⊆ {y} := fun z hz => Finset.mem_singleton.mpr (h z hz)
    have := Finset.card_le_card sub
    simp at this
    omega
  obtain ⟨hxU,hax⟩ := Finset.mem_filter.mp hx
  let T := M.erase {a,b}
  have ht : T ⊆ M := Finset.erase_subset _ _
  have hT : matching T := ⟨fun f hf => hM.1 _ (ht hf),
    fun f hf g hg hfg => hM.2 _ (ht hf) _ (ht hg) hfg⟩
  have old (f) (hf : f ∈ T) : a ∉ f ∧ b ∉ f := by
    have hd := Finset.disjoint_left.mp (hM.2 _ he _ (ht hf) (Finset.mem_erase.mp hf).1.symm)
    exact ⟨hd (by simp),hd (by simp)⟩
  obtain ⟨first,hn₁⟩ := addEdge T hT a x hax (fun f hf => ⟨(old f hf).1,free _ hxU _ (ht hf)⟩)
  obtain ⟨second,hn₂⟩ := addEdge _ first b y hby (by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · have hbx : x ≠ b := fun h => free _ hxU _ he (by simp [h])
      have hya : y ≠ a := fun h => free _ hyU _ he (by simp [h])
      simp [Ne.symm hab.ne,Ne.symm hbx,hya,Ne.symm hxy]
    · exact ⟨(old _ hf).2,free _ hyU _ (ht hf)⟩)
  have hc := hmax _ second
  rw [Finset.card_insert_of_notMem hn₂,Finset.card_insert_of_notMem hn₁] at hc
  have htcard : T.card + 1 = M.card := Finset.card_erase_add_one he
  omega

theorem main : H1 → H2 → type_of% @Erdos556.erdos_556.variants.benevides_skokan_large_even := by
  intro _ hforce
  unfold H2 at hforce
  filter_upwards [hforce, eventually_ge_atTop 4] with n hn hfour
  intro heven
  refine le_antisymm ?_ (even_cycle_lower_bound n hfour heven)
  apply Nat.sInf_le
  exact hn heven

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1
