import FormalConjectures.ErdosProblems.«556»

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
      simp [colour, hs, Nat.mod_eq_of_lt hs] at hv
      rw [min_def] at hv
      split at hv <;> contradiction
    · have hx3 : 3 ≤ x := le_trans (Nat.le_of_not_lt hs) (min_le_left _ _)
      have hy3 : 3 ≤ y := le_trans (Nat.le_of_not_lt hs) (min_le_right _ _)
      refine ⟨hx3, hy3, ?_⟩
      by_cases hp : x % 2 = y % 2
      · have hi : (0 : Fin 3) = i := by simpa [colour, hs, hp] using hc
        simpa [← hi, key] using hp
      · by_cases hb : x / 2 % 2 = y / 2 % 2
        · have hi : (1 : Fin 3) = i := by simpa [colour, hs, hp, hb] using hc
          simpa [← hi, key] using hb
        · have hi : (2 : Fin 3) = i := by simpa [colour, hs, hp, hb] using hc
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
    fin_cases i <;> simp [key, bit] at heq hc <;> (try split_ifs at heq) <;> omega
  have impossible := Fintype.card_le_of_injective code inj
  simp only [Fintype.card_fin] at impossible
  omega

theorem main : H1 → H2 → type_of% @Erdos556.erdos_556.variants.benevides_skokan_large_even := by
  classical
  intro hbad hforce
  unfold H2 at hforce
  filter_upwards [hforce, eventually_ge_atTop 4] with n hn hfour
  intro heven
  let S : Set ℕ := {N | ∀ c : Fin 3 → SimpleGraph (Fin N),
    (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c → ∃ i, (cycleGraph n).IsContained (c i)}
  change sInf S = 2 * n
  have hgood : 2 * n ∈ S := hn heven
  refine le_antisymm (Nat.sInf_le hgood) (le_csInf ⟨_, hgood⟩ ?_)
  intro N hN
  by_contra! hsmall
  let colour (x y : ℕ) : Fin 3 :=
    if min x y < 3 then ⟨min x y % 3, Nat.mod_lt _ (by decide)⟩
    else if x % 2 = y % 2 then 0
    else if (x / 2) % 2 = (y / 2) % 2 then 1 else 2
  have sym (x y : ℕ) : colour x y = colour y x := by
    unfold colour
    rw [min_comm y x, eq_comm (y % 2) (x % 2),
      eq_comm (y / 2 % 2) (x / 2 % 2)]
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

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1
