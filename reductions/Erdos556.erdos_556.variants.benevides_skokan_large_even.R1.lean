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
