import FormalConjectures.Wikipedia.MaximalPrimeGap

namespace OMA

lemma exists_gap_gt (b : ℕ) : ∃ i, b < primeGap i := by
  classical
  let f := (b + 2).factorial
  have hf : 0 < f := Nat.factorial_pos _
  have hex : ∃ i, f + 1 < Nat.nth Nat.Prime i :=
    ⟨f + 1, by have := Nat.add_two_le_nth_prime (f + 1); omega⟩
  have hnext := Nat.find_spec hex
  cases hi : Nat.find hex with
  | zero =>
    rw [hi, Nat.nth_prime_zero_eq_two] at hnext
    omega
  | succ i =>
    rw [hi] at hnext
    have hprev : Nat.nth Nat.Prime i ≤ f + 1 := by
      apply le_of_not_gt
      exact Nat.find_min hex (by omega : i < Nat.find hex)
    refine ⟨i, ?_⟩
    change b < Nat.nth Nat.Prime (i + 1) - Nat.nth Nat.Prime i
    by_contra! hsmall
    let q := Nat.nth Nat.Prime (i + 1)
    change f + 1 < q at hnext
    change q - Nat.nth Nat.Prime i ≤ b at hsmall
    let d := q - f
    have hd : 2 ≤ d := by dsimp [d]; omega
    have hd' : d ≤ b + 2 := by dsimp [d]; omega
    have heq : q = f + d := by dsimp [d]; omega
    have hdiv : d ∣ f := Nat.dvd_factorial (by omega) hd'
    have hdq : d ∣ q := by
      rw [heq]
      exact dvd_add hdiv (dvd_refl d)
    exact (Nat.not_prime_of_dvd_of_lt hdq hd (by omega)) (Nat.prime_nth_prime (i + 1))

end OMA

theorem OMA.solution : type_of% @MaximalPrimeGap.infinite_maximalPrimeGapIndex := by
  classical
  rw [Set.infinite_iff_exists_gt]
  intro n
  let bound := (Finset.range (n + 1)).sup primeGap
  have hex := OMA.exists_gap_gt bound
  have hrec := Nat.find_spec hex
  refine ⟨Nat.find hex, ?_, ?_⟩
  · intro m hm
    have hle : primeGap m ≤ bound := le_of_not_gt (Nat.find_min hex hm)
    exact hle.trans_lt hrec
  · by_contra! hle
    have hmem : Nat.find hex ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    exact (not_lt_of_ge (Finset.le_sup (f := primeGap) hmem)) hrec
