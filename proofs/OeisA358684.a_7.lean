import FormalConjectures.OEIS.«358684»
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar

namespace OMA

lemma prime_2 : Nat.Prime 2 := by norm_num

lemma prime_7 : Nat.Prime 7 := by norm_num

lemma prime_449 : Nat.Prime 449 := by norm_num

lemma prime_3 : Nat.Prime 3 := by norm_num

lemma prime_181 : Nat.Prime 181 := by norm_num

lemma prime_52673 : Nat.Prime 52673 := by norm_num

lemma prime_1896229 : Nat.Prime 1896229 := by
  apply lucas_primality 1896229 2
  · change (2 : ZMod 1896229) ^ 1896228 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (1896229 : ℕ) - 1 = 2 ^ 2 * (3 ^ 2 * (52673 ^ 1)) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (2 : ZMod 1896229) ^ 948114 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_3 h
      subst r
      change (2 : ZMod 1896229) ^ 632076 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_52673 h
      subst r
      change (2 : ZMod 1896229) ^ 36 ≠ 1
      reduce_mod_char <;> decide

lemma prime_18533742247 : Nat.Prime 18533742247 := by
  apply lucas_primality 18533742247 6
  · change (6 : ZMod 18533742247) ^ 18533742246 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (18533742247 : ℕ) - 1 = 2 ^ 1 * (3 ^ 3 * (181 ^ 1 * (1896229 ^ 1))) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h | h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (6 : ZMod 18533742247) ^ 9266871123 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_3 h
      subst r
      change (6 : ZMod 18533742247) ^ 6177914082 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_181 h
      subst r
      change (6 : ZMod 18533742247) ^ 102396366 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_1896229 h
      subst r
      change (6 : ZMod 18533742247) ^ 9774 ≠ 1
      reduce_mod_char <;> decide

lemma prime_116503103764643 : Nat.Prime 116503103764643 := by
  apply lucas_primality 116503103764643 2
  · change (2 : ZMod 116503103764643) ^ 116503103764642 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (116503103764643 : ℕ) - 1 = 2 ^ 1 * (7 ^ 1 * (449 ^ 1 * (18533742247 ^ 1))) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h | h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (2 : ZMod 116503103764643) ^ 58251551882321 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_7 h
      subst r
      change (2 : ZMod 116503103764643) ^ 16643300537806 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_449 h
      subst r
      change (2 : ZMod 116503103764643) ^ 259472391458 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_18533742247 h
      subst r
      change (2 : ZMod 116503103764643) ^ 6286 ≠ 1
      reduce_mod_char <;> decide

lemma prime_59649589127497217 : Nat.Prime 59649589127497217 := by
  apply lucas_primality 59649589127497217 3
  · change (3 : ZMod 59649589127497217) ^ 59649589127497216 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (59649589127497217 : ℕ) - 1 = 2 ^ 9 * (116503103764643 ^ 1) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (3 : ZMod 59649589127497217) ^ 29824794563748608 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_116503103764643 h
      subst r
      change (3 : ZMod 59649589127497217) ^ 512 ≠ 1
      reduce_mod_char <;> decide

lemma prime_5 : Nat.Prime 5 := by norm_num

lemma prime_12497 : Nat.Prime 12497 := by norm_num

lemma prime_2203 : Nat.Prime 2203 := by norm_num

lemma prime_139 : Nat.Prime 139 := by norm_num

lemma prime_1783 : Nat.Prime 1783 := by norm_num

lemma prime_6939437 : Nat.Prime 6939437 := by
  apply lucas_primality 6939437 2
  · change (2 : ZMod 6939437) ^ 6939436 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (6939437 : ℕ) - 1 = 2 ^ 2 * (7 ^ 1 * (139 ^ 1 * (1783 ^ 1))) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h | h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (2 : ZMod 6939437) ^ 3469718 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_7 h
      subst r
      change (2 : ZMod 6939437) ^ 991348 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_139 h
      subst r
      change (2 : ZMod 6939437) ^ 49924 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_1783 h
      subst r
      change (2 : ZMod 6939437) ^ 3892 ≠ 1
      reduce_mod_char <;> decide

lemma prime_55515497 : Nat.Prime 55515497 := by
  apply lucas_primality 55515497 3
  · change (3 : ZMod 55515497) ^ 55515496 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (55515497 : ℕ) - 1 = 2 ^ 3 * (6939437 ^ 1) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (3 : ZMod 55515497) ^ 27757748 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_6939437 h
      subst r
      change (3 : ZMod 55515497) ^ 8 ≠ 1
      reduce_mod_char <;> decide

lemma prime_733803839347 : Nat.Prime 733803839347 := by
  apply lucas_primality 733803839347 2
  · change (2 : ZMod 733803839347) ^ 733803839346 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (733803839347 : ℕ) - 1 = 2 ^ 1 * (3 ^ 1 * (2203 ^ 1 * (55515497 ^ 1))) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h | h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (2 : ZMod 733803839347) ^ 366901919673 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_3 h
      subst r
      change (2 : ZMod 733803839347) ^ 244601279782 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2203 h
      subst r
      change (2 : ZMod 733803839347) ^ 333092982 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_55515497 h
      subst r
      change (2 : ZMod 733803839347) ^ 13218 ≠ 1
      reduce_mod_char <;> decide

lemma prime_5704689200685129054721 : Nat.Prime 5704689200685129054721 := by
  apply lucas_primality 5704689200685129054721 21
  · change (21 : ZMod 5704689200685129054721) ^ 5704689200685129054720 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (5704689200685129054721 : ℕ) - 1 = 2 ^ 9 * (3 ^ 5 * (5 ^ 1 * (12497 ^ 1 * (733803839347 ^ 1)))) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h | h | h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (21 : ZMod 5704689200685129054721) ^ 2852344600342564527360 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_3 h
      subst r
      change (21 : ZMod 5704689200685129054721) ^ 1901563066895043018240 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_5 h
      subst r
      change (21 : ZMod 5704689200685129054721) ^ 1140937840137025810944 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_12497 h
      subst r
      change (21 : ZMod 5704689200685129054721) ^ 456484692380981760 ≠ 1
      reduce_mod_char <;> decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_733803839347 h
      subst r
      change (21 : ZMod 5704689200685129054721) ^ 7774133760 ≠ 1
      reduce_mod_char <;> decide

end OMA

theorem OMA.solution : type_of% @OeisA358684.a_7 := by
  let n := Nat.fermatNumber 7
  have hprod : n = 59649589127497217 * 5704689200685129054721 := by decide
  have hprime : n.minFac.Prime := Nat.minFac_prime (by rw [hprod]; decide)
  have hd := Nat.minFac_dvd n
  have hle : n.minFac ≤ 59649589127497217 := Nat.minFac_le_of_dvd (by decide) (by rw [hprod]; exact dvd_mul_right _ _)
  rw [hprod] at hd
  have heq : n.minFac = 59649589127497217 := by
    rcases hprime.dvd_mul.mp hd with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hprime OMA.prime_59649589127497217).mp h
    · have := (Nat.prime_dvd_prime_iff_eq hprime OMA.prime_5704689200685129054721).mp h
      omega
  change 2 ^ 7 - Nat.log2 n.minFac = 73
  rw [heq]
  decide
