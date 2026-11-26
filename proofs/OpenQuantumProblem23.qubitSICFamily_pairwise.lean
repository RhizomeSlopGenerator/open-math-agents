import FormalConjectures.OpenQuantumProblems.«23»

open OpenQuantumProblem23

lemma OMA.overlap_vec2 (a b c d : ℂ) :
    overlapSq (vec2 a b) (vec2 c d) = Complex.normSq (star a * c + star b * d) := by
  simp [overlapSq, vec2, mkStateVector, Fin.sum_univ_two]

set_option maxHeartbeats 2000000 in
theorem OMA.solution : type_of% @OpenQuantumProblem23.qubitSICFamily_pairwise := by
  have ha : tetraA ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
  have hb : tetraB ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ha4 : tetraA ^ 4 = (1 / 3 : ℝ) ^ 2 := by rw [← ha]; ring
  have hb4 : tetraB ^ 4 = (2 / 3 : ℝ) ^ 2 := by rw [← hb]; ring
  have hs4 : Real.sqrt 3 ^ 4 = 9 := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hs]; norm_num
  have hs6 : Real.sqrt 3 ^ 6 = 27 := by rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, hs]; norm_num
  have hs8 : Real.sqrt 3 ^ 8 = 81 := by rw [show (8 : ℕ) = 2 * 4 by decide, pow_mul, hs]; norm_num
  have q0 : qubitSICFamily 0 = vec2 1 0 := rfl
  have q1 : qubitSICFamily 1 = vec2 tetraA tetraB := rfl
  have q2 : qubitSICFamily 2 = vec2 tetraA (tetraB * ω) := rfl
  have q3 : qubitSICFamily 3 = vec2 tetraA (tetraB * ω ^ 2) := rfl
  have cases4 : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  intro i j hij
  rcases cases4 i with rfl | rfl | rfl | rfl <;>
    rcases cases4 j with rfl | rfl | rfl | rfl <;> try exact (hij rfl).elim
  all_goals simp only [q0, q1, q2, q3, OMA.overlap_vec2]
  all_goals
    norm_num [sicOverlapSq, ω, Complex.normSq_apply,
      Complex.star_def, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, pow_two]
  all_goals
    ring_nf
  all_goals
    norm_num [ha, hb, hs, ha4, hb4, hs4, hs6, hs8] <;> ring
