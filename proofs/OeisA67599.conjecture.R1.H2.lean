import OMAReductions.R_OeisA67599_conjecture_R1
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sort

-- Credit: @ArtemCherbaev
theorem OMA.solution : OMA.R_OeisA67599_conjecture_R1.H2 := by
  intro q hq prime
  have hne : (7 : ℕ) ≠ q := by omega
  have hperm := Nat.perm_primeFactorsList_mul (by decide : 2401 ≠ 0) prime.ne_zero
  have hsmall : Nat.primeFactorsList 2401 = [7, 7, 7, 7] := by decide
  rw [hsmall, Nat.primeFactorsList_prime prime] at hperm
  have hfac : (2401 * q).primeFactorsList = [7, 7, 7, 7, q] :=
    hperm.eq_of_pairwise' (Nat.primeFactorsList_sorted _).pairwise
      (by simp [List.pairwise_cons, hq.le])
  have hbig : ¬ 2401 * q < 2 := by omega
  rw [OeisA67599.a, if_neg hbig, hfac]
  have hlist : [7, 7, 7, 7, q].dedup = [7, q] := by
    simp [List.dedup_cons, hne, Ne.symm hne]
  rw [hlist]
  have hc7 : [7, 7, 7, 7, q].count 7 = 4 := by
    simp [List.count_cons, hne, Ne.symm hne]
  have hcq : [7, 7, 7, 7, q].count q = 1 := by
    simp [List.count_cons, hne, Ne.symm hne]
  simp only [List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    List.foldl_cons, List.foldl_nil, hc7, hcq]
  change (74 * 10 ^ (Nat.digits 10 q).length + q) * 10 + 1 = _
  ring
