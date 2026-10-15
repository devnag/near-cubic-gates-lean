import Proof.Gates.Expand.Print6

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

theorem testBit_lt_size {s j : ℕ} (h : s.testBit j = true) : j < Nat.size s :=
  Nat.lt_size.mpr (Nat.ge_two_pow_of_testBit h)

/-- The sorted elements of a set are its set bits. -/
theorem sort_setOf (V s : ℕ) (hs : s < 2 ^ V) :
    ((setOf V s).sort (· ≤ ·)).map Fin.val = bitsOf s := by
  have hsz : Nat.size s ≤ V := Nat.size_le.mpr hs
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact List.Pairwise.map _ (fun a b h => h) (Finset.sortedLT_sort (setOf V s)).pairwise
  · exact (List.pairwise_lt_range).filter _
  · intro j
    simp only [List.mem_map, Finset.mem_sort, bitsOf, List.mem_filter, List.mem_range, setOf, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨testBit_lt_size ha, ha⟩
    · rintro ⟨hj, hb⟩; exact ⟨⟨j, by omega⟩, hb, rfl⟩

/-- **One record prints one monomial.** -/
theorem recOut_eq (V W s acc : ℕ) (hs : s < 2 ^ V) (hacc : acc < 2 ^ W) (hW : 1 ≤ W) :
    recOut V W ((s + (setOf V s).card * 2 ^ V) * 2 ^ W + acc) = monoWord (setOf V s, decodeAcc W acc) := by
  have hWp : 0 < 2 ^ W := Nat.two_pow_pos W
  have hTM : 0 < 2 ^ V * 2 ^ W := Nat.mul_pos (Nat.two_pow_pos V) hWp
  set d := (setOf V s).card
  have hlow : s * 2 ^ W + acc < 2 ^ V * 2 ^ W := by
    have : (s + 1) * 2 ^ W ≤ 2 ^ V * 2 ^ W := Nat.mul_le_mul_right _ hs
    nlinarith
  have hx : (s + d * 2 ^ V) * 2 ^ W + acc = (s * 2 ^ W + acc) + (2 ^ V * 2 ^ W) * d := by ring
  have hdiv : ((s + d * 2 ^ V) * 2 ^ W + acc) / (2 ^ V * 2 ^ W) = d := by
    rw [hx, Nat.add_mul_div_left _ _ hTM, Nat.div_eq_of_lt hlow, zero_add]
  have hmod : ((s + d * 2 ^ V) * 2 ^ W + acc) % (2 ^ V * 2 ^ W) = s * 2 ^ W + acc := by
    rw [hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
  have hs' : (s * 2 ^ W + acc) / 2 ^ W = s := by
    rw [show s * 2 ^ W + acc = acc + 2 ^ W * s by ring, Nat.add_mul_div_left _ _ hWp, Nat.div_eq_of_lt hacc, zero_add]
  have ha' : (s * 2 ^ W + acc) % 2 ^ W = acc := by
    rw [show s * 2 ^ W + acc = acc + 2 ^ W * s by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hacc]
  unfold recOut monoWord
  rw [hdiv, hmod, hs', ha', ← sort_setOf V s hs, List.flatMap_map]
  simp only [Interfaces.listWord, List.length_map, Finset.length_sort, Interfaces.intWord, decodeAcc, List.flatMap_map]
  have hHW : 2 ^ (W - 1) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  by_cases h1 : acc < 2 ^ (W - 1)
  · have : ¬ ((acc : ℤ) < 0) := by omega
    simp [h1, this, List.append_assoc, d]
  · have hneg : ((acc : ℤ) - 2 ^ W) < 0 := by
      have : (acc : ℤ) < 2 ^ W := by exact_mod_cast hacc
      linarith
    have habs : ((acc : ℤ) - 2 ^ W).natAbs = 2 ^ W - acc := by
      have : (acc : ℤ) - 2 ^ W = -((2 ^ W - acc : ℕ) : ℤ) := by push_cast [hacc.le]; ring
      rw [this, Int.natAbs_neg, Int.natAbs_natCast]
    simp [h1, hneg, habs, List.append_assoc, d]

theorem famPairs_le (V D : ℕ) (p : ℕ × ℕ) (hp : p ∈ famPairs V D) : p.2 ≤ D := by
  simp only [famPairs, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨d, hd, t, _, rfl⟩ := hp
  simp; omega

theorem fam_eq_pairs (V D : ℕ) : fam V D = (famPairs V D).map Prod.fst := by
  simp only [fam, famPairs, List.map_flatMap, List.map_map]
  congr 1; funext d; simp [Function.comp_def]

theorem orc_map {V : ℕ} (F : Formula V) (W D : ℕ) (hW : F.weight + 2 ≤ W) (l : List (ℕ × ℕ))
    (hl : ∀ p ∈ l, p ∈ famPairs V D) :
    (orcRecs V W ((famRecs V D).map (valRec V W F)) (l.map fun p => p.1 + p.2 * 2 ^ V)).map (recOut V W) =
      (((l.map fun p => setOf V p.1).filter fun S => coeff F.expand S ≠ 0).map
        fun S => (S, coeff F.expand S)).map monoWord := by
  induction l with
  | nil => simp [orcRecs]
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    obtain ⟨hs, hc⟩ := famPairs_mem V D p hp
    have hD : (setOf V p.1).card ≤ D := by rw [hc]; exact famPairs_le V D p hp
    have ih' := ih (fun q hq => hl q (List.mem_cons_of_mem p hq))
    set vals := (famRecs V D).map (valRec V W F)
    have hdec := decode_accOf F W D p.1 hs hD hW
    rw [hc] at hdec
    have hlt := accOf_lt V W vals (p.1 + p.2 * 2 ^ V)
    have hz := decodeAcc_zero W _ hlt
    simp only [List.map_cons, orcRecs, List.filterMap_cons] at ih' ⊢
    by_cases h0 : accOf V W vals (p.1 + p.2 * 2 ^ V) = 0
    · have hco : coeff F.expand (setOf V p.1) = 0 := by rw [← hdec]; exact hz.mpr h0
      simp only [h0, if_true]
      rw [List.filter_cons_of_neg (by simp [hco])]
      exact ih'
    · have hco : coeff F.expand (setOf V p.1) ≠ 0 := by rw [← hdec]; exact fun e => h0 (hz.mp e)
      simp only [h0, if_false]
      rw [List.filter_cons_of_pos (by simp [hco])]
      simp only [List.map_cons]
      rw [ih']
      congr 1
      rw [← hdec, ← hc]
      exact recOut_eq V W p.1 _ hs (accOf_lt _ _ _ _) (by omega)

theorem orc_print {V : ℕ} (F : Formula V) (W : ℕ) (hW : F.weight + 2 ≤ W) :
    (orcRecs V W ((famRecs V F.degree).map (valRec V W F)) (famRecs V F.degree)).flatMap (recOut V W) =
      (expandM F).flatMap monoWord ∧
    (orcRecs V W ((famRecs V F.degree).map (valRec V W F)) (famRecs V F.degree)).length = (expandM F).length := by
  have h := orc_map F W F.degree hW (famPairs V F.degree) (fun p hp => hp)
  rw [← famRecs_eq] at h
  have e : ((famPairs V F.degree).map fun p => setOf V p.1) = famS V F.degree := by
    rw [famS, fam_eq_pairs, List.map_map]; rfl
  rw [e] at h
  refine ⟨?_, ?_⟩
  · have := congrArg List.flatten h
    simpa [List.flatMap, expandM] using this
  · have := congrArg List.length h
    simpa [expandM] using this

end NearCubicGates.Close.Expand
