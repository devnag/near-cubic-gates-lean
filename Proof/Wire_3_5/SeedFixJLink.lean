import Proof.Wire_3_5.SeedFixJEnum

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.BlockPlatform
open Split Cells Valid Cons FetchAll FetchCells Emit JBank JStages JBody SplitT JEnum
open Finset

namespace JLink

/-! ## The counter's high bits -/

theorem div_mod_shift (a M j d m : ℕ) (hd : 0 < d) (hdm : d * m ∣ M) : (a * M + j) / d % m = j / d % m := by
  obtain ⟨c, rfl⟩ := hdm
  have e : a * (d * m * c) + j = j + d * (m * (a * c)) := by ring
  rw [e, Nat.add_mul_div_left _ _ hd, Nat.add_mul_mod_self_left]

theorem pow_dvd_w (P : SeedParams) (e : ℕ) (he : e ≤ 8 + 8 * P.ell + 8 * P.kh) : 2 ^ e ∣ 2 ^ (8 + 8 * P.ell + 8 * P.kh) :=
  pow_dvd_pow 2 he

variable (P : SeedParams)

theorem bOf_shift (a j : ℕ) : bOf (a * 2 ^ (8 + 8 * P.ell + 8 * P.kh) + j) = bOf j := by
  funext k
  unfold bOf
  have h := div_mod_shift a (2 ^ (8 + 8 * P.ell + 8 * P.kh)) j 1 (2 ^ 8) one_pos
    (by rw [one_mul]; exact pow_dvd_w P 8 (by omega))
  rw [Nat.div_one, Nat.div_one] at h
  simp only [h]

theorem aOf_shift (a j : ℕ) : aOf P (a * 2 ^ (8 + 8 * P.ell + 8 * P.kh) + j) = aOf P j := by
  funext k
  unfold aOf
  have h := div_mod_shift a (2 ^ (8 + 8 * P.ell + 8 * P.kh)) j (2 ^ 8) ((2 ^ P.ell) ^ 8) (by positivity)
    (by rw [← pow_mul, ← pow_add]; exact pow_dvd_w P _ (by omega))
  rw [h]

theorem wOf_shift (a j : ℕ) : wOf P (a * 2 ^ (8 + 8 * P.ell + 8 * P.kh) + j) = wOf P j := by
  funext k
  apply Fin.ext
  unfold wOf
  simp only [Nat.div_div_eq_div_mul]
  have hk := k.isLt
  have hd : (2 ^ P.ell) ^ 8 * 2 ^ 8 * P.N ^ (k : ℕ) * P.N = 2 ^ (8 * P.ell + 8 + P.kh * ((k : ℕ) + 1)) := by
    simp only [SeedParams.N, ← pow_mul, ← pow_add]
    ring_nf
  exact div_mod_shift a _ j _ P.N (by positivity) (by rw [hd]; exact pow_dvd_w P _ (by nlinarith))

/-! ## The sign word -/

theorem bOf_testBit (j : ℕ) (k : Fin 8) : bOf j k = j.testBit k := by
  have hk := k.isLt
  have e : (j % 2 ^ 8).testBit k = j.testBit k := by rw [Nat.testBit_mod_two_pow]; simp [hk]
  rw [← e, Nat.testBit_eq_decide_div_mod_eq]
  unfold bOf
  rcases Nat.mod_two_eq_zero_or_one (j % 2 ^ 8 / 2 ^ (k : ℕ)) with h | h
  · have e0 : (⟨j % 2 ^ 8 / 2 ^ (k : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = 0 := Fin.ext h
    rw [e0, h]; rfl
  · have e1 : (⟨j % 2 ^ 8 / 2 ^ (k : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = 1 := Fin.ext h
    rw [e1, h]; rfl

theorem count_binary : ∀ (n x : ℕ), (binary n x).count true = (univ.filter fun k : Fin n => x.testBit k = true).card
  | 0, x => by simp [binary]
  | n + 1, x => by
    rw [binary, List.count_cons, count_binary n (x / 2), card_filter, card_filter, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.testBit_zero, Nat.testBit_add_one]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h, Nat.add_comm]

theorem parity_fold : ∀ (bs : List Bool) (s : Bool),
    foldBits parityStep s (List.replicate bs.length true) bs = xor s (decide (bs.count true % 2 = 1))
  | [], s => by simp [foldBits]
  | b :: bs, s => by
    rw [List.length_cons, List.replicate_succ, foldBits, parity_fold bs, List.count_cons]
    cases b <;> cases s <;> rcases Nat.mod_two_eq_zero_or_one (bs.count true) with h | h <;>
      simp [parityStep, h, Nat.add_mod]

theorem sign_eq (c : ℕ) : (if decide (c % 2 = 1) then (-1 : ℤ) else 1) = (-1) ^ c := by
  rcases Nat.even_or_odd c with h | h
  · rw [h.neg_one_pow, Nat.even_iff.mp h]; rfl
  · rw [h.neg_one_pow, Nat.odd_iff.mp h]; rfl

theorem parity_eq (bs : List Bool) : parity bs = decide (bs.count true % 2 = 1) := by
  unfold parity
  rw [parity_fold, Bool.false_xor]

theorem cnt_length (bs : List Bool) : cnt bs bs.length = bs.count true := by
  unfold cnt
  rw [List.take_length]

/-- **The coefficient word of the sign bits `binary 8 j` and exponent `e` is `coefTerm`'s**. -/
theorem coefT_eq (j e : ℕ) : coefT (binary 8 j) (2 * P.kh) e = coefTerm P (bOf j) (2 ^ e) := by
  have hc : (binary 8 j).count true = (univ.filter fun k : Fin 8 => bOf j k = true).card := by
    rw [count_binary]; simp only [bOf_testBit]
  rw [coefTerm_pow]
  unfold coefT
  rw [parity_eq, cnt_length, hc, sign_eq]

/-! ## The group of a counter value -/

/-- The batch's entries, `R` rows each, in state-major order (entry `(t, u, v)` at `(t·N + u)·N + v`). -/
def EntsOk (N nT R : ℕ) (batch : List SExpr) (ents : List (List SExpr)) : Prop :=
  ∀ t < nT, ∀ c : Cell N, ents.getD (cellNumC c + N ^ 2 * t) [] = entryRows batch R N t c.1 c.2

/-- The chunked batch is such a list of entries. -/
def chunk (N nT R : ℕ) (batch : List SExpr) : List (List SExpr) :=
  (List.range (nT * N ^ 2)).map fun e => (List.range R).map fun r => batch.getD (e * R + r) []

theorem chunk_ok (N nT R : ℕ) (batch : List SExpr) : EntsOk N nT R batch (chunk N nT R batch) := by
  intro t ht c
  have hc : cellNumC c < N ^ 2 := by
    unfold cellNumC
    have h1 := c.1.isLt
    have h2 := c.2.isLt
    nlinarith
  have hlt : cellNumC c + N ^ 2 * t < nT * N ^ 2 := by nlinarith
  unfold chunk entryRows
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt, Option.map_some, Option.getD_some]
  refine List.map_congr_left fun r _ => ?_
  congr 2
  unfold cellNumC
  ring

theorem rowsJ_eq (X : JCtx) (nT R : ℕ) (batch : List SExpr) (hE : EntsOk X.P.N nT R batch X.ents) (t j' : ℕ)
    (ht : t < nT) (w : Fin 8 → Fin X.P.N) (hw : wOf X.P j' = w) :
    (at_ X t).rowsJ j' = walkRows X.P batch R w t := by
  unfold JCtx.rowsJ JCtx.esJ walkRows
  rw [List.flatMap_map]
  refine List.flatMap_congr fun k _ => ?_
  show X.ents.getD (cellNumC (cellOf (by norm_num) (wOf X.P j') k) + X.P.N ^ 2 * t) [] = _
  rw [hw]
  exact hE t ht _

theorem condProb_fst (p ℓ k plen pre : ℕ) (cons : List (ℕ × ℕ)) :
    (JoinElimination.condProbGauss p ℓ 8 k plen pre cons).1 =
      if (JoinElimination.gauss (8 * ℓ - plen) (JoinElimination.system p ℓ 8 k plen pre cons)).1 then
        2 ^ (8 * ℓ - plen - (JoinElimination.gauss (8 * ℓ - plen) (JoinElimination.system p ℓ 8 k plen pre cons)).2)
      else 0 := by
  unfold JoinElimination.condProbGauss
  rfl

/-- **The group of counter value `t·2^{w₀} + j` is `groupAt t j`.** -/
theorem emitJ_eq (X : JCtx) (nT R : ℕ) (batch : List SExpr) (hE : EntsOk X.P.N nT R batch X.ents) (hQ : 1 ≤ X.P.Q)
    (t j : ℕ) (ht : t < nT) :
    (at_ X t).emitJ (t * 2 ^ X.w + j) = groupAt X.P R batch X.plen X.pfx t j := by
  set j' := t * 2 ^ X.w + j with hj'
  have ha : aOf X.P j' = aOf X.P j := aOf_shift X.P t j
  have hw : wOf X.P j' = wOf X.P j := wOf_shift X.P t j
  have hb : bOf j' = bOf j := bOf_shift X.P t j
  have hv : (at_ X t).validJ j' = decide (∀ k, aOf X.P j k < X.P.Q) := by
    unfold JCtx.validJ JCtx.asJ JCtx.q
    rw [← ha]
    exact valid_eq X.P j' hQ
  have hcons : (at_ X t).consJ j' = consL X.P.N (aOf X.P j) (fun k => cellOf (by norm_num) (wOf X.P j) k) (bOf j) := by
    show consL X.P.N (aOf X.P j') (fun k => cellOf (by norm_num) (wOf X.P j') k) (bOf j') = _
    rw [ha, hw, hb]
  have hcnt : cntL X.P X.plen X.pfx (aOf X.P j) (wOf X.P j) (bOf j) =
      if ((at_ X t).ggJ j').1 then 2 ^ ((at_ X t).eJ j') else 0 := by
    unfold cntL JCtx.eJ JCtx.ggJ
    rw [condProb_fst, hcons]
    rfl
  unfold JCtx.emitJ groupAt
  rw [hv]
  by_cases hval : ∀ k, aOf X.P j k < X.P.Q
  · rw [if_pos hval]
    by_cases hg : ((at_ X t).ggJ j').1 = true
    · rw [if_pos ⟨decide_eq_true hval, hg⟩, hcnt, if_pos hg, if_neg (by positivity)]
      unfold termsAt
      rw [hcnt, if_pos hg]
      congr 1
      · show coefT (binary 8 j') (2 * X.P.kh) ((at_ X t).eJ j') = _
        have hm : j' % 2 ^ 8 = j % 2 ^ 8 := by
          have h := div_mod_shift t (2 ^ (8 + 8 * X.P.ell + 8 * X.P.kh)) j 1 (2 ^ 8) one_pos
            (by rw [one_mul]; exact pow_dvd_w X.P 8 (by omega))
          rw [Nat.div_one, Nat.div_one] at h
          exact h
        have hb8 : binary 8 j' = binary 8 j := by rw [← binary_mod 8 j', hm, binary_mod]
        rw [hb8, coefT_eq]
      · exact rowsJ_eq X nT R batch hE t j' ht _ hw
    · rw [if_neg (fun h => hg h.2), hcnt, if_neg hg, if_pos rfl]
  · rw [if_neg (fun h => hval (of_decide_eq_true h.1)), if_neg hval]

/-! ## The whole output -/

theorem two_pow_w (X : JCtx) : 2 ^ X.w = X.P.N ^ 8 * ((2 ^ X.P.ell) ^ 8 * 2 ^ 8) := by
  unfold JCtx.w
  simp only [SeedParams.N, ← pow_mul, ← pow_add]
  ring_nf

/-- **The enumeration's output after all `nT·2^{w₀}` counter values is the printed objective.** -/
theorem outAt_sampTerms (X : JCtx) (nT R : ℕ) (batch : List SExpr) (hE : EntsOk X.P.N nT R batch X.ents)
    (hQ : 1 ≤ X.P.Q) : outAt X (nT * 2 ^ X.w) = sampTerms X.P nT R batch X.plen X.pfx := by
  unfold outAt sampTerms
  rw [flatMap_range_mul]
  refine List.flatMap_congr fun t ht => ?_
  have ht' := List.mem_range.mp ht
  rw [sampTermsT_flat, ← two_pow_w]
  refine List.flatMap_congr fun j hj => ?_
  have hj' := List.mem_range.mp hj
  have htj : tOf X (t * 2 ^ X.w + j) = t := by
    unfold tOf
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hj', Nat.zero_add]
  rw [htj]
  exact emitJ_eq X nT R batch hE hQ t j ht'

/-! ## The elimination's registers stay admissible -/

/-- The cell's state keeps `Regs.Ok` (the elimination block's precondition `GroupOk.hR`) at every counter value. -/
theorem stAt_ok (X : JCtx) (S0 : JState) (h0 : S0.R.Ok X.P.ell 8) : ∀ j, (stAt X S0 j).R.Ok X.P.ell 8
  | 0 => h0
  | j + 1 => by
    have ih := stAt_ok X S0 h0 j
    show ((at_ X (tOf X j)).jNext j (stAt X S0 j)).R.Ok X.P.ell 8
    unfold JCtx.jNext
    split
    · split
      · exact regsAt_ok _ _ _ _ _ _ _ ih _
      · exact regsAt_ok _ _ _ _ _ _ _ ih _
    · exact ih

/-! ## The enumeration machine writes the printed objective -/

/-- **C4.Sb: the sampler builder's enumeration.** From the bank before counter value `0` (the fields of `0`, the
cell's state `S0`, an empty output over the backing `OB`), the loop of `nT·2^{w₀}` cells ends with the output tape
`overlay (exprWord (sampTerms …)) OB`, the printed objective of the prefix `(plen, pfx)` over the batch whose
state-major entries are `ents`. Hypotheses: the capacities (`CellOk`, `SplitOk`, and `GroupOk` at every valid
counter value), a uniform cell cost bound `K`, `nT ≤ 2^{TWd}` and `1 ≤ Q`. -/
theorem sampEnum_run (X : JCtx) (S0 : JState) (nT R K : ℕ) (batch : List SExpr)
    (hE : EntsOk X.P.N nT R batch X.ents) (hQ : 1 ≤ X.P.Q) (hnT : nT ≤ 2 ^ X.TWd) (hc : CellOk X) (hs : SplitOk X)
    (hK : ∀ j, j < nT * 2 ^ X.w → cellCost X j (outAt X j) ≤ K)
    (hg : ∀ j, j < nT * 2 ^ X.w → (at_ X (tOf X j)).validJ j = true →
      GroupOk (at_ X (tOf X j)) j (stAt X S0 j) (outAt X j)) :
    Step (CloseoutRowsDegreeLoop.machine bodyT) (nT * 2 ^ X.w * (K + 3) + 3)
      (Fin.addCases (fun _ : Fin 64 => 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (lay X ((at_ X (tOf X 0)).jt 0 S0 [] 0) 0)
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word (nT * 2 ^ X.w)))
      (Fin.addCases (fun _ : Fin 64 => 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (lay X ((at_ X (tOf X (nT * 2 ^ X.w - 1))).jt (nT * 2 ^ X.w - 1) (stAt X S0 (nT * 2 ^ X.w))
          (sampTerms X.P nT R batch X.plen X.pfx) 0) (nT * 2 ^ X.w))
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word (nT * 2 ^ X.w))) := by
  have h := enum_run X S0 nT K hnT hc hs hK hg
  unfold src at h
  rw [outAt_sampTerms X nT R batch hE hQ] at h
  exact h

end JLink

end NearCubicWires.WireExponent3_5.SeedFix
