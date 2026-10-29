import SourceAdapters.RAMACSP.GenTMain
import SourceAdapters.RAMACSP.GenFinal
import SourceAdapters.Proximity.OrdinaryCalls
import SourceAdapters.Routing.CoordinateMachineFinal

/-!
# The constraint-circuit printer `ConsWF` from the joins

Paper: `lem:generator` ("It emits the neighbor offsets …; the guard patterns …; and, for each equation family and bit
index, the selector times the equation, whose reads are the offsets of its catalog entries"; the generator is a
`poly(n, log t)` algorithm).

`ConsWF` (`GenMain`) is `composeFramed P Q`:
- `P = composeFramed (composeFramed prefix boost) terms`: the term printer `termsP` (`GenTMain`, callee
  `sumWF Shoup (sumWF coordinates items)`) on the boosted request word, printing `frame (termsInput (termsRequest r))`;
- `Q`: the join `Joins.TermsCircuitWF` at the generator's requests, framed (`Proximity.source_framed_polynomial`),
  printing `frame (listWord gateWord (termsCircuit (termsRequest r)))`, which is `frame (consWord r)`
  (`ownConsOf_eq_terms`).
`consWF_of_joins` takes `Joins.CoordArrayWF`, `Joins.TermsCircuitWF` and `MachineItemsWF` as hypotheses; the export
`generatorMachine_of_joins` discharges the coordinate array.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters
open NearCubicGates.Adapters.Machine.ComposeCarry
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)
open NearCubicWires.RepairRepresentation (natWord)
open Polynomial

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) (hI : Published.Shoup.IrreducibleChoice irrPoly)

/-! ## Sizes -/

theorem irrM_lt (r : ClockRequest) : irrM V irrPoly r < 2 ^ (fieldExp V r.2 + 1) := WireExponent3_5.GF.ofPoly_lt _ _

theorem nbl_small (r : ClockRequest) :
    natBitLength (fieldExp V r.2) ≤ fieldExp V r.2 + 1 ∧ natBitLength (irrM V irrPoly r) ≤ fieldExp V r.2 + 1 ∧
      natBitLength (domExp V r.2) ≤ fieldExp V r.2 + 1 := by
  have := domExp_add_two_le_fieldExp V r.2
  refine ⟨natBitLength_le _, natBitLength_le_of_lt (by omega) (irrM_lt V irrPoly r), ?_⟩
  have := natBitLength_le (domExp V r.2); omega

theorem coordInput_len (r : ClockRequest) :
    (Joins.coordInput (coordRequest V irrPoly r)).length ≤ 6 * fieldExp V r.2 + 9 := by
  obtain ⟨a, b, c⟩ := nbl_small V irrPoly r
  simp only [Joins.coordInput, coordRequest, List.length_append, FL.natWord_len]
  have : modMask (irrPoly (fieldExp V r.2)) (fieldExp V r.2) = irrM V irrPoly r := rfl
  rw [this]; omega

theorem bnd_ci : Bnd (fun r => (Joins.coordInput (coordRequest V irrPoly r)).length) :=
  ((Bnd.mul (Bnd.const 6) (bnd_f V)).add (Bnd.const 9)).mono (fun r => coordInput_len V irrPoly r)

/-- The three callee budgets. -/
def tCalleeBud (Ks es Kc ec Ki ei : ℕ) (r : ClockRequest) : ℕ :=
  (2 * (8 + dropBudget (fieldExp V r.2) (Ks * (fieldExp V r.2 + 1) ^ es)) + 2) +
  (2 * (8 + dropBudget ((Joins.coordInput (coordRequest V irrPoly r)).length + 1)
    (2 * (8 + dropBudget (Joins.coordInput (coordRequest V irrPoly r)).length
      (Kc * ((Joins.coordInput (coordRequest V irrPoly r)).length + 1) ^ ec)) + 2)) + 2) +
  (2 * (8 + dropBudget ((ClockRequest.word r).length + 1)
    (2 * (8 + dropBudget (ClockRequest.word r).length (Ki * (r.1.1 + natBitLength r.2 + 1) ^ ei)) + 2)) + 2)

theorem bnd_tCalleeBud (Ks es Kc ec Ki ei : ℕ) : Bnd (tCalleeBud V irrPoly Ks es Kc ec Ki ei) := by
  have hd : ∀ L B, dropBudget L B = 120 * L + 129 + 2 * B := fun L B => by unfold dropBudget; ring
  have hc := bnd_ci V irrPoly
  refine ((((((((Bnd.const 5000).add (Bnd.mul (Bnd.const 240) (bnd_f V))).add (Bnd.mul (Bnd.const 4)
    (Bnd.mul (Bnd.const Ks) (Bnd.pow ((bnd_f V).add (Bnd.const 1)) es)))).add (Bnd.mul (Bnd.const 2000) hc)).add
    (Bnd.mul (Bnd.const 16) (Bnd.mul (Bnd.const Kc) (Bnd.pow (hc.add (Bnd.const 1)) ec)))).add
    (Bnd.mul (Bnd.const 2000) (bnd_len))).add
    (Bnd.mul (Bnd.const 16) (Bnd.mul (Bnd.const Ki) (Bnd.pow (bnd_nt) ei))))).mono (fun r => ?_)
  unfold tCalleeBud; rw [hd, hd, hd, hd, hd]; omega

theorem tBudAll_inl (Ks es Kc ec Ki ei : ℕ) (r : ClockRequest) (h : 1 ≤ fieldExp V r.2) :
    tBudAll V irrPoly Ks es Kc ec Ki ei (.inl ⟨fieldExp V r.2, h⟩) ≤ tCalleeBud V irrPoly Ks es Kc ec Ki ei r := by
  unfold tBudAll tCalleeBud
  rw [sumBudget_inl]
  simp only [List.length_replicate]
  omega

theorem tBudAll_co (Ks es Kc ec Ki ei : ℕ) (r : ClockRequest) :
    tBudAll V irrPoly Ks es Kc ec Ki ei (.inr (.inl r)) ≤ tCalleeBud V irrPoly Ks es Kc ec Ki ei r := by
  unfold tBudAll tCalleeBud
  rw [sumBudget_inr]
  simp only [tIn, tBud, sumInput, sumBudget_inl, List.length_cons]
  omega

theorem tBudAll_it (Ks es Kc ec Ki ei : ℕ) (r : ClockRequest) :
    tBudAll V irrPoly Ks es Kc ec Ki ei (.inr (.inr r)) ≤ tCalleeBud V irrPoly Ks es Kc ec Ki ei r := by
  unfold tBudAll tCalleeBud
  rw [sumBudget_inr]
  simp only [tIn, tBud, sumInput, sumBudget_inr, List.length_cons]
  omega

/-! ## The term printer's size conditions -/

/-- `8·linConst·Y < 64^(c + s)`. -/
theorem lin8_lt_pow (r : ClockRequest) :
    8 * (linConst V * Yr r) < 64 ^ (boostC V + Nat.size (ClockRequest.word r).length) := by
  have h1 : linConst V < 2 ^ boostC V := by
    have := Nat.lt_two_pow_self (n := boostC V); unfold boostC at *; omega
  have h2 := Yr_le_pow r
  have hb : 1 ≤ boostC V := by unfold boostC; omega
  have h3 : 8 * (2 ^ boostC V * 2 ^ Nat.size (ClockRequest.word r).length) ≤
      64 ^ (boostC V + Nat.size (ClockRequest.word r).length) := by
    rw [← pow_add, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : linConst V * Yr r < 2 ^ boostC V * 2 ^ Nat.size (ClockRequest.word r).length :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1 (one_le_Yr r)) (Nat.mul_le_mul_left _ h2)
  omega

section Terms

variable {Ks es Kc ec Ki ei : ℕ} (WS : ShoupWF irrPoly Ks es) (WC : CoordFWF V irrPoly hI Kc ec)
  (WI : ItemsWF V irrPoly Ki ei)

theorem tFits (AB aB : ℕ) (hB : ∀ r, tCalleeBud V irrPoly Ks es Kc ec Ki ei r ≤ AB * Yr r ^ aB) (r : ClockRequest) :
    TFits V irrPoly (Ks := Ks) (es := es) (Kc := Kc) (ec := ec) (Ki := Ki) (ei := ei) r
      (ctxOf (termsCallee V irrPoly hI WS WC WI) (zG AB aB) (inpOf V r)) (globOf (inpOf V r)) := by
  set s := Nat.size (ClockRequest.word r).length with hs
  set L := boostC V + s with hL
  have hlead : leadOnes (inpOf V r) = L := lead_inpOf V r
  have hK : (globOf (inpOf V r)).K = 2 * 64 ^ L := by show kOf _ = _; unfold kOf; rw [hlead]
  have hN : (globOf (inpOf V r)).N = 2 * 64 ^ L := hK
  have hW : (ctxOf (termsCallee V irrPoly hI WS WC WI) (zG AB aB) (inpOf V r)).Wd = 4 * 64 ^ L := by
    show 2 ^ (6 * leadOnes (inpOf V r)) * 4 = _; rw [hlead, sixtyfour_pow]; ring
  have hLk : (ctxOf (termsCallee V irrPoly hI WS WC WI) (zG AB aB) (inpOf V r)).Lk = 4 * 64 ^ L := by
    show 2 ^ (6 * leadOnes (inpOf V r)) * 4 = _; rw [hlead, sixtyfour_pow]; ring
  have hBk : (ctxOf (termsCallee V irrPoly hI WS WC WI) (zG AB aB) (inpOf V r)).Bk = 2 ^ (aB * L) * (AB + 1) := by
    show 2 ^ (aB * leadOnes (inpOf V r)) * (AB + 1) = _; rw [hlead]
  have hlin := lin_bound V r
  have hlt := lin_lt_pow V r
  rw [← hs, ← hL] at hlt
  have hlt8 := lin8_lt_pow V r
  rw [← hs, ← hL] at hlt8
  have hY1 := one_le_Yr r
  have hlc : 1 ≤ linConst V := linConst_pos V
  have hYl : Yr r ≤ linConst V * Yr r := Nat.le_mul_of_pos_left _ hlc
  have hYw : Yr r = 2 * r.1.1 + 2 * r.2.bits.length + 3 := by have := word_len r; simp only [Yr]; omega
  have hA : r.1.1 + r.2.bits.length + fieldExp V r.2 + clockConst V + tagExp V + 20 ≤ linConst V * Yr r := by
    have := hlin; generalize 2 ^ inExp V r = P at this; generalize 2 ^ colExp V r.2 = Q at this; omega
  have hQ : 16 * 2 ^ colExp V r.2 + 2 * laneExp V r.2 + 2 * tau V r.2 + 2 ≤ linConst V * Yr r := by
    have := hlin; generalize 2 ^ inExp V r = P at this; generalize 2 ^ colExp V r.2 = Q at this ⊢; omega
  clear hlin
  obtain ⟨n1, n2, n3⟩ := nbl_small V irrPoly r
  have hWlt : 4 * 64 ^ L < 2 ^ (4 * 64 ^ L) := Nat.lt_two_pow_self
  have hbud : tCalleeBud V irrPoly Ks es Kc ec Ki ei r ≤ 2 ^ (aB * L) * (AB + 1) := by
    have h1 := hB r
    have h2 : Yr r ^ aB ≤ 2 ^ (aB * s) := by
      rw [Nat.mul_comm, pow_mul]; exact Nat.pow_le_pow_left (Yr_le_pow r) aB
    have h3 : 2 ^ (aB * s) ≤ 2 ^ (aB * L) := Nat.pow_le_pow_right (by norm_num) (by rw [hL]; nlinarith)
    have h4 : AB * Yr r ^ aB ≤ (AB + 1) * 2 ^ (aB * L) := Nat.mul_le_mul (by omega) (h2.trans h3)
    rw [Nat.mul_comm (2 ^ (aB * L))]; omega
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, fun h => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK]; omega
  · rw [hK, hN]
  · rw [hK]; omega
  · rw [hN]; omega
  · rw [hK, hN]
  · rw [hLk]; omega
  · rw [hLk]; omega
  · rw [hLk]; omega
  · rw [hBk]; exact (tBudAll_inl V irrPoly Ks es Kc ec Ki ei r h).trans hbud
  · rw [hBk]; exact (tBudAll_co V irrPoly Ks es Kc ec Ki ei r).trans hbud
  · rw [hBk]; exact (tBudAll_it V irrPoly Ks es Kc ec Ki ei r).trans hbud
  · rw [hW]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · rw [hW]; omega
  · rw [hW]; omega

/-- The cost bound of the term printer's run. -/
def tN (AB aB : ℕ) (r : ClockRequest) : ℕ :=
  tCost V irrPoly hI (ctxOf (termsCallee V irrPoly hI WS WC WI) (zG AB aB) (inpOf V r)) (globOf (inpOf V r))
    (inpOf V r) r

/-- **The term printer** (`wordFunction_of_lang`). -/
noncomputable def termsWF (AB aB : ℕ) (hB : ∀ r, tCalleeBud V irrPoly Ks es Kc ec Ki ei r ≤ AB * Yr r ^ aB) :
    WordFunction ClockRequest (inpOf V)
      (fun r => RepairSource.frame (Joins.termsInput (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r)))
      (fun r => langBudget (termsCallee V irrPoly hI WS WC WI) (zG AB aB) VV MM (inpOf V r)
        (tN V irrPoly hI WS WC WI AB aB r)) :=
  wordFunction_of_lang (inpOf V) _ (termsCallee V irrPoly hI WS WC WI) (zG AB aB) (termsP V)
    (tN V irrPoly hI WS WC WI AB aB)
    (fun r => terms_run V irrPoly hI WS WC WI 4 6 (AB + 1) aB r (boostC V + Nat.size (ClockRequest.word r).length)
      (by unfold boostC; omega) (tFits V irrPoly hI WS WC WI AB aB hB r))
    (fun r => by show 1 ≤ 2 ^ (6 * _) * 4; have := Nat.one_le_two_pow (n := 6 * leadOnes (inpOf V r)); omega)

include WC in
theorem bnd_cwT : Bnd (fun r => (cwOf V irrPoly hI r).length) := by
  refine (Bnd.add (Bnd.mul (Bnd.const Kc) (Bnd.pow ((bnd_ci V irrPoly).add (Bnd.const 1)) ec)) (Bnd.const 1)).mono
    (fun r => ?_)
  have h1 := wf_out_len WC r
  have h2 : (cwOf V irrPoly hI r).length ≤ (RepairSource.frame (cwOf V irrPoly hI r)).length := by
    rw [FL.frame_len]; omega
  exact h2.trans h1

include WI in
theorem bnd_iwT : Bnd (fun r => (machineItemsWord V irrPoly r).length) := by
  refine (Bnd.add (Bnd.mul (Bnd.const Ki) (Bnd.pow (bnd_nt) ei)) (Bnd.const 1)).mono (fun r => ?_)
  have h1 := wf_out_len WI r
  have h2 : (machineItemsWord V irrPoly r).length ≤ (RepairSource.frame (machineItemsWord V irrPoly r)).length := by
    rw [FL.frame_len]; omega
  exact h2.trans h1

theorem bnd_tN (AB aB : ℕ) : Bnd (tN V irrPoly hI WS WC WI AB aB) := by
  have hL := bnd_lead V
  have hk := bnd_kOf V
  have hW := bnd_pow_L V 6
  have hB := bnd_pow_L V aB
  have hn : Bnd (fun r => r.1.1) := ⟨1, 1, fun r => by have := word_len r; simp only [Yr, pow_one]; omega⟩
  have hb : Bnd (fun r => r.2.bits.length) := ⟨1, 1, fun r => by have := word_len r; simp only [Yr, pow_one]; omega⟩
  refine (((((((((((((Bnd.mul (Bnd.const 20) hL).add (Bnd.mul (Bnd.const 5) hk)).add (Bnd.const 300)).add
    (bnd_costS V (stageR V))).add (Bnd.mul (Bnd.const 80) (bnd_f V))).add (Bnd.mul (Bnd.const 16) hW)).add
    (Bnd.mul (Bnd.const (4 * (AB + 1))) hB)).add (bnd_costS V headP)).add (bnd_costS V bodyP)).add
    ((Bnd.mul (Bnd.const 12) hn).add (Bnd.mul (Bnd.const 12) hb))).add
    (Bnd.mul (Bnd.const 10) (bnd_cwT V irrPoly hI WC))).add (Bnd.mul (Bnd.const 10) (bnd_iwT V irrPoly WI))).add
    ((bnd_costS V (emitNatE (.k 0))).add (bnd_costS V (.emit (.k 0))))).mono (fun r => ?_)
  obtain ⟨n1, n2, n3⟩ := nbl_small V irrPoly r
  unfold tN tCost FL.preCost callIrrCost callCoordCost callItemsCost
  simp only [ctxOf, zG, zM, Sz.Lk, Sz.Bk]
  ring_nf
  omega

theorem bnd_stage3T (AB aB : ℕ) :
    Bnd (fun r => langBudget (termsCallee V irrPoly hI WS WC WI) (zG AB aB) VV MM (inpOf V r)
      (tN V irrPoly hI WS WC WI AB aB r)) := by
  have hL := bnd_lead V
  have hW := bnd_pow_L V 6
  have hB := bnd_pow_L V aB
  have hG : Bnd (fun r => NearCubicGates.Close.CellsPack.Gof (termsCallee V irrPoly hI WS WC WI) (zG AB aB)
      (leadOnes (inpOf V r))) := by
    refine ((((Bnd.mul (Bnd.const 8) hW).add (Bnd.mul (Bnd.const (AB + 1)) hB)).add hL).add
      (Bnd.const (AB + aB + 30 + TSK (termsCallee V irrPoly hI WS WC WI)))).mono (fun r => ?_)
    unfold NearCubicGates.Close.CellsPack.Gof
    simp only [zG, zM, Sz.W, Sz.Lk, Sz.Bk]
    ring_nf; omega
  have hI' : Bnd (fun r => (inpOf V r).length) := by
    refine ((hL.add (Bnd.const 1)).add bnd_len).mono (fun r => le_of_eq ?_)
    show (inpOf V r).length = leadOnes (inpOf V r) + 1 + (ClockRequest.word r).length
    rw [lead_inpOf]; simp only [inpOf, boostWord, List.length_append, List.length_replicate, List.length_cons]
    ring
  refine ((Bnd.mul (Bnd.const (10 ^ 6)) (Bnd.mul ((bnd_tN V irrPoly hI WS WC WI AB aB).add (Bnd.const 1))
    (Bnd.pow hG 2))).add (Bnd.mul (Bnd.const 10) hI')).mono (fun r => ?_)
  exact NearCubicGates.Close.CellsPack.lang_le2 _ _ _ _

end Terms

/-! ## The input printer and the composition into `ConsWF` -/

section Compose

variable {Ks es Kc ec Ki ei : ℕ} (WS : ShoupWF irrPoly Ks es) (WC : CoordFWF V irrPoly hI Kc ec)
  (WI : ItemsWF V irrPoly Ki ei)

/-- The input printer: prefix, boost, term printer. -/
noncomputable def tgenWF (AB aB : ℕ) (hB : ∀ r, tCalleeBud V irrPoly Ks es Kc ec Ki ei r ≤ AB * Yr r ^ aB) :=
  NearCubicGates.Adapters.Code.composeFramed (NearCubicGates.Adapters.Code.composeFramed stageP (boostWF V))
    (termsWF V irrPoly hI WS WC WI AB aB hB)

/-- The input printer's budget. -/
def tgenBud (AB aB : ℕ) (r : ClockRequest) : ℕ :=
  (2 * ((2 * Machines.WidthPrefix.prefixBudget (ClockRequest.word r).length + 2) + 1 +
      (2 * langBudget noCallee zF VV MM (Time.prefixWord (ClockRequest.word r))
        (preCost (Time.prefixWord (ClockRequest.word r)) +
          costS (globOf (Time.prefixWord (ClockRequest.word r))) (boostFL (boostC V)) + 1) + 2)) + 2) + 1 +
      (2 * langBudget (termsCallee V irrPoly hI WS WC WI) (zG AB aB) VV MM (inpOf V r)
        (tN V irrPoly hI WS WC WI AB aB r) + 2)

/-- The input printer's budget is polynomial. -/
theorem bnd_tgen (AB aB : ℕ) : Bnd (tgenBud V irrPoly hI WS WC WI AB aB) :=
  ((Bnd.mul (Bnd.const 2) ((((Bnd.mul (Bnd.const 2) bnd_stage1).add (Bnd.const 3)).add
    (Bnd.mul (Bnd.const 2) (bnd_stage2 V))).add (Bnd.const 2))).add (Bnd.const 3)).add
    (Bnd.mul (Bnd.const 2) (bnd_stage3T V irrPoly hI WS WC WI AB aB)) |>.add (Bnd.const 2) |>.mono
      (fun r => by unfold tgenBud; omega)

end Compose

/-- The constraint circuit's word is the join's output at the generator's request. -/
theorem consWord_eq_terms (r : ClockRequest) :
    consWord V irrPoly r = Joins.termsOutput (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r) := by
  unfold consWord ownCons Joins.termsOutput
  rw [dif_pos (modulusGood V irrPoly hI r), ownConsOf_eq_terms]

/-- **The constraint-circuit printer from the joins.** -/
theorem consWF_of_joins (hI : Published.Shoup.IrreducibleChoice irrPoly) (hP : Published.Shoup.PolyTimeIrrChoice irrPoly) (hC : Joins.CoordArrayWF)
    (hT : Joins.TermsCircuitWF) (hM : MachineItemsWF V irrPoly) : ∃ K e : ℕ, Nonempty (ConsWF V irrPoly K e) := by
  obtain ⟨Ks, es, ⟨WS⟩⟩ := hP
  -- the coordinate machine, framed
  obtain ⟨Kc, ec, ⟨WC⟩⟩ := Proximity.source_framed_polynomial _ _ (coordWF hC V irrPoly hI)
  -- the machine items
  obtain ⟨Ki, ei, ⟨WI⟩⟩ := hM
  obtain ⟨AB, aB, hB⟩ := bnd_tCalleeBud V irrPoly Ks es Kc ec Ki ei
  let P := tgenWF V irrPoly hI WS WC WI AB aB hB
  -- the join at the generator's requests, framed
  obtain ⟨KT, eT, ⟨WT⟩⟩ := hT
  have hQ : NearCubicGates.Published.CW19Proximity.SourcePolyTime
      (fun r : ClockRequest => Joins.termsInput (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r))
      (fun r => Joins.termsOutput (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r)) :=
    ⟨KT, eT, ⟨⟨WT.program, fun r => WT.realizes ⟨tReq V irrPoly hI r, tReq_ok V irrPoly hI r⟩⟩⟩⟩
  obtain ⟨KQ, eQ, ⟨Q⟩⟩ := Proximity.source_framed_polynomial _ _ hQ
  let R := NearCubicGates.Adapters.Code.composeFramed P Q
  -- the budget
  obtain ⟨A1, a1, h1⟩ := bnd_tgen V irrPoly hI WS WC WI AB aB
  have hlen : ∀ r, (Joins.termsInput (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r)).length ≤ A1 * Yr r ^ a1 + 1 :=
    fun r => by
      have h0 : (RepairSource.frame (Joins.termsInput (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r))).length ≤
          tgenBud V irrPoly hI WS WC WI AB aB r + 1 := wf_out_len P r
      have h2 : (Joins.termsInput (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r)).length ≤
          (RepairSource.frame (Joins.termsInput (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r))).length := by
        rw [FL.frame_len]; omega
      have h3 := h1 r
      omega
  have hT2 : Bnd (fun r => (2 * tgenBud V irrPoly hI WS WC WI AB aB r + 2) + 1 +
      (2 * (KQ * ((Joins.termsInput (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r)).length + 1) ^ eQ) + 2)) := by
    refine (((Bnd.mul (Bnd.const 2) ⟨A1, a1, h1⟩).add (Bnd.const 5)).add (Bnd.mul (Bnd.const (2 * KQ))
      (Bnd.pow ((Bnd.mul (Bnd.const A1) (Bnd.pow Bnd.scale a1)).add (Bnd.const 2)) eQ))).mono (fun r => ?_)
    have e1 : (Joins.termsInput (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r)).length + 1 ≤ A1 * Yr r ^ a1 + 2 := by
      have := hlen r; omega
    have e2 := Nat.pow_le_pow_left e1 eQ
    have e3 := Nat.mul_le_mul_left KQ e2
    nlinarith
  obtain ⟨A, a, hA⟩ := hT2
  let R' : WordFunction ClockRequest ClockRequest.word (fun r => RepairSource.frame (consWord V irrPoly r)) _ :=
    ⟨R.program, fun r => by
      obtain ⟨rc, hr1, hr2⟩ := R.realizes r
      exact ⟨rc, hr1, hr2.trans (by rw [consWord_eq_terms V irrPoly hI r])⟩⟩
  refine ⟨A * 3 ^ a, a, ⟨wordFunctionRelax (fun r => ?_) R'⟩⟩
  calc _ ≤ A * Yr r ^ a := hA r
    _ ≤ A * (3 * (r.1.1 + natBitLength r.2 + 1)) ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Yr_le_input r) a)
    _ = A * 3 ^ a * (r.1.1 + natBitLength r.2 + 1) ^ a := by rw [mul_pow]; ring

/-- **The generator (`lem:generator`) from the term-circuit printer and the machine-items printer**; the coordinate
array is `Routing.CoordinateMachine.coordinateArrayWF`. -/
theorem generatorMachine_of_joins (hT : Joins.TermsCircuitWF)
    (hM : ∀ (irrPoly : ℕ → (ZMod 2)[X]) (V : Verifier), Published.Shoup.IrreducibleChoice irrPoly →
      Published.Shoup.PolyTimeIrrChoice irrPoly → MachineItemsWF V irrPoly) :
    ∀ (irrPoly : ℕ → (ZMod 2)[X]) (V : Verifier), Published.Shoup.IrreducibleChoice irrPoly →
      Published.Shoup.PolyTimeIrrChoice irrPoly → GeneratorMachine V irrPoly (ownCons V irrPoly) :=
  fun irrPoly V hI hP => generatorMachine_of_consWF V irrPoly hP
    (consWF_of_joins V irrPoly hI hP Routing.CoordinateMachine.coordinateArrayWF hT (hM irrPoly V hI hP))

end NearCubicGates.Adapters.RAMACSP.Gen

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters.Joins NearCubicWires.RepairOrdinary Polynomial

/-- **Export: the generator** (`lem:generator`, `cor:short-pcp-clock`) of the instance with the emitted constraint
circuit `ownCons`, total on every clock request, from the join `Joins.TermsCircuitWF` and the machine-items printer
`Gen.MachineItemsWF` (`RAMACSP/GenItemsSeam`). -/
theorem generatorMachine_of_joins (hT : Joins.TermsCircuitWF)
    (hM : ∀ (irrPoly : ℕ → (ZMod 2)[X]) (V : Verifier), Published.Shoup.IrreducibleChoice irrPoly →
      Published.Shoup.PolyTimeIrrChoice irrPoly → Gen.MachineItemsWF V irrPoly) :
    ∀ (irrPoly : ℕ → (ZMod 2)[X]) (V : Verifier), Published.Shoup.IrreducibleChoice irrPoly →
      Published.Shoup.PolyTimeIrrChoice irrPoly → GeneratorMachine V irrPoly (ownCons V irrPoly) :=
  Gen.generatorMachine_of_joins hT hM

end NearCubicGates.Adapters.RAMACSP
