import Proof.Gates.Setup.PhaseD5
import Proof.Gates.CheckedPCPP.SubstitutedPoly

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.ExecutableInterfaces NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu PairOK)
open NearCubicGates.Close.Worker.Format (readField)

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

/-! ## The set-up data -/

section Data
variable (s P g)

/-- The register capacity of the common prefix (every rejecting run). -/
def capAOf (N0 N pad : ℕ) : ℕ := 1000 * (N + pad + N0 + width s g N + 1) ^ 2 + capK g N

/-- The register capacity of the accepting runs. -/
def setupCapOf (N0 : ℕ) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N)) :
    ℕ :=
  capAOf s g N0 N pad + 1000000 * (setupSizeOf s P g N0 x bits pad B + 1) ^ 2

/-- The cost of the rejecting runs (every guard, the worst case). -/
def rejectCostOf (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s)) (N0 : ℕ) {N : ℕ}
    (x : BitInput N) (bits : List Bool) (pad : ℕ) : ℕ :=
  2000 * (N + N0 + 1) + powCostP N + costB W x bits pad + costR R N + costK g N (lenL g (nu N)) + 100

/-- The cost of the accepting runs. -/
def setupCostOf (cf : CompFull s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s))
    (N0 : ℕ) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N)) : ℕ :=
  rejectCostOf s g W R N0 x bits pad +
    2 * (cf.C * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length + width s g N + 1) ^ cf.e) +
    1000000000000 * (setupSizeOf s P g N0 x bits pad B + 1) ^ 5 + 100

theorem tAOf_pos (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s)) : 0 < tAOf W R := by
  unfold tAOf oR; omega

/-- **The set-up data** of this layout. -/
def mkSetupData (cf : CompFull s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s))
    (tc N0 : ℕ) (hN0 : ∀ N, N0 ≤ N → 4 ≤ N ∧ (width s g N).bits.length ≤ N + 1) : SetupData s P g where
  cf := cf
  tA := tAOf W R
  flag := ⟨0, tAOf_pos s g W R⟩
  tc := tc
  N0 := N0
  hN0 := hN0
  capA := capAOf s g N0
  setupCap := fun x bits pad B => setupCapOf s P g N0 x bits pad B
  rejectCost := fun x bits pad => rejectCostOf s g W R N0 x bits pad
  setupCost := fun x bits pad B => setupCostOf s P g cf W R N0 x bits pad B
  sizeLe := fun x bits pad B => by
    unfold setupCostOf
    have : setupSizeOf s P g N0 x bits pad B + 1 ≤ (setupSizeOf s P g N0 x bits pad B + 1) ^ 5 :=
      Nat.le_self_pow (by norm_num) _
    omega

theorem mk_lay (cf : CompFull s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s))
    (tc N0 : ℕ) (hN0 : ∀ N, N0 ≤ N → 4 ≤ N ∧ (width s g N).bits.length ≤ N + 1) :
    Lay (mkSetupData s P g cf W R tc N0 hN0) W R := ⟨rfl, rfl⟩

end Data

/-! ## The program -/

/-- **The set-up program.** -/
def setupP (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s)) :
    WMX (nsW D) nrW :=
  .seq (phA0 D) (.ifr gF (.seq (phA1 D) (.seq (powP (sFL D))
    (.ifs (sFL D) (.seq (phB D W) (.ifs (sFL D) (.seq (phR D W R) (.ifs (sFL D) (.seq (phK D W)
      (.ifs (sFL D) (.seq (phC D W R) (phD D)) WMX.skip)) WMX.skip)) WMX.skip)) WMX.skip))) WMX.skip)

/-! ## Cost bounds -/

theorem pow_le_c5 (t c a k : ℕ) (h : t ≤ c * a) (hk : k ≤ 5) (ha : 1 ≤ a) : t ^ k ≤ c ^ k * a ^ 5 := by
  calc t ^ k ≤ (c * a) ^ k := Nat.pow_le_pow_left h k
    _ = c ^ k * a ^ k := mul_pow c a k
    _ ≤ c ^ k * a ^ 5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right ha hk)

theorem two_pow_natBitLength_le (v : ℕ) : 2 ^ natBitLength v ≤ 4 * v + 2 := by
  have h1 := SubstitutedPoly.bitLen_le_bits v
  have h2 := LitDecode.two_pow_bits_le v
  calc 2 ^ natBitLength v ≤ 2 ^ (v.bits.length + 1) := Nat.pow_le_pow_right (by norm_num) h1
    _ = 2 * 2 ^ v.bits.length := by ring
    _ ≤ 4 * v + 2 := by omega

theorem regsCost_le (pb rb sc cl q S : ℕ) (hpb : pb ≤ S) (hrb : rb ≤ S) (hsc : sc ≤ 2 * S) (hcl : 2 ^ cl ≤ S)
    (hq : q ≤ S) : regsCost pb rb sc cl q ≤ 100000 * (S + 1) ^ 5 := by
  have ha : 1 ≤ S + 1 := by omega
  have b1 := LitDecode.binCost_le pb
  have b2 := LitDecode.binCost_le rb
  have l1 := LitDecode.bits_len_le pb
  have l2 := LitDecode.bits_len_le rb
  have p1 := pow_le_c5 (pb + 1) 1 (S + 1) 2 (by omega) (by norm_num) ha
  have p2 := pow_le_c5 (rb + 1) 1 (S + 1) 2 (by omega) (by norm_num) ha
  have p3 := pow_le_c5 (sc + 2) 2 (S + 1) 2 (by omega) (by norm_num) ha
  have p4 := two_pow_natBitLength_le sc
  have p5 := pow_le_c5 (2 ^ cl + q + 2) 2 (S + 1) 3 (by omega) (by norm_num) ha
  have p6 := pow_le_c5 (2 ^ cl + 1) 1 (S + 1) 2 (by omega) (by norm_num) ha
  have p7 : 2 ^ natBitLength sc * (sc + 3) ≤ 24 * (S + 1) ^ 5 := by
    have e1 : 2 ^ natBitLength sc ≤ 8 * (S + 1) := by omega
    have e2 : sc + 3 ≤ 3 * (S + 1) := by omega
    have := pow_le_c5 (S + 1) 1 (S + 1) 2 (by omega) (by norm_num) ha
    calc 2 ^ natBitLength sc * (sc + 3) ≤ (8 * (S + 1)) * (3 * (S + 1)) := Nat.mul_le_mul e1 e2
      _ = 24 * (S + 1) ^ 2 := by ring
      _ ≤ 24 * (1 ^ 2 * (S + 1) ^ 5) := Nat.mul_le_mul_left _ this
      _ = 24 * (S + 1) ^ 5 := by ring
  have p8 := pow_le_c5 (S + 1) 1 (S + 1) 1 (by omega) (by norm_num) ha
  norm_num at p1 p2 p3 p5 p6 p8
  unfold regsCost
  nlinarith

section Costs
variable (D : SetupData s P g) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ)
  (B : Outer.OuterGuess (width s g N))

theorem phDCost_le : phDCost D x bits pad B ≤ 1000000000000 * (setupSize D x bits pad B + 1) ^ 5 := by
  obtain ⟨hpb, hrb, hq, hM, -, hsw, -, -, -, hL⟩ := size_facts D x bits pad B
  have hg : gadgets s g N = 2 ^ clauseWidth g.clauseDegree (width s g N) := rfl
  have hr := regsCost_le (pcpp s P g x B).proofBits (pcpp s P g x B).randomBits
    (width s g N + P.code.length (width s g N)) (clauseWidth g.clauseDegree (width s g N)) (width s g N)
    (setupSize D x bits pad B) hpb hrb (by omega) (by omega) hq
  have ha : 1 ≤ setupSize D x bits pad B + 1 := by omega
  have p1 := pow_le_c5 (setupSize D x bits pad B + 1) 1 (setupSize D x bits pad B + 1) 1 (by omega) (by norm_num) ha
  have p2 := pow_le_c5 (10 * setupSize D x bits pad B + 10 + 1) 11 (setupSize D x bits pad B + 1) 2 (by omega)
    (by norm_num) ha
  norm_num at p1 p2
  unfold phDCost WorkerArith.headerCost
  nlinarith

/-! ## CHECK's cost is monotone in the description length -/

theorem checkCost_mono {dl dl' : ℕ} (h : dl ≤ dl') (lb lp N : ℕ) :
    Succinct.checkCost dl lb lp N ≤ Succinct.checkCost dl' lb lp N := by
  unfold Succinct.checkCost Succinct.pointCost Succinct.evalCost Succinct.nodeCost
  have h1 := Succinct.fieldCost_mono (b := lb + lp) (b' := lb + lp) h le_rfl
  have h2 := Succinct.fieldCost_mono (b := lb) (b' := lb) h le_rfl
  gcongr

theorem costK_mono (g : GateParams) (N : ℕ) {dl dl' : ℕ} (h : dl ≤ dl') : costK g N dl ≤ costK g N dl' := by
  unfold costK
  have := checkCost_mono h (lbOf g (nu N)) (lpOf (nu N)) N
  simp only
  omega

end Costs

/-! ## After phase P -/

section AfterP
variable (D : SetupData s P g)

/-- The state after phase P. -/
def stP (N : ℕ) (xs bits : List Bool) : WState (nsW D) nrW :=
  ((stA1 D N xs bits).setv rNu (Nat.clog 2 N)).sets (sFL D) (powFlag N)

/-- The ideal state before phase B: the guess word with its padding on `WT`. -/
def stB (N : ℕ) (xs bits : List Bool) (pad : ℕ) : WState (nsW D) nrW :=
  (stP D N xs bits).sets (sWT D) (guessWord N bits pad)

theorem simW_stB (N : ℕ) (xs bits : List Bool) (pad : ℕ) (hL : sFL D ≠ sWT D) :
    SimW (stB D N xs bits pad) (stP D N xs bits) := by
  apply CheckedPCPP.SimW.symm
  apply Worker.simW_sets
  simp only [stP, stA1, WState.sets_st, Function.update_of_ne (Ne.symm hL), Function.update_self]
  unfold guessWord
  exact RdEq.symm (rdEq_append_blank _ _ (fun b hb => (List.mem_replicate.1 hb).2))

theorem preB_stB {W : OuterM.WidthDonor s.mw (g.sv s)} {R : OuterM.ARun s.mw (g.sv s)} (hL : Lay D W R) {N : ℕ}
    (x : BitInput N) (bits : List Bool) (pad : ℕ) (hpow : N = 2 ^ nu N) :
    PreB D x bits pad (stB D N (List.ofFn x) bits pad) := by
  have vFL := sFL_val hL
  have hfl : powFlag N = [true] := by
    unfold powFlag; rw [if_pos ((pow2_iff N).2 hpow)]
  have hcl : Nat.clog 2 N = nu N := clog_eq_log_of_pow N hpow
  have nFW : sFL D ≠ sWT D := fin_ne_of_val (by simp; omega)
  have nXF : sX D ≠ sFL D := fin_ne_of_val (by simp; omega)
  have nXW : sX D ≠ sWT D := fin_ne_of_val (by simp)
  have nBF : sBW D ≠ sFL D := fin_ne_of_val (by simp; omega)
  have nBW : sBW D ≠ sWT D := fin_ne_of_val (by simp)
  have nBX : sBW D ≠ sX D := fin_ne_of_val (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [stB, stP, stA1, WState.sets_st, WState.setv_st]
    rw [Function.update_of_ne nXW, Function.update_of_ne nXF, Function.update_of_ne nXW]
    simp [coldState]
  · simp only [stB, stP, stA1, WState.sets_st, WState.setv_st]
    rw [Function.update_of_ne nBW, Function.update_of_ne nBF, Function.update_of_ne nBW]
    simp [coldState, nBX]
  · simp [stB]
  · simp [stB, stP, Function.update_of_ne nFW, hfl]
  · intro i h0 h1 h2 h16
    simp only [stB, stP, stA1, WState.sets_st, WState.setv_st]
    rw [Function.update_of_ne (fin_ne_of_val (by simpa using h2)), Function.update_of_ne (fin_ne_of_val (by omega)),
      Function.update_of_ne (fin_ne_of_val (by simpa using h2))]
    simp [coldState, fin_ne_of_val (by simpa using h0 : i.val ≠ (sX D).val),
      fin_ne_of_val (by simpa using h1 : i.val ≠ (sBW D).val)]
  · intro i; simp [stB, stP, stA1, coldState]
  · funext r
    simp only [stB, stP, stA1, WState.sets_val, WState.setv_val, coldState, Function.update_apply, hcl]
    have d1 : rNu ≠ rN := by decide
    by_cases h1 : r = rNu
    · subst h1; simp [d1]
    · by_cases h2 : r = rN
      · subst h2; simp [Ne.symm d1]
      · simp [h1, h2]
  · simp [stB, stP, stA1, coldState]

end AfterP

/-! ## Branching on ideal states -/

theorem ifs_simT {ns nr cap : ℕ} {i : Fin (ns + 1)} {P Q : WMX ns nr} {ι ι' : WState ns nr} {n : ℕ}
    (hb : wbit ι i = true) (h : ∃ τ', WXExec cap P ι τ' n ∧ SimW ι' τ') :
    ∃ τ', WXExec cap (.ifs i P Q) ι τ' (n + 1) ∧ SimW ι' τ' := by
  obtain ⟨τ', e, s⟩ := h
  exact ⟨τ', WXExec.ifsT hb e, s⟩

theorem ifs_simF {ns nr cap : ℕ} {i : Fin (ns + 1)} {P : WMX ns nr} {ι : WState ns nr}
    (hb : wbit ι i = false) : WXExec cap (.ifs i P WMX.skip) ι ι 1 :=
  WXExec.ifsF hb (WXExec.skip cap ι)

theorem wbit_one {ns : ℕ} (σ : WState ns nrW) (i : Fin (ns + 1)) (b : Bool) (h : σ.st i = [b]) (hh : σ.sh i = 0) :
    wbit σ i = b := by
  unfold wbit; rw [h, hh]; rfl

/-! ## The accepting runs -/

section Accept
variable (cf : CompFull s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s)) (tc N0 : ℕ)
  (hN0 : ∀ N, N0 ≤ N → 4 ≤ N ∧ (width s g N).bits.length ≤ N + 1)

theorem setup_accept {N : ℕ} (x : BitInput N) (bits : List Bool) (pad cap : ℕ) (hpad : N / 16 + 1 ≤ pad)
    (hcap : capA (mkSetupData s P g cf W R tc N0 hN0) N pad ≤ cap) (B : Outer.OuterGuess (width s g N))
    (hN : N0 ≤ N) (hdec : Worker.Decodes (width s g N) (guessWord N bits pad) B) (hok : PairOK s g x B)
    (hcapS : setupCap (mkSetupData s P g cf W R tc N0 hN0) x bits pad B ≤ cap) :
    ∃ jk τ, WXExec cap (setupP (mkSetupData s P g cf W R tc N0 hN0) W R)
        (coldState (mkSetupData s P g cf W R tc N0 hN0) (List.ofFn x) bits) τ
        (setupCost (mkSetupData s P g cf W R tc N0 hN0) x bits pad B) ∧
      SimW (LoopEntry (mkSetupData s P g cf W R tc N0 hN0) N x bits pad B jk) τ := by
  classical
  set D := mkSetupData s P g cf W R tc N0 hN0 with hD
  have hL : Lay D W R := mk_lay s P g cf W R tc N0 hN0
  have vFL := sFL_val hL
  obtain ⟨hN4, hqb⟩ := hN0 N hN
  obtain ⟨hpow, hon, hfit, hchk⟩ := hok
  have hcA : capA D N pad = capAOf s g N0 N pad := rfl
  have hcS : setupCap D x bits pad B = setupCapOf s P g N0 x bits pad B := rfl
  unfold capAOf at hcA
  unfold setupCapOf capAOf at hcS
  have hsq := Nat.le_self_pow (n := 2) (by norm_num) (N + pad + N0 + width s g N + 1)
  have hD0 : D.N0 = N0 := rfl

  have e0 := phA0_exec D x bits cap (by rw [hD0]; omega)
  have e1 := phA1_exec D x bits cap (by rw [hD0]; omega) (by rw [hD0]; exact hN)
  have eP := powP_exec (cap := cap) (sFL D) N (stA1 D N (List.ofFn x) bits) (by simp [stA1, coldState]) (by omega)
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) [stA1, coldState, Function.update_apply])
    (by
      simp only [stA1, WState.sets_st, WState.setv_st]
      rw [Function.update_of_ne (fin_ne_of_val (by rw [vFL]; simp))]
      exact coldState_other D _ _ _ (fin_ne_of_val (by rw [vFL]; simp)) (fin_ne_of_val (by rw [vFL]; simp)))
    (by simp [stA1, coldState]) (by omega)
  have s0 : SimW (stB D N (List.ofFn x) bits pad) (stP D N (List.ofFn x) bits) :=
    simW_stB D N _ bits pad (fin_ne_of_val (by rw [vFL]; simp))
  -- phase B
  obtain ⟨τB, ιB, eB, sB, aB⟩ := phB_ideal D W R hL x bits pad cap hpad (by rw [hD0]; exact hN) hpow
    (by nlinarith) _ (preB_stB D hL x bits pad hpow)
  have hokB : oracleOK s g N (guessWord N bits pad) = true := Worker.oracleOK_of_decodes s g hdec
  have hshB : ∀ i, i ≠ sWT D → ιB.sh i = 0 := fun i hi => by rw [aB.sh]; simp [hi]
  have nFW : sFL D ≠ sWT D := fin_ne_of_val (by rw [vFL]; simp)
  -- phase R
  have hnuN : nu N ≤ N := Nat.log_le_self 2 N
  obtain ⟨τR, ιR, eR, sR, aR⟩ := phR_ideal D W R hL x bits pad cap B hdec (by omega) ιB aB
  have hshR : ∀ i, i ≠ sWT D → ιR.sh i = 0 := fun i hi => by rw [aR.sh]; simp [hi]
  have hFLR : ιR.st (sFL D) = [true] := by rw [aR.fl]; simp [hfit]
  -- phase K
  obtain ⟨τK, eK, aK⟩ := phK_exec D W R hL x bits pad cap B hpow hN4 hfit (by omega) ιR aR hFLR
  have hFLK : τK.st (sFL D) = [true] := by rw [aK.fl]; simp [hchk]
  have hshK : ∀ i, i ≠ sWT D → τK.sh i = 0 := fun i hi => by rw [aK.sh]; simp [hi]
  -- phase C
  obtain ⟨τC, ιC, eC, sC, aC⟩ := phC_ideal D W R hL x bits pad cap B hN4 τK aK hFLK
  -- phase D
  have eD := phD_exec D x bits pad B cap (by
    have : setupSize D x bits pad B = setupSizeOf s P g N0 x bits pad B := rfl
    rw [this]; omega) ιC aC
  have sD := final_simW D x bits pad B ιC aC
  -- the chain
  have EC := Worker.seq_sim eC sC ⟨_, eD, sD⟩
  have EC' := ifs_simT (Q := WMX.skip) (wbit_one _ _ true hFLK (hshK _ nFW)) EC
  have EK := Worker.seq_sim eK (SimW.refl _) EC'
  have EK' := ifs_simT (Q := WMX.skip) (wbit_one _ _ true hFLR (hshR _ nFW)) EK
  have ER := Worker.seq_sim eR sR EK'
  have ER' := ifs_simT (Q := WMX.skip) (wbit_one _ _ true (by rw [aB.fl, hokB]) (hshB _ nFW)) ER
  have EB := Worker.seq_sim eB sB ER'
  have EB' := ifs_simT (Q := WMX.skip) (wbit_one _ _ true (preB_stB D hL x bits pad hpow).fl
    ((preB_stB D hL x bits pad hpow).sh _)) EB
  obtain ⟨τ1, e1', s1'⟩ := EB'
  obtain ⟨τ, eT, sT⟩ := Worker.run_of_simW s0 e1'
  have hgF : (stA0 D N (List.ofFn x) bits).val gF ≠ 0 := by simp [stA0, hD0, hN]
  refine ⟨_, τ, ?_, CheckedPCPP.SimW.trans s1' sT⟩
  refine WXExec.mono (WXExec.seq e0 (WXExec.ifrT hgF (WXExec.seq e1 (WXExec.seq eP eT)))) ?_
  have hK := costK_mono g N (dl := (PCPPNative.descriptor B.src).length) (dl' := lenL g (nu N)) hfit
  have hDc := phDCost_le D x bits pad B
  have hS : setupSize D x bits pad B = setupSizeOf s P g N0 x bits pad B := rfl
  have hC : compBudget D B = cf.C * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length +
      width s g N + 1) ^ cf.e := rfl
  have hSC : setupCost D x bits pad B = setupCostOf s P g cf W R N0 x bits pad B := rfl
  rw [hSC, hD0]
  rw [hS] at hDc
  unfold setupCostOf rejectCostOf
  omega

/-! ## The rejecting runs -/

theorem bit_false {ns : ℕ} {ι τ : WState ns nrW} (i : Fin (ns + 1)) (hs : SimW ι τ) (h : wbit ι i = false) :
    readTapeBit (τ.st i) (τ.sh i) = false := by
  have := hs.bit i; unfold wbit at this; rw [this]; exact h

theorem setup_reject (hon : ∀ N, N0 ≤ N → (g.sv s).onset ≤ nu N) {N : ℕ} (x : BitInput N) (bits : List Bool)
    (pad cap : ℕ) (hpad : N / 16 + 1 ≤ pad) (hcap : capA (mkSetupData s P g cf W R tc N0 hN0) N pad ≤ cap)
    (hrej : N < (mkSetupData s P g cf W R tc N0 hN0).N0 ∨
      Worker.setupFlag s P g N x (guessWord N bits pad) = false) :
    ∃ τ, WXExec cap (setupP (mkSetupData s P g cf W R tc N0 hN0) W R)
        (coldState (mkSetupData s P g cf W R tc N0 hN0) (List.ofFn x) bits) τ
        (rejectCost (mkSetupData s P g cf W R tc N0 hN0) x bits pad) ∧
      readTapeBit (τ.st (sFL (mkSetupData s P g cf W R tc N0 hN0)))
        (τ.sh (sFL (mkSetupData s P g cf W R tc N0 hN0))) = false ∧ τ.cell = false := by
  classical
  set D := mkSetupData s P g cf W R tc N0 hN0 with hD
  have hL : Lay D W R := mk_lay s P g cf W R tc N0 hN0
  have vFL := sFL_val hL
  have hcA : capA D N pad = capAOf s g N0 N pad := rfl
  unfold capAOf at hcA
  have hsq := Nat.le_self_pow (n := 2) (by norm_num) (N + pad + N0 + width s g N + 1)
  have hD0 : D.N0 = N0 := rfl
  have hRC : rejectCost D x bits pad = rejectCostOf s g W R N0 x bits pad := rfl
  rw [hRC]
  unfold rejectCostOf
  have e0 := phA0_exec D x bits cap (by rw [hD0]; omega)
  have nFX : sFL D ≠ sX D := fin_ne_of_val (by rw [vFL]; simp)
  have nFB : sFL D ≠ sBW D := fin_ne_of_val (by rw [vFL]; simp)
  have nFW : sFL D ≠ sWT D := fin_ne_of_val (by rw [vFL]; simp)
  by_cases hN : N0 ≤ N
  swap
  · -- below the guard
    have hgF : (stA0 D N (List.ofFn x) bits).val gF = 0 := by simp [stA0, hD0, hN]
    refine ⟨_, WXExec.mono (WXExec.seq e0 (WXExec.ifrF (P := .seq (phA1 D) (.seq (powP (sFL D)) _)) hgF
      (WXExec.skip cap _))) (by omega), ?_, by simp [stA0]⟩
    simp only [stA0, WState.setv_st, WState.setv_sh, coldState_sh]
    rw [coldState_other D _ _ _ nFX nFB]; rfl
  obtain ⟨hN4, hqb⟩ := hN0 N hN
  have hflag : Worker.setupFlag s P g N x (guessWord N bits pad) = false := by
    rcases hrej with h | h
    · rw [hD0] at h; omega
    · exact h
  have e1 := phA1_exec D x bits cap (by rw [hD0]; omega) (by rw [hD0]; exact hN)
  have eP := powP_exec (cap := cap) (sFL D) N (stA1 D N (List.ofFn x) bits) (by simp [stA1, coldState]) (by omega)
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) [stA1, coldState, Function.update_apply])
    (by
      simp only [stA1, WState.sets_st, WState.setv_st]
      rw [Function.update_of_ne nFW]
      exact coldState_other D _ _ _ nFX nFB)
    (by simp [stA1, coldState]) (by omega)
  have hgF : (stA0 D N (List.ofFn x) bits).val gF ≠ 0 := by simp [stA0, hD0, hN]
  -- the prefix, then the rest from the state after phase P
  suffices hrest : ∃ τ n, WXExec cap (.ifs (sFL D) (.seq (phB D W) (.ifs (sFL D) (.seq (phR D W R) (.ifs (sFL D)
      (.seq (phK D W) (.ifs (sFL D) (.seq (phC D W R) (phD D)) WMX.skip)) WMX.skip)) WMX.skip)) WMX.skip)
      (stP D N (List.ofFn x) bits) τ n ∧
      n ≤ costB W x bits pad + costR R N + costK g N (lenL g (nu N)) + 20 ∧
      readTapeBit (τ.st (sFL D)) (τ.sh (sFL D)) = false ∧ τ.cell = false by
    obtain ⟨τ, n, e, hn, hb, hc⟩ := hrest
    exact ⟨τ, WXExec.mono (WXExec.seq e0 (WXExec.ifrT hgF (WXExec.seq e1 (WXExec.seq eP e)))) (by
      unfold powCostP at *; omega), hb, hc⟩
  by_cases hpow : N = 2 ^ nu N
  swap
  · -- not a power of two
    have hfl : powFlag N = [] := by unfold powFlag; rw [if_neg (fun h => hpow ((pow2_iff N).1 h))]
    have hst : (stP D N (List.ofFn x) bits).st (sFL D) = [] := by simp [stP, hfl]
    refine ⟨_, 1, ifs_simF (by unfold wbit; rw [hst]; rfl), by omega, by rw [hst]; rfl, by simp [stP, stA1, coldState]⟩
  have s0 : SimW (stB D N (List.ofFn x) bits pad) (stP D N (List.ofFn x) bits) := simW_stB D N _ bits pad nFW
  have hpre := preB_stB D hL x bits pad hpow
  obtain ⟨τB, ιB, eB, sB, aB⟩ := phB_ideal D W R hL x bits pad cap hpad (by rw [hD0]; exact hN) hpow
    (by nlinarith) _ hpre
  have hshB : ∀ i, i ≠ sWT D → ιB.sh i = 0 := fun i hi => by rw [aB.sh]; simp [hi]
  -- transfer a run from the ideal state before phase B
  have fin : ∀ (ιE : WState (nsW D) nrW) (n : ℕ), (∃ τ', WXExec cap (.seq (phB D W) (.ifs (sFL D) (.seq (phR D W R)
      (.ifs (sFL D) (.seq (phK D W) (.ifs (sFL D) (.seq (phC D W R) (phD D)) WMX.skip)) WMX.skip)) WMX.skip))
      (stB D N (List.ofFn x) bits pad) τ' n ∧ SimW ιE τ') → wbit ιE (sFL D) = false → ιE.cell = false →
      n ≤ costB W x bits pad + costR R N + costK g N (lenL g (nu N)) + 19 →
      ∃ τ n', WXExec cap (.ifs (sFL D) (.seq (phB D W) (.ifs (sFL D) (.seq (phR D W R) (.ifs (sFL D)
        (.seq (phK D W) (.ifs (sFL D) (.seq (phC D W R) (phD D)) WMX.skip)) WMX.skip)) WMX.skip)) WMX.skip)
        (stP D N (List.ofFn x) bits) τ n' ∧
        n' ≤ costB W x bits pad + costR R N + costK g N (lenL g (nu N)) + 20 ∧
        readTapeBit (τ.st (sFL D)) (τ.sh (sFL D)) = false ∧ τ.cell = false := by
    intro ιE n h hb hc hn
    obtain ⟨τ1, e1', s1'⟩ := ifs_simT (Q := WMX.skip) (wbit_one _ _ true hpre.fl (hpre.sh _)) h
    obtain ⟨τ, eT, sT⟩ := Worker.run_of_simW s0 e1'
    have sE := CheckedPCPP.SimW.trans s1' sT
    exact ⟨τ, _, eT, by omega, bit_false _ sE hb, by rw [sE.cell]; exact hc⟩
  by_cases hok : oracleOK s g N (guessWord N bits pad) = true
  swap
  · -- a field does not decode
    have hokf : oracleOK s g N (guessWord N bits pad) = false := by simpa using hok
    exact fin ιB _ (Worker.seq_sim eB sB ⟨_, ifs_simF (wbit_one _ _ false (by rw [aB.fl, hokf]) (hshB _ nFW)),
      SimW.refl _⟩) (wbit_one _ _ false (by rw [aB.fl, hokf]) (hshB _ nFW)) aB.cell (by omega)
  obtain ⟨B, hdec⟩ := Worker.exists_decodes_of_oracleOK s g hok
  obtain ⟨τR, ιR, eR, sR, aR⟩ := phR_ideal D W R hL x bits pad cap B hdec (by
    have : nu N ≤ N := Nat.log_le_self 2 N; omega) ιB aB
  have hshR : ∀ i, i ≠ sWT D → ιR.sh i = 0 := fun i hi => by rw [aR.sh]; simp [hi]
  by_cases hfit : Outer.SrcFits g.lenExp (nu N) B.src
  swap
  · -- `⟨B_src⟩_ν` does not fit
    have hF : ιR.st (sFL D) = [false] := by rw [aR.fl]; simp [hfit]
    exact fin ιR _ (Worker.seq_sim eB sB (ifs_simT (Q := WMX.skip) (wbit_one _ _ true (by rw [aB.fl, hok]) (hshB _ nFW))
      (Worker.seq_sim eR sR ⟨_, ifs_simF (wbit_one _ _ false hF (hshR _ nFW)), SimW.refl _⟩)))
      (wbit_one _ _ false hF (hshR _ nFW)) aR.cell (by omega)
  have hFLR : ιR.st (sFL D) = [true] := by rw [aR.fl]; simp [hfit]
  obtain ⟨τK, eK, aK⟩ := phK_exec D W R hL x bits pad cap B hpow hN4 hfit (by omega) ιR aR hFLR
  have hshK : ∀ i, i ≠ sWT D → τK.sh i = 0 := fun i hi => by rw [aK.sh]; simp [hi]
  have hKc := costK_mono g N (dl := (PCPPNative.descriptor B.src).length) (dl' := lenL g (nu N)) hfit
  by_cases hchk : Outer.CheckAt (nu N) x B.src
  swap
  · -- CHECK fails
    have hF : τK.st (sFL D) = [false] := by rw [aK.fl]; simp [hchk]
    exact fin τK _ (Worker.seq_sim eB sB (ifs_simT (Q := WMX.skip) (wbit_one _ _ true (by rw [aB.fl, hok]) (hshB _ nFW))
      (Worker.seq_sim eR sR (ifs_simT (Q := WMX.skip) (wbit_one _ _ true hFLR (hshR _ nFW))
        (Worker.seq_sim eK (SimW.refl _) ⟨_, ifs_simF (wbit_one _ _ false hF (hshK _ nFW)), SimW.refl _⟩)))))
      (wbit_one _ _ false hF (hshK _ nFW)) aK.cell (by omega)
  -- every guard holds: the set-up's flag is true
  exfalso
  have hpair : PairOK s g x B := ⟨hpow, hon N hN, hfit, hchk⟩
  have : Worker.setupFlag s P g N x (guessWord N bits pad) = true := by
    unfold Worker.setupFlag
    rw [hok, Bool.true_and, decide_eq_true_iff]
    show PairOK s g x (Worker.decodeGuess s P g N x (guessWord N bits pad)).oracle
    rw [Worker.decodeGuess_oracle_eq s P g N x _ B hdec]
    exact hpair
  rw [this] at hflag
  exact Bool.noConfusion hflag

theorem setup_ideal (hon : ∀ N, N0 ≤ N → (g.sv s).onset ≤ nu N) :
    SetupSpec (mkSetupData s P g cf W R tc N0 hN0) (setupP (mkSetupData s P g cf W R tc N0 hN0) W R) := by
  intro N x bits pad cap hpad hcap
  exact ⟨fun B hN hdec hok hcapS => setup_accept cf W R tc N0 hN0 x bits pad cap hpad hcap B hN hdec hok hcapS,
    fun hrej => setup_reject cf W R tc N0 hN0 hon x bits pad cap hpad hcap hrej⟩

end Accept

end

end NearCubicGates.Close.Setup
