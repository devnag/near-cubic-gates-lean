import Proof.Gates.Recovery.HTBudget
import Proof.Gates.CheckedPCPP.FramedWord
import Proof.Hierarchy.HierarchyBinaryPower
import Proof.Amplification.RecoveryReadyCalls
import Proof.Gates.Setup.UniformSpec

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.HT

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5 NearCubicWires.ExtDecompositionBatch
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicGates.Close NearCubicGates.Close.Gadget
open NearCubicGates.PublishedSources.PCPP NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound oracleDepth)

section Cost

variable {s : GateSources} {P : ThreeQueryPCPP} {g : Transfer.GateParams}

/-- The cap at an instance: what the fit test and the main branch need. -/
noncomputable def Inst.cap (P : ThreeQueryPCPP) (cd pl : ℕ) (i : Inst s g) : ℕ :=
  ((i.R + 2) ^ cd + i.R + 2 * i.n + pl + 4) ^ 2 + mainReq (P := P) i.z i.Bs i.c ((i.R + 2) ^ cd - 1).size pl

/-- The word-level cost bound at an instance (`ht_exec`). -/
noncomputable def Inst.cost (cx : Setup.CompFull s P g) (Ke ee Kh eh cd pl : ℕ) (i : Inst s g) : ℕ :=
  200 * (cd + pl + 1) * (i.cap P cd pl + 1) ^ 2 + 10 + mainBound cx Ke ee Kh eh (i.cap P cd pl) i.B i.z i.Bs i.c

theorem poly_cap (cx : Setup.CompFull s P g) (pe ph : Program) (Ke ee Kh eh : ℕ)
    (hpe : ∀ m : MessageRequest, ∃ out, ClockJoin.ReadyRun pe.machine (Ke * ((messageWord m).length + 1) ^ ee)
      (pe.inputTapes (messageWord m)) out ∧ out pe.outputTape = FramedSim.pairs (List.ofFn (P.code.enc m.1 m.2.val)))
    (hph : ∀ a : AcceptedCircuitInput, ∃ out, ClockJoin.ReadyRun ph.machine
      (Kh * ((acceptedCircuitInputWord a).length + 1) ^ eh) (ph.inputTapes (acceptedCircuitInputWord a)) out ∧
      out ph.outputTape = FramedSim.pairs (List.ofFn (P.honest a))) (cd pl : ℕ) :
    PolyB (Inst.S (s := s) (g := g)) (fun i => i.cap P cd pl) := by
  have hR := poly_R (s := s) (g := g)
  have hn := poly_n (s := s) (g := g)
  have hd := poly_desc (s := s) (g := g)
  have hL := poly_L (s := s) (g := g) pe Ke ee hpe
  have hW := poly_Cw (s := s) (g := g) cx
  have hV := PolyB.pow (PolyB.add hR (PolyB.const 2)) cd
  have hpb : PolyB (Inst.S (s := s) (g := g))
      (fun i => (P.output (i.C P)).proofBits) :=
    (PolyB.add (PolyB.add (PolyB.mul (PolyB.const 2) (PolyB.add hW (PolyB.add hR hL))) (PolyB.const 1))
      (PolyB.mul (PolyB.const Kh) (PolyB.pow (PolyB.add (PolyB.add hW (PolyB.add hR hL)) (PolyB.const 1)) eh))).mono
      fun i => by
        have h := proofBits_le ph Kh eh hph i
        have hCn : (i.C P).n = i.R + P.code.length i.R := C_n i
        have hp : ((i.C P).word.length + (i.C P).n + 1) ^ eh ≤
            ((i.C P).word.length + (P.output (i.C P)).word.length + (i.R + P.code.length i.R) + 1) ^ eh :=
          Nat.pow_le_pow_left (by omega) _
        have := Nat.mul_le_mul_left Kh hp
        omega
  have hG := PolyB.add (PolyB.pow (PolyB.add (PolyB.add (PolyB.add hV hR) (PolyB.mul (PolyB.const 2) hn))
    (PolyB.const (pl + 4))) 2)
    (PolyB.mul (PolyB.const 100) (PolyB.add (PolyB.add (PolyB.add (PolyB.add (PolyB.add hd hR) hL) hW) hpb)
      (PolyB.add hV (PolyB.const (2 ^ pl + pl + 1)))))
  refine hG.mono fun i => ?_
  have hV1 : 1 ≤ (i.R + 2) ^ cd := Nat.one_le_pow _ _ (by omega)
  have h2 := two_pow_size_le ((i.R + 2) ^ cd - 1)
  have h3 : ((i.R + 2) ^ cd - 1).size < 2 ^ ((i.R + 2) ^ cd - 1).size := Nat.lt_two_pow_self
  have hCn : (i.C P).n = i.R + P.code.length i.R := C_n i
  have hf : ((i.R + 2) ^ cd + i.R + 2 * i.n + pl + 4) ^ 2 = ((i.R + 2) ^ cd + i.R + 2 * i.n + (pl + 4)) ^ 2 := by
    ring
  unfold Inst.cap mainReq
  change ((i.R + 2) ^ cd + i.R + 2 * i.n + pl + 4) ^ 2 + (2 * (PCPPNative.descriptor i.c).length + 8 * i.R + 8 +
      (8 * (i.R + P.code.length i.R) + 4 * (i.C P).word.length + 2 * (P.output (i.C P)).proofBits + 16) +
      (2 * 2 ^ ((i.R + 2) ^ cd - 1).size + 2 * 2 ^ pl + 4 * (i.R + ((i.R + 2) ^ cd - 1).size + pl) + 4 +
        16 * ((P.output (i.C P)).word.length + 2 ^ ((i.R + 2) ^ cd - 1).size + (i.C P).n +
          (P.output (i.C P)).proofBits + 2) +
        4 * ((i.C P).n + (P.output (i.C P)).proofBits + 3 * ((i.C P).n + (P.output (i.C P)).proofBits)) +
        2 ^ pl + 20)) ≤ _
  omega

theorem poly_cost (cx : Setup.CompFull s P g) (pe ph : Program) (Ke ee Kh eh : ℕ)
    (hpe : ∀ m : MessageRequest, ∃ out, ClockJoin.ReadyRun pe.machine (Ke * ((messageWord m).length + 1) ^ ee)
      (pe.inputTapes (messageWord m)) out ∧ out pe.outputTape = FramedSim.pairs (List.ofFn (P.code.enc m.1 m.2.val)))
    (hph : ∀ a : AcceptedCircuitInput, ∃ out, ClockJoin.ReadyRun ph.machine
      (Kh * ((acceptedCircuitInputWord a).length + 1) ^ eh) (ph.inputTapes (acceptedCircuitInputWord a)) out ∧
      out ph.outputTape = FramedSim.pairs (List.ofFn (P.honest a))) (cd pl : ℕ) :
    PolyB (Inst.S (s := s) (g := g))
      (fun i => 2 * i.cost cx Ke ee Kh eh cd pl + 2) := by
  have hR := poly_R (s := s) (g := g)
  have hL := poly_L (s := s) (g := g) pe Ke ee hpe
  have hW := poly_Cw (s := s) (g := g) cx
  have hc := poly_cap (s := s) (g := g) cx pe ph Ke ee Kh eh hpe hph cd pl
  have hc2 := PolyB.pow (PolyB.add hc (PolyB.const 1)) 2
  have hT := PolyB.add (PolyB.mul (PolyB.const 2) (PolyB.add (PolyB.add (PolyB.mul (PolyB.const (200 * (cd + pl + 1)))
    hc2) (PolyB.const 10)) (PolyB.add (PolyB.add (PolyB.add (PolyB.add poly_cold (poly_cxFuel cx))
      (PolyB.mul (PolyB.const Ke) (PolyB.pow (PolyB.add (PolyB.mul (PolyB.const 4) hR) (PolyB.const 3)) ee)))
      (PolyB.mul (PolyB.const Kh) (PolyB.pow (PolyB.add (PolyB.add hW (PolyB.add hR hL)) (PolyB.const 1)) eh)))
      (PolyB.mul (PolyB.const 30000) hc2)))) (PolyB.const 2)
  refine hT.mono fun i => ?_
  have hb := bits_len_le_self i.R
  have p1 : (2 * i.R.bits.length + 2 * i.R + 3) ^ ee ≤ (4 * i.R + 3) ^ ee := Nat.pow_le_pow_left (by omega) _
  have p2 : ((i.C P).word.length + (i.C P).n + 1) ^ eh ≤
      ((i.C P).word.length + (P.output (i.C P)).word.length + (i.R + P.code.length i.R) + 1) ^ eh :=
    Nat.pow_le_pow_left (by have hCn : (i.C P).n = i.R + P.code.length i.R := C_n i; omega) _
  have q1 := Nat.mul_le_mul_left Ke p1
  have q2 := Nat.mul_le_mul_left Kh p2
  unfold Inst.cost mainBound
  change 2 * (200 * (cd + pl + 1) * (i.cap P cd pl + 1) ^ 2 + 10 + (CloseoutCaseTwo.Cold.budget i.B i.c +
    cxFuel cx i + Ke * (2 * i.R.bits.length + 2 * i.R + 3) ^ ee + Kh * ((i.C P).word.length + (i.C P).n + 1) ^ eh +
    30000 * (i.cap P cd pl + 1) ^ 2)) + 2 ≤ _
  omega

end Cost

/-! ## The tape relabelling -/

theorem sTape_val' {ns nr : ℕ} (i : Fin (ns + 1)) :
    (sTape (nr := nr) i).val = if i.val = 0 then 0 else i.val + 1 := rfl

def slotHT (T : ℕ) (hT : 6 ≤ T) (j : Fin T) : Fin T :=
  ⟨if j.val = 1 then 5 else if 2 ≤ j.val ∧ j.val ≤ 5 then j.val - 1 else j.val, by
    have := j.isLt; split_ifs <;> omega⟩

theorem slotHT_val (T : ℕ) (hT : 6 ≤ T) (j : Fin T) :
    (slotHT T hT j).val = if j.val = 1 then 5 else if 2 ≤ j.val ∧ j.val ≤ 5 then j.val - 1 else j.val := rfl

theorem slotHT_inj (T : ℕ) (hT : 6 ≤ T) : Function.Injective (slotHT T hT) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [slotHT_val, slotHT_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem coldBank_initHT (tK tE tH : ℕ) (h desc addr : List Bool) (Rv Bv : ℕ) (j : Fin (NS tK tE tH + 2 + 64)) :
    coldBank (initHT tK tE tH h desc addr Rv Bv) j =
      if hj : j.val = 0 then h else if hj2 : 2 ≤ j.val ∧ j.val ≤ 5 then
        fiveWords h desc addr Rv Bv ⟨j.val - 1, by omega⟩ else [] := by
  have hNS : 144 ≤ NS tK tE tH := by unfold NS; omega
  rcases NearCubicWires.WireExponent3_5.PrimAsm.DockW.tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [coldBank_s]
    have hst : (initHT tK tE tH h desc addr Rv Bv).st i =
        if hi : i.val < 5 then fiveWords h desc addr Rv Bv ⟨i.val, hi⟩ else [] := rfl
    rw [hst]
    have hv := sTape_val' (nr := 64) i
    by_cases h0 : i.val = 0
    · rw [if_pos h0] at hv
      rw [dif_pos (show i.val < 5 by omega), dif_pos (show (sTape (nr := 64) i).val = 0 from hv)]
      simp [fiveWords, h0]
    · rw [if_neg h0] at hv
      rw [dif_neg (show ¬ (sTape (nr := 64) i).val = 0 by omega)]
      by_cases h5 : i.val < 5
      · rw [dif_pos h5, dif_pos (show 2 ≤ (sTape (nr := 64) i).val ∧ (sTape (nr := 64) i).val ≤ 5 by omega)]
        congr 1; apply Fin.ext; simp only []; omega
      · rw [dif_neg h5, dif_neg (show ¬ (2 ≤ (sTape (nr := 64) i).val ∧ (sTape (nr := 64) i).val ≤ 5) by omega)]
  · rw [coldBank_c]
    have hc : (cTape (ns := NS tK tE tH) (nr := 64)).val = 1 := rfl
    rw [dif_neg (by omega), dif_neg (by omega)]
  · rw [coldBank_r]
    have : (rTape (ns := NS tK tE tH) (nr := 64) r).val = NS tK tE tH + 2 + r.val := rfl
    rw [dif_neg (by omega), dif_neg (by omega)]

theorem bank_slot (tK tE tH : ℕ) (h desc addr : List Bool) (Rv Bv : ℕ)
    (j : Fin (NS tK tE tH + 2 + 64 + 1)) :
    portInput (NS tK tE tH + 2 + 64 + 1) h desc addr Rv Bv (slotHT _ (by unfold NS; omega) j) =
      Fin.addCases (coldBank (initHT tK tE tH h desc addr Rv Bv)) (fun _ => []) j := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.addCases_left, coldBank_initHT]
    unfold portInput
    have hs := slotHT_val (NS tK tE tH + 2 + 64 + 1) (by unfold NS; omega) (Fin.castAdd 1 j)
    simp only [Fin.val_castAdd] at hs
    by_cases h0 : j.val = 0
    · rw [dif_pos (by rw [hs]; simp [h0]), dif_pos h0]
      simp only [hs, h0]; rfl
    · by_cases h1 : j.val = 1
      · rw [dif_neg (by rw [hs]; simp [h1]), dif_neg h0, dif_neg (by omega)]
      · by_cases h25 : 2 ≤ j.val ∧ j.val ≤ 5
        · rw [dif_pos (by rw [hs]; simp [h1, h25]; omega), dif_neg h0, dif_pos h25]
          congr 1; apply Fin.ext; simp only [hs, h1, h25]; simp
        · rw [dif_neg (by rw [hs]; simp [h1, h25]; omega), dif_neg h0, dif_neg h25]
  · rw [Fin.addCases_right]
    unfold portInput
    have hs := slotHT_val (NS tK tE tH + 2 + 64 + 1) (by unfold NS; omega) (Fin.natAdd (NS tK tE tH + 2 + 64) j)
    simp only [Fin.val_natAdd] at hs
    rw [dif_neg (by rw [hs]; have := j.isLt; unfold NS; split_ifs <;> omega)]

end NearCubicGates.Close.Recovery.HT

namespace NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5 NearCubicWires.ExtDecompositionBatch
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicGates.Close NearCubicGates.Close.Gadget
open NearCubicGates.PublishedSources.PCPP NearCubicWires.Bindings.CLW20Lemma311

theorem hardTableRuns_of_compFull (hcomp : ∀ (s : GateSources) (P : ThreeQueryPCPP) (g : Transfer.GateParams),
    Nonempty (Setup.CompFull s P g)) : HardTableRuns := by
  intro s P g
  obtain ⟨cx⟩ := hcomp s P g
  obtain ⟨pe, Ke, ee, hpe⟩ := encFramed_ready P
  obtain ⟨ph, Kh, eh, hph⟩ := honestFramed_ready P
  obtain ⟨C, E, hCE⟩ := HT.poly_cost (s := s) (g := g) cx pe ph Ke ee Kh eh hpe hph g.clauseDegree g.positionLog
  have hT6 : 6 ≤ HT.NS cx.t pe.tapeCount ph.tapeCount + 2 + 64 + 1 := by unfold HT.NS; omega
  refine ⟨HT.NS cx.t pe.tapeCount ph.tapeCount + 2 + 64 + 1, _,
    RecoveryFocus.machine (HT.slotHT _ hT6) (Rewind.machine (HT.htW cx pe ph g.clauseDegree g.positionLog).compile),
    ⟨10, by unfold HT.NS; omega⟩, by simp, max 2 (2 ^ (g.sv s).onset), C, E, ?_⟩
  intro n point ν z hν hcut h
  have hcut2 : 2 ≤ 2 ^ ν := (le_max_left _ _).trans hcut
  have hon : (g.sv s).onset ≤ ν :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp ((le_max_right _ _).trans hcut)
  let i : HT.Inst s g := ⟨n, ν, z, hν, hcut2, hon, h⟩
  obtain ⟨τ, n', e, hn', hout⟩ := HT.ht_exec cx pe ph Ke ee Kh eh hpe hph g.clauseDegree g.positionLog
    (i.cap P g.clauseDegree g.positionLog) ν z h i.two_le n point (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  obtain ⟨out, hrun, hst⟩ := WXExec.readyRewound e (fun _ => rfl) (fun _ => rfl) rfl
  have hf := ClockJoin.ReadyRun.focus hrun (HT.slotHT _ hT6) (HT.slotHT_inj _ hT6) _
    (HT.bank_slot cx.t pe.tapeCount ph.tapeCount _ _ _ _ _)
  refine ⟨_, ClockJoin.enlarge _ _ _ _ _ hf ?_, ?_⟩
  · have h1 := hCE i
    have h2 : n' ≤ i.cost cx Ke ee Kh eh g.clauseDegree g.positionLog := hn'
    change 2 * i.cost cx Ke ee Kh eh g.clauseDegree g.positionLog + 2 ≤ C * (2 ^ n + 1) ^ E at h1
    omega
  · have hslot : (⟨10, by unfold HT.NS; omega⟩ : Fin (HT.NS cx.t pe.tapeCount ph.tapeCount + 2 + 64 + 1)) =
        HT.slotHT _ hT6 ((sTape (nr := 64) (HT.OUT cx.t pe.tapeCount ph.tapeCount)).castAdd 1) := by
      apply Fin.ext
      rw [HT.slotHT_val]
      simp [HT.sTape_val']
    rw [hslot, RecoveryRootRound.install_slot _ (HT.slotHT_inj _ hT6), hst, hout,
      show CloseoutLanguage.clauseWidth g.clauseDegree (g.width s ν) =
        ((Outer.width s.mw (g.sv s) (2 ^ ν) + 2) ^ g.clauseDegree - 1).size from
        TableSem.clog_eq_size _]

theorem hardTableRuns_of_compU (hcomp : ∀ (s : GateSources) (P : ThreeQueryPCPP), Setup.CompU s P) :
    HardTableRuns :=
  hardTableRuns_of_compFull fun s P g => by
    obtain ⟨_, hE⟩ := hcomp s P
    obtain ⟨cf, -⟩ := hE g
    exact ⟨cf⟩

end NearCubicGates.Close.Recovery
