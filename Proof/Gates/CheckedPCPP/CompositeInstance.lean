import Proof.Gates.CheckedPCPP.CompRunRaw
import Proof.Gates.CheckedPCPP.CostClass
import Proof.Gates.CheckedPCPP.WMXReady
import Proof.Gates.Succinct.SubstitutionSpec

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP.Comp.SubstFront

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicWires.Bindings.MW20

noncomputable section

/-! ## The donors -/

structure Objs (P : ThreeQueryPCPP) where
  t2 : ℕ
  s2 : ℕ
  M2 : Machine t2 s2
  iW : Fin t2
  iD : Fin t2
  o2 : Fin t2
  C2 : ℕ
  e2 : ℕ
  nd2 : [iW, iD, o2].Nodup
  h2 : ∀ (oc : OracleOutput) {q : ℕ} (B : BooleanCircuit q), ∃ out,
    ClockJoin.ReadyRun M2 (C2 * (oc.word.length + (PCPPNative.descriptor B).length + q + 1) ^ e2)
      (portBank t2 iW iD oc.word (PCPPNative.descriptor B)) out ∧
    out o2 = RepairOrdinary.frame (PCPPNative.descriptor (Outer.substCircuit oc.circuit B).padToArity)
  K : ℕ
  e : ℕ
  wf : WordFunction MessageRequest messageWord (fun m => FramedSim.pairs (List.ofFn (P.code.enc m.1 m.2.val)))
    (fun m => K * (m.1 + 1) ^ e)
  Kc : ℕ
  hKc : ∀ n, 2 ≤ n → P.code.length n ≤ Kc * (n + 1)
  p5 : Program
  PolyTab : ℕ
  e5 : ℕ
  h5 : ∀ C : Circuit, ∃ out, ClockJoin.ReadyRun p5.machine (PolyTab * (C.word.length + 1) ^ e5) (p5.inputTapes C.word) out ∧
    out p5.outputTape = (P.output C).word

theorem objs_exist (hH : Succinct.SubstMachine.SubstReadySpec) (P : ThreeQueryPCPP) : Nonempty (Objs P) := by
  obtain ⟨t2, s2, M2, iW, iD, o2, C2, e2, nd, h2⟩ := hH
  obtain ⟨K, e, ⟨wf⟩⟩ := EncSetup.encWord P
  obtain ⟨Kc, hKc⟩ := P.codeLength
  obtain ⟨p5, PolyTab, e5, h5⟩ := pcppWord_ready P
  refine ⟨⟨t2, s2, M2, iW, iD, o2, C2, e2, nd, fun oc q B => ?_, K, e, wf, Kc, hKc, p5, PolyTab, e5, h5⟩⟩
  obtain ⟨out, hr, ho, -, -⟩ := h2 oc B
  exact ⟨out, hr, ho⟩

/-! ## The machine -/

variable {P : ThreeQueryPCPP} (o : Objs P)

def in4 : Fin CloseoutCaseTwo.RequestInput.tapes := ⟨0, by
  have := CloseoutCaseTwo.RequestInput.outputSlot.isLt; omega⟩
def in5 : Fin o.p5.tapeCount := ⟨0, by have := o.p5.twoTapes; omega⟩
def Cb : ℕ := o.K + 2 * o.Kc + 20
def eb : ℕ := o.e + 1

def prog := compW2 (iW := o.iW) (iD := o.iD) (M2 := o.M2) (out2 := o.o2) (E := P.code) (wf := o.wf) (Cb := Cb o)
  (eb := eb o) (M4 := CloseoutCaseTwo.RequestInput.machine) (in4 := in4) (out4 := CloseoutCaseTwo.RequestInput.outputSlot)
  (M5 := o.p5.machine) (in5 := in5 o) (out5 := o.p5.outputTape)

theorem out4_ne : in4 ≠ CloseoutCaseTwo.RequestInput.outputSlot := by
  intro e; have := congrArg Fin.val e; simp [in4] at this
  exact absurd this.symm (by decide)

theorem out5_ne : in5 o ≠ o.p5.outputTape := by
  intro e; have := congrArg Fin.val e; simp [in5] at this; exact o.p5.outputFresh this.symm

/-! ## One instance -/

/-- **An instance of the composite**: an oracle-circuit word (the import's output), a width `q ≥ 2` and `B_pf` on `q`
inputs. -/
structure Inst where
  oc : OracleOutput
  q : ℕ
  B : BooleanCircuit q
  hq : 2 ≤ q

section Inst
variable (i : Inst)

/-- `D_B = ¬C^{O_{B_pf}}` on `q` inputs, size-padded (definitionally `Outer.Dat` at `oc = outC … B_src`). -/
def Dx : Circuit := ⟨i.q, (Outer.substCircuit i.oc.circuit i.B).padToArity, BooleanCircuit.arity_le_padToArity_size _⟩
def wx : List Bool := PCPPNative.descriptor (Dx i).D
def qx : ℕ := (Dx i).n
def Lx : ℕ := P.code.length (qx i)
def Vx : ℕ := (wx i).length + Lx (P := P) i * (5 * qx i + 8) + qx i + Lx (P := P) i + 8
def Cx : Circuit := checkedCircuit P.code (Dx i)
def hx : List Bool := i.oc.word
def dx : List Bool := PCPPNative.descriptor i.B
def f2x : ℕ := o.C2 * ((hx i).length + (dx i).length + qx i + 1) ^ o.e2
def f4x : ℕ := CloseoutCaseTwo.RequestInput.budget (Cx (P := P) i).D
def f5x : ℕ := o.PolyTab * ((Cx (P := P) i).word.length + 1) ^ o.e5
def pbx : List Bool := (P.output (Cx (P := P) i)).proofBits.bits
def rbx : List Bool := (P.output (Cx (P := P) i)).randomBits.bits

/-- The composite's cost on one instance. -/
def costOf : ℕ :=
  costA (Cb o) (eb o) 0 0 (f2x o i) (wx i).length (qx i) (Lx (P := P) i) (Cb o * (qx i + 1) ^ eb o)
    o.wf.program.tapeCount + 1 +
  (costB (qx i) (Lx (P := P) i) (Vx (P := P) i) (f4x (P := P) i) (Cx (P := P) i).word.length (f5x o i)
    (pbx (P := P) i).length (rbx (P := P) i).length + 1 + costC (qx i) (Lx (P := P) i))

/-- A capacity large enough for every register of the instance. -/
def capx : ℕ :=
  10000 * ((hx i).length + (dx i).length + (wx i).length + Cb o * (qx i + 1) ^ eb o + qx i +
    Lx (P := P) i + Vx (P := P) i + (Cx (P := P) i).word.length + (P.output (Cx (P := P) i)).word.length + 1) ^ 3

theorem wx_eq : wx i = natWord (qx i) ++ (natWord (Dx i).D.nodes.length ++
    (Dx i).D.nodes.flatMap PCPPRequestNodeSchema.native ++ natWord (Dx i).D.output.val) := by
  unfold wx qx; rw [PCPPNative.descriptor_eq]; simp only [List.append_assoc]

theorem q_le_w : qx i ≤ (wx i).length :=
  (Dx i).sizeAtLeast.trans (SubstitutedPoly.size_le_desc _)

theorem hq_x : 2 ≤ qx i := i.hq

theorem descH16' : descH 16 = encR 9 := by decide

/-- Phases A and B on one instance. -/
theorem inst_AB :
    ∃ τA τB nA nB, WXExec (capx o i) (phaseA2 o.iW o.iD CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount o.M2 o.o2
        P.code o.wf (Cb o) (eb o))
        (init o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount (hx i) (dx i)) τA nA ∧
      WXExec (capx o i) (phaseB (t2 := o.t2) P.code o.wf CloseoutCaseTwo.RequestInput.machine in4
          CloseoutCaseTwo.RequestInput.outputSlot o.p5.machine (in5 o) o.p5.outputTape) τA τB nB ∧
      nA = costA (Cb o) (eb o) 0 0 (f2x o i) (wx i).length (qx i) (Lx (P := P) i) (Cb o * (qx i + 1) ^ eb o)
        o.wf.program.tapeCount ∧
      nB = costB (qx i) (Lx (P := P) i) (Vx (P := P) i) (f4x (P := P) i) (Cx (P := P) i).word.length
          (f5x o i) (pbx (P := P) i).length (rbx (P := P) i).length ∧
      τB.st (b4 o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount
        CloseoutCaseTwo.RequestInput.outputSlot) = RepairOrdinary.frame (Cx (P := P) i).word ∧
      τB.st (b5 o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount
        o.p5.outputTape) = (P.output (Cx (P := P) i)).word ∧
      τB.st (PO o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount) =
        RepairOrdinary.frame (pbx (P := P) i) ∧
      τB.st (RO o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount) =
        RepairOrdinary.frame (rbx (P := P) i) ∧
      (∀ p, readTapeBit (τB.st (MAT o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes
        o.p5.tapeCount)) p = matBit P.code (qx i) p) ∧
      τB.sh (MAT o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount) =
        P.code.length (qx i) * qx i ∧
      τB.val (descH 9) = qx i ∧ τB.val (descH 16) = P.code.length (qx i) ∧
      τB.st (SUP o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount) = [] ∧
      τB.sh (SUP o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount) = 0 ∧
      (∀ j, τB.val (supG j) = 0) ∧ τB.val rP2 = 0 ∧ τB.val rA2 = 0 ∧ τB.val rT = 0 := by
  have hq := hq_x i
  -- the size W and the capacity
  set W := (hx i).length + (dx i).length + (wx i).length + Cb o * (qx i + 1) ^ eb o + qx i + Lx (P := P) i +
    Vx (P := P) i + (Cx (P := P) i).word.length + (P.output (Cx (P := P) i)).word.length with hWdef
  have hcapW : capx o i = 10000 * (W + 1) ^ 3 := rfl
  have hW3 : (W + 1) * (W + 1) ≤ (W + 1) ^ 3 := by
    rw [pow_succ, sq]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hW2 : W * W ≤ (W + 1) ^ 3 := le_trans (Nat.mul_le_mul (by omega) (by omega)) hW3
  have hW1 : W + 1 ≤ (W + 1) ^ 3 := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hW3

  obtain ⟨o2, h2run, h2out⟩ := o.h2 i.oc i.B
  have h2run' : ClockJoin.ReadyRun o.M2 (f2x o i) (portBank o.t2 o.iW o.iD (hx i) (dx i)) o2 := h2run
  have hw : o2 o.o2 = RepairOrdinary.frame (natWord (qx i) ++
      (natWord (Dx i).D.nodes.length ++ (Dx i).D.nodes.flatMap PCPPRequestNodeSchema.native ++
        natWord (Dx i).D.output.val)) := by
    rw [← wx_eq]; exact h2out
  have hqw : qx i ≤ (natWord (qx i) ++ (natWord (Dx i).D.nodes.length ++
      (Dx i).D.nodes.flatMap PCPPRequestNodeSchema.native ++ natWord (Dx i).D.output.val)).length := by
    rw [← wx_eq]; exact q_le_w i
  have hbnd := EncSetup.bound_ok P.code o.K o.e o.Kc o.hKc (qx i) hq
  have hBv : EncSetup.bound o.K o.e o.Kc (qx i) = Cb o * (qx i + 1) ^ eb o := rfl
  obtain ⟨τA, eA, hA_DD, hA_DDh, hA_mat, hA_math, hA_L, hA_F⟩ := runA2 o.M2 o.iW o.iD o.o2 P.code o.wf
    CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount (Cb o) (eb o) o.nd2 (hx i) (dx i) (f2x o i) o2 h2run'
    (qx i) _ hw hq hqw (fun j _ => by rw [← hBv]; exact (hbnd j hq).1) (by rw [← hBv]; exact (hbnd 0 hq).2)
    (capx o i) (by
      rw [hcapW]
      have e3 : (natWord (qx i) ++ (natWord (Dx i).D.nodes.length ++
          (Dx i).D.nodes.flatMap PCPPRequestNodeSchema.native ++ natWord (Dx i).D.output.val)).length ≤ W := by
        rw [← wx_eq]; omega
      have e4 : Cb o * (qx i + 1) ^ eb o ≤ W := by omega
      have e5 : qx i ≤ W := by omega
      have e6 : P.code.length (qx i) ≤ W := (show Lx (P := P) i ≤ W by omega)
      have e7 := Nat.mul_le_mul e4 e4
      have e8 := Nat.mul_le_mul (show P.code.length (qx i) + 1 ≤ W + 1 by omega) e5
      nlinarith)

  obtain ⟨o4, h4run, h4out⟩ := word_run (Cx (P := P) i)
  obtain ⟨o5, h5run, h5out⟩ := o.h5 (Cx (P := P) i)
  have hpb : (P.output (Cx (P := P) i)).word = RepairOrdinary.frame (pbx (P := P) i) ++
      RepairOrdinary.frame (rbx (P := P) i) ++ (List.ofFn fun coins : Fin (2 ^ (P.output (Cx (P := P) i)).randomBits) =>
        (List.ofFn fun j : Fin 3 => RepairOrdinary.frame (RepairSource.literalCode
          ((P.output (Cx (P := P) i)).clause coins j)).bits).flatten).flatten := rfl
  have hpbl : (pbx (P := P) i).length + (rbx (P := P) i).length ≤ (P.output (Cx (P := P) i)).word.length := by
    rw [hpb]; simp only [List.length_append, SubstitutedPoly.frame_len']; omega
  have hVle : (PCPPNative.descriptor (Dx i).D).length + P.code.length (Dx i).n * (5 * (Dx i).n + 8) +
      (Dx i).n + P.code.length (Dx i).n + 8 ≤ Vx (P := P) i := le_rfl
  obtain ⟨τB, eB, hB_CW, hB_WO, hB_PO, hB_RO, hB_MAT, hB_math, hB_9, hB_16, hB_SUP, hB_SUPh, hB_sg, hB_P2, hB_A2,
      hB_T⟩ := runB (t2 := o.t2) P.code o.wf CloseoutCaseTwo.RequestInput.machine in4
    CloseoutCaseTwo.RequestInput.outputSlot o.p5.machine (in5 o) o.p5.outputTape rfl out4_ne rfl (out5_ne o) (Dx i)
    (Vx (P := P) i) hVle (capx o i)
    (by rw [hcapW]; have : Vx (P := P) i ≤ W := by omega
        nlinarith)
    (f4x (P := P) i) o4 h4run (Cx (P := P) i).word h4out (by rw [hcapW]; omega) (f5x o i) o5 h5run
    (pbx (P := P) i) (rbx (P := P) i) _ (h5out.trans hpb) (by rw [hcapW]; omega) τA
    (hA_DD.trans (congrArg RepairOrdinary.frame (wx_eq i).symm)) hA_DDh hA_mat hA_math
    (by rw [descH16']; exact hA_L) hA_F
  refine ⟨τA, τB, _, _, eA, eB, ?_, rfl, hB_CW, hB_WO.trans h5out, hB_PO, hB_RO, fun p => hB_MAT ▸ hA_mat p,
    hB_math, hB_9, hB_16, hB_SUP, hB_SUPh, hB_sg, hB_P2, hB_A2, hB_T⟩
  rw [wx_eq]; rfl

/-- **One instance of the composite.** -/
theorem inst_run :
    ∃ τ, WXExec (capx o i) (prog o) (init o.t2 o.wf.program.tapeCount
        CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount (hx i) (dx i)) τ (costOf o i) ∧
      τ.st (b4 o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount
        CloseoutCaseTwo.RequestInput.outputSlot) = RepairOrdinary.frame (Cx (P := P) i).word ∧
      τ.st (b5 o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount
        o.p5.outputTape) = (P.output (Cx (P := P) i)).word ∧
      τ.st (SUP o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount) =
        RepairOrdinary.frame (CheckedPCPP.supportsWord P.code (qx i)) ∧
      τ.st (PO o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount) =
        RepairOrdinary.frame (pbx (P := P) i) ∧
      τ.st (RO o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount) =
        RepairOrdinary.frame (rbx (P := P) i) := by
  obtain ⟨τA, τB, nA, nB, eA, eB, hnA, hnB, hB_CW, hB_WO, hB_PO, hB_RO, hB_mat, hB_math, hB_9, hB_16, hB_SUP, hB_SUPh,
    hB_sg, hB_P2, hB_A2, hB_T⟩ := inst_AB o i
  set W := (hx i).length + (dx i).length + (wx i).length + Cb o * (qx i + 1) ^ eb o + qx i + Lx (P := P) i +
    Vx (P := P) i + (Cx (P := P) i).word.length + (P.output (Cx (P := P) i)).word.length with hWdef
  have hcapW : capx o i = 10000 * (W + 1) ^ 3 := rfl
  -- the supports
  obtain ⟨τC, eC, hC_SUP, hC_fr⟩ := runC (t2 := o.t2) P.code o.wf CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount
    (qx i) (capx o i)
    (by
      rw [hcapW]
      have e5 : qx i ≤ W := by omega
      have e6 : P.code.length (qx i) ≤ W := (show Lx (P := P) i ≤ W by omega)
      have e7 : P.code.length (qx i) * ((qx i + 1) * (2 * qx i + 3)) ≤ W * ((W + 1) * (2 * W + 3)) :=
        Nat.mul_le_mul e6 (Nat.mul_le_mul (by omega) (by omega))
      have e8 : qx i * (2 * qx i + 3) ≤ W * (2 * W + 3) := Nat.mul_le_mul e5 (by omega)
      have e9 : qx i * P.code.length (qx i) ≤ W * W := Nat.mul_le_mul e5 e6
      have e10 : W * ((W + 1) * (2 * W + 3)) ≤ 3 * (W + 1) ^ 3 := by
        have : (W + 1) ^ 3 = (W + 1) * ((W + 1) * (W + 1)) := by ring
        rw [this]; nlinarith
      nlinarith)
    τB hB_mat hB_math hB_9 hB_16 hB_SUP hB_SUPh hB_sg hB_P2 hB_A2 hB_T
  refine ⟨τC, WXExec.mono (WXExec.seq eA (WXExec.seq eB eC)) (le_of_eq ?_), ?_, ?_, hC_SUP, ?_, ?_⟩
  · unfold costOf; rw [hnA, hnB]; rfl
  · rw [hC_fr (b4 o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount
      CloseoutCaseTwo.RequestInput.outputSlot) (by dst) (by dst)]; exact hB_CW
  · rw [hC_fr (b5 o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount o.p5.outputTape)
      (by dst) (by dst)]; exact hB_WO
  · rw [hC_fr (PO o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount) (by dst)
      (by dst)]; exact hB_PO
  · rw [hC_fr (RO o.t2 o.wf.program.tapeCount CloseoutCaseTwo.RequestInput.tapes o.p5.tapeCount) (by dst)
      (by dst)]; exact hB_RO

end Inst

/-! ## The cost class -/

/-- The input size `|word| + |descriptor B_pf| + q`. -/
def Sz (i : Inst) : ℕ := (hx i).length + (dx i).length + qx i

theorem checked_size_le (i : Inst) :
    (Cx (P := P) i).D.size ≤ (wx i).length + Lx (P := P) i * (5 * qx i + 8) := by
  have h1 : (Cx (P := P) i).D.size = (Dx i).D.nodes.length +
      (checksNodes P.code (Dx i).n (Dx i).D.nodes.length (List.finRange (P.code.length (Dx i).n))
        (Dx i).D.output.val).1.length :=
    (congrArg List.length (checkedCircuit_pad P.code (Dx i))).trans (checkedRaw_length P.code (Dx i))
  have h2 := ChecksW.checksNodes_length_le P.code (Dx i).n (Dx i).D.nodes.length
    (List.finRange (P.code.length (Dx i).n)) (Dx i).D.output.val
  have h3 : (Dx i).D.nodes.length ≤ (wx i).length := SubstitutedPoly.size_le_desc _
  rw [List.length_finRange] at h2
  unfold Lx qx; omega

open PolyB in

theorem cost_poly : PolyB Sz (fun i => costOf o i) := by
  -- atoms
  have pS : PolyB Sz (fun i => Sz i) := size
  have pf2 : PolyB Sz (fun i => f2x o i) :=
    (mul (const o.C2) (pow (add pS (const 1)) o.e2)).mono (fun i => le_of_eq rfl)
  have pwl : PolyB Sz (fun i => (wx i).length) := by
    refine (add (add pS (const 1)) pf2).mono (fun i => ?_)
    obtain ⟨o2, h2run, h2out⟩ := o.h2 i.oc i.B
    have hl := Dock.ready_len h2run ((hx i).length + (dx i).length) (fun j => by
      unfold portBank; split_ifs <;> simp [hx, dx])
    have := hl o.o2
    rw [h2out, SubstitutedPoly.frame_len'] at this
    have hwx : (wx i).length = (PCPPNative.descriptor (Outer.substCircuit i.oc.circuit i.B).padToArity).length := rfl
    have hf2 : f2x o i = o.C2 * (i.oc.word.length + (PCPPNative.descriptor i.B).length + i.q + 1) ^ o.e2 := rfl
    rw [hwx, hf2]
    unfold Sz
    omega
  have pq : PolyB Sz (fun i => qx i) := pS.mono (fun i => by unfold Sz; omega)
  have pL : PolyB Sz (fun i => Lx (P := P) i) :=
    (mul (const o.Kc) (add pq (const 1))).mono (fun i => o.hKc _ (hq_x i))
  have pB : PolyB Sz (fun i => Cb o * (qx i + 1) ^ eb o) :=
    mul (const _) (pow (add pq (const 1)) _)
  have pV : PolyB Sz (fun i => Vx (P := P) i) :=
    (add (add (add (add pwl (mul pL (add (mul (const 5) pq) (const 8)))) pq) pL) (const 8)).mono
      (fun i => le_of_eq rfl)
  have psz : PolyB Sz (fun i => (Cx (P := P) i).D.size) :=
    pV.mono (fun i => by have := checked_size_le (P := P) i; unfold Vx; omega)
  have pn : PolyB Sz (fun i => (Cx (P := P) i).n) :=
    (add pq pL).mono (fun _ => le_of_eq rfl)
  have pf4 : PolyB Sz (fun i => f4x (P := P) i) := by
    refine (add (mul (const 2) (mul (const (PCPPRequestRuntime.inputCoefficient * 39 ^ 156))
      (pow (add (add pn psz) (const 5)) 312))) (const 2)).mono (fun i => ?_)
    have := PCPPRequestRuntime.input_source_bound (Cx (P := P) i).D
    unfold PCPPRequestRuntime.sourceParameter at this
    show 2 * PCPPRequestInput.budget (Cx (P := P) i).D + 2 ≤ _
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 this) 2
  have pdesc : PolyB Sz (fun i => (PCPPNative.descriptor (Cx (P := P) i).D).length) := by
    refine (add (add (add (mul (add psz (const 1)) (add (mul (const 6) (add (add psz pn) (const 4))) (const 9)))
      (mul (const 2) pn)) (mul (const 4) psz)) (const 9)).mono (fun i => ?_)
    exact desc_len_le (Cx (P := P) i).D
  have pcw : PolyB Sz (fun i => (Cx (P := P) i).word.length) := by
    refine (add (add (mul (const 2) pdesc) (const 2)) pf4).mono (fun i => ?_)
    obtain ⟨o4, h4run, h4out⟩ := word_run (Cx (P := P) i)
    have hl := Dock.ready_len h4run (2 * (PCPPNative.descriptor (Cx (P := P) i).D).length + 1)
      (fun j => by
        show (SourceHandoff.sourceTapes (RepairOrdinary.frame _) j).length ≤ _
        unfold SourceHandoff.sourceTapes; split
        · simp only [SubstitutedPoly.frame_len']; omega
        · simp)
    have := hl CloseoutCaseTwo.RequestInput.outputSlot
    rw [h4out, SubstitutedPoly.frame_len'] at this
    unfold f4x; omega
  have pf5 : PolyB Sz (fun i => f5x o i) :=
    mul (const _) (pow (add pcw (const 1)) _)
  have praw : PolyB Sz (fun i => (P.output (Cx (P := P) i)).word.length) := by
    refine (add (add (mul (const 2) pcw) (const 1)) pf5).mono (fun i => ?_)
    obtain ⟨o5, h5run, h5out⟩ := o.h5 (Cx (P := P) i)
    have hl := Dock.ready_len h5run (2 * (Cx (P := P) i).word.length + 1)
      (fun j => by
        unfold Program.inputTapes; split
        · simp only [SubstitutedPoly.frame_len']; omega
        · simp)
    have := hl o.p5.outputTape
    rw [h5out] at this
    unfold f5x; omega
  have ppb : PolyB Sz (fun i => (pbx (P := P) i).length) := by
    refine praw.mono (fun i => ?_)
    show _ ≤ (RepairOrdinary.frame _ ++ RepairOrdinary.frame _ ++ _).length
    simp only [List.length_append, SubstitutedPoly.frame_len']; unfold pbx; omega
  have prb : PolyB Sz (fun i => (rbx (P := P) i).length) := by
    refine praw.mono (fun i => ?_)
    show _ ≤ (RepairOrdinary.frame _ ++ RepairOrdinary.frame _ ++ _).length
    simp only [List.length_append, SubstitutedPoly.frame_len']; unfold rbx; omega
  have pA := CostClass.costA_pb (Cb o) (eb o) o.wf.program.tapeCount (const 0) (const 0) pf2 pwl pq pL pB
  have pBc := CostClass.costB_pb pq pL pV pf4 pcw pf5 ppb prb
  have pC := CostClass.costC_pb pq pL
  exact (add (add (add pA (const 1)) (add (add pBc (const 1)) pC)) (const 0)).mono (fun i => by unfold costOf; omega)

/-! ## The port bank -/

theorem sTape_v {ns nr : ℕ} (i : Fin (ns + 1)) : (sTape (nr := nr) i).val = if i.val = 0 then 0 else i.val + 1 := rfl

theorem bank_eq' (T2 te t4 t5 : ℕ) (h d : List Bool) :
    Fin.addCases (m := NS T2 te t4 t5 + 2 + 64) (n := 1) (motive := fun _ => List Bool)
      (coldBank (init T2 te t4 t5 h d)) (fun _ => []) =
    portBank (NS T2 te t4 t5 + 2 + 64 + 1) ((sTape (nr := 64) (HS T2 te t4 t5)).castAdd 1)
      ((sTape (nr := 64) (DS T2 te t4 t5)).castAdd 1) h d := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.addCases_left]
    rcases NearCubicWires.WireExponent3_5.PrimAsm.DockW.tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
    · rw [coldBank_s]
      unfold portBank
      have e1 : (Fin.castAdd 1 (sTape (nr := 64) i) = Fin.castAdd 1 (sTape (nr := 64) (HS T2 te t4 t5))) ↔
          i = HS T2 te t4 t5 := by
        constructor
        · intro e
          have hv := congrArg Fin.val e
          simp only [Fin.val_castAdd, sTape_v, HS_val] at hv
          apply Fin.ext; simp only [HS_val]
          by_cases hi : (i : ℕ) = 0
          · exact hi
          · rw [if_neg hi] at hv; simp at hv
        · intro e; rw [e]
      have e2 : (Fin.castAdd 1 (sTape (nr := 64) i) = Fin.castAdd 1 (sTape (nr := 64) (DS T2 te t4 t5))) ↔
          i = DS T2 te t4 t5 := by
        constructor
        · intro e
          have hv := congrArg Fin.val e
          simp only [Fin.val_castAdd, sTape_v, DS_val] at hv
          apply Fin.ext; simp only [DS_val]
          by_cases hi : (i : ℕ) = 0
          · rw [if_pos hi] at hv; simp at hv
          · rw [if_neg hi] at hv; simp at hv; omega
        · intro e; rw [e]
      simp only [init, e1, e2]
    · rw [coldBank_c]
      unfold portBank
      have e1 : Fin.castAdd 1 (cTape (ns := NS T2 te t4 t5) (nr := 64)) ≠
          Fin.castAdd 1 (sTape (nr := 64) (HS T2 te t4 t5)) := by
        intro e; have := congrArg Fin.val e; simp [cTape, sTape_v] at this
      have e2 : Fin.castAdd 1 (cTape (ns := NS T2 te t4 t5) (nr := 64)) ≠
          Fin.castAdd 1 (sTape (nr := 64) (DS T2 te t4 t5)) := by
        intro e; have := congrArg Fin.val e; simp [cTape, sTape_v] at this
      simp [e1, e2]
    · rw [coldBank_r]
      unfold portBank
      have e1 : Fin.castAdd 1 (rTape (ns := NS T2 te t4 t5) r) ≠ Fin.castAdd 1 (sTape (nr := 64) (HS T2 te t4 t5)) := by
        intro e; have := congrArg Fin.val e; simp [rTape, sTape_v] at this
      have e2 : Fin.castAdd 1 (rTape (ns := NS T2 te t4 t5) r) ≠ Fin.castAdd 1 (sTape (nr := 64) (DS T2 te t4 t5)) := by
        intro e; have := congrArg Fin.val e; simp [rTape, sTape_v, NS] at this; omega
      simp [e1, e2]
  · rw [Fin.addCases_right]
    unfold portBank
    have e1 : Fin.natAdd (NS T2 te t4 t5 + 2 + 64) j ≠ Fin.castAdd 1 (sTape (nr := 64) (HS T2 te t4 t5)) := by
      intro e; have := congrArg Fin.val e; have := (sTape (nr := 64) (HS T2 te t4 t5)).isLt
      simp at *; omega
    have e2 : Fin.natAdd (NS T2 te t4 t5 + 2 + 64) j ≠ Fin.castAdd 1 (sTape (nr := 64) (DS T2 te t4 t5)) := by
      intro e; have := congrArg Fin.val e; have := (sTape (nr := 64) (DS T2 te t4 t5)).isLt
      simp at *; omega
    simp [e1, e2]

end

end NearCubicGates.Close.CheckedPCPP.Comp.SubstFront
