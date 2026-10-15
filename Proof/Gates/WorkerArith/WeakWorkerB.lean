import Proof.Gates.WorkerArith.WeakWorkerA
import Proof.Gates.CheckedPCPP.Harness

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.WorkerArith.WeakWorker

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Setup NearCubicGates.Close.TermLoop
open NearCubicGates.Close.Worker (width pcpp gadgets)

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)

theorem named_vals : (sX D).val = 0 ∧ (sBW D).val = 1 ∧ (sWT D).val = 2 ∧ (sCW D).val = 3 ∧ (sVI D).val = 4 ∧
    (sJ D).val = 16 + D.tA + D.cf.wOut.val ∧ (sSUP D).val = 16 + D.tA + D.cf.sOut.val ∧
    (sFL D).val = 16 + D.flag.val :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem named_ne (i : Fin (nsW D + 1))
    (hi : (5 ≤ i.val ∧ i.val < 16) ∨ 16 + D.tA + D.cf.t ≤ i.val) :
    i ≠ sX D ∧ i ≠ sBW D ∧ i ≠ sWT D ∧ i ≠ sCW D ∧ i ≠ sVI D ∧ i ≠ sJ D ∧ i ≠ sSUP D ∧ i ≠ sFL D := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := named_vals D
  have w1 := D.cf.wOut.isLt
  have w2 := D.cf.sOut.isLt
  have w3 : D.flag.val < D.tA := D.flag.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> have := congrArg Fin.val e
  · rw [v1] at this; omega
  · rw [v2] at this; omega
  · rw [v3] at this; omega
  · rw [v4] at this; omega
  · rw [v5] at this; omega
  · rw [v6] at this; omega
  · rw [v7] at this; omega
  · rw [v8] at this; omega

/-- The blank streams of `LoopEntry`. -/
theorem entry_blank {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
    (jk : Fin (nsW D + 1) → List Bool) (i : Fin (nsW D + 1))
    (hi : (5 ≤ i.val ∧ i.val < 16) ∨ 16 + D.tA + D.cf.t ≤ i.val) :
    (LoopEntry D N x bits pad B jk).st i = [] ∧ (LoopEntry D N x bits pad B jk).sh i = 0 := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := named_ne D i hi
  constructor
  · simp only [LoopEntry]
    rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6, if_neg n7, if_neg n8,
      if_pos (by rcases hi with ⟨_, h⟩ | h; exact Or.inl h; exact Or.inr h)]
  · simp only [LoopEntry]
    rw [if_neg n3, if_neg n5]

/-- The blank streams of `LoopExit`. -/
theorem exit_blank {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ)
    (B : Outer.OuterGuess (width s g N)) (jk : Fin (nsW D + 1) → List Bool) (i : Fin (nsW D + 1))
    (hi : (5 ≤ i.val ∧ i.val < 16) ∨ 16 + D.tA + D.cf.t ≤ i.val) :
    (LoopExit D ctr ω x bits pad B jk).st i = [] ∧ (LoopExit D ctr ω x bits pad B jk).sh i = 0 := by
  have hn : i ≠ sWT D ∧ i ≠ sVI D := ⟨(named_ne D i hi).2.2.1, (named_ne D i hi).2.2.2.2.1⟩
  have he := entry_blank D x bits pad B jk i hi
  unfold LoopExit
  rw [WireExponent3_5.PrimAsm.WriteNat.appendO_st, WireExponent3_5.PrimAsm.WriteNat.appendO_sh,
    Function.update_of_ne hn.2, Function.update_of_ne hn.2]
  unfold LoopIter
  simp only
  rw [Function.update_of_ne hn.2, Function.update_of_ne hn.1, Function.update_of_ne hn.2]
  exact he

theorem bitWord_getD (b : Bool) : (bitWord b).getD 2 false = b := by cases b <;> rfl

/-- **The tail.** -/
theorem tail_run {γ εT : ℚ} (vm : Worker.VerdictMachine γ εT) (vmap : Fin vm.wf.program.tapeCount → Fin (nsW D + 1))
    (hinj : Function.Injective vmap) (hin : vmap (inTape vm.wf.program) = sVI D) (hL : ∀ j, vmap j ≠ sL D)
    (hbl : ∀ j, j ≠ inTape vm.wf.program → BlankAtExit D (vmap j))
    {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ)
    (B : Outer.OuterGuess (width s g N)) (jk : Fin (nsW D + 1) → List Bool) (req : Worker.VerdictReq)
    (hvi : (LoopExit D ctr ω x bits pad B jk).st (sVI D) = RepairOrdinary.frame (Worker.verdictWord req)) (cap : ℕ)
    (hcap : 2 * (Worker.verdictWord req).length + 2 ≤ cap) (σ : WState (nsW D) nrW)
    (hs : SimW (LoopExit D ctr ω x bits pad B jk) σ) :
    ∃ τ, WXExec cap (tailW D vm vmap) σ τ (10 * (Worker.verdictWord req).length + 2 * vm.budget req + 20) ∧
      τ.cell = Worker.verdictBit γ εT req := by
  set E := LoopExit D ctr ω x bits pad B jk with hE
  have hVW : sVI D ≠ sWT D := fun e => by have := congrArg Fin.val e; simp [sVI, sWT, fixS] at this
  have hLV : sL D ≠ sVI D := fun e => by have := congrArg Fin.val e; simp [sVI, sL, fixS] at this
  have hLval : (sL D).val = 9 := rfl
  set vw := Worker.verdictWord req with hvw
  have hfl : (RepairOrdinary.frame vw).length = 2 * vw.length + 1 := frame_len' vw
  -- the I-stream at the exit
  have hsh : E.sh (sVI D) = (RepairOrdinary.frame vw).length := by
    rw [← hvi]; simp only [hE, LoopExit, LoopIter, WireExponent3_5.PrimAsm.WriteNat.appendO_sh,
      WireExponent3_5.PrimAsm.WriteNat.appendO_st, Function.update_self]
    rw [Function.update_of_ne hVW, Function.update_self]; simp
  have hr9 : E.val (regE 9) = (RepairOrdinary.frame vw).length := by
    rw [← hvi]; simp only [hE, LoopExit, LoopIter, WireExponent3_5.PrimAsm.WriteNat.appendO_val,
      WireExponent3_5.PrimAsm.WriteNat.appendO_st, Function.update_self]
    rw [Function.update_of_ne (show regE 9 ≠ rLC by decide), Function.update_of_ne (show regE 9 ≠ rA by decide),
      Function.update_self]; simp
  have e1 := wrewind_spec (cap := cap) (sVI D) (regE 9) _ E hr9 (by rw [hr9]; omega)
  set E1 := (E.setv (regE 9) 0).seth (sVI D) (E.sh (sVI D) - (RepairOrdinary.frame vw).length) with hE1
  have hL9 : (5 ≤ (sL D).val ∧ (sL D).val < 16) ∨ 16 + D.tA + D.cf.t ≤ (sL D).val :=
    Or.inl ⟨by rw [hLval]; omega, by rw [hLval]; omega⟩
  have hbl' : ∀ j, j ≠ inTape vm.wf.program →
      (5 ≤ (vmap j).val ∧ (vmap j).val < 16) ∨ 16 + D.tA + D.cf.t ≤ (vmap j).val := by
    intro j hj
    rcases hbl j hj with ⟨h1, h2, _⟩ | h
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr h
  have hVne : ∀ j, j ≠ inTape vm.wf.program → vmap j ≠ sVI D := fun j hj e => by
    have := congrArg Fin.val e; have h4 : (sVI D).val = 4 := rfl
    rcases hbl' j hj with ⟨h1, _⟩ | h <;> omega
  obtain ⟨τ2, tout, e2, s2, hout⟩ := WorkerArith.wordFunction_blank_ideal vm.wf req cap vmap hinj (sL D) hL E1
    (fun j => by
      by_cases hj : j = inTape vm.wf.program
      · subst hj; rw [hin]; simp [hE1, hsh]
      · simp only [hE1, WState.seth_sh, WState.setv_sh]
        rw [Function.update_of_ne (hVne j hj)]
        exact (exit_blank D ctr ω x bits pad B jk (vmap j) (hbl' j hj)).2)
    (fun j => by
      rw [program_inputTapes]
      by_cases hj : j = inTape vm.wf.program
      · subst hj
        rw [if_pos (show (inTape vm.wf.program).val = 0 from rfl), hin]
        simp only [hE1, WState.seth_st, WState.setv_st]
        rw [hvi]; exact RdEq.refl _
      · have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
        rw [if_neg hj0]
        simp only [hE1, WState.seth_st, WState.setv_st]
        rw [(exit_blank D ctr ω x bits pad B jk (vmap j) (hbl' j hj)).1]; exact RdEq.refl _)
    (by simp only [hE1, WState.seth_st, WState.setv_st]
        rw [(exit_blank D ctr ω x bits pad B jk (sL D) hL9).1]; intro p; rfl)
    (by simp only [hE1, WState.seth_sh, WState.setv_sh]
        rw [Function.update_of_ne hLV]
        exact (exit_blank D ctr ω x bits pad B jk (sL D) hL9).2)
  -- read the verdict bit
  set o := vmap vm.wf.program.outputTape with ho
  have hosh : τ2.sh o = 0 := by
    rw [s2.sh, updS_sh_slot vmap E1 (fun _ => 0) tout hinj]
  have hord : ∀ p, readTapeBit (τ2.st o) p = readTapeBit (tout vm.wf.program.outputTape) p := by
    intro p
    have := s2.st o
    rw [updS_st_slot vmap E1 (fun _ => 0) tout hinj] at this
    exact (this p).symm
  have f1 := WExec.fwd (cap := cap) o τ2
  have f2 := WExec.fwd (cap := cap) o (τ2.seth o (τ2.sh o + 1))
  set τ3 := (τ2.seth o (τ2.sh o + 1)).seth o ((τ2.seth o (τ2.sh o + 1)).sh o + 1) with hτ3
  have hbit : wbit τ3 o = Worker.verdictBit γ εT req := by
    unfold wbit
    rw [show τ3.st o = τ2.st o from rfl, show τ3.sh o = 2 by simp [hτ3, hosh], hord, hout]
    exact bitWord_getD _
  have f3 : WExec cap (.ifs o (.setc true) (.setc false)) τ3 (τ3.setc (Worker.verdictBit γ εT req)) 2 := by
    cases hb : Worker.verdictBit γ εT req
    · rw [hb] at hbit; exact WExec.ifsF hbit (WExec.setc false τ3)
    · rw [hb] at hbit; exact WExec.ifsT hbit (WExec.setc true τ3)
  have eR : WXExec cap (.wm (resultW o)) τ2 (τ3.setc (Worker.verdictBit γ εT req)) 6 :=
    WXExec.wm (WExec.mono (WExec.seq f1 (WExec.seq f2 f3)) (by omega))
  have etot : WXExec cap (tailW D vm vmap) E (τ3.setc (Worker.verdictBit γ εT req))
      (10 * vw.length + 2 * vm.budget req + 20) :=
    WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 eR)) (by rw [hfl]; omega)
  obtain ⟨τ, e, sτ⟩ := wxexec_sim etot σ hs
  exact ⟨τ, e, by rw [sτ.cell]; rfl⟩

end NearCubicGates.Close.WorkerArith.WeakWorker
