import Proof.Gates.TermLoop.LoopC
import Proof.Gates.TermLoop.Shape

set_option autoImplicit false

namespace NearCubicGates.Close.TermLoop

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Setup
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount)

noncomputable section

/-! ## The cost class -/

/-- **The loop's cost is `loopCost`**: `M` passes of `gadgetCost` (budgets `b i`), the loop overhead `4` per pass
and `1`, the sequencing step `1` and the close `7`. -/
theorem loop_cost_eq (tc Z Bc S M : ℕ) (b : ℕ → ℕ) :
    (∑ i ∈ Finset.range M, (gadgetCost tc Z Bc S (b i) + 4)) + 1 + 1 + 7 =
      loopCost tc Z Bc S M (∑ i ∈ Finset.range M, b i) := by
  simp only [gadgetCost, loopCost, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.mul_sum]
  ring

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (hct : ctr.program.program.tapeCount = D.tc) (ω : ℚ)

/-! ## The ideal states of the loop -/

section States
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
  (jk : Fin (nsW D + 1) → List Bool)

theorem viOf_zero : viOf s P g x bits pad B ctr ω 0 = headerOf s P g x B := by
  simp [viOf, entriesUpTo, marks]

theorem loopEntry_sh_VI : (LoopEntry D N x bits pad B jk).sh (sVI D) = (headerOf s P g x B).length := by
  simp only [LoopEntry]
  rw [if_neg (sWT_ne_sVI D).symm, if_pos trivial]

theorem loopEntry_st_VI : (LoopEntry D N x bits pad B jk).st (sVI D) = headerOf s P g x B := by
  simp only [LoopEntry]
  rw [if_neg (fin_ne (by simp)), if_neg (fin_ne (by simp)), if_neg (fin_ne (by simp)),
    if_neg (fin_ne (by simp)), if_pos trivial]

/-- **The first ideal state is the loop entry.** -/
theorem loopIter_zero : LoopIter D ctr ω x bits pad B jk 0 = LoopEntry D N x bits pad B jk := by
  set E := LoopEntry D N x bits pad B jk with hE
  have hsV : (viOf s P g x bits pad B ctr ω 0).length = E.sh (sVI D) := by
    rw [viOf_zero, hE, loopEntry_sh_VI]
  have hsW : fieldPos (guessWord N bits pad) (fieldsStart s P g x bits pad B) (10 * 0) = E.sh (sWT D) := by
    rw [hE, loopEntry_sh_WT, Nat.mul_zero]; rfl
  have hst : viOf s P g x bits pad B ctr ω 0 = E.st (sVI D) := by
    rw [viOf_zero, hE, loopEntry_st_VI]
  have h9 : (viOf s P g x bits pad B ctr ω 0).length = E.val (regE 9) := by
    rw [viOf_zero, hE, loopEntry_val]; rfl
  have hA : (0 : ℕ) = E.val rA := by
    rw [hE, loopEntry_val]; rfl
  have hL : gadgets s g N - 0 = E.val rLC := by
    rw [hE, loopEntry_val, Nat.sub_zero]; rfl
  apply WState.eq
  · show Function.update (Function.update E.sh (sVI D) _) (sWT D) _ = E.sh
    rw [show Function.update E.sh (sVI D) _ = E.sh from Function.update_eq_self_iff.2 hsV,
      Function.update_eq_self_iff.2 hsW]
  · show Function.update E.st (sVI D) _ = E.st
    rw [Function.update_eq_self_iff.2 hst]
  · show Function.update (Function.update (Function.update E.val (regE 9) _) rA 0) rLC _ = E.val
    rw [show Function.update E.val (regE 9) _ = E.val from Function.update_eq_self_iff.2 h9,
      show Function.update E.val rA 0 = E.val from Function.update_eq_self_iff.2 hA,
      Function.update_eq_self_iff.2 hL]
  · rfl

theorem loopIter_rLC (i : ℕ) : (LoopIter D ctr ω x bits pad B jk i).val rLC = gadgets s g N - i := by
  simp [LoopIter]

theorem loopIter_R9 (i : ℕ) :
    (LoopIter D ctr ω x bits pad B jk i).val (regE 9) = (viOf s P g x bits pad B ctr ω i).length := by
  simp only [LoopIter]
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]

theorem loopIter_sh_VI (i : ℕ) :
    (LoopIter D ctr ω x bits pad B jk i).sh (sVI D) =
      ((LoopIter D ctr ω x bits pad B jk i).st (sVI D)).length := by
  simp only [LoopIter]
  rw [Function.update_of_ne (sWT_ne_sVI D).symm, Function.update_self, Function.update_self]

end States

/-! ## The loop -/

theorem termLoop_ideal_of (hG : GadgetIdeal D ctr hct ω) : TermLoopIdeal D ctr hct ω := by
  intro N x bits pad B jk cap Z Bc V hL σ hσ
  have hMpos : 0 < gadgets s g N := Nat.two_pow_pos _
  have hMcap : gadgets s g N ≤ cap := by
    have := hL.front; unfold frontSize at this; omega
  obtain ⟨τ1, e1, s1⟩ := repLoopX_simC (cap := cap) rLC (gadgetW D ctr hct ω) (gadgets s g N)
    (fun i => gadgetCost D.tc Z Bc (frontSize s P g x B) (gadgetBud s P g x bits pad B ctr ω i))
    (fun i => LoopIter D ctr ω x bits pad B jk i)
    (fun i _ => loopIter_rLC D ctr ω x bits pad B jk i) hMcap
    (fun i hi => hG x bits pad B jk cap Z Bc V hL i hi _ (SimW.refl _)) σ
    (by rw [loopIter_zero D ctr ω x bits pad B jk]; exact hσ)
  have hR9 : (LoopIter D ctr ω x bits pad B jk (gadgets s g N)).val (regE 9) < cap := by
    rw [loopIter_R9]
    have := hL.capT 0 hMpos 0
    omega
  have ec := WorkerArith.closeW_spec cap (sVI D) (regE 9) (LoopIter D ctr ω x bits pad B jk (gadgets s g N))
    (loopIter_sh_VI D ctr ω x bits pad B jk _) hR9
  obtain ⟨τ2, e2, s2⟩ := wxexec_sim (WXExec.wm ec) τ1 s1
  refine ⟨τ2, WXExec.seq' cap e1 e2 ?_, s2⟩
  rw [loop_cost_eq]
  rfl

end

end NearCubicGates.Close.TermLoop
