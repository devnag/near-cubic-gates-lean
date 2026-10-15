import Proof.Gates.Setup.PhaseK
import Proof.Gates.Worker.NativeLower

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu PairOK)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

def phC (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s)) :
    WMX (nsW D) nrW :=
  WMX.machZ D.cf.M (mK D W R) (sL D)

def UntC (D : SetupData s P g) (i : Fin (nsW D + 1)) : Prop :=
  (i.val < 16 ∧ i.val ≠ 0 ∧ i.val ≠ 1 ∧ i.val ≠ 2) ∨ 16 + D.tA + D.cf.t ≤ i.val

structure AfterC (D : SetupData s P g) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ)
    (B : Outer.OuterGuess (width s g N)) (ι : WState (nsW D) nrW) : Prop where
  sx : ι.st (sX D) = RepairOrdinary.frame (List.ofFn x)
  bw : ι.st (sBW D) = RepairOrdinary.frame bits
  wt : ι.st (sWT D) = guessWord N bits pad
  fl : ι.st (sFL D) = [true]
  cw : ι.st (kB D D.cf.cOut) = RepairOrdinary.frame (checkedCircuit P.code (Worker.substituted s g x B)).word
  j8 : ι.st (sJ D) = (pcpp s P g x B).word
  sup : ι.st (sSUP D) = RepairOrdinary.frame (supportsWord P.code (width s g N))
  pb : ι.st (kB D D.cf.pOut) = RepairOrdinary.frame (pcpp s P g x B).proofBits.bits
  rb : ι.st (kB D D.cf.rOut) = RepairOrdinary.frame (pcpp s P g x B).randomBits.bits
  blank : ∀ i, UntC D i → ι.st i = []
  sh : ι.sh = fun i => if i = sWT D then pairEnd (guessWord N bits pad) else 0
  val : ι.val = fun r => if r = regE 6 then width s g N else if r = rN then N
    else if r = rBs then baseOf g (nu N) else 0
  cell : ι.cell = false

/-- The composite's budget on the pair. -/
def compBudget (D : SetupData s P g) {N : ℕ} (B : Outer.OuterGuess (width s g N)) : ℕ :=
  D.cf.C * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length + width s g N + 1) ^ D.cf.e

theorem phC_ideal (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s))
    (hL : Lay D W R) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad cap : ℕ) (B : Outer.OuterGuess (width s g N))
    (hN4 : 4 ≤ N) (ι : WState (nsW D) nrW) (hι : AfterK D W R x bits pad B ι) (hFL : ι.st (sFL D) = [true]) :
    ∃ τ ι', WXExec cap (phC D W R) ι τ (2 * compBudget D B + 2) ∧ SimW ι' τ ∧ AfterC D x bits pad B ι' := by
  classical
  have hA := tA_eq hL
  have htO := tO_eq
  have hq2 : 2 ≤ width s g N := Worker.two_le_nativeWidth s g N hN4
  obtain ⟨outK, hrunK, hcK, hwK, hsK, hpK, hrK⟩ := D.cf.run x B hq2
  have nd := D.cf.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at nd
  obtain ⟨⟨hcd, hcc, hcw, hcs, hcp, hcr⟩, ⟨hdc, hdw, hds, hdp, hdr⟩, -, -, -, -⟩ := nd
  have hsh : ∀ i, i ≠ sWT D → ι.sh i = 0 := fun i hi => by rw [hι.sh]; simp [hi]
  have hmL : ∀ j, mK D W R j ≠ sL D := fun j => fin_ne_of_val (by
    rw [mK_val hL]; show _ ≠ 9; split_ifs <;> omega)
  have hmW : ∀ j, mK D W R j ≠ sWT D := fun j => fin_ne_of_val (by
    rw [mK_val hL]; show _ ≠ 2; split_ifs <;> omega)
  have hcIn : mK D W R D.cf.cIn = sMW D W R := by simp [mK]
  have hdIn : mK D W R D.cf.dIn = sD2 D W := by simp [mK, Ne.symm hcd]
  have hof : ∀ j, j ≠ D.cf.cIn → j ≠ D.cf.dIn → mK D W R j = kB D j := fun j h1 h2 => by simp [mK, h1, h2]
  obtain ⟨τ, e, sτ⟩ := Worker.portDonor_ideal D.cf.M _ D.cf.cIn D.cf.dIn hcd _ _ outK hrunK (cap := cap) (mK D W R)
    (mK_inj hL) (sL D) hmL ι (fun j => hsh _ (hmW j)) (by rw [hcIn]; exact hι.mw) (by rw [hdIn]; exact hι.d2)
    (fun j h1 h2 => by
      rw [hof j h1 h2]
      have := kB_val' hL j
      exact hι.blank _ (by omega) (by omega) (by omega) (by omega) (by right; omega))
    (fun p => by
      rw [hι.blank _ (by simp [sL, fixS]) (by simp [sL, fixS]) (by simp [sL, fixS]) (by simp [sL, fixS])
        (by left; simp [sL, fixS])]; rfl)
    (hsh _ (fin_ne_of_val (by simp [sL, sWT, fixS])))
  refine ⟨τ, _, WXExec.mono e le_rfl, sτ, ?_⟩
  have hnotK : ∀ i : Fin (nsW D + 1), (i.val < 21 + 2 * tWB W + 2 * tWU W + tO ∨
      (21 + 2 * tWB W + 2 * tWU W + tO + 1299 < i.val ∧ i.val < 21 + 2 * tWB W + 2 * tWU W + 2 * tO + R.t) ∨
      21 + 2 * tWB W + 2 * tWU W + 2 * tO + R.t + D.cf.t ≤ i.val) →
      i.val ≠ 21 + 2 * tWB W + 2 * tWU W + 2 * tO + R.wOut.val → ∀ j, mK D W R j ≠ i := fun i hi hw j h => by
    have hv := mK_val hL j; rw [h] at hv; have := j.isLt; have := R.wOut.isLt
    split_ifs at hv <;> omega
  have hst : ∀ i : Fin (nsW D + 1), i.val < 21 → (updS (mK D W R) ι (fun _ => 0) outK).st i = ι.st i :=
    fun i hi => updS_st_other _ _ _ _ i (hnotK i (by left; omega) (by omega))
  have hslot : ∀ j ∈ [D.cf.cOut, D.cf.wOut, D.cf.sOut, D.cf.pOut, D.cf.rOut],
      (updS (mK D W R) ι (fun _ => 0) outK).st (kB D j) = outK j := fun j hj => by
    have h1 : j ≠ D.cf.cIn := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> [exact Ne.symm hcc; exact Ne.symm hcw; exact Ne.symm hcs;
        exact Ne.symm hcp; exact Ne.symm hcr]
    have h2 : j ≠ D.cf.dIn := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> [exact Ne.symm hdc; exact Ne.symm hdw; exact Ne.symm hds;
        exact Ne.symm hdp; exact Ne.symm hdr]
    rw [← hof j h1 h2, updS_st_slot _ _ _ _ (mK_inj hL)]
  have vFL := sFL_val hL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst _ (by simp [sX, fixS])]; exact hι.sx
  · rw [hst _ (by simp [sBW, fixS])]; exact hι.bw
  · rw [hst _ (by simp [sWT, fixS])]; exact hι.wt
  · rw [hst _ (by omega)]; exact hFL
  · rw [hslot _ (by simp)]; exact hcK
  · rw [sJ, hslot _ (by simp)]; exact hwK
  · rw [sSUP, hslot _ (by simp)]; exact hsK
  · rw [hslot _ (by simp)]; exact hpK
  · rw [hslot _ (by simp)]; exact hrK
  · intro i hi
    unfold UntC at hi
    rcases hi with ⟨h1, h2, h3, h4⟩ | h
    · rw [hst _ (by omega)]
      exact hι.blank _ h2 h3 h4 (by omega) (by left; omega)
    · rw [updS_st_other _ _ _ _ i (hnotK i (by right; right; rw [hA] at h; omega) (by rw [hA] at h; omega))]
      exact hι.blank _ (by omega) (by omega) (by omega) (by omega) (by right; omega)
  · funext i
    rw [updS_sh_zero _ (mK_inj hL), hι.sh]
    by_cases hi : i = sWT D
    · subst hi; rw [if_neg (fun ⟨j, hj⟩ => hmW j hj)]
    · simp only [hi, if_false]; split_ifs <;> rfl
  · rw [updS_val]; exact hι.val
  · rw [updS_cell]; exact hι.cell

end

end NearCubicGates.Close.Setup
