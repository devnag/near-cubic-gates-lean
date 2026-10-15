import Proof.CaseAnalysis.CaseTwoDock
import Proof.CaseAnalysis.CaseTwoFunding

/-! A complete cold canonical-to-native conversion from the approved five
ports. Allocation, reset logs, field copies, traversal, header and final
framing are actual paid runs. The three original logical words survive. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
open LocalBitMultitape RecoveryRootRound RepairRepresentation OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def converterProgram:=RecoveryFocus.machine nativeSlots NativeConverter.framed
noncomputable def machine:=Composition.machine (Composition.machine (fundingProgram 1048576) prepareProgram) converterProgram
def budget {R : ℕ} (B : ℕ) (c : BooleanCircuit R):=
  ColdLogs.budget 1048576 R B+1+prepareBudget (ColdFits.capacity R B)+1+
    NativeConverter.framedBudget (ColdFits.capacity R B) c

theorem converter_run {R B : ℕ} (c : BooleanCircuit R) (hc : c.size≤B)
    (hierarchy address : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget B c)
      (input hierarchy (frame (canonicalBoundedCircuitDescription B c)) address R B) out ∧
      out 132=frame (PCPPNative.descriptor c) ∧ out 0=hierarchy ∧
      out 1=frame (canonicalBoundedCircuitDescription B c) ∧ out 2=address:=by
  let C:=ColdFits.capacity R B
  let description:=frame (canonicalBoundedCircuitDescription B c)
  have hf:=ColdFits.fits c hc
  have hd : description.length≤C:=by
    simpa only [description,frame_length] using hf.source
  have h6 : 6≤C:=by have h:=hf.nine;omega
  have hF : R+B+1≤C:=by have h:=hf.offset;unfold boundedCircuitFieldLimit at h;omega
  obtain ⟨A,ha,hA⟩:=funding_run 1048576 R B hierarchy description address
  have hp:=prepare_ready hierarchy description address R B C A hA hd h6 hF
  obtain ⟨r,hr,hs,ht,hh⟩:=NativeConverter.framed_run C c hc hf
  have ready : ClockJoin.ReadyRun NativeConverter.framed (NativeConverter.framedBudget C c)
      (NativeConverter.framedInput C B c) r.final.tapes:=⟨r,hr,rfl,hh,hs⟩
  have focused:=ready.focus nativeSlots native_injective (prepared R B C description A)
    (converter_dock c C hierarchy address A hA (by omega))
  have whole:=ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ ha hp) focused
  refine ⟨_,whole,?_,?_,?_,?_⟩
  · exact (install_slot nativeSlots native_injective _ _ 72).trans ht
  · rw [install_other nativeSlots _ _ 0 (by decide),prepared_old R B C description A 0 (by decide)]
    exact hA.hierarchy
  · rw [install_other nativeSlots _ _ 1 (by decide),prepared_old R B C description A 1 (by decide)]
    exact hA.description
  · rw [install_other nativeSlots _ _ 2 (by decide),prepared_old R B C description A 2 (by decide)]
    exact hA.address

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
