import Proof.CaseAnalysis.CaseTwoExecutionLayout

/-! Complete physical Case 2 from the original five cold fields. The same
canonical circuit is converted once and used for every fixed original PCPP
block; the output is the paper's unsigned padded XOR bit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Execution
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RepairSource.ProjectionNormalization
open RecoveryPipeline OuterPCPRecovery RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
def budget {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hpad : k+3≤Cpad)
    (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (B D copies : ℕ) {target : ℕ} (point : BitInput target):=
  PreparedFrames.budget B oracle (List.ofFn r.2) (H.time r.1).bits+1+
    FixedFold.budget (XorFamily.cost source a H Cpad hpad r oracle D point) copies

theorem run {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (B D copies : ℕ) (hc : oracle.size≤B) (hD : 1≤D) {target : ℕ} (point : BitInput target)
    (hcb : (a.output (WholeBlock.request source a H Cpad hpad r oracle)).clauseBits≤
      CloseoutLanguage.clauseWidth D (WholeBlock.request source a H Cpad hpad r oracle).arity)
    (hfit : copies*((WholeBlock.request source a H Cpad hpad r oracle).arity+
      CloseoutLanguage.clauseWidth D (WholeBlock.request source a H Cpad hpad r oracle).arity+1)≤target) :
    let req:=WholeBlock.request source a H Cpad hpad r oracle
    let R:=PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
    let hierarchy:=HierarchySourceInput.hierarchyInput H r
    let description:=frame (canonicalBoundedCircuitDescription B oracle)
    let address:=frame (List.ofFn point)
    ∃ out,ClockJoin.ReadyRun (machine source a k D copies H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (budget source a H Cpad hpad r oracle B D copies point)
      (input source a k D copies hierarchy description address R B) out ∧
      out (outputSlot source a k D copies)=
        [padCore (xorPower (CloseoutLanguage.paddedUnsigned (a.output req) hcb) copies) hfit point] ∧
      out (old source a k D copies 0)=hierarchy ∧
      out (old source a k D copies 1)=description ∧ out (old source a k D copies 2)=address:=by
  dsimp only
  let hierarchy:=HierarchySourceInput.hierarchyInput H r
  let description:=frame (canonicalBoundedCircuitDescription B oracle)
  let address:=frame (List.ofFn point)
  let R:=PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  let initial:=input source a k D copies hierarchy description address R B
  obtain ⟨prepared,hp,hHframe,hDframe,hH,hDword,hA⟩:=PreparedFrames.frames_run oracle hc
    (List.ofFn r.2) (H.time r.1).bits address
  have firstReady:=hp.focus (old source a k D copies) (old_injective source a k D copies) initial
    (by intro j;exact Fin.addCases_left j)
  let middle:=install (old source a k D copies) initial prepared
  obtain ⟨folded,hf,hw,hbit⟩:=XorFamily.run source a H Cpad hcoeff hpad r oracle D copies hD point hcb hfit
  have hfields (i : Fin 3) : prepared (fields i)=
      XorFamily.words hierarchy (PCPPNative.descriptor oracle) (List.ofFn point) i:=by
    fin_cases i
    · exact hHframe
    · exact hDframe
    · exact hA
  have lastReady:=hf.focus (slots source a k D copies) (slots_injective source a k D copies) middle (by
    intro j
    by_cases hj : j.val<3
    · let i : Fin 3:=⟨j.val,hj⟩
      have he : j=FixedFold.low (XorFamily.tapes source a k D) copies (i.castAdd 1):=Fin.ext rfl
      rw [he,field_slot]
      change install (old source a k D copies) initial prepared (old source a k D copies (fields i))=_
      rw [install_slot (old source a k D copies) (old_injective source a k D copies),hfields i]
      change _=(if h : i.val<3 then _ else [])
      rw [dif_pos i.isLt]
      rfl
    · rw [slots,dif_neg hj]
      change install (old source a k D copies) initial prepared (j.natAdd 140)=_
      rw [install_other (old source a k D copies) _ _ _ (by
        intro i he
        have hv:=congrArg Fin.val he
        have hi:=i.isLt
        simp only [old,Fin.val_castAdd,Fin.val_natAdd] at hv
        omega)]
      simp only [initial,input,FixedFold.initial,dif_neg hj]
      exact Fin.addCases_right j)
  have whole:=ClockJoin.join (first source a k D copies)
    (last source a k D copies H.coefficient Cpad (VerifierEncoding.code H.verifier)) _ _ _ _ _ firstReady lastReady
  refine ⟨_,whole,?_,?_,?_,?_⟩
  · exact (install_slot (slots source a k D copies) (slots_injective source a k D copies) _ _
      (FixedFold.low (XorFamily.tapes source a k D) copies 3)).trans hbit
  · exact (install_other (slots source a k D copies) middle folded (old source a k D copies 0)
      (old_outside source a k D copies 0)).trans
        ((install_slot (old source a k D copies) (old_injective source a k D copies) _ _ 0).trans hH)
  · exact (install_other (slots source a k D copies) middle folded (old source a k D copies 1)
      (old_outside source a k D copies 1)).trans
        ((install_slot (old source a k D copies) (old_injective source a k D copies) _ _ 1).trans hDword)
  · have ha:=field_slot source a k D copies 2
    change slots source a k D copies (FixedFold.low (XorFamily.tapes source a k D) copies 2)=old source a k D copies 2 at ha
    rw [←ha]
    exact (install_slot (slots source a k D copies) (slots_injective source a k D copies) _ _
      (FixedFold.low (XorFamily.tapes source a k D) copies 2)).trans (hw 2)

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Execution
