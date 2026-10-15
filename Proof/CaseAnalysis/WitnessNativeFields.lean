import Proof.CaseAnalysis.WitnessNativePipelineDock

/-! The five cold-prefix fields are the same source word, actual raw R/Q,
canonical Q bits and decoded oracle descriptor. Their aliases are disjoint. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdNative
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k : ℕ):=GuardedOracle.tapes (ColdOracle.base source k)
def sourceFields (k : ℕ) : Fin 4→Fin (HierarchySelectedSource.tapes source k):=
  Fin.addCases (m:=3) (n:=1) (motive:=fun _=>Fin (HierarchySelectedSource.tapes source k))
    (SelectedStreams.selectedFields source k) (fun _=>SelectedStreams.selectedBits source k 1)
def fields (k : ℕ) : Fin 5→Fin (base source k):=
  Fin.addCases (m:=4) (n:=1) (motive:=fun _=>Fin (base source k))
    (ColdOracle.sourceSlots source k ∘ sourceFields source k)
    (fun _=>GuardedOracle.descriptorSlot (ColdOracle.base source k))

theorem sourceFields_injective (k : ℕ) : Function.Injective (sourceFields source k):=by
  apply RecoveryColdAllCode.join_injective
  · intro i j h
    exact SelectedStreams.fields_injective source k (congrArg (SelectedOracle.old source k) h)
  · intro i j _
    exact Subsingleton.elim i j
  · intro i j he
    exact SelectedStreams.bits_not_fields source k 1 i (congrArg (SelectedOracle.old source k) he.symm)
theorem fields_injective (k : ℕ) : Function.Injective (fields source k):=by
  apply RecoveryColdAllCode.join_injective
  · intro i j he
    have hv:=congrArg (fun z : Fin (base source k)=>z.val) he
    exact sourceFields_injective source k (Fin.ext hv)
  · intro i j _
    exact Subsingleton.elim i j
  · intro i j he
    have hv:=congrArg (fun z : Fin (base source k)=>z.val) he
    have hi:=(sourceFields source k i).isLt
    change (sourceFields source k i).val=HierarchySelectedSource.tapes source k+8+4+1299 at hv
    omega

theorem retained_fields (k CH Cpad : ℕ) (code x : List Bool) (out : Fin (base source k)→List Bool)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code x))
    (hf : HierarchySelectedSource.Fields source k CH Cpad code x
      (out ∘ ColdOracle.sourceSlots source k ∘ HierarchySelectedSource.old source k))
    (hw : out (ColdOracle.sourceSlots source k (HierarchySelectedSource.outputTape source k))=
      (SelectedStreams.pcp source k CH Cpad code x).word)
    (hd : out (GuardedOracle.descriptorSlot (ColdOracle.base source k))=PCPPNative.descriptor oracle) :
    ∀ i,out (fields source k i)=NativePipeline.Dock.values oracle
      (SelectedStreams.pcp source k CH Cpad code x) (SelectedStreams.queries source k CH Cpad code x) i:=by
  intro i
  fin_cases i
  · exact hw
  · exact hf.rawR
  · exact hf.rawQ
  · exact hf.bitsQ
  · exact hd

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdNative
