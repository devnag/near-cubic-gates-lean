import Proof.CaseAnalysis.WitnessSelectedStreams
import Proof.PCP.PCPPNativeHierarchyCountersDock

/-! Same retained stream fields enter the original native metadata/mass
producer. This preserves the size counter for the exact paper cap guard. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedCounters
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k : ℕ):=SelectedStreams.tapes source k
abbrev tapes (k : ℕ):=base source k+75
def sourcePorts (k : ℕ) : Fin 6→Fin (base source k):=
  ![SelectedStreams.old source k (SelectedOracle.descriptorSlot source k),
    SelectedStreams.old source k (SelectedStreams.bits source k 1),
    StreamCall.slots (SelectedStreams.fields source k) 46,
    StreamCall.slots (SelectedStreams.fields source k) 29,
    StreamCall.slots (SelectedStreams.fields source k) 25,
    StreamCall.slots (SelectedStreams.fields source k) 38]
def sourceValues (k : ℕ) : Fin 6→ℕ:=
  ![SelectedOracle.base source k+1299,(SelectedStreams.selectedBits source k 1).val,
    SelectedStreams.base source k+46,SelectedStreams.base source k+29,
    SelectedStreams.base source k+25,SelectedStreams.base source k+38]

theorem source_values (k : ℕ) (i : Fin 6) : (sourcePorts source k i).val=sourceValues source k i:=by
  fin_cases i <;> rfl

theorem source_injective (k : ℕ) : Function.Injective (sourcePorts source k):=by
  intro a b h
  have hq:(SelectedStreams.selectedBits source k 1).val<SelectedOracle.base source k:=
    (SelectedStreams.selectedBits source k 1).isLt
  have hbase:SelectedStreams.base source k=SelectedOracle.base source k+1385:=rfl
  have hv:=congrArg Fin.val h
  rw [source_values,source_values] at hv
  fin_cases a <;> fin_cases b <;> simp [sourceValues,Fin.ext_iff] at hv ⊢ <;> omega

def slots (k : ℕ) (i : Fin 75) : Fin (tapes source k):=
  if i=0 then (sourcePorts source k 0).castAdd 75
  else if i=40 then (sourcePorts source k 1).castAdd 75
  else if i=47 then (sourcePorts source k 2).castAdd 75
  else if i=52 then (sourcePorts source k 3).castAdd 75
  else if i=54 then (sourcePorts source k 4).castAdd 75
  else if i=57 then (sourcePorts source k 5).castAdd 75
  else i.natAdd (base source k)

theorem slots_injective (k : ℕ) : Function.Injective (slots source k):=by
  intro a b he
  have hq:(SelectedStreams.selectedBits source k 1).val<SelectedOracle.base source k:=
    (SelectedStreams.selectedBits source k 1).isLt
  have hbase:SelectedStreams.base source k=SelectedOracle.base source k+1385:=rfl
  have hb:base source k=SelectedStreams.base source k+48:=rfl
  have hv:=congrArg Fin.val he
  dsimp only [slots] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd,source_values] at hv
  all_goals try simp [sourceValues] at hv
  all_goals (subst_vars; first | rfl | exact Fin.ext (by omega))

def first (k CH Cpad : ℕ) (code : List Bool):=TapeEmbedding.machine 75 (SelectedStreams.machine source k CH Cpad code)
def second (k : ℕ):=RecoveryFocus.machine (slots source k) PCPPNativeColdCounters.machine
def machine (k CH Cpad : ℕ) (code : List Bool):=Composition.machine (first source k CH Cpad code) (second source k)
def input (k : ℕ) (x raw : List Bool):=
  Fin.addCases (m:=base source k) (n:=75) (motive:=fun _=>List Bool) (SelectedStreams.input source k x raw) (fun _=>[])

theorem dock_input {s : ℕ} (k CH Cpad : ℕ) (code x : List Bool)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code x))
    (a : ExecutionReceipt (base source k) s)
    (hf : StreamCall.Fields (SelectedStreams.fields source k) (SelectedStreams.pcp source k CH Cpad code x)
      (SelectedOracle.width source k CH Cpad code x) (SelectedStreams.queries source k CH Cpad code x) a.final)
    (hb : ∀ i,a.final.heads (SelectedStreams.old source k (SelectedStreams.bits source k i))=0 ∧
      a.final.tapes (SelectedStreams.old source k (SelectedStreams.bits source k i))=
        frame (SelectedStreams.scalarValues source k CH Cpad code x i).bits)
    (ho : a.final.heads (SelectedStreams.old source k (SelectedOracle.descriptorSlot source k))=0 ∧
      a.final.tapes (SelectedStreams.old source k (SelectedOracle.descriptorSlot source k))=PCPPNative.descriptor oracle)
    (i : Fin 75) :
    let lifted:=TapeEmbedding.receipt (fun _ : Fin 75=>0) (fun _=>[]) a
    lifted.final.heads (slots source k i)=PCPPNativeColdCounters.heads i ∧
    lifted.final.tapes (slots source k i)=PCPPNativeColdCounters.input (PCPPNative.descriptor oracle)
      (SelectedStreams.pcp source k CH Cpad code x) (SelectedOracle.width source k CH Cpad code x)
      (SelectedStreams.queries source k CH Cpad code x) i:=by
  intro lifted
  by_cases h0:i=0
  · subst i
    simpa [lifted,slots,sourcePorts,PCPPNativeHierarchyCounters.counter_heads,
      PCPPNativeHierarchyCounters.counter_input] using ho
  by_cases h40:i=40
  · subst i
    simpa [lifted,slots,sourcePorts,PCPPNativeHierarchyCounters.counter_heads,
      PCPPNativeHierarchyCounters.counter_input,SelectedStreams.scalarValues] using hb 1
  by_cases h47:i=47
  · subst i
    simpa [lifted,slots,sourcePorts,PCPPNativeHierarchyCounters.counter_heads,
      PCPPNativeHierarchyCounters.counter_input] using And.intro hf.clauseCountHead hf.clauseCount
  by_cases h52:i=52
  · subst i
    simpa [lifted,slots,sourcePorts,PCPPNativeHierarchyCounters.counter_heads,
      PCPPNativeHierarchyCounters.counter_input,PCPPNativeMetadataMass.queryBytes] using And.intro hf.queryHead hf.query
  by_cases h54:i=54
  · subst i
    simpa [lifted,slots,sourcePorts,PCPPNativeHierarchyCounters.counter_heads,
      PCPPNativeHierarchyCounters.counter_input] using And.intro hf.queryCountHead hf.queryCount
  by_cases h57:i=57
  · subst i
    simpa [lifted,slots,sourcePorts,PCPPNativeHierarchyCounters.counter_heads,
      PCPPNativeHierarchyCounters.counter_input] using And.intro hf.clauseHead hf.clause
  simp [lifted,slots,h0,h40,h47,h52,h54,h57,PCPPNativeHierarchyCounters.counter_heads,
    PCPPNativeHierarchyCounters.counter_input]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedCounters
