import Proof.PCP.PCPPNativeCounterNodes
import Proof.PCP.PCPPNativeHierarchyCountersDock

/-! The same literal original hierarchy fields feed the complete counted
node emitter; its workspace is fresh and its counters execute once. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchyNodes
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def base (k : ℕ) := PCPPNativeHierarchy.tapes source k
def tapes (k : ℕ) := base source k+438
def slots (k : ℕ) (i : Fin 438) : Fin (tapes source k) :=
  if i=0 then (PCPPNativeHierarchyCounters.sourcePorts source k 0).castAdd 438
  else if i=40 then (PCPPNativeHierarchyCounters.sourcePorts source k 1).castAdd 438
  else if i=47 then (PCPPNativeHierarchyCounters.sourcePorts source k 2).castAdd 438
  else if i=52 then (PCPPNativeHierarchyCounters.sourcePorts source k 3).castAdd 438
  else if i=54 then (PCPPNativeHierarchyCounters.sourcePorts source k 4).castAdd 438
  else if i=57 then (PCPPNativeHierarchyCounters.sourcePorts source k 5).castAdd 438
  else i.natAdd (base source k)
theorem slots_injective (k : ℕ) : Function.Injective (slots source k) := by
  intro a b he
  have hbits := (HierarchyStreams.bitsQ source k).isLt
  have hp : 0<(HierarchyStreams.bitsQ source k).val := HierarchyStreams.slot_positive source k _
  have hv := congrArg Fin.val he
  have hb : base source k=4+(HierarchyStreams.base source k+48) := rfl
  dsimp only [slots] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd,PCPPNativeHierarchyCounters.source_values] at hv
  all_goals try simp [PCPPNativeHierarchyCounters.sourceValues] at hv
  all_goals (subst_vars; first | rfl | exact Fin.ext (by omega))
def first (k CH Cpad : ℕ) (code : List Bool) :=
  TapeEmbedding.machine 438 (PCPPNativeHierarchy.machine source k CH Cpad code)
def second (k : ℕ) := RecoveryFocus.machine (slots source k) PCPPNativeCounterNodes.machine
def machine (k CH Cpad : ℕ) (code : List Bool) :=
  Composition.machine (first source k CH Cpad code) (second source k)
def input (k : ℕ) (a oracle : List Bool) : Fin (tapes source k) → List Bool :=
  Fin.addCases (m:=base source k) (n:=438) (motive:=fun _=>List Bool)
    (PCPPNativeHierarchy.input source k a oracle) (fun _=>[])

theorem node_input (oracle : List Bool) (p : RawProjectionPCP) (R Q : ℕ) (i : Fin 438) :
    PCPPNativeCounterNodes.input oracle p R Q i=
      if i=0 then oracle else if i=40 then frame Q.bits
      else if i=47 then VerifierDecoding.CompareMachine.word (Codec.clauses p).length
      else if i=52 then PCPPNativeMetadataMass.queryBytes p R Q
      else if i=54 then VerifierDecoding.CompareMachine.word (R*Q)
      else if i=57 then DedupBytes.fields p else [] := by
  fin_cases i <;> rfl
theorem node_heads (i : Fin 438) :
    PCPPNativeCounterNodes.heads i=if i=47 then 1 else if i=54 then 1 else 0 := by
  fin_cases i <;> rfl

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchyNodes
