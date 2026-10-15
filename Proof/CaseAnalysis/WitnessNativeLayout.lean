import Proof.CaseAnalysis.WitnessNativeFields
import Proof.CaseAnalysis.RowsGateSourceCalls

/-! The original cold input/oracle prefix enters the guarded native
pipeline only after cutoff, actual-width and canonical-decoder success. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdNative
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev tapes (a : PointwisePCPPAlgorithm) (k D G : ℕ):=base source k+NativePipeline.Dock.extra a D G
def old (a : PointwisePCPPAlgorithm) (k D G : ℕ) (i : Fin (base source k)):=NativePipeline.Dock.old a D G i
def slots (a : PointwisePCPPAlgorithm) (k D G : ℕ):=NativePipeline.Dock.slots a D G (fields source k)
def cacheSlots (a : PointwisePCPPAlgorithm) (k D G : ℕ) (j : Fin (PCPPSourceCache.tapes a)):=
  slots source a k D G (NativePipeline.cacheSlots a D G j)
def lengthSlot (a : PointwisePCPPAlgorithm) (k D G : ℕ):=old source a k D G (ColdOracle.lengthSlot source k)
def gateSlot (a : PointwisePCPPAlgorithm) (k D G : ℕ):=
  old source a k D G (GuardedOracle.flagSlot (ColdOracle.base source k))
def flagSlot (a : PointwisePCPPAlgorithm) (k D G : ℕ):=slots source a k D G (NativePipeline.flagSlot a D G)
def first (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G : ℕ) (code : List Bool):=
  ClockJoin.lifted (Equiv.refl (Fin (tapes source a k D G))) (ColdOracle.machine source k CH Cpad cutoff code)
def second (a : PointwisePCPPAlgorithm) (k D G copies : ℕ) (delta : ℚ):=
  NativePipeline.Dock.machine a D G copies delta (fields source k)
def machine (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies : ℕ) (delta : ℚ) (code : List Bool):=
  CloseoutRowsGateColdPair.machine (first source a k CH Cpad cutoff D G code) (second source a k D G copies delta)
    (fun scanned=>scanned (gateSlot source a k D G))
def input (a : PointwisePCPPAlgorithm) (k D G : ℕ) (x raw : List Bool):=
  NativePipeline.Dock.input a D G (ColdOracle.input source k x raw)
def request (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool) {n : ℕ}
    (x : BitInput n) (hpad : k+3 ≤ Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))):=
  NativeCache.request a (SelectedStreams.pcp source k CH Cpad code (List.ofFn x))
    (SelectedOracle.width source k CH Cpad code (List.ofFn x))
    (SelectedStreams.queries source k CH Cpad code (List.ofFn x))
    (PCPPNativeHierarchyNodes.width_fits source k CH Cpad code x hpad)
    (PCPPNativeHierarchyNodes.queries_fit source k CH Cpad code x hpad) x oracle
def tailBudget (a : PointwisePCPPAlgorithm) (k CH Cpad D G copies : ℕ) (delta : ℚ) (code : List Bool)
    {n : ℕ} (x : BitInput n) (hpad : k+3 ≤ Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))):=
  NativePipeline.budget a D G copies delta (SelectedStreams.pcp source k CH Cpad code (List.ofFn x))
    (SelectedOracle.width source k CH Cpad code (List.ofFn x))
    (SelectedStreams.queries source k CH Cpad code (List.ofFn x))
    (PCPPNativeHierarchyNodes.width_fits source k CH Cpad code x hpad)
    (PCPPNativeHierarchyNodes.queries_fit source k CH Cpad code x hpad) x oracle
def budget (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies : ℕ) (delta : ℚ) (code : List Bool)
    {n : ℕ} (x : BitInput n) (raw : List Bool) (hpad : k+3 ≤ Cpad):=
  ColdOracle.budget source k CH Cpad cutoff code (List.ofFn x) raw+1+
    (if ColdOracle.passed source k CH Cpad cutoff code (List.ofFn x) raw=true then
      (decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)).elim 0
        (tailBudget source a k CH Cpad D G copies delta code x hpad) else 0)+1
def passed (k CH Cpad cutoff G : ℕ) (code x raw : List Bool):=
  ColdOracle.passed source k CH Cpad cutoff code x raw &&
    (decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code x) (value raw)).any
      (fun oracle=>decide (oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G
        (SelectedOracle.width source k CH Cpad code x)))
def project (a : PointwisePCPPAlgorithm) (k D G : ℕ) {s : ℕ} (cfg : Configuration (tapes source a k D G) s):=
  NativePolicy.Call.project a D (NativePipeline.counter G)
    (⟨cfg.control,cfg.heads ∘ slots source a k D G,cfg.tapes ∘ slots source a k D G⟩ :
      Configuration (NativePipeline.Dock.extra a D G) s)

theorem fields_ne_length (k : ℕ) : ∀ i,fields source k i≠ColdOracle.lengthSlot source k:=by
  intro i
  refine Fin.addCases (m:=4) (n:=1) (fun j=>?_) (fun j=>?_) i
  · intro he
    rw [fields,Fin.addCases_left] at he
    have hv:=congrArg (fun z : Fin (base source k)=>z.val) he
    have hj:=(sourceFields source k j).isLt
    change (sourceFields source k j).val=HierarchySelectedSource.tapes source k+2 at hv
    omega
  · intro he
    rw [fields,Fin.addCases_right] at he
    have hv:=congrArg (fun z : Fin (base source k)=>z.val) he
    change HierarchySelectedSource.tapes source k+8+4+1299=HierarchySelectedSource.tapes source k+2 at hv
    omega

def originalTape (a : PointwisePCPPAlgorithm) (k D G : ℕ) :=
  old source a k D G (ColdOracle.sourceSlots source k
    (HierarchySelectedSource.old source k (HierarchyPrefix.old k (HierarchySelectedSource.p source)
      (HierarchySelectedSource.q source) (HierarchyFramedInput.old k (HierarchyReduction.xTape k)))))

theorem slots_ne_originalTape (a : PointwisePCPPAlgorithm) (k D G : ℕ) :
    ∀ i, slots source a k D G i ≠ originalTape source a k D G := by
  have dimAway : ∀ i, HierarchySelectedSource.dimension source k i ≠ HierarchyPrefix.old k (HierarchySelectedSource.p source) (HierarchySelectedSource.q source) (HierarchyFramedInput.old k (HierarchyReduction.xTape k)) := by
    intro i he
    have hv := congrArg Fin.val he
    have hb := HierarchyReduction.base_lower k
    change (HierarchyPrefix.dimensionSlots k (HierarchySelectedSource.p source) (HierarchySelectedSource.q source) i).val = _ at hv
    dsimp [HierarchyPrefix.dimensionSlots, HierarchyPrefix.old] at hv
    split_ifs at hv
    · simp [HierarchyFramedInput.fresh, HierarchyFramedInput.old, HierarchyReduction.xTape, HierarchyReduction.low,
        HierarchyFromInput.field, HierarchyReduction.tapes] at hv
    · have hxbound := (HierarchyFramedInput.old k (HierarchyReduction.xTape k)).isLt
      dsimp at hv
      omega
  have selectedAway : ∀ i, ColdNative.sourceFields source k i ≠ HierarchySelectedSource.old source k (HierarchyPrefix.old k (HierarchySelectedSource.p source) (HierarchySelectedSource.q source) (HierarchyFramedInput.old k (HierarchyReduction.xTape k))) := by
    intro i he
    fin_cases i
    · exact HierarchyStreams.source_distinct source k _ (congrArg (HierarchySourceInput.slots source k) he)
    all_goals
      apply dimAway _
      exact HierarchySelectedSource.old_injective source k he
  have fieldsAway : ∀ i, ColdNative.fields source k i ≠ ColdOracle.sourceSlots source k (HierarchySelectedSource.old source k (HierarchyPrefix.old k (HierarchySelectedSource.p source) (HierarchySelectedSource.q source) (HierarchyFramedInput.old k (HierarchyReduction.xTape k)))) := by
    intro i
    refine Fin.addCases (m:=4) (n:=1) (fun j => ?_) (fun j => ?_) i
    · intro he
      apply selectedAway j
      have hv := congrArg Fin.val he
      simp only [ColdNative.fields, Fin.addCases_left, Function.comp_apply] at hv
      exact Fin.ext hv
    · intro he
      have hv := congrArg Fin.val he
      simp only [ColdNative.fields, Fin.addCases_right] at hv
      have hi := (HierarchySelectedSource.old source k (HierarchyPrefix.old k (HierarchySelectedSource.p source) (HierarchySelectedSource.q source) (HierarchyFramedInput.old k (HierarchyReduction.xTape k)))).isLt
      change HierarchySelectedSource.tapes source k + 8 + 4 + 1299 = (HierarchySelectedSource.old source k (HierarchyPrefix.old k (HierarchySelectedSource.p source) (HierarchySelectedSource.q source) (HierarchyFramedInput.old k (HierarchyReduction.xTape k)))).val at hv
      omega
  have nativeAway : ∀ i, ColdNative.slots source a k D G i ≠ ColdNative.old source a k D G (ColdOracle.sourceSlots source k (HierarchySelectedSource.old source k (HierarchyPrefix.old k (HierarchySelectedSource.p source) (HierarchySelectedSource.q source) (HierarchyFramedInput.old k (HierarchyReduction.xTape k))))) :=
    NativePipeline.Dock.outside a D G (ColdNative.fields source k) _ fieldsAway
  exact nativeAway

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdNative
