import Proof.CaseAnalysis.WitnessOracleCallRun
import Proof.Hierarchy.HierarchySelectedSource
import Proof.PCP.ProjectionDimensionCanonical

/-! Original input and raw oracle guess through the one selected PCP call,
then the cold oracle decoder. The exact source bank survives for the native
PCPP continuation, so neither the hierarchy nor the source is run twice. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedOracle
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k : ℕ):=HierarchySelectedSource.tapes source k
abbrev tapes (k : ℕ):=OracleCall.tapes (base source k)
def old (k : ℕ) : Fin (base source k)→Fin (tapes source k):=OracleCall.old
def fields (k : ℕ) : Fin 3→Fin (base source k):=
  ![HierarchySelectedSource.old source k
      (HierarchyPrefix.old k (HierarchySelectedSource.p source) (HierarchySelectedSource.q source)
        (HierarchyFramedInput.old k (HierarchyReduction.xTape k))),
    HierarchySelectedSource.old source k
      (HierarchySelectedSource.dimension source k (DimensionsFromInput.bitsR
        (HierarchySelectedSource.p source) (HierarchySelectedSource.q source))),
    HierarchySelectedSource.old source k
      (HierarchySelectedSource.dimension source k (DimensionsFromInput.rawR
        (HierarchySelectedSource.p source) (HierarchySelectedSource.q source)))]
def width (k CH Cpad : ℕ) (code x : List Bool):=
  Dimensions.width source (HierarchyPadding.rawInput k CH Cpad code x).length
def input (k : ℕ) (x bits : List Bool):=OracleCall.input (HierarchySelectedSource.input source k x) bits
def first (k CH Cpad : ℕ) (code : List Bool):=
  RecoveryFocus.machine (old source k) (HierarchySelectedSource.machine source k CH Cpad code)
def second (k : ℕ):=OracleCall.machine (fields source k)
def machine (k CH Cpad : ℕ) (code : List Bool):=Composition.machine (first source k CH Cpad code) (second source k)
def budget (k CH Cpad : ℕ) (code x bits : List Bool):=
  HierarchySelectedSource.budget source k CH Cpad code x+1+
    OracleCall.budget x bits (width source k CH Cpad code x).bits
def flagSlot (k : ℕ):=OracleCall.parserSlots (base source k) Oracle.flagSlot
def descriptorSlot (k : ℕ):=OracleCall.parserSlots (base source k) Oracle.descriptorSlot

theorem initial_install (k : ℕ) (x bits : List Bool) (prior : Fin (base source k)→List Bool) :
    install (old source k) (input source k x bits) prior=OracleCall.input prior bits:=by
  funext i
  refine Fin.addCases (m:=base source k) (n:=1385) ?_ ?_ i
  · intro j
    change install (old source k) _ _ (old source k j)=_
    rw [install_slot (old source k) (OracleCall.old_injective _)]
    exact (OracleCall.input_old prior bits j).symm
  · intro j
    rw [install_other _ _ _ _ (by
      intro l hl
      exact OracleCall.old_ne_extra l j hl)]
    simp only [input,OracleCall.input,Fin.addCases_right]

theorem selected_run (k CH Cpad : ℕ) (code x bits : List Bool) (hpad : k+3  ≤  Cpad)
    (hN : 2  ≤  x.length) (hcap : 16*bits.length  ≤  x.length)
    (hb : (width source k CH Cpad code x).bits.length  ≤  x.length+1) : ∃ out,
    ClockJoin.ReadyRun (machine source k CH Cpad code) (budget source k CH Cpad code x bits)
      (input source k x bits) out ∧
    HierarchySelectedSource.Fields source k CH Cpad code x
      (out ∘ old source k ∘ HierarchySelectedSource.old source k) ∧
    out (old source k (HierarchySelectedSource.outputTape source k))=
      (source.output (HierarchySelectedSource.request (HierarchyPadding.rawInput k CH Cpad code x))).word ∧
    out (flagSlot source k)=[(decodeBooleanCircuit (width source k CH Cpad code x) (value bits)).isSome] ∧
    (∀ c : BooleanCircuit (width source k CH Cpad code x),
      decodeBooleanCircuit (width source k CH Cpad code x) (value bits)=some c →
      out (descriptorSlot source k)=PCPPNative.descriptor c):=by
  obtain ⟨prior,hp,hf,hw⟩:=HierarchySelectedSource.selected_run source k CH Cpad code x hpad
  have hfirst:=hp.focus (old source k) (OracleCall.old_injective _) (input source k x bits)
    (by intro i;exact OracleCall.input_old _ _ i)
  rw [initial_install source k x bits prior] at hfirst
  have hx:prior (fields source k 0)=frame x:=hf.input
  have hqb:prior (fields source k 1)=frame (width source k CH Cpad code x).bits:=hf.bitsR
  have hqr:prior (fields source k 2)=List.replicate (value (width source k CH Cpad code x).bits) true:=by
    rw [DimensionProducer.bits_value]
    exact hf.rawR
  obtain ⟨out,hc,hret,hflag,hdesc⟩:=OracleCall.call_run (fields source k) prior bits x
    (width source k CH Cpad code x).bits hx hqb hqr hN hcap hb
  rw [DimensionProducer.bits_value] at hflag hdesc
  have he:out ∘ old source k=prior:=funext hret
  refine ⟨out,ClockJoin.join (first source k CH Cpad code) (second source k) _ _ _ _ _ hfirst hc,?_,?_,?_,?_⟩
  · change HierarchySelectedSource.Fields source k CH Cpad code x
      ((out ∘ old source k) ∘ HierarchySelectedSource.old source k)
    rw [he]
    exact hf
  · exact (hret _).trans hw
  · exact hflag
  · exact hdesc

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedOracle
