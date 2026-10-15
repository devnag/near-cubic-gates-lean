import Proof.CaseAnalysis.WitnessSelectedCountersLayout
import Proof.MachineModel.OrdinaryMatrixWilliamsProduct

/-! The actual input and decoded oracle now produce the complete original
native metadata and measured source counts. The retained size and arity
counters feed the exact cap guard before the node/cache continuation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedCounters
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def budget (k CH Cpad : ℕ) (code x raw : List Bool)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code x)):=
  SelectedStreams.budget source k CH Cpad code x raw+1+
    PCPPNativeColdCounters.budget (SelectedStreams.pcp source k CH Cpad code x)
      (SelectedOracle.width source k CH Cpad code x) (SelectedStreams.queries source k CH Cpad code x) oracle.size

theorem counters_run (k CH Cpad : ℕ) (code x raw : List Bool) (hpad : k+3  ≤  Cpad)
    (hN : 2  ≤  x.length) (hcap : 16*raw.length  ≤  x.length)
    (hwidth : (SelectedOracle.width source k CH Cpad code x).bits.length  ≤  x.length+1)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code x))
    (hd : decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code x) (value raw)=some oracle) :
    ∃ actual,run (machine source k CH Cpad code) (budget source k CH Cpad code x raw oracle)
      (input source k x raw)=some actual ∧ actual.steps  ≤  budget source k CH Cpad code x raw oracle ∧
      (∀ j,actual.final.heads (slots source k (PCPPNativeColdCounters.ports j))=0 ∧
        actual.final.tapes (slots source k (PCPPNativeColdCounters.ports j))=
          PCPPNativeMetadataMass.values oracle (SelectedStreams.pcp source k CH Cpad code x)
            (SelectedStreams.queries source k CH Cpad code x) j) ∧
      actual.final.heads (slots source k 72)=0 ∧
      actual.final.tapes (slots source k 72)=List.replicate (SelectedOracle.width source k CH Cpad code x) true:=by
  obtain ⟨a,ha,asteps,af,abits,_,_,adesh,ades⟩:=
    SelectedStreams.stream_run source k CH Cpad code x raw hpad hN hcap hwidth
  let lifted:=TapeEmbedding.receipt (fun _ : Fin 75=>0) (fun _=>[]) a
  have hfirst:=TapeEmbedding.run_embed (SelectedStreams.machine source k CH Cpad code)
    (fun _ : Fin 75=>0) (fun _=>[]) _ _ a ha
  have hn:1  ≤  (HierarchySelectedSource.request (HierarchyPadding.rawInput k CH Cpad code x)).1:=by
    have hl:=(HierarchyPadding.linear_length k CH Cpad code x hpad).1
    change 1  ≤  (HierarchyPadding.rawInput k CH Cpad code x).length
    omega
  obtain ⟨b,hb,bsteps,bf,b72h,b72t⟩:=PCPPNativeColdCounters.counters_run oracle
    (SelectedStreams.pcp source k CH Cpad code x) (SelectedStreams.queries source k CH Cpad code x)
    (Dimensions.width_fits source _ hn) (Dimensions.queries_fit source _ hn)
  have hdata:=dock_input source k CH Cpad code x oracle a af abits ⟨adesh,ades oracle hd⟩
  obtain ⟨c,hc,_,cs,ch,ct,_⟩:=RecoveryFocus.dock (slots source k) (slots_injective source k)
    PCPPNativeColdCounters.machine _ lifted.final.heads lifted.final.tapes
    (PCPPNativeColdCounters.entry (PCPPNative.descriptor oracle) (SelectedStreams.pcp source k CH Cpad code x)
      (SelectedOracle.width source k CH Cpad code x) (SelectedStreams.queries source k CH Cpad code x))
    (fun i=>(hdata i).1) (fun i=>(hdata i).2) b hb
  have hall:=Composition.run_join (first source k CH Cpad code) (second source k) _ _ _ lifted c hfirst hc
  rw [MatrixWilliamsProduct.initial_join (SelectedStreams.machine source k CH Cpad code)
    (second source k) (SelectedStreams.input source k x raw)] at hall
  refine ⟨Composition.joinedReceipt lifted c,hall,?_,?_,?_,?_⟩
  · change a.steps+1+c.steps  ≤  budget source k CH Cpad code x raw oracle
    rw [cs]
    exact Nat.add_le_add (Nat.add_le_add_right asteps 1) bsteps
  · intro j
    rw [PCPTripleGlobal.joined_heads,PCPTripleGlobal.joined_tapes]
    exact ⟨(ch _).trans (bf j).1,(ct _).trans (bf j).2⟩
  · rw [PCPTripleGlobal.joined_heads]
    exact (ch 72).trans b72h
  · rw [PCPTripleGlobal.joined_tapes]
    exact (ct 72).trans b72t

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedCounters
