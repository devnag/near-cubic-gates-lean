import Proof.CaseAnalysis.WitnessSelectedStreamsLayout
import Proof.MachineModel.OrdinaryMatrixPacketBranch

/-! Original input and raw oracle through one selected source, the complete
cold decoder and the actual query/clause producer. Width/query frames and
the typed native descriptor remain available at their physical heads. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedStreams
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def scalarValues (k CH Cpad : ℕ) (code x : List Bool) : Fin 2→ℕ:=
  ![SelectedOracle.width source k CH Cpad code x,queries source k CH Cpad code x]

theorem stream_run (k CH Cpad : ℕ) (code x raw : List Bool) (hpad : k+3  ≤  Cpad)
    (hN : 2  ≤  x.length) (hcap : 16*raw.length  ≤  x.length)
    (hb : (SelectedOracle.width source k CH Cpad code x).bits.length  ≤  x.length+1) : ∃ actual,
    run (machine source k CH Cpad code) (budget source k CH Cpad code x raw) (input source k x raw)=some actual ∧
    actual.steps  ≤  budget source k CH Cpad code x raw ∧
    StreamCall.Fields (fields source k) (pcp source k CH Cpad code x)
      (SelectedOracle.width source k CH Cpad code x) (queries source k CH Cpad code x) actual.final ∧
    (∀ i,actual.final.heads (old source k (bits source k i))=0 ∧
      actual.final.tapes (old source k (bits source k i))=frame (scalarValues source k CH Cpad code x i).bits) ∧
    actual.final.heads (old source k (SelectedOracle.flagSlot source k))=0 ∧
    actual.final.tapes (old source k (SelectedOracle.flagSlot source k))=
      [(decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code x) (value raw)).isSome] ∧
    actual.final.heads (old source k (SelectedOracle.descriptorSlot source k))=0 ∧
    (∀ c : BooleanCircuit (SelectedOracle.width source k CH Cpad code x),
      decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code x) (value raw)=some c →
      actual.final.tapes (old source k (SelectedOracle.descriptorSlot source k))=PCPPNative.descriptor c):=by
  obtain ⟨prior,hp,hf,hw,hflag,hdesc⟩:=SelectedOracle.selected_run source k CH Cpad code x raw hpad hN hcap hb
  have hfirst:=hp.focus (old source k) (StreamCall.old_injective _) (input source k x raw)
    (by intro i;exact StreamCall.input_old _ i)
  rw [initial_install source k x raw prior] at hfirst
  obtain ⟨a,ha,atape,ahead,asteps⟩:=hfirst
  have hsource:prior (fields source k 0)=(pcp source k CH Cpad code x).word:=hw
  have hwidth:prior (fields source k 1)=List.replicate (SelectedOracle.width source k CH Cpad code x) true:=hf.rawR
  have hqueries:prior (fields source k 2)=List.replicate (queries source k CH Cpad code x) true:=hf.rawQ
  have hn:1  ≤  (HierarchySelectedSource.request (HierarchyPadding.rawInput k CH Cpad code x)).1:=by
    have hl:=(HierarchyPadding.linear_length k CH Cpad code x hpad).1
    change 1  ≤  (HierarchyPadding.rawInput k CH Cpad code x).length
    omega
  obtain ⟨b,hbrun,bsteps,bfields,bret⟩:=StreamCall.call_run (fields source k) (fields_injective source k)
    prior (pcp source k CH Cpad code x) (SelectedOracle.width source k CH Cpad code x)
    (queries source k CH Cpad code x) hsource hwidth hqueries
    (Dimensions.width_fits source _ hn) (Dimensions.queries_fit source _ hn)
  have he:Composition.restart a.final (second source k).start=
      initialConfiguration (second source k) (StreamCall.input prior):=by
    exact (MatrixPacketBranch.restart_fields (second source k) a.final (fun _=>0)
      (StreamCall.input prior) (funext ahead) atape).symm
  have hcall:runFrom (second source k)
      (Streams.budget (pcp source k CH Cpad code x) (SelectedOracle.width source k CH Cpad code x)
        (queries source k CH Cpad code x)) (Composition.restart a.final (second source k).start)=some b:=by
    rw [he]
    exact hbrun
  have hall:=Composition.run_join (first source k CH Cpad code) (second source k) _ _ _ a b ha hcall
  have hbits (i : Fin 2) : prior (bits source k i)=frame (scalarValues source k CH Cpad code x i).bits:=by
    fin_cases i
    · exact hf.bitsR
    · exact hf.bitsQ
  have hbf:=bret (SelectedOracle.flagSlot source k)
    (parser_not_field source k Oracle.flagSlot 0) (parser_not_field source k Oracle.flagSlot 1)
    (parser_not_field source k Oracle.flagSlot 2)
  have hbd:=bret (SelectedOracle.descriptorSlot source k)
    (parser_not_field source k Oracle.descriptorSlot 0) (parser_not_field source k Oracle.descriptorSlot 1)
    (parser_not_field source k Oracle.descriptorSlot 2)
  refine ⟨Composition.joinedReceipt a b,hall,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps  ≤  budget source k CH Cpad code x raw
    exact Nat.add_le_add (Nat.add_le_add_right asteps 1) bsteps
  · constructor
    · rw [PCPTripleGlobal.joined_tapes];exact bfields.query
    · rw [PCPTripleGlobal.joined_heads];exact bfields.queryHead
    · rw [PCPTripleGlobal.joined_tapes];exact bfields.queryCount
    · rw [PCPTripleGlobal.joined_heads];exact bfields.queryCountHead
    · rw [PCPTripleGlobal.joined_tapes];exact bfields.clause
    · rw [PCPTripleGlobal.joined_heads];exact bfields.clauseHead
    · rw [PCPTripleGlobal.joined_tapes];exact bfields.clauseCount
    · rw [PCPTripleGlobal.joined_heads];exact bfields.clauseCountHead
  · intro i
    rw [PCPTripleGlobal.joined_heads,PCPTripleGlobal.joined_tapes]
    have h:=bret (bits source k i) (bits_not_fields source k i 0)
      (bits_not_fields source k i 1) (bits_not_fields source k i 2)
    exact ⟨h.1,h.2.trans (hbits i)⟩
  · rw [PCPTripleGlobal.joined_heads];exact hbf.1
  · rw [PCPTripleGlobal.joined_tapes];exact hbf.2.trans hflag
  · rw [PCPTripleGlobal.joined_heads];exact hbd.1
  · intro c hc
    rw [PCPTripleGlobal.joined_tapes]
    exact hbd.2.trans (hdesc c hc)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedStreams
