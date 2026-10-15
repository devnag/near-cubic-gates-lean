import Proof.CaseAnalysis.WitnessOracleCapCall

/-! The actual source and decoded oracle produce the exact size verdict.
The full measured native bank survives for the original node/cache continuation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedCap
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k : ℕ):=SelectedCounters.tapes source k
abbrev tapes (k G : ℕ):=base source k+OracleCap.Call.extra G
def fields (k : ℕ) : Fin 2→Fin (base source k):=
  SelectedCounters.slots source k ∘ (![72,32] : Fin 2→Fin 75)
theorem fields_injective (k : ℕ) : Function.Injective (fields source k):=by
  intro a b h
  have hslot:(![72,32] : Fin 2→Fin 75) a=(![72,32] : Fin 2→Fin 75) b:=
    SelectedCounters.slots_injective source k h
  fin_cases a <;> fin_cases b <;> simp at hslot ⊢
def old (k G : ℕ) (i : Fin (base source k)) : Fin (tapes source k G):=OracleCap.Call.old G i
def slots (k G : ℕ) (i : Fin 75):=old source k G (SelectedCounters.slots source k i)
def flagSlot (k G : ℕ):=OracleCap.Call.flagSlot G (fields source k)
def first (k CH Cpad G : ℕ) (code : List Bool):=
  TapeEmbedding.machine (OracleCap.Call.extra G) (SelectedCounters.machine source k CH Cpad code)
def second (k G : ℕ):=OracleCap.Call.machine G (fields source k)
def machine (k CH Cpad G : ℕ) (code : List Bool):=
  Composition.machine (first source k CH Cpad G code) (second source k G)
def input (k G : ℕ) (x raw : List Bool):=OracleCap.Call.input G (SelectedCounters.input source k x raw)
def budget (k CH Cpad G : ℕ) (code x raw : List Bool)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code x)):=
  SelectedCounters.budget source k CH Cpad code x raw oracle+1+
    OracleCap.budget G (SelectedOracle.width source k CH Cpad code x) oracle.size

theorem cap_run (k CH Cpad G : ℕ) (code x raw : List Bool) (hpad : k+3  ≤  Cpad)
    (hN : 2  ≤  x.length) (hcap : 16*raw.length  ≤  x.length)
    (hwidth : (SelectedOracle.width source k CH Cpad code x).bits.length  ≤  x.length+1)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code x))
    (hd : decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code x) (value raw)=some oracle) :
    ∃ actual,run (machine source k CH Cpad G code) (budget source k CH Cpad G code x raw oracle)
      (input source k G x raw)=some actual ∧ actual.steps  ≤  budget source k CH Cpad G code x raw oracle ∧
      (∀ j,actual.final.heads (slots source k G (PCPPNativeColdCounters.ports j))=0 ∧
        actual.final.tapes (slots source k G (PCPPNativeColdCounters.ports j))=
          PCPPNativeMetadataMass.values oracle (SelectedStreams.pcp source k CH Cpad code x)
            (SelectedStreams.queries source k CH Cpad code x) j) ∧
      actual.final.heads (slots source k G 72)=0 ∧
      actual.final.tapes (slots source k G 72)=List.replicate (SelectedOracle.width source k CH Cpad code x) true ∧
      actual.final.heads (flagSlot source k G)=0 ∧
      actual.final.tapes (flagSlot source k G)=[decide (oracle.size  ≤  RecoveryScheduleEnvelope.oracleSizeBound G
        (SelectedOracle.width source k CH Cpad code x))]:=by
  obtain ⟨a,ha,asteps,af,ah72,at72⟩:=SelectedCounters.counters_run source k CH Cpad code x raw hpad hN hcap hwidth oracle hd
  let lifted:=TapeEmbedding.receipt (fun _ : Fin (OracleCap.Call.extra G)=>0) (fun _=>[]) a
  have hfirst:=TapeEmbedding.run_embed (SelectedCounters.machine source k CH Cpad code)
    (fun _ : Fin (OracleCap.Call.extra G)=>0) (fun _=>[]) _ _ a ha
  have hh (j : Fin 2) : a.final.heads (fields source k j)=0:=by
    fin_cases j
    · exact ah72
    · exact (af 1).1
  obtain ⟨b,hb,bs,bkeep,bfh,bft⟩:=OracleCap.Call.call_run G (fields source k) (fields_injective source k)
    a.final.tapes a.final.heads (SelectedOracle.width source k CH Cpad code x) oracle.size hh at72 (af 1).2
  have he:=MatrixPacketBranch.restart_fields (second source k G) lifted.final
    (OracleCap.Call.heads G a.final.heads) (OracleCap.Call.input G a.final.tapes) rfl rfl
  dsimp only [second,RecoveryCalls.restarted] at he
  rw [he] at hb
  have hall:=Composition.run_join (first source k CH Cpad G code) (second source k G) _ _ _ lifted b hfirst hb
  rw [MatrixWilliamsProduct.initial_join (SelectedCounters.machine source k CH Cpad code)
    (second source k G) (SelectedCounters.input source k x raw)] at hall
  refine ⟨Composition.joinedReceipt lifted b,hall,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps  ≤  budget source k CH Cpad G code x raw oracle
    exact Nat.add_le_add (Nat.add_le_add_right asteps 1) bs
  · intro j
    rw [PCPTripleGlobal.joined_heads,PCPTripleGlobal.joined_tapes]
    exact ⟨(bkeep _).1.trans (af j).1,(bkeep _).2.trans (af j).2⟩
  · rw [PCPTripleGlobal.joined_heads]
    exact (bkeep _).1.trans ah72
  · rw [PCPTripleGlobal.joined_tapes]
    exact (bkeep _).2.trans at72
  · rw [PCPTripleGlobal.joined_heads]
    exact bfh
  · rw [PCPTripleGlobal.joined_tapes]
    exact bft

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedCap
