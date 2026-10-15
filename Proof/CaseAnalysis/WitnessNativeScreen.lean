import Proof.CaseAnalysis.WitnessNativeMeasured
import Proof.CaseAnalysis.WitnessOracleCapCall

/-! One post-decoder stream/counter execution supplies the exact full
oracle-size screen. Its measured native fields survive for the gated
node and faithful PCPP-source continuation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeScreen
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def fields : Fin 2 → Fin 125:=NativeMeasured.slots ∘ (![72,32] : Fin 2 → Fin 75)
def slots (G : ℕ) (i : Fin 75):=OracleCap.Call.old G (NativeMeasured.slots i)
def flagSlot (G : ℕ):=OracleCap.Call.flagSlot G fields
def first (G : ℕ):=TapeEmbedding.machine (OracleCap.Call.extra G) NativeMeasured.machine
def second (G : ℕ):=OracleCap.Call.machine G fields
def machine (G : ℕ):=Composition.machine (first G) (second G)
def input (G : ℕ) {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ):=
  OracleCap.Call.input G (NativeMeasured.input oracle p Q)
def budget (G : ℕ) (p : RawProjectionPCP) (R Q size : ℕ):=
  NativeMeasured.budget p R Q size+1+OracleCap.budget G R size

theorem fields_injective : Function.Injective fields:=
  NativeMeasured.slots_injective.comp (by decide : Function.Injective (![72,32] : Fin 2 → Fin 75))
theorem slots_injective (G : ℕ) : Function.Injective (slots G):=by
  intro i j h
  apply NativeMeasured.slots_injective
  exact Fin.ext (congrArg (fun z : Fin (125+OracleCap.Call.extra G)=>z.val) h)

theorem screen_run (G : ℕ) {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ)
    (hR : p.width ≤ R) (hQ : p.queries ≤ Q) :
    ∃ actual,run (machine G) (budget G p R Q oracle.size) (input G oracle p Q)=some actual ∧
      actual.steps ≤ budget G p R Q oracle.size ∧
      (∀ j,actual.final.heads (slots G (PCPPNativeColdCounters.ports j))=0 ∧
        actual.final.tapes (slots G (PCPPNativeColdCounters.ports j))=PCPPNativeMetadataMass.values oracle p Q j) ∧
      actual.final.heads (slots G 72)=0 ∧ actual.final.tapes (slots G 72)=List.replicate R true ∧
      actual.final.heads (flagSlot G)=0 ∧
      actual.final.tapes (flagSlot G)=[decide (oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound G R)]:=by
  obtain ⟨a,ha,as,af,ah,atape⟩:=NativeMeasured.measured_run oracle p Q hR hQ
  let lifted:=TapeEmbedding.receipt (fun _ : Fin (OracleCap.Call.extra G)=>0) (fun _=>[]) a
  have firstRun:=TapeEmbedding.run_embed NativeMeasured.machine
    (fun _ : Fin (OracleCap.Call.extra G)=>0) (fun _=>[]) _ _ a ha
  rw [StreamPrepare.embed_initial] at firstRun
  obtain ⟨last,lastRun,lastSteps,keep,lastHead,lastFlag⟩:=OracleCap.Call.call_run G fields fields_injective
    a.final.tapes a.final.heads R oracle.size (by intro j;fin_cases j;exact ah;exact (af 1).1)
    atape (af 1).2
  have whole:=Composition.run_join (first G) (second G) _ _ _ lifted last firstRun lastRun
  refine ⟨Composition.joinedReceipt lifted last,whole,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+last.steps ≤ budget G p R Q oracle.size
    exact Nat.add_le_add (Nat.add_le_add_right as 1) lastSteps
  · intro j
    exact ⟨(keep _).1.trans (af j).1,(keep _).2.trans (af j).2⟩
  · exact (keep _).1.trans ah
  · exact (keep _).2.trans atape
  · exact lastHead
  · exact lastFlag

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeScreen
