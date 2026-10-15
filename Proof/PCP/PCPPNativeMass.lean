import Proof.PCP.PCPPNativeOracleScalars
import Proof.PCP.PCPSerializerMassReady

/-! Paid byte measurement on the original hierarchy query stream, with
the original actual R*Q count. The existing scan restores both cursors. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeMass
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem query_run (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width ≤ R) (hQ : p.queries ≤ Q) :
    let fields := QueryBytes.framedCodes (normalizedRows p R Q).flatten
    ∃ result sourceLog massLog,
      runFrom PCPSerializerCapacity.MassReady.machine (16*fields.length+18)
        (PCPSerializerCapacity.MassReady.cfg PCPSerializerCapacity.MassReady.machine.start fields 0 0 (R*Q) 0 0)=some result ∧
      result.steps ≤ 16*fields.length+18 ∧
      result.final=PCPSerializerCapacity.MassReady.cfg PCPSerializerCapacity.MassReady.finalCode fields 0 fields.length (R*Q) sourceLog massLog := by
  intro fields
  have hcount : ((normalizedRows p R Q).flatten.map Nat.bits).length=R*Q := by
    rw [List.length_map,Streams.query_count p R Q hR hQ]
  obtain ⟨result,sl,ml,hr,hs,hf⟩ := PCPSerializerCapacity.MassReady.bounded_run []
    ((normalizedRows p R Q).flatten.map Nat.bits) []
  rw [hcount] at hr hf
  simp only [List.nil_append,List.append_nil,List.length_nil] at hr hf
  exact ⟨result,sl,ml,hr,hs,hf⟩

def padding (count : ℕ) (i : Fin 5) := if i=2 then count+2 else 0
noncomputable def templateCfg {s : ℕ} (q : Fin s) (source : List Bool) (mass count sourceLog massLog : ℕ) : Configuration 5 s :=
  ZeroPadding.config (padding count) (PCPSerializerCapacity.MassReady.cfg q source 0 mass count sourceLog massLog)

theorem template_input (fields : List (List Bool)) :
    (templateCfg PCPSerializerCapacity.MassReady.machine.start (FieldList.stream fields) 0 fields.length 0 0).tapes=
      ![FieldList.stream fields,[],UnaryTemplate.tape fields.length,[],[]] ∧
    (templateCfg PCPSerializerCapacity.MassReady.machine.start (FieldList.stream fields) 0 fields.length 0 0).heads=![0,0,1,0,0] := by
  constructor
  · funext i; fin_cases i <;>
      simp [templateCfg,PCPSerializerCapacity.MassReady.cfg,padding,ZeroPadding.config,ZeroPadding.pad,UnaryTemplate.tape,
        VerifierDecoding.CompareMachine.word]
  · rfl

theorem template_run (fields : List (List Bool)) : ∃ result sourceLog massLog,
    runFrom PCPSerializerCapacity.MassReady.machine (16*(FieldList.stream fields).length+18)
      (templateCfg PCPSerializerCapacity.MassReady.machine.start (FieldList.stream fields) 0 fields.length 0 0)=some result ∧
    result.steps ≤ 16*(FieldList.stream fields).length+18 ∧
    result.final=templateCfg PCPSerializerCapacity.MassReady.finalCode (FieldList.stream fields)
      (FieldList.stream fields).length fields.length sourceLog massLog := by
  obtain ⟨base,sl,ml,hb,bs,bf⟩ := PCPSerializerCapacity.MassReady.bounded_run [] fields []
  simp only [List.nil_append,List.append_nil,List.length_nil] at hb bf
  obtain ⟨result,hr,hf,hs,_⟩ := ZeroPadding.run_config PCPSerializerCapacity.MassReady.machine (padding fields.length) _ _ base hb
  exact ⟨result,sl,ml,hr,hs.trans_le bs,by rw [hf,bf]; rfl⟩

end NearCubicWires.RepairOrdinary.PCPPNativeMass
