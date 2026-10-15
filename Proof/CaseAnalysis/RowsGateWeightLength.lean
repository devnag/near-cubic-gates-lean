import Proof.CaseAnalysis.RowsGateGuardPorts

/-! Measure the retained native weights with the existing append-only copier.
This paid scan counts bytes, never expands integer magnitudes, and does not
reparse the canonical gate. Its exact count feeds original description guards. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateWeightLength
open LocalBitMultitape RecoveryExecution CanonicalWitnessCodec SupplierPipeline RepairRepresentation
open CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := AppendOutputLength.machine (preparedMachine false) 2
def input (fields : List (Bool×List Bool)) (membership : List Bool) :=
  AppendOutputLength.input (AppendOutputLength.input (CloseoutRowsGateSupport.input fields membership))
def budget (w count : ℕ) := 2*preparedBudget w count+2

theorem unfiltered (fields : List (Bool×List Bool)) (membership : List Bool) :
    (List.range fields.length).flatMap (emission false fields membership)=fields.flatMap fieldWord := by
  change (List.range fields.length).flatMap (fun j=>fieldWord (fields.getD j (false,[])))=_
  exact CloseoutRowsFamilyLoop.flatMap_index fields (false,[]) fieldWord

theorem measured_run (fields : List (Bool×List Bool)) (membership : List Bool) (w : ℕ)
    (hw : ∀ field∈fields,field.2.length ≤ w) : ∃ out,
    ClockJoin.ReadyRun machine (budget w fields.length) (input fields membership) out ∧
      out 2=fields.flatMap fieldWord ∧ out 6=List.replicate (fields.flatMap fieldWord).length true := by
  obtain ⟨a,ha,as,aT,aH,_flag⟩ := append_run false fields membership [] w hw
  have hi : appendEntry false fields membership []=
      initialConfiguration (preparedMachine false) (CloseoutRowsGateSupport.input fields membership) := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
  rw [hi] at ha
  obtain ⟨r,hr,rt,count,rh,rs⟩ := AppendOutputLength.length_run (preparedMachine false) 2
    (append_forward false) _ _ a ha
  have hb : 2*a.steps+2 ≤ budget w fields.length := by unfold budget;omega
  have more := run_moreFuel machine _ (budget w fields.length-(2*a.steps+2)) (input fields membership) r hr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r.final.tapes,⟨r,more,rfl,rh,rs.le.trans hb⟩,?_,?_⟩
  · exact (rt 2).trans (by simpa only [List.nil_append,unfiltered] using aT)
  · change r.final.tapes (((0 : Fin 1).natAdd 6).castAdd 1)=_
    rw [count,aH,List.nil_append,unfiltered]

theorem gate_description {n : ℕ} (g : SupportedNormalizedGate n) :
    ((List.ofFn g.gate.weight).flatMap intWord).length+(natWord g.gate.threshold.natAbs).length=
      2*g.descriptionBits+1 := by
  simp only [List.length_flatMap,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    DecompositionSource.intWord_length,DecompositionSource.natWord_length,
    SupportedNormalizedGate.descriptionBits,NormalizedThresholdGate.encodingBits,
    Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  simp only [natBitLength,intBitLength]
  ring

end NearCubicWires.RepairOrdinary.CloseoutRowsGateWeightLength
