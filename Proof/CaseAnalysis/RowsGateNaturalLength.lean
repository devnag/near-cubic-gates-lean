import Proof.CaseAnalysis.RowsGateWeightLength

/-! Measure the retained original threshold natWord using the existing
native field copier and append-cursor count. Only its bit length is unary. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateNaturalLength
open LocalBitMultitape RecoveryExecution RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := AppendOutputLength.machine (PCPPQueryField.machine true) 2
def input (n : ℕ) : Fin 5→List Bool :=
  AppendOutputLength.input (AppendOutputLength.input (![natWord n,[],[]] : Fin 3→List Bool))

theorem forward : CursorRestore.NoLeft (PCPPQueryField.machine true) 2 := by
  intro q bits a ha
  simp only [PCPPQueryField.machine] at ha
  split_ifs at ha <;> cases ha <;> simp

theorem measured_run (n : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (4*natBitLength n+8) (input n) out ∧
      out 0=natWord n ∧ out 2=natWord n ∧ out 3=List.replicate (natWord n).length true := by
  obtain ⟨a,ha,af,as⟩ := PCPPQueryField.nat_run true [] [] [] [] n
  have ha' : run (PCPPQueryField.machine true) (2*natBitLength n+3) ![natWord n,[],[]]=some a := by
    have hi : PCPPQueryField.cfg 0 (natWord n) 0 [] 0 []=
        initialConfiguration (PCPPQueryField.machine true) ![natWord n,[],[]] := by
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> rfl
      · rfl
    simpa only [LocalBitMultitape.run,List.nil_append,List.append_nil,List.length_nil,hi] using ha
  obtain ⟨r,hr,rt,count,rh,rs⟩ := AppendOutputLength.length_run (PCPPQueryField.machine true) 2 forward
    _ _ a ha'
  have he : 2*a.steps+2=4*natBitLength n+8 := by rw [as];omega
  rw [he] at hr rs
  refine ⟨r.final.tapes,⟨r,hr,rfl,rh,rs.le⟩,?_,?_,?_⟩
  · exact (rt 0).trans (by rw [af];simp [PCPPQueryField.payload,PCPPQueryField.cfg,PCPPQueryField.selected])
  · exact (rt 2).trans (by rw [af];simp [PCPPQueryField.payload,PCPPQueryField.cfg,PCPPQueryField.selected])
  · change r.final.tapes (((0 : Fin 1).natAdd 3).castAdd 1)=_
    rw [count,af]
    rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsGateNaturalLength
