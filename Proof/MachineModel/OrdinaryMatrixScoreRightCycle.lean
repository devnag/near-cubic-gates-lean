import Proof.MachineModel.OrdinaryMatrixScoreRightRecord
import Proof.MachineModel.OrdinaryMatrixScoreLeftCycle

/-! Actual right-record cycle with paid masked cursor return. Its counter
shares the already retained left-body bound across the two halves. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreRightCycle
open LocalBitMultitape SignedSortKey MatrixScoreLeftCycle
open MatrixScoreWeight (zeros scalar)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 26) : Bool := decide (i=0 ∨ i=1)
noncomputable def machine := MaskedReset.machine MatrixScoreRightRecord.machine selected
def budget (d p s c m : ℕ) := 2*MatrixScoreRightRecord.budget d p s c m+2
theorem record_le_left (d p s c m : ℕ) : MatrixScoreRightRecord.budget d p s c m≤MatrixScoreLeftRecord.budget d p s c m := by
  unfold MatrixScoreRightRecord.budget MatrixScoreRight.budget MatrixScoreLeftRecord.budget
    MatrixScoreLeft.budget MatrixScoreLinear.budget
  omega

theorem cycle_run (weights right : List ℤ) (suffix : List Bool)
    (p n s c cap m id template returnCap : ℕ) (work : Fin 12 → List Bool) (driver counter out : List Bool)
    (hlen : right.length=weights.length)
    (hf : ∀ z ∈ right,z.natAbs<2^p)
    (hw : p≤ s+1) (hc : 4*(s+1)+5≤c) (hm : 2*m≤c) (hcap : cap≤c+1)
    (hs : ∀ i,(work i).length≤c)
    (hrcap : returnCap≤MatrixScoreLeftRecord.budget weights.length p s c m)
    (hp : MatrixScoreBatch.part false right n<2^s)
    (hn : MatrixScoreBatch.part true right n<2^s) :
    ∃ finalWork : Fin 12 → List Bool,(∀ i,(finalWork i).length≤c) ∧
      ∃ finalCap : ℕ,finalCap≤MatrixScoreLeftRecord.budget weights.length p s c m ∧
      ∃ actual,runFrom machine (budget weights.length p s c m)
        (RecoveryCalls.restarted machine (heads out.length)
          (tapes (MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++suffix)
            (frame (binary weights.length n)) weights.length c cap (s+1) (2^s) m id template work driver counter out returnCap))=some actual ∧
        actual.final.heads=heads (out++StablePartition.recordBits (encode s m (MatrixScoreBatch.linearForm right n) id)).length ∧
        actual.final.tapes=tapes
          (MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++suffix)
          (frame (binary weights.length n)) weights.length c (c+1) (s+1) (2^s) m id template finalWork
          driver counter
          (out++StablePartition.recordBits (encode s m (MatrixScoreBatch.linearForm right n) id)) finalCap ∧
        actual.steps≤budget weights.length p s c m := by
  let source := MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++suffix
  let assignment := frame (binary weights.length n)
  obtain ⟨finalWork,hws,_,body,hb,bh,bt,bs⟩ := MatrixScoreRightRecord.right_record_run weights right [] suffix [] []
    p n s c cap m id template work driver counter out hlen hf hw hc hm hcap hs hp hn
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hb bh bt
  let input := RecoveryCalls.restarted MatrixScoreRightRecord.machine (MatrixScoreRecordDock.heads 0 0 out.length)
    (MatrixScoreRecordDock.tapes source assignment weights.length c cap (s+1) (2^s) m id template work driver counter out)
  have hhead (i : Fin 26) (hi : selected i=true) : body.final.heads i≤body.steps := by
    have h := SelectiveReset.prefix_head (prefix_of_run MatrixScoreRightRecord.machine _ input body hb).1 i
    have hs0 : input.heads i=0 := by
      have disj : i=0 ∨ i=1 := by simpa only [selected,decide_eq_true_eq] using hi
      rcases disj with rfl | rfl <;> rfl
    simpa only [hs0,Nat.zero_add] using h
  obtain ⟨base,hr,hfFinal,hrs,_⟩ := MaskedReset.reset_run MatrixScoreRightRecord.machine selected _ input body hb hhead
  obtain ⟨actual,ha,haf,has,_⟩ := ZeroPadding.run_config machine (Rewind.Workspace.capacities 26 returnCap) _ _ base hr
  have hi : ZeroPadding.config (Rewind.Workspace.capacities 26 returnCap) (Rewind.recording input 0)=
      RecoveryCalls.restarted machine (heads out.length)
        (tapes source assignment weights.length c cap (s+1) (2^s) m id template work driver counter out returnCap) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,Rewind.Workspace.capacities,Rewind.recording,Rewind.config,input,
        RecoveryCalls.restarted,tapes,Fin.addCases,ZeroPadding.pad,zeros]
  rw [hi] at ha
  have hbnd : 2*body.steps+2≤budget weights.length p s c m := by unfold budget; omega
  have he := runFrom_moreFuel machine (2*body.steps+2) (budget weights.length p s c m-(2*body.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hbnd] at he
  have hf' : actual.final=SelectiveReset.finished
      (fun i => if selected i then 0 else body.final.heads i) body.final.tapes (max returnCap body.steps) := by
    rw [haf,hfFinal,SelectiveReset.padded_finished]
  refine ⟨finalWork,hws,max returnCap body.steps,max_le hrcap (bs.trans (record_le_left _ _ _ _ _)),actual,he,?_,?_,?_⟩
  · rw [hf',bh]
    funext i
    fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,selected,heads,MatrixScoreRecordDock.heads,
      MatrixScoreLeftFields.heads,MatrixScoreFoldEntry.heads,Fin.addCases]
  · rw [hf',bt]
    rfl
  · rw [has,hrs]
    exact hbnd

end NearCubicWires.RepairOrdinary.MatrixScoreRightCycle
