import Proof.CaseAnalysis.RowsCircuitTagged

/-! Complete cold tagged-four decision from the original circuit code.
The exact mode/count/bottom-list/top fields survive for enclosing checks. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTagged
open LocalBitMultitape RecoveryRootRound RadixSemantics CompetitorRationalProducts
open CloseoutRowsCircuitHeader RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tests (bits : List Bool) (j : Fin 5) := decide (value (tagWord bits j)=if j.val<4 then 1 else 0)
def selected (j : Fin 5) : Fin 6 := if j.val<4 then 2 else 1
def finishSlots : Fin 6→Fin 268 := ![243,248,253,258,262,267]
noncomputable def finish := RecoveryFocus.machine finishSlots CompetitorWitnessHeader.gate
noncomputable def prefixMachine := Composition.machine header classify
noncomputable def machine := Composition.machine prefixMachine finish
noncomputable def output (bits : List Bool) :=
  install finishSlots (before bits 5) (CompetitorWitnessHeader.gateOutput (tests bits))
def budget (bits : List Bool) := 51000*(bits.length+1)^2

theorem before_output (bits : List Bool) (k : ℕ) (j : Fin 5) (hk:j.val<k) (h5:k≤5) (i : Fin 6) :
    before bits k (slots j i)=result bits j i := by
  induction k with
  | zero=>omega
  | succ k ih=>
    rw [before,dif_pos (show k<5 by omega)]
    by_cases he:k=j.val
    · have hj:(⟨k,by omega⟩ : Fin 5)=j:=Fin.ext he
      rw [hj,install_slot _ (slots_injective j)]
    · rw [install_other]
      · exact ih (by omega) (by omega)
      · intro z
        exact slots_disjoint ⟨k,by omega⟩ j (by intro hh;exact he (congrArg Fin.val hh)) z i

theorem before_other (bits : List Bool) (k : ℕ) (i : Fin 268) (hi:∀ j z,slots j z≠i) :
    before bits k i=start bits i := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [before]
    split_ifs with hk
    · rw [install_other _ _ _ _ (hi _)];exact ih
    · exact ih

theorem literal_one (bits : List Bool) :
    CompetitorWitnessKind.tapes (CompetitorWitnessKind.after bits) (CompetitorWitnessKind.flags bits)
      (2*bits.length+1) 2=[decide (value bits=1)] := rfl

theorem literal_zero (bits : List Bool) :
    CompetitorWitnessKind.tapes (CompetitorWitnessKind.after bits) (CompetitorWitnessKind.flags bits)
      (2*bits.length+1) 1=[decide (value bits=0)] := rfl

theorem result_selected (bits : List Bool) (j : Fin 5) : result bits j (selected j)=[tests bits j] := by
  by_cases hj:j.val<4
  · simp only [selected,tests,if_pos hj]
    exact literal_one (tagWord bits j)
  · simp only [selected,tests,if_neg hj]
    exact literal_zero (tagWord bits j)

theorem physical_tests (bits : List Bool) (j : Fin 5) : before bits 5 (finishSlots (j.castAdd 1))=[tests bits j] := by
  have he:finishSlots (j.castAdd 1)=slots j (selected j):=by fin_cases j <;> rfl
  exact (congrArg (before bits 5) he).trans
    ((before_output bits 5 j j.isLt (by rfl) (selected j)).trans (result_selected bits j))

theorem finish_ready (bits : List Bool) : ClockJoin.ReadyRun finish 1 (before bits 5) (output bits) := by
  obtain ⟨r,hr,rt,rh,rs⟩ := CompetitorWitnessHeader.gate_ready (tests bits)
  refine (show ClockJoin.ReadyRun CompetitorWitnessHeader.gate 1 _ _ from ⟨r,hr,rt,rh,rs.le⟩).focus
    finishSlots (by decide) (before bits 5) ?_
  intro i
  fin_cases i
  · exact physical_tests bits 0
  · exact physical_tests bits 1
  · exact physical_tests bits 2
  · exact physical_tests bits 3
  · exact physical_tests bits 4
  · rw [before_other _ _ _ (by intro j z;fin_cases j <;> fin_cases z <;> decide)]
    rfl

theorem header_ready (bits : List Bool) : ClockJoin.ReadyRun header (CloseoutRowsCircuitHeader.budget bits)
    (input bits) (start bits) := by
  obtain ⟨r,hr,rt,rh,rs⟩ := CloseoutRowsCircuitHeader.header_ready bits
  have h := TapeEmbedding.run_embed CloseoutRowsCircuitHeader.machine (fun _ : Fin 26=>0) (fun _=>[]) _ _ r hr
  rw [StreamPrepare.embed_initial] at h
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 26=>0) (fun _=>[]) r,h,?_,?_,rs⟩
  · change (TapeEmbedding.config (fun _ : Fin 26=>0) (fun _=>[]) r.final).tapes=_
    simp only [TapeEmbedding.config,rt];rfl
  · intro i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · exact (TapeEmbedding.receipt_heads_old (fun _ : Fin 26=>0) (fun _=>[]) r j).trans (rh j)
    · exact TapeEmbedding.receipt_heads_new (fun _ : Fin 26=>0) (fun _=>[]) r j

theorem tagged_run (bits : List Bool) :
    ClockJoin.ReadyRun machine (budget bits) (input bits) (output bits) ∧
      (readTapeBit (output bits 267) 0=true ↔ CloseoutRowsCircuitHeader.structural bits) ∧
      ∀ j,output bits (old (port j))=frame (codeWord bits j) := by
  have hp := ClockJoin.join header classify _ _ _ _ _ (header_ready bits) (classify_ready bits)
  have all := ClockJoin.join prefixMachine finish _ _ _ _ _ hp (finish_ready bits)
  have hb:CloseoutRowsCircuitHeader.budget bits+1+(80*bits.length+139)+1+1 ≤ budget bits := by
    have h1:bits.length+1 ≤ (bits.length+1)^2:=Nat.le_self_pow (by decide) _
    have h2:1 ≤ (bits.length+1)^2:=Nat.one_le_pow _ _ (by omega)
    unfold CloseoutRowsCircuitHeader.budget budget
    omega
  refine ⟨ClockJoin.enlarge machine _ _ _ _ all hb,?_,?_⟩
  · change readTapeBit (install finishSlots _ _ (finishSlots 5)) 0=true ↔_
    rw [install_slot _ (by decide)]
    change CompetitorWitnessHeader.allTests (tests bits)=true ↔_
    simp [CompetitorWitnessHeader.allTests,tests,tagWord,CloseoutRowsCircuitHeader.structural,
      CompetitorWitnessTriple.field,CompetitorWitnessTriple.node,and_assoc]
  · intro j
    rw [output,install_other _ _ _ _ (by fin_cases j <;> decide),before_other _ _ _ (by
      intro i z;fin_cases j <;> fin_cases i <;> fin_cases z <;> decide)]
    simpa only [start,old,Fin.addCases_left] using output_fields bits j

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTagged
