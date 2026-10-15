import Proof.MachineModel.CountIndexPadded
import Proof.CaseAnalysis.RowsMetadataCopy

/-! The same physical last-row index fills both native fields. The paid
shared driver copies it once; all local work extents stay within that driver. -/
namespace NearCubicWires.ExtIncidence.CountIndexCopy
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 15) : Fin 18:=i.castAdd 3
def slots : Fin 4→Fin 18:=![11,15,16,17]
def extra (C : ℕ) : Fin 3→List Bool:=
  ![List.replicate C false,List.replicate C true,List.replicate (C+1) false]
def input (C w M : ℕ) : Fin 18→List Bool:=Fin.addCases (m:=15) (n:=3) (motive:=fun _=>List Bool) (CountIndex.padded C w M) (extra C)
noncomputable def count:=TapeEmbedding.machine 3 CountIndex.machine
noncomputable def copy:=RecoveryFocus.machine slots RecoveryBoundedTapeCopy.machine
noncomputable def machine:=Composition.machine count copy
def budget (C w M : ℕ):=CountIndex.budget w M+2*C+5

theorem copy_run (C w M : ℕ) (hM : 0<M) (hw : M<2^w)
    (hC : CountIndex.budget w M+1≤C) : ∃ out,
    ClockJoin.ReadyRun machine (budget C w M) (input C w M) out ∧
      out 10=ZeroPadding.pad C (List.replicate w true) ∧
      out 11=ZeroPadding.pad C (frame (binary w (M-1))) ∧
      out 15=out 11 ∧ out 16=List.replicate C true ∧
      out 17=List.replicate (C+1) false ∧
      (∀ i,i≠17 → (out i).length≤C) := by
  obtain ⟨a,ca,a10,a11,ab⟩:=CountIndex.padded_run C w M hM hw hC
  let A : Fin 18→List Bool:=Fin.addCases (m:=15) (n:=3) (motive:=fun _=>List Bool) a (extra C)
  have copyReady:=CloseoutRowsMetadataCopy.copy_ready (a 11) C (ab 11)
  have focused:=copyReady.focus slots (by decide) A (by intro i;fin_cases i <;> rfl)
  let out:=install slots A (CloseoutRowsMetadataCopy.output (a 11) C)
  have cp : ClockJoin.ReadyRun copy (2*C+4) A out:=by
    obtain ⟨r,hr,rt,rh,rs⟩:=focused
    exact ⟨r,hr,rt,rh,rs.le⟩
  have countReady : ClockJoin.ReadyRun count (CountIndex.budget w M) (input C w M) A:=by
    obtain ⟨r,hr,rt,rh,rs⟩:=ca
    have he:=TapeEmbedding.run_embed CountIndex.machine (fun _ : Fin 3=>0) (extra C) _ _ r hr
    refine ⟨TapeEmbedding.receipt (fun _=>0) (extra C) r,?_,?_,?_,rs⟩
    · have hi : TapeEmbedding.config (fun _ : Fin 3=>0) (extra C)
          (initialConfiguration CountIndex.machine (CountIndex.padded C w M))=
          initialConfiguration count (input C w M):=by
        apply configuration_ext
        · rfl
        · funext i
          refine Fin.addCases (m:=15) (n:=3) (fun j=>?_) (fun j=>?_) i
          · simp only [TapeEmbedding.config,initialConfiguration,Fin.addCases_left]
          · simp only [TapeEmbedding.config,initialConfiguration,Fin.addCases_right]
        · rfl
      rw [hi] at he
      exact he
    · change Fin.addCases (m:=15) (n:=3) (motive:=fun _=>List Bool) r.final.tapes (extra C)=A
      rw [rt]
    · intro i
      refine Fin.addCases (m:=15) (n:=3) (fun j=>?_) (fun j=>?_) i
      · simpa only [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left] using rh j
      · simp only [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]
  have whole:=ClockJoin.join count copy _ _ _ _ _ countReady cp
  have ht : CountIndex.budget w M+1+(2*C+4)=budget C w M:=by unfold budget;omega
  rw [ht] at whole
  have o11 : out 11=a 11:=install_slot slots (by decide) A _ 0
  have o15 : out 15=ZeroPadding.pad C (a 11):=install_slot slots (by decide) A _ 1
  have o16 : out 16=List.replicate C true:=install_slot slots (by decide) A _ 2
  have o17 : out 17=List.replicate (C+1) false:=install_slot slots (by decide) A _ 3
  refine ⟨out,whole,(install_other slots A _ 10 (by decide)).trans a10,o11.trans a11,
    ?_,o16,o17,?_⟩
  · rw [o15,o11,a11]
    exact MatrixBucketRootPower.pad_pad C C _ le_rfl
  · intro i hi
    by_cases inside : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=inside
      fin_cases j
      · change (out 11).length≤C
        rw [o11];exact ab 11
      · change (out 15).length≤C
        rw [o15,ZeroPadding.pad_length];exact max_le le_rfl (ab 11)
      · change (out 16).length≤C
        rw [o16,List.length_replicate]
      · exact False.elim (hi rfl)
    · rw [show out i=A i from install_other slots A _ i (by simpa only [not_exists] using inside)]
      revert hi
      refine Fin.addCases (m:=15) (n:=3) (fun j=>?_) (fun j=>?_) i
      · intro _
        simpa only [A,Fin.addCases_left] using ab j
      · intro hi
        simp only [A,Fin.addCases_right]
        fin_cases j
        · change (List.replicate C false).length≤C
          simp only [List.length_replicate,le_refl]
        · change (List.replicate C true).length≤C
          simp only [List.length_replicate,le_refl]
        · exact False.elim (hi rfl)

end NearCubicWires.ExtIncidence.CountIndexCopy
