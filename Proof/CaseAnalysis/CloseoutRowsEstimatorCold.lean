import Proof.CaseAnalysis.RowsEstimatorFramed
import Proof.Hierarchy.CompetitorRecordRewind

/-! Entry from the actual native bank's append cursor. The same retained
C driver pays the rewind before the cold cut/header/frame construction. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Cold
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3→Fin 70:=![52,68,69]
def input (row : EquationRow.Input) (C : ℕ) : Fin 70→List Bool:=
  fun i=>Fin.addCases (m:=68) (n:=2) (motive:=fun _=>List Bool)
    (Framed.input row) ![List.replicate C true,[]] i
def heads (row : EquationRow.Input) (i : Fin 70):=if i=52 then (Header.stream row).length else 0
noncomputable def first:=RecoveryFocus.machine slots CompetitorRecordRewind.machine
noncomputable def last:=TapeEmbedding.machine 2 Framed.machine
noncomputable def machine:=Composition.machine first last
noncomputable def entry (row : EquationRow.Input) (C : ℕ):=
  (⟨machine.start,heads row,input row C⟩ : Configuration 70 _)
def budget (row : EquationRow.Input) (C : ℕ):=(2*C+2)+1+Framed.budget row

theorem run (row : EquationRow.Input) (C : ℕ) (hC:(Header.stream row).length≤C) : ∃ actual,
    runFrom machine (budget row C) (entry row C)=some actual ∧
    actual.final.tapes 66=frame (EquationRowRaw.source row) ∧
    actual.final.tapes 68=List.replicate C true ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps≤budget row C:=by
  obtain ⟨rwrun,hr,rf,rs⟩:=CompetitorRecordRewind.rewind_run
    (Header.stream row) C (Header.stream row).length hC
  obtain ⟨before,hb,_,bs,bh,bt,keep⟩:=RecoveryFocus.dock slots (by decide)
    CompetitorRecordRewind.machine (2*C+2) (heads row) (input row C) _
    (by intro j;fin_cases j <;> rfl) (by intro j;fin_cases j <;> rfl) rwrun hr
  have allH:∀ i,before.final.heads i=0:=by
    intro i
    by_cases hs:∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [bh j,rf]
      fin_cases j <;> rfl
    · have hi:i≠52:=fun he=>hs ⟨0,he.symm⟩
      rw [(keep i (by simpa only [not_exists] using hs)).1]
      simp only [heads,hi,ite_false]
  have oldT (j : Fin 68):before.final.tapes (j.castAdd 2)=Framed.input row j:=by
    by_cases hj:j=52
    · subst j
      exact (bt 0).trans (by rw [rf];rfl)
    · have hn:∀ k,slots k≠j.castAdd 2:=by
        intro k;fin_cases k
        · intro he;apply hj;exact Fin.ext (congrArg Fin.val he).symm
        all_goals intro he;have hv:=congrArg Fin.val he;dsimp [slots] at hv;omega
      exact (keep _ hn).2.trans (by simp only [input,Fin.addCases_left])
  have newT (j : Fin 2):before.final.tapes (j.natAdd 68)=
      (![List.replicate C true,List.replicate C false] : Fin 2→List Bool) j:=by
    fin_cases j
    · exact (bt 1).trans (by rw [rf];rfl)
    · exact (bt 2).trans (by rw [rf];rfl)
  obtain ⟨child,ch,ct,chh,cs⟩:=Framed.run row
  let after:=TapeEmbedding.receipt (fun _ : Fin 2=>0)
    (![List.replicate C true,List.replicate C false] : Fin 2→List Bool) child
  have hl:=TapeEmbedding.run_embed Framed.machine (fun _ : Fin 2=>0)
    (![List.replicate C true,List.replicate C false] : Fin 2→List Bool) _ _ child ch
  have hi:TapeEmbedding.config (fun _ : Fin 2=>0)
      (![List.replicate C true,List.replicate C false] : Fin 2→List Bool)
      (initialConfiguration Framed.machine (Framed.input row))=
      Composition.restart before.final last.start:=by
    apply configuration_ext
    · rfl
    · funext i
      rw [show (Composition.restart before.final last.start).heads i=0 from allH i]
      refine Fin.addCases (fun j=>?_) (fun j=>?_) i
      all_goals simp [TapeEmbedding.config,initialConfiguration]
    · funext i
      refine Fin.addCases (fun j=>?_) (fun j=>?_) i
      · simpa only [TapeEmbedding.config,initialConfiguration,Composition.restart,Fin.addCases_left] using (oldT j).symm
      · simpa only [TapeEmbedding.config,initialConfiguration,Composition.restart,Fin.addCases_right] using (newT j).symm
  rw [hi] at hl
  have hj:=Composition.run_join first last _ _ _ before after hb hl
  refine ⟨Composition.joinedReceipt before after,?_,?_,?_,?_,?_⟩
  · exact hj
  · change after.final.tapes ((66 : Fin 68).castAdd 2)=_
    exact (TapeEmbedding.receipt_tapes_old _ _ child 66).trans ct
  · change after.final.tapes ((0 : Fin 2).natAdd 68)=_
    exact TapeEmbedding.receipt_tapes_new _ _ child 0
  · intro i
    change after.final.heads i=0
    refine Fin.addCases (m:=68) (n:=2) (fun j=>?_) (fun j=>?_) i
    · exact (TapeEmbedding.receipt_heads_old _ _ child j).trans (chh j)
    · exact TapeEmbedding.receipt_heads_new _ _ child j
  · change before.steps+1+child.steps≤_
    rw [bs,rs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Cold
