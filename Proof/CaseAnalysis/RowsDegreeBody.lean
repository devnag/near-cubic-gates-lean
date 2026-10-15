import Proof.CaseAnalysis.RowsLoopInterface

/-! One executed degree transition: print and clean the positional cuts,
advance the retained counters, and reload six short templates. The joined
receipt has exactly the next degree's entry configuration. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeBody
open LocalBitMultitape CloseoutRowsLoopLayout CloseoutRowsLoopBoundary CloseoutRowsLoopInterface
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first {s : ℕ} (callee : Machine 112 s) :=
  Composition.machine callee CloseoutRowsDegreeNext.machine
noncomputable def machine {s : ℕ} (callee : Machine 112 s) :=
  Composition.machine (first callee) CloseoutRowsMetadataReload.machine
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w j C : ℕ)
    (rows : List (List Bool)) :=
  CloseoutRowsReusableCuts.budget gs p F w j C rows+1+
    CloseoutRowsDegreeNext.budget w (j+1) j+1+6*(2*C+5)

theorem join_run {s n : ℕ} (callee : Machine 112 s) (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool)
    (work : ExecutionReceipt 112 s)
    (hr : runFrom callee (CloseoutRowsReusableCuts.budget gs p F w j C rows)
      ⟨callee.start,inputHeads gs p F w j rows out,inputTapes gs p F w j C rows out⟩=some work)
    (hh : work.final.heads=finalHeads gs p F w j rows out)
    (ht : work.final.tapes=finalTapes gs p F w j C rows out)
    (hcopy : 4*w+3≤C) (hmeta : 2*w+p+j+3≤C)
    (h47 : RowTupleCursorReady.capacity gs.length w rows.length (j+2)≤C) :
    ∃ actual,runFrom (machine callee) (budget gs p F w j C rows)
      ⟨(machine callee).start,inputHeads gs p F w j rows out,inputTapes gs p F w j C rows out⟩=some actual ∧
      actual.final.heads=inputHeads gs p F w (j+1) rows (out++emitted gs p w j rows) ∧
      actual.final.tapes=inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) ∧
      actual.steps≤budget gs p F w j C rows := by
  obtain ⟨a0,a1,an,aTemplate,aj,a2,a3,aH,aN,aT,aJ⟩ := advance_fields gs p F w j C rows out
  obtain ⟨next,hn,nh,nt,_⟩ := CloseoutRowsDegreeNext.next_run
    (finalTapes gs p F w j C rows out) (finalHeads gs p F w j rows out)
    w _ (j+1) j C a0 a1 an aTemplate aj a2 a3 aH aN aT aJ hcopy (by omega)
  have hni : (⟨CloseoutRowsDegreeNext.machine.start,finalHeads gs p F w j rows out,
      finalTapes gs p F w j C rows out⟩ : Configuration 112 _)=
      Composition.restart work.final CloseoutRowsDegreeNext.machine.start := by
    apply configuration_ext
    · rfl
    · exact hh.symm
    · exact ht.symm
  rw [hni] at hn
  have hfirst := Composition.run_join callee CloseoutRowsDegreeNext.machine _ _ _ work next hr hn
  obtain ⟨hs,hd,hl,hH⟩ := metadata_fields gs p F w j C rows out
  obtain ⟨last,hLast,lh,lt,_⟩ := CloseoutRowsMetadataReload.reload_run
    (advanced gs p F w j C rows out) (finalHeads gs p F w j rows out) C
    (templates p w rows.length (j+1)) hs (templates_bound p w rows.length j C hmeta) hd hl hH
  rw [initial_reload] at hLast
  have hli : (⟨CloseoutRowsMetadataReload.machine.start,finalHeads gs p F w j rows out,
      advanced gs p F w j C rows out⟩ : Configuration 112 _)=
      Composition.restart (Composition.joinedReceipt work next).final CloseoutRowsMetadataReload.machine.start := by
    apply configuration_ext
    · rfl
    · exact nh.symm
    · exact nt.symm
  rw [hli] at hLast
  have whole := Composition.run_join (first callee) CloseoutRowsMetadataReload.machine _ _ _
    (Composition.joinedReceipt work next) last hfirst hLast
  refine ⟨_,whole,lh.trans (all_heads gs p F w j rows out),
    lt.trans (all_tapes gs p F w j C rows out h47),runFrom_steps_le (machine callee) _ _ _ whole⟩

theorem body_run {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w j C : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hj : j<Q) (hQp : Q≤p)
    (hp : RowTupleFixedCapacity.width gs Q≤p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (hc : CloseoutRowsComputedCuts.budget gs p F w j rows+1≤C)
    (ht : ∀ i,CloseoutRowsDegreeReset.selected i=true →
      ((rawInput gs p F w j rows out).tapes i).length≤C)
    (hcopy : 4*w+3≤C) (hmeta : 2*w+p+j+3≤C)
    (h47 : RowTupleCursorReady.capacity gs.length w rows.length (j+2)≤C) :
    ∃ actual,runFrom (machine worker) (budget gs p F w j C rows)
      ⟨(machine worker).start,inputHeads gs p F w j rows out,inputTapes gs p F w j C rows out⟩=some actual ∧
      actual.final.heads=inputHeads gs p F w (j+1) rows (out++emitted gs p w j rows) ∧
      actual.final.tapes=inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) ∧
      actual.steps≤budget gs p F w j C rows := by
  obtain ⟨r,hr,rh,rt,_⟩ := worker_run gs p F Q w j C rows out hl hM hw hj hQp hp hF hc ht
  exact join_run worker gs p F w j C rows out r hr rh rt hcopy hmeta h47

theorem budget_le {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool))
    (hc : CloseoutRowsComputedCuts.budget gs p F w j rows+1≤C)
    (hmeta : 2*w+p+j+3≤C) :
    budget gs p F w j C rows≤40*C+100 := by
  unfold budget CloseoutRowsReusableCuts.budget CloseoutRowsDegreeClean.budget
    CloseoutRowsDegreeNext.budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeBody
