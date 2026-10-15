import Proof.PCP.ProjectionNormalizationDedupGraph

/-! One enclosing keep-last iteration: advance the actual outer count, retain
one candidate, scan its later clauses with both cursors restored, and execute
the keep/discard branch and physical kept-count increment. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Dedup
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def afterScan (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :=
  scanOut (copyOut (bootOut d) row) row rows
noncomputable def result (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :=
  if row∈rows then discardOut (afterScan d row rows) row else bumpOut (keepOut (afterScan d row rows) row)
def bodyBudget (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :=
  3*(ClauseEquality.stream row).length+4*(rows.length*(2*d.cap+6)+1)+21

theorem body_run (d : Store) (pre : List Bool) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause)
    (suffix : List Bool) (pos : ℕ) (hsource : d.source=pre++SuffixScan.stream (row::rows)++suffix)
    (hpos : d.sourcePos=pre.length) (hcp : d.candidatePos=d.candidate.length)
    (hdriver : d.driverPos=pos+1) (hn : pos+(row::rows).length=d.count)
    (hcopy : (ClauseEquality.stream row).length+2 ≤ d.copyCap)
    (hcap : ∀ r∈rows,ClauseProbe.budget row r ≤ d.cap)
    (hlog : 2*(rows.length*(2*d.cap+6)+1)+2 ≤ d.scanCap) :
    ∃ r,runFrom body (bodyBudget d row rows) (cfg body.start d)=some r ∧
      r.steps ≤ bodyBudget d row rows ∧ r.final=stopped (result d row rows) := by
  classical
  let d₀ := bootOut d
  let d₁ := copyOut d₀ row
  let d₂ := scanOut d₁ row rows
  obtain ⟨a,ha,haf,hat⟩ := boot_run d
  have pa := call_phase 0 1 d d₀ (1 : Fin 2) 1 a ha haf (by simp [next])
  obtain ⟨b,hb,hbt,hbf⟩ := copy_run d₀ pre row (SuffixScan.stream rows++suffix)
    (by simpa [d₀,bootOut,SuffixScan.stream_cons,List.append_assoc] using hsource)
    hpos hcp hcopy
  have pb := call_phase 1 2 d₀ d₁ CandidateCopy.finalCode _ b hb hbf (by simp [next])
  obtain ⟨c,hc,hct,hcf⟩ := scan_run d₁ row rows d.candidate (pre++ClauseEquality.stream row) suffix (pos+1)
    (by simpa [d₁,d₀,copyOut,bootOut,SuffixScan.stream_cons,List.append_assoc] using hsource)
    (by simp [d₁,d₀,copyOut,bootOut,hpos])
    rfl rfl (by simp [d₁,d₀,copyOut,bootOut,hdriver])
    (by simp only [List.length_cons] at hn; dsimp [d₁,d₀,copyOut,bootOut]; omega)
    hcap hlog
  have heq : d₂.found=decide (row∈rows) := by simp [d₂,d₁,d₀,scanOut,copyOut,bootOut,SuffixScan.seen]
  by_cases hm : row∈rows
  · have pc := call_phase 2 4 d₁ d₂ SharedDriverRestore.finalCode _ c hc hcf (by
      simp [next,cfg,Configuration.scanned,heq,hm,readTapeBit,List.getD])
    obtain ⟨e,he,het,hef⟩ := discard_run d₂ d.candidate row rfl rfl
    have pe := stop_phase 4 d₂ (discardOut d₂ row) ClauseCopy.finalCode _ e he hef (by simp [next])
    have hp := pa.trans (pb.trans (pc.trans pe))
    obtain ⟨r,hr,hrf,hrs⟩ := hp.run (stopped_halted _)
    have htime : (a.steps+1)+((b.steps+1)+((c.steps+1)+(e.steps+1))) ≤ bodyBudget d row rows := by
      dsimp only [bodyBudget]
      change c.steps ≤ 4*(rows.length*(2*d.cap+6)+1)+6 at hct
      omega
    have hmore := runFrom_moreFuel body _
      (bodyBudget d row rows-((a.steps+1)+((b.steps+1)+((c.steps+1)+(e.steps+1))))) _ r hr
    rw [Nat.add_sub_of_le htime] at hmore
    refine ⟨r,hmore,by omega,?_⟩
    simpa only [result,if_pos hm,afterScan,d₂,d₁,d₀] using hrf
  · have pc := call_phase 2 3 d₁ d₂ SharedDriverRestore.finalCode _ c hc hcf (by
      simp [next,cfg,Configuration.scanned,heq,hm,readTapeBit,List.getD])
    obtain ⟨e,he,het,hef⟩ := keep_run d₂ d.candidate row rfl rfl
    have pe := call_phase 3 5 d₂ (keepOut d₂ row) ClauseCopy.finalCode _ e he hef (by simp [next])
    obtain ⟨f,hf,hff,hft⟩ := bump_run (keepOut d₂ row)
    have pf := stop_phase 5 (keepOut d₂ row) (bumpOut (keepOut d₂ row)) (1 : Fin 2) 1 f hf hff (by simp [next])
    have hp := pa.trans (pb.trans (pc.trans (pe.trans pf)))
    obtain ⟨r,hr,hrf,hrs⟩ := hp.run (stopped_halted _)
    have htime : (a.steps+1)+((b.steps+1)+((c.steps+1)+((e.steps+1)+(f.steps+1)))) ≤ bodyBudget d row rows := by
      dsimp only [bodyBudget]
      change c.steps ≤ 4*(rows.length*(2*d.cap+6)+1)+6 at hct
      omega
    have hmore := runFrom_moreFuel body _
      (bodyBudget d row rows-((a.steps+1)+((b.steps+1)+((c.steps+1)+((e.steps+1)+(f.steps+1)))))) _ r hr
    rw [Nat.add_sub_of_le htime] at hmore
    refine ⟨r,hmore,by omega,?_⟩
    simpa only [result,if_neg hm,afterScan,d₂,d₁,d₀] using hrf

end NearCubicWires.RepairSource.ProjectionNormalization.Dedup
