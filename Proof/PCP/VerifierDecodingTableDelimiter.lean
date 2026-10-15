import Proof.PCP.VerifierDecodingTableValidation

/-! The accepted delimiter reader is used on the actual nine-tape table
workspace. It retains every tape/head and then physically writes acceptance. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.TableValidation
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem delimiter_run (pre rest : List Bool) (heads : Fin 9 → ℕ) (tapes : Fin 9 → List Bool)
    (hp : heads 0=pre.length) (hs : tapes 0=pre++frame rest) :
    ∃ r, runFrom delimiterProgram 1 ⟨0,heads,tapes⟩=some r ∧
      r.final=⟨if rest=[] then 1 else 2,heads,tapes⟩ ∧ r.steps=1 := by
  obtain ⟨base,hr,hf,hsteps⟩ := DelimiterMachine.delimiter_run pre rest
  let eh : Fin 8 → ℕ := fun i => heads (i.natAdd 1)
  let et : Fin 8 → List Bool := fun i => tapes (i.natAdd 1)
  have he (q : Fin 3) : TapeEmbedding.config eh et (DelimiterMachine.cfg q pre rest)=⟨q,heads,tapes⟩ := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,DelimiterMachine.cfg,eh,Fin.addCases,hp]
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,DelimiterMachine.cfg,et,Fin.addCases,hs]
  have hrun := TapeEmbedding.run_embed DelimiterMachine.machine eh et _ _ base hr
  rw [he] at hrun
  refine ⟨TapeEmbedding.receipt eh et base,hrun,?_,hsteps⟩
  simp only [TapeEmbedding.receipt,hf,he]

theorem delimiter_tail (pre rest : List Bool) (heads : Fin 9 → ℕ) (tapes : Fin 9 → List Bool)
    (hp : heads 0=pre.length) (hs : tapes 0=pre++frame rest) :
    Timed machine 4 (controlConfig (RecoveryCalls.code sizes 1) ⟨(programs 1).start,heads,tapes⟩)
      (finished (decide (rest=[])) heads tapes) := by
  obtain ⟨r,hr,hf,hsteps⟩ := delimiter_run pre rest heads tapes hp hs
  by_cases h : rest=[]
  · have hn : next 1 r.final.control r.final.scanned=some 2 := by simp [next,hf,h]
    have hcall := call_prefix 1 2 1 _ r hr hn
    rw [hf,hsteps] at hcall
    simp only [h,decide_true]
    exact hcall.trans (flag_tail true heads tapes)
  · have hn : next 1 r.final.control r.final.scanned=some 3 := by simp [next,hf,h]
    have hcall := call_prefix 1 3 1 _ r hr hn
    rw [hf,hsteps] at hcall
    simp only [h,decide_false]
    exact hcall.trans (flag_tail false heads tapes)

end NearCubicWires.RepairSource.VerifierDecoding.TableValidation
