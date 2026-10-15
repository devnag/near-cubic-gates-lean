import Proof.MachineModel.OrdinaryMatrixScoreRightLoop
import Proof.MachineModel.OrdinaryMatrixScoreLeftEnumeration

namespace NearCubicWires.RepairOrdinary.MatrixScoreRightEnumeration
open LocalBitMultitape RecoveryExecution SignedSortKey MatrixScoreBatch MatrixScoreRightLoop
open MatrixScoreWeight (zeros)
open MatrixScoreLeftLoop (C bodyBudget State source_eq)
open MatrixScoreLeftEnumeration (heads tapes advance advance_run padding)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def initial (r : Request) (gate : Fin r.Gates) (state : State r) (out : List Bool) :=
  RecoveryCalls.restarted MatrixScoreRightNext.cycle (data r gate 0 state out).heads (data r gate 0 state out).tapes

theorem first_run (r : Request) (gate : Fin r.Gates) (state : State r) (out : List Bool) :
    ∃ next : State r,∃ actual,
      runFrom MatrixScoreRightNext.cycle (MatrixScoreRightCycle.budget r.width r.p r.S (C r) r.M)
        (initial r gate state out)=some actual ∧
      actual.final.heads=(data r gate 0 next (out++record r gate 0)).heads ∧
      actual.final.tapes=(data r gate 0 next (out++record r gate 0)).tapes ∧
      actual.steps≤MatrixScoreRightCycle.budget r.width r.p r.S (C r) r.M := by
  have mem := List.get_mem r.cuts gate
  obtain ⟨hl,hr⟩ := r.lengths _ mem
  obtain ⟨hweights,_,_⟩ := r.fits _ mem
  have hrcap : state.returnCap≤MatrixScoreLeftRecord.budget (r.cuts.get gate).leftWeights.length r.p r.S (C r) r.M := by
    rw [hl]; exact state.returnBound
  obtain ⟨work,hws,returnCap,hrb,actual,ha,ah,atapes,as⟩ := MatrixScoreRightCycle.cycle_run
    (r.cuts.get gate).leftWeights (r.cuts.get gate).rightWeights
    (frame (signMagnitude r.p (r.cuts.get gate).threshold)++frame (signMagnitude r.p (r.cuts.get gate).coefficient))
    r.p (r.phi 0) r.S (C r) (C r+1) r.M r.U r.U state.returnCap state.work
    (ZeroPadding.pad (C r) [true,true]) (zeros (C r)) out
    (by omega) (by intro z hz; exact hweights z (List.mem_append_right _ hz))
    (by unfold Request.S; omega) (by unfold C; omega) (by unfold C; omega) (by omega) state.bounded hrcap
    (partial_fit r gate _ false) (partial_fit r gate _ true)
  simp only [hl] at ha ah atapes as hrb
  rw [← List.append_assoc,source_eq] at ha atapes
  have he := TapeEmbedding.run_embed MatrixScoreRightCycle.machine (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => MatrixScorePhi.columnsWord r.width r.cols) _ _ actual ha
  refine ⟨⟨work,hws,returnCap,hrb⟩,_,he,?_,?_,as⟩
  · simp only [TapeEmbedding.receipt,TapeEmbedding.config,ah,data,MatrixScoreRightLoop.record,
      RecoveryCalls.restarted,MatrixScorePhiLayout.heads,Nat.add_zero]
  · simp only [TapeEmbedding.receipt,TapeEmbedding.config,atapes,data,MatrixScoreRightLoop.record,
      RecoveryCalls.restarted,MatrixScorePhiLayout.tapes,Nat.add_zero]

noncomputable def first := TapeEmbedding.machine 1 MatrixScoreRightNext.cycle
noncomputable def prefixMachine := Composition.machine first advance
noncomputable def machine := Composition.machine prefixMachine MatrixScoreRightLoop.machine

noncomputable def cfg (phase : Fin 5) (r : Request) (gate : Fin r.Gates) (n driver : ℕ) (state : State r) (out : List Bool) :=
  ZeroPadding.config (padding r.U) (RepeatMachine.cfg phase (data r gate n state out) r.U driver)

theorem cfg_heads (phase : Fin 5) (r : Request) (gate : Fin r.Gates) (n driver : ℕ) (state : State r) (out : List Bool) :
    (cfg phase r gate n driver state out).heads=heads (data r gate n state out).heads driver := by rfl

theorem cfg_tapes (phase : Fin 5) (r : Request) (gate : Fin r.Gates) (n driver : ℕ) (state : State r) (out : List Bool) :
    (cfg phase r gate n driver state out).tapes=tapes (data r gate n state out).tapes r.U := by
  funext i
  fin_cases i <;> simp [cfg,ZeroPadding.config,padding,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    tapes,Fin.addCases,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

def budget (r : Request) := (MatrixScoreRightCycle.budget r.width r.p r.S (C r) r.M+1+1)+1+
  ((r.U-1)*(MatrixScoreRightNext.budget r.width r.p r.S (C r) r.M r.d+2)+r.U+3)

theorem enumeration_run (r : Request) (gate : Fin r.Gates) (state : State r) (out : List Bool) :
    ∃ final : State r,∃ actual,
      runFrom machine (budget r)
        (RecoveryCalls.restarted machine (heads (initial r gate state out).heads 1)
          (tapes (initial r gate state out).tapes r.U))=some actual ∧
      actual.final=Composition.rightConfig _ (cfg 3 r gate (r.U-1) 1 final (out++records r gate 0 r.U)) ∧ actual.steps≤budget r := by
  obtain ⟨next,base,hb,bh,bt,bs⟩ := first_run r gate state out
  have he := TapeEmbedding.run_embed MatrixScoreRightNext.cycle (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => UnaryTemplate.tape r.U) _ _ base hb
  let expanded := TapeEmbedding.receipt (fun _ : Fin 1 => 1) (fun _ : Fin 1 => UnaryTemplate.tape r.U) base
  obtain ⟨moved,hm,mf,ms⟩ := advance_run (data r gate 0 next (out++record r gate 0)).heads expanded.final.tapes
  have hi : Composition.restart expanded.final advance.start=
      (⟨0,heads (data r gate 0 next (out++record r gate 0)).heads 1,expanded.final.tapes⟩ : Configuration 29 2) := by
    apply configuration_ext
    · rfl
    · change expanded.final.heads=_
      funext i
      fin_cases i <;> simp [expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,bh,heads]
    · rfl
  rw [← hi] at hm
  have hpref := Composition.run_join first advance _ 1 _ expanded moved he hm
  obtain ⟨final,loop,hl,lf,ls⟩ := loop_run r gate (r.U-1) 0 next (out++record r gate 0) (by have hu := dimension_positive r; omega)
  obtain ⟨padded,hp,pf,ps,_⟩ := ZeroPadding.run_config MatrixScoreRightLoop.machine (padding r.U) _ _ loop hl
  have pi : Composition.restart (Composition.joinedReceipt expanded moved).final MatrixScoreRightLoop.machine.start=
      cfg 0 r gate 0 2 next (out++record r gate 0) := by
    apply configuration_ext
    · rfl
    · change moved.final.heads=_
      rw [mf,cfg_heads]
    · change moved.final.tapes=_
      rw [mf,cfg_tapes]
      funext i
      fin_cases i <;> simp [expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,bt,tapes]
  change runFrom MatrixScoreRightLoop.machine _ (cfg 0 r gate 0 2 next (out++record r gate 0))=some padded at hp
  rw [← pi] at hp
  have joined := Composition.run_join prefixMachine MatrixScoreRightLoop.machine _ _ _
    (Composition.joinedReceipt expanded moved) padded hpref hp
  have hi0 : Composition.leftConfig _ (Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 1 => 1)
      (fun _ : Fin 1 => UnaryTemplate.tape r.U) (initial r gate state out)))=
      RecoveryCalls.restarted machine (heads (initial r gate state out).heads 1)
        (tapes (initial r gate state out).tapes r.U) := by rfl
  rw [hi0] at joined
  have hrec : out++record r gate 0++records r gate 1 (r.U-1)=out++records r gate 0 r.U := by
    have hU : r.U=r.U-1+1 := by have hu := dimension_positive r; omega
    conv_rhs => rw [hU,records]
    simp only [List.append_assoc]
  refine ⟨final,Composition.joinedReceipt (Composition.joinedReceipt expanded moved) padded,joined,?_,?_⟩
  · change Composition.rightConfig _ padded.final=_
    rw [pf,lf]
    simp only [Nat.zero_add]
    change Composition.rightConfig _ (cfg 3 r gate (r.U-1) 1 final ((out++record r gate 0)++records r gate 1 (r.U-1)))=_
    rw [hrec]
  · change (base.steps+1+moved.steps)+1+padded.steps≤_
    rw [ms,ps]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreRightEnumeration
