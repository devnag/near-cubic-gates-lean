import Proof.MachineModel.OrdinaryMatrixScoreLeftLoop

namespace NearCubicWires.RepairOrdinary.MatrixScoreLeftEnumeration
open LocalBitMultitape RecoveryExecution SignedSortKey MatrixScoreBatch MatrixScoreLeftLoop
open MatrixScoreWeight (zeros)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def initial (r : Request) (gate : Fin r.Gates) (state : State r) (cap : ℕ)
    (driver counter out : List Bool) :=
  RecoveryCalls.restarted MatrixScoreLeftNext.cycle (MatrixScorePhiLayout.heads out.length)
    (MatrixScorePhiLayout.tapes (cutWord r.p (r.cuts.get gate)) (frame (binary r.width 0)) r.width (C r) cap
      (r.S+1) (2^r.S) r.M 0 r.U state.work driver counter out state.returnCap r.cols)

theorem first_run (r : Request) (gate : Fin r.Gates) (state : State r) (cap : ℕ) (driver counter out : List Bool)
    (hcap : cap≤C r+1) (hd : driver.length≤C r) (hc : counter.length≤C r) :
    ∃ next : State r,∃ actual,
      runFrom MatrixScoreLeftNext.cycle (MatrixScoreLeftCycle.budget r.width r.p r.S (C r) r.M)
        (initial r gate state cap driver counter out)=some actual ∧
      actual.final.heads=(data r gate 0 next (out++record r gate 0)).heads ∧
      actual.final.tapes=(data r gate 0 next (out++record r gate 0)).tapes ∧
      actual.steps≤MatrixScoreLeftCycle.budget r.width r.p r.S (C r) r.M := by
  have mem := List.get_mem r.cuts gate
  obtain ⟨hl,hr⟩ := r.lengths _ mem
  obtain ⟨hweights,htheta,_⟩ := r.fits _ mem
  have hrcap : state.returnCap≤MatrixScoreLeftRecord.budget (r.cuts.get gate).leftWeights.length r.p r.S (C r) r.M := by
    rw [hl]; exact state.returnBound
  obtain ⟨work,hws,returnCap,hrb,actual,ha,ah,atapes,as⟩ := MatrixScoreLeftCycle.cycle_run
    (r.cuts.get gate).leftWeights (r.cuts.get gate).rightWeights
    (frame (signMagnitude r.p (r.cuts.get gate).coefficient))
    r.p 0 r.S (C r) cap r.M 0 r.U state.returnCap (r.cuts.get gate).threshold state.work driver counter out
    (by omega) (by intro z hz; exact hweights z (List.mem_append_left _ hz)) htheta
    (by unfold Request.S; omega) (by unfold C; omega) (by unfold C; omega) hcap state.bounded hd hc hrcap
    (partial_fit r gate 0 true) (partial_fit r gate 0 false)
  simp only [hl] at ha ah atapes as hrb
  rw [source_eq] at ha atapes
  have he := TapeEmbedding.run_embed MatrixScoreLeftCycle.machine (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => MatrixScorePhi.columnsWord r.width r.cols) _ _ actual ha
  refine ⟨⟨work,hws,returnCap,hrb⟩,_,he,?_,?_,as⟩
  · simp only [TapeEmbedding.receipt,TapeEmbedding.config,ah,data,MatrixScoreLeftLoop.record,phi_zero,
      RecoveryCalls.restarted,MatrixScorePhiLayout.heads]
  · simp only [TapeEmbedding.receipt,TapeEmbedding.config,atapes,data,MatrixScoreLeftLoop.record,phi_zero,
      RecoveryCalls.restarted,MatrixScorePhiLayout.tapes]

def advance : Machine 29 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,fun i => if i=28 then .right else .stay⟩ else none
noncomputable def first := TapeEmbedding.machine 1 MatrixScoreLeftNext.cycle
noncomputable def prefixMachine := Composition.machine first advance
noncomputable def machine := Composition.machine prefixMachine MatrixScoreLeftLoop.machine

def heads (localHeads : Fin 28 → ℕ) (driver : ℕ) : Fin 29 → ℕ :=
  Fin.addCases (m := 28) (n := 1) (motive := fun _ => ℕ) localHeads (fun _ => driver)
def tapes (ambient : Fin 28 → List Bool) (U : ℕ) : Fin 29 → List Bool :=
  Fin.addCases (m := 28) (n := 1) (motive := fun _ => List Bool) ambient (fun _ => UnaryTemplate.tape U)

theorem advance_run (localHeads : Fin 28 → ℕ) (ambient : Fin 29 → List Bool) :
    ∃ actual,runFrom advance 1 (⟨0,heads localHeads 1,ambient⟩ : Configuration 29 2)=some actual ∧
      actual.final=⟨1,heads localHeads 2,ambient⟩ ∧ actual.steps=1 := by
  have hs : step advance (⟨0,heads localHeads 1,ambient⟩ : Configuration 29 2)=some ⟨1,heads localHeads 2,ambient⟩ := by
    simp [step,advance]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,heads,Fin.addCases,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

def padding (U : ℕ) : Fin 29 → ℕ := fun i => if i=28 then U+2 else 0
noncomputable def cfg (phase : Fin 5) (r : Request) (gate : Fin r.Gates) (n driver : ℕ) (state : State r) (out : List Bool) :=
  ZeroPadding.config (padding r.U) (RepeatMachine.cfg phase (data r gate n state out) r.U driver)

theorem cfg_heads (phase : Fin 5) (r : Request) (gate : Fin r.Gates) (n driver : ℕ) (state : State r) (out : List Bool) :
    (cfg phase r gate n driver state out).heads=heads (data r gate n state out).heads driver := by rfl

theorem cfg_tapes (phase : Fin 5) (r : Request) (gate : Fin r.Gates) (n driver : ℕ) (state : State r) (out : List Bool) :
    (cfg phase r gate n driver state out).tapes=tapes (data r gate n state out).tapes r.U := by
  funext i
  fin_cases i <;> simp [cfg,ZeroPadding.config,padding,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    tapes,Fin.addCases,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

def budget (r : Request) := (MatrixScoreLeftCycle.budget r.width r.p r.S (C r) r.M+1+1)+1+
  ((r.U-1)*(MatrixScoreLeftNext.budget r.width r.p r.S (C r) r.M r.d+2)+r.U+3)

theorem enumeration_run (r : Request) (gate : Fin r.Gates) (state : State r) (cap : ℕ) (driver counter out : List Bool)
    (hcap : cap≤C r+1) (hd : driver.length≤C r) (hc : counter.length≤C r) :
    ∃ final : State r,∃ actual,
      runFrom machine (budget r)
        (RecoveryCalls.restarted machine (heads (initial r gate state cap driver counter out).heads 1)
          (tapes (initial r gate state cap driver counter out).tapes r.U))=some actual ∧
      actual.final=Composition.rightConfig _ (cfg 3 r gate (r.U-1) 1 final (out++records r gate 0 r.U)) ∧ actual.steps≤budget r := by
  obtain ⟨next,base,hb,bh,bt,bs⟩ := first_run r gate state cap driver counter out hcap hd hc
  have he := TapeEmbedding.run_embed MatrixScoreLeftNext.cycle (fun _ : Fin 1 => 1)
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
  obtain ⟨padded,hp,pf,ps,_⟩ := ZeroPadding.run_config MatrixScoreLeftLoop.machine (padding r.U) _ _ loop hl
  have pi : Composition.restart (Composition.joinedReceipt expanded moved).final MatrixScoreLeftLoop.machine.start=
      cfg 0 r gate 0 2 next (out++record r gate 0) := by
    apply configuration_ext
    · rfl
    · change moved.final.heads=_
      rw [mf,cfg_heads]
    · change moved.final.tapes=_
      rw [mf,cfg_tapes]
      funext i
      fin_cases i <;> simp [expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,bt,tapes]
  change runFrom MatrixScoreLeftLoop.machine _ (cfg 0 r gate 0 2 next (out++record r gate 0))=some padded at hp
  rw [← pi] at hp
  have joined := Composition.run_join prefixMachine MatrixScoreLeftLoop.machine _ _ _
    (Composition.joinedReceipt expanded moved) padded hpref hp
  have hi0 : Composition.leftConfig _ (Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 1 => 1)
      (fun _ : Fin 1 => UnaryTemplate.tape r.U) (initial r gate state cap driver counter out)))=
      RecoveryCalls.restarted machine (heads (initial r gate state cap driver counter out).heads 1)
        (tapes (initial r gate state cap driver counter out).tapes r.U) := by rfl
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

end NearCubicWires.RepairOrdinary.MatrixScoreLeftEnumeration
