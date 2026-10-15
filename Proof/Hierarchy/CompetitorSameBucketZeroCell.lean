import Proof.Hierarchy.CompetitorSameBucketColdGate

/-! One actual zero-grid cell: append the existing signed key with zero
coefficient and physically increment the tagged column. The appender and
increment share reset scratch and preserve the global output cursor. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroCell
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def incrementSlots : Fin 2 → Fin 8 := ![2,7]
theorem increment_injective : Function.Injective incrementSlots := by decide
noncomputable def increment:=RecoveryFocus.machine incrementSlots FramedIncrement.machine
noncomputable def machine:=Composition.machine CompetitorSameBucketKeyAppend.machine increment
def cfg {s : ℕ} (q : Fin s) (p m right left cap : ℕ) (out : List Bool) :=
  CompetitorSameBucketKeyAppend.paddedCfg q (MatrixScoreBatch.signMagnitude p 0) m right left cap out
def budget (p m : ℕ):=4*p+12*m+20

theorem increment_ready (m right cap : ℕ) (hr : right+1<2^m) (hc : 2*m≤cap) :
    ClockJoin.ReadyRun FramedIncrement.machine (4*m+2)
      ![ZeroPadding.pad cap (frame (binary m right)),List.replicate cap false]
      ![ZeroPadding.pad cap (frame (binary m (right+1))),List.replicate cap false] := by
  obtain ⟨base,hb,bt,bh,bs⟩:=MatrixScoreAdvance.ready m right cap hr hc
  obtain ⟨actual,ha,af,ast,_⟩:=ZeroPadding.run_config FramedIncrement.machine (fun _ => cap) _ _ base hb
  have hi : ZeroPadding.config (fun _ : Fin 2 => cap)
      (initialConfiguration FramedIncrement.machine ![frame (binary m right),List.replicate cap false])=
      initialConfiguration FramedIncrement.machine ![ZeroPadding.pad cap (frame (binary m right)),List.replicate cap false] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,Rewind.Workspace.pad_zeros]
  simp only [MatrixScoreWeight.zeros] at ha bt
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,ast.trans_le bs⟩
  · rw [af]
    funext i
    simp only [ZeroPadding.config,bt]
    fin_cases i <;> simp [Rewind.Workspace.pad_zeros]
  · intro i; rw [af]; exact bh i

theorem increment_pick (i : Fin 8) : RecoveryFocus.pick incrementSlots i=
    (![none,none,some 0,none,none,none,none,some 1] : Fin 8 → Option (Fin 2)) i := by
  fin_cases i
  all_goals first | decide | exact RecoveryFocus.pick_slot incrementSlots increment_injective 0 |
    exact RecoveryFocus.pick_slot incrementSlots increment_injective 1

theorem increment_run (p m right left cap : ℕ) (out : List Bool)
    (hr : right+1<2^m) (hc : 2*m≤cap) :
    ∃ actual,runFrom increment (4*m+2) (cfg increment.start p m right left cap out)=some actual ∧
      actual.final.heads=(cfg increment.start p m (right+1) left cap out).heads ∧
      actual.final.tapes=(cfg increment.start p m (right+1) left cap out).tapes ∧ actual.steps≤4*m+2 := by
  let start:=cfg increment.start p m right left cap out
  obtain ⟨actual,ha,ah,atapes,ast⟩:=CompetitorReusableDecision.bounded_focused_run incrementSlots increment_injective
    FramedIncrement.machine _ _ (increment_ready m right cap hr hc) start.heads start.tapes
    (by intro i; fin_cases i <;> rfl)
    (by intro i; fin_cases i
        · rfl
        · simp [incrementSlots,start,cfg,CompetitorSameBucketKeyAppend.paddedCfg,CompetitorSameBucketKeyAppend.capacities,
            CompetitorSameBucketKeyAppend.cfg,ZeroPadding.config,Rewind.Workspace.pad_zeros])
  refine ⟨actual,ha,ah,?_,ast⟩
  rw [atapes]
  funext i
  simp only [install,increment_pick]
  fin_cases i <;> simp [start,cfg,CompetitorSameBucketKeyAppend.paddedCfg,CompetitorSameBucketKeyAppend.capacities,
    CompetitorSameBucketKeyAppend.cfg,ZeroPadding.config,Rewind.Workspace.pad_zeros]

theorem cell_run (p m right left cap : ℕ) (out : List Bool)
    (hp : 2*(p+1)≤cap) (hm : 2*m≤cap) (hr : right+1<2^m) :
    ∃ actual,runFrom machine (budget p m) (cfg machine.start p m right left cap out)=some actual ∧
      actual.final.heads=(cfg machine.start p m (right+1) left cap
        (out++CompetitorSameBucketKeyAppend.word p m 0 left right)).heads ∧
      actual.final.tapes=(cfg machine.start p m (right+1) left cap
        (out++CompetitorSameBucketKeyAppend.word p m 0 left right)).tapes ∧ actual.steps≤budget p m := by
  obtain ⟨first,hf,fh,ft,fs⟩:=CompetitorSameBucketKeyAppend.signed_run p m right left cap 0 out hp hm
  obtain ⟨last,hl,lh,lt,ls⟩:=increment_run p m right left cap (out++CompetitorSameBucketKeyAppend.word p m 0 left right) hr hm
  have hi : Composition.restart first.final increment.start=
      cfg increment.start p m right left cap (out++CompetitorSameBucketKeyAppend.word p m 0 left right) :=
    configuration_ext rfl fh ft
  rw [←hi] at hl
  have joined:=Composition.run_join CompetitorSameBucketKeyAppend.machine increment _ _ _ first last hf hl
  have total : (4*p+8*m+17)+1+(4*m+2)=budget p m := by unfold budget; omega
  rw [total] at joined
  refine ⟨Composition.joinedReceipt first last,joined,lh,lt,?_⟩
  change first.steps+1+last.steps≤budget p m
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroCell
