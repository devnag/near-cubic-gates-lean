import Proof.MachineModel.OrdinaryMatrixRankPacketReverse

/-! A physical gate-count loop restores the ranked stream in one pass.
Both pre-existing U and gate sentinels are retained, including empty batches. -/
namespace NearCubicWires.RepairOrdinary.MatrixRankStreamReverse
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def packetStates := 2+(MatrixRankPacketReverse.rowStates+MatrixRankPacketReverse.rowStates)
def accepted (_ : Fin packetStates) (_ : Fin 3 → Bool) := true
noncomputable def loop := RepeatMachine.machine MatrixRankPacketReverse.machine accepted
def loopBudget (H U G : ℕ) := G*(MatrixRankPacketReverse.budget H U+3)+3
noncomputable def loopCfg (phase : Fin 5) (source : List Bool) (H U G pos : ℕ) :=
  ZeroPadding.config (![0,0,0,G+2] : Fin 4 → ℕ)
    (RepeatMachine.cfg phase (MatrixRankPacketReverse.cfg source H U pos) G 1)

theorem loop_run (source : List Bool) (H U G pos : ℕ) :
    ∃ actual,runFrom loop (loopBudget H U G) (loopCfg 0 source H U G pos)=some actual ∧
      actual.steps ≤ loopBudget H U G ∧
      actual.final=loopCfg 3 source H U G (pos-G*MatrixRankPacketReverse.distance H U) := by
  let state := fun p => MatrixRankPacketReverse.cfg source H U p
  let next := fun p : ℕ => (true,p-MatrixRankPacketReverse.distance H U)
  obtain ⟨base,hb,hs,hf⟩ := RepeatMachine.repeat_run (s := packetStates) MatrixRankPacketReverse.machine accepted
    state next (fun _ => True) (MatrixRankPacketReverse.budget H U) (by intros; rfl)
    (by
      intro p _
      obtain ⟨actual,ha,has,hah,hat⟩ := MatrixRankPacketReverse.packet_run source H U p
      exact ⟨actual,ha,has,hah,hat,rfl,by intros; trivial⟩) G pos trivial
  have hfinal : base.final=RepeatMachine.cfg 3
      (state (pos-G*MatrixRankPacketReverse.distance H U)) G 1 := by
    simp only [RepeatMachine.Result,next,MatrixRankRowReverse.iterate_sub,↓reduceIte] at hf
    exact hf
  obtain ⟨actual,ha,haf,has,_⟩ := ZeroPadding.run_config loop (![0,0,0,G+2] : Fin 4 → ℕ) _ _ base hb
  refine ⟨actual,ha,has.trans_le hs,?_⟩
  rw [haf,hfinal]
  rfl

theorem loopCfg_heads (phase : Fin 5) (source : List Bool) (H U G pos : ℕ) :
    (loopCfg phase source H U G pos).heads=![pos,0,1,1] := by
  funext i
  fin_cases i <;> rfl

theorem loopCfg_tapes (phase : Fin 5) (source : List Bool) (H U G pos : ℕ) :
    (loopCfg phase source H U G pos).tapes=
      ![source,UnaryTemplate.tape H,UnaryTemplate.tape U,UnaryTemplate.tape G] := by
  funext i
  fin_cases i <;> simp [loopCfg,ZeroPadding.config,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    MatrixRankPacketReverse.cfg,Composition.leftConfig,MatrixRankPacketReverse.bootCfg,
    ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape,Fin.addCases]

def move (direction : HeadMove) : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun _ => none,![.stay,.stay,direction,direction]⟩
def moveCfg (q : Fin 2) (source : List Bool) (H U G pos head : ℕ) : Configuration 4 2 :=
  ⟨q,![pos,0,head,head],![source,UnaryTemplate.tape H,UnaryTemplate.tape U,UnaryTemplate.tape G]⟩
noncomputable def tail := Composition.machine loop (move .left)
noncomputable def machine := Composition.machine (move .right) tail
def loopStates := Fintype.card (RepeatMachine.Control packetStates)
noncomputable def cfg (source : List Bool) (H U G pos : ℕ) :=
  Composition.leftConfig (loopStates+2) (moveCfg 0 source H U G pos 0)
def budget (H U G : ℕ) := 1+1+(loopBudget H U G+1+1)

theorem move_step (direction : HeadMove) (source : List Bool) (H U G pos head : ℕ) :
    step (move direction) (moveCfg 0 source H U G pos head)=
      some (moveCfg 1 source H U G pos (direction.apply head)) := by
  simp [step,move,moveCfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem reverse_run (source : List Bool) (H U G pos : ℕ) :
    ∃ actual,runFrom machine (budget H U G) (cfg source H U G pos)=some actual ∧
      actual.steps ≤ budget H U G ∧
      actual.final.heads=![pos-G*MatrixRankPacketReverse.distance H U,0,0,0] ∧
      actual.final.tapes=![source,UnaryTemplate.tape H,UnaryTemplate.tape U,UnaryTemplate.tape G] := by
  obtain ⟨body,hb,bs,bf⟩ := loop_run source H U G pos
  obtain ⟨last,hl,lf,ls⟩ := (Timed.single (by rfl)
    (move_step .left source H U G (pos-G*MatrixRankPacketReverse.distance H U) 1)).run (by rfl)
  have heLast : Composition.restart body.final (move .left).start=
      moveCfg 0 source H U G (pos-G*MatrixRankPacketReverse.distance H U) 1 := by
    rw [bf]
    apply configuration_ext
    · rfl
    · exact loopCfg_heads 3 source H U G _
    · exact loopCfg_tapes 3 source H U G _
  have hl' : runFrom (move .left) 1 (Composition.restart body.final (move .left).start)=some last := by
    rw [heLast]
    exact hl
  have ht := Composition.run_join loop (move .left) _ _ _ body last hb hl'
  obtain ⟨first,hfirst,ff,fs⟩ := (Timed.single (by rfl) (move_step .right source H U G pos 0)).run (by rfl)
  have heFirst : Composition.restart first.final tail.start=
      Composition.leftConfig 2 (loopCfg 0 source H U G pos) := by
    rw [ff]
    apply configuration_ext
    · rfl
    · exact (loopCfg_heads 0 source H U G pos).symm
    · exact (loopCfg_tapes 0 source H U G pos).symm
  have ht' : runFrom tail (loopBudget H U G+1+1)
      (Composition.restart first.final tail.start)=some (Composition.joinedReceipt body last) := by
    rw [heFirst]
    exact ht
  have hall := Composition.run_join (move .right) tail _ _ _ first _ hfirst ht'
  refine ⟨_,hall,?_,?_,?_⟩
  · change first.steps+1+(body.steps+1+last.steps) ≤ budget H U G
    unfold budget
    omega
  · change last.final.heads=_
    rw [lf]
    rfl
  · change last.final.tapes=_
    rw [lf]
    rfl

end NearCubicWires.RepairOrdinary.MatrixRankStreamReverse
