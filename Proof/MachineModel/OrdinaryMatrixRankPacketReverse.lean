import Proof.MachineModel.OrdinaryMatrixRankRowReverse

/-! One ranked gate packet contains two U-row passes and one final false
cell. The actual delimiter move and both loop returns are charged. -/
namespace NearCubicWires.RepairOrdinary.MatrixRankPacketReverse
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boot : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun _ => none,![.left,.stay,.stay]⟩
def bootCfg (q : Fin 2) (source : List Bool) (H U pos : ℕ) : Configuration 3 2 :=
  ⟨q,![pos,0,1],![source,UnaryTemplate.tape H,UnaryTemplate.tape U]⟩
noncomputable def rows := Composition.machine MatrixRankRowReverse.machine MatrixRankRowReverse.machine
noncomputable def machine := Composition.machine boot rows
def rowStates := Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control 7)
noncomputable def cfg (source : List Bool) (H U pos : ℕ) :=
  Composition.leftConfig (rowStates+rowStates) (bootCfg 0 source H U pos)
def distance (H U : ℕ) := 2*U*MatrixRankFieldReverse.distance H+1
def budget (H U : ℕ) := 1+1+(MatrixRankRowReverse.budget H U+1+MatrixRankRowReverse.budget H U)

theorem boot_step (source : List Bool) (H U pos : ℕ) :
    step boot (bootCfg 0 source H U pos)=some (bootCfg 1 source H U (pos-1)) := by
  simp [step,boot,bootCfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem restart_row (phase : Fin 5) (source : List Bool) (H U pos : ℕ) :
    Composition.restart (MatrixRankRowReverse.cfg phase source H U pos) MatrixRankRowReverse.machine.start=
      MatrixRankRowReverse.cfg 0 source H U pos := rfl

theorem packet_run (source : List Bool) (H U pos : ℕ) :
    ∃ actual,runFrom machine (budget H U) (cfg source H U pos)=some actual ∧
      actual.steps ≤ budget H U ∧
      actual.final.heads=![pos-distance H U,0,1] ∧
      actual.final.tapes=![source,UnaryTemplate.tape H,UnaryTemplate.tape U] := by
  obtain ⟨first,hfirst,fs,ff⟩ := MatrixRankRowReverse.row_run source H U (pos-1)
  obtain ⟨second,hsecond,ss,sf⟩ := MatrixRankRowReverse.row_run source H U
    (pos-1-U*MatrixRankFieldReverse.distance H)
  have hsecond' : runFrom MatrixRankRowReverse.machine (MatrixRankRowReverse.budget H U)
      (Composition.restart first.final MatrixRankRowReverse.machine.start)=some second := by
    rw [ff,restart_row]
    exact hsecond
  have hrows := Composition.run_join MatrixRankRowReverse.machine MatrixRankRowReverse.machine
    _ _ _ first second hfirst hsecond'
  obtain ⟨moved,hm,mf,ms⟩ := (Timed.single (by rfl) (boot_step source H U pos)).run (by rfl)
  have he : Composition.restart moved.final rows.start=
      Composition.leftConfig _ (MatrixRankRowReverse.cfg 0 source H U (pos-1)) := by
    rw [mf]
    apply configuration_ext
    · rfl
    · exact (MatrixRankRowReverse.cfg_heads 0 source H U (pos-1)).symm
    · exact (MatrixRankRowReverse.cfg_tapes 0 source H U (pos-1)).symm
  have hrows' : runFrom rows (MatrixRankRowReverse.budget H U+1+MatrixRankRowReverse.budget H U)
      (Composition.restart moved.final rows.start)=some (Composition.joinedReceipt first second) := by
    rw [he]
    exact hrows
  have hall := Composition.run_join boot rows _ _ _ moved _ hm hrows'
  refine ⟨_,hall,?_,?_,?_⟩
  · change moved.steps+1+(first.steps+1+second.steps) ≤ budget H U
    unfold budget
    omega
  · change second.final.heads=_
    rw [sf,MatrixRankRowReverse.cfg_heads]
    congr 1
    unfold distance
    simp only [Nat.sub_sub]
    congr 1
    ring
  · change second.final.tapes=_
    rw [sf,MatrixRankRowReverse.cfg_tapes]

end NearCubicWires.RepairOrdinary.MatrixRankPacketReverse
