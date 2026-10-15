import Proof.Hierarchy.CompetitorSameBucketZeroCell
import Proof.Hierarchy.CompetitorSameBucketColdGateBounds

/-! One physical row of the zero grid, controlled by the actual unary
column sentinel. Right tagged IDs advance once per emitted zero record. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroRow
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open CompetitorSameBucketZeroCell (cfg)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted {s : ℕ} (_ : Fin s) (_ : Fin 8 → Bool):=true
noncomputable def machine:=RepeatMachine.machine CompetitorSameBucketZeroCell.machine accepted
def bits (p m left : ℕ) : ℕ → ℕ → List Bool
  | _,0 => []
  | right,n+1 => CompetitorSameBucketKeyAppend.word p m 0 left right++bits p m left (right+1) n
def budget (p m n : ℕ):=n*(CompetitorSameBucketZeroCell.budget p m+3)+3

theorem driver_run (p m left right cap n total pos : ℕ) (out : List Bool)
    (hpos : pos+n=total) (hp : 2*(p+1)≤cap) (hm : 2*m≤cap) (hr : right+n<2^m) :
    ∃ actual,runFrom machine (n*(CompetitorSameBucketZeroCell.budget p m+2)+total+3)
        (RepeatMachine.cfg 0 (cfg CompetitorSameBucketZeroCell.machine.start p m right left cap out) total (pos+1))=some actual ∧
      actual.steps≤n*(CompetitorSameBucketZeroCell.budget p m+2)+total+3 ∧
      actual.final=RepeatMachine.cfg 3
        (cfg CompetitorSameBucketZeroCell.machine.start p m (right+n) left cap (out++bits p m left right n)) total 1 := by
  induction n generalizing right pos out with
  | zero =>
    have he : pos=total := by omega
    subst pos
    obtain ⟨actual,ha,af,ast⟩:=(RepeatMachine.exhaust CompetitorSameBucketZeroCell.machine accepted
      (cfg CompetitorSameBucketZeroCell.machine.start p m right left cap out) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨actual,by simpa [machine] using ha,by simpa using ast.le,by simpa [bits] using af⟩
  | succ n ih =>
    obtain ⟨one,ho,oh,ot,os⟩:=CompetitorSameBucketZeroCell.cell_run p m right left cap out hp hm (by omega)
    have iteration:=RepeatMachine.iteration CompetitorSameBucketZeroCell.machine accepted
      (cfg CompetitorSameBucketZeroCell.machine.start p m right left cap out) total pos one rfl (by omega) ho
    simp only [accepted,if_true] at iteration
    have hend : RepeatMachine.cfg 0 one.final total (pos+2)=RepeatMachine.cfg 0
        (cfg CompetitorSameBucketZeroCell.machine.start p m (right+1) left cap
          (out++CompetitorSameBucketKeyAppend.word p m 0 left right)) total (pos+2) := by
      apply configuration_ext
      · rfl
      · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,oh]
      · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ot]
    rw [hend] at iteration
    obtain ⟨tail,ht,ts,tf⟩:=ih (right+1) (pos+1) (out++CompetitorSameBucketKeyAppend.word p m 0 left right)
      (by omega) (by omega)
    have htail : runFrom machine (n*(CompetitorSameBucketZeroCell.budget p m+2)+total+3)
        (RepeatMachine.cfg 0
          (cfg CompetitorSameBucketZeroCell.machine.start p m (right+1) left cap
            (out++CompetitorSameBucketKeyAppend.word p m 0 left right)) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using ht
    rcases iteration with ⟨space,path⟩
    obtain ⟨actual,ha,af,ast,_⟩:=path.followedBy tail htail
    have bound : (one.steps+2)+(n*(CompetitorSameBucketZeroCell.budget p m+2)+total+3)≤
        (n+1)*(CompetitorSameBucketZeroCell.budget p m+2)+total+3 := by nlinarith
    have more:=runFrom_moreFuel machine _
      ((n+1)*(CompetitorSameBucketZeroCell.budget p m+2)+total+3-
        ((one.steps+2)+(n*(CompetitorSameBucketZeroCell.budget p m+2)+total+3))) _ actual ha
    rw [Nat.add_sub_of_le bound] at more
    refine ⟨actual,more,?_,?_⟩
    · rw [ast]; nlinarith
    · rw [af,tf]
      simp only [bits,List.append_assoc]
      rw [show right+1+n=right+(n+1) from by omega]

theorem row_run (p m left right cap n : ℕ) (out : List Bool)
    (hp : 2*(p+1)≤cap) (hm : 2*m≤cap) (hr : right+n<2^m) :
    ∃ actual,runFrom machine (budget p m n)
        (RepeatMachine.cfg 0 (cfg CompetitorSameBucketZeroCell.machine.start p m right left cap out) n 1)=some actual ∧
      actual.steps≤budget p m n ∧
      actual.final=RepeatMachine.cfg 3
        (cfg CompetitorSameBucketZeroCell.machine.start p m (right+n) left cap (out++bits p m left right n)) n 1 := by
  obtain ⟨actual,ha,ast,af⟩:=driver_run p m left right cap n n 0 out (by omega) hp hm hr
  have cost : n*(CompetitorSameBucketZeroCell.budget p m+2)+n+3=budget p m n := by unfold budget; ring
  rw [cost] at ha ast
  exact ⟨actual,ha,ast,af⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroRow
