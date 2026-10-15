import Proof.Hierarchy.CompetitorSameBucketZeroBody

/-! Actual outer row repetition of the zero grid. Each inner row consumes
its real column sentinel, resets its tagged column, and increments its row. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroGrid
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open CompetitorSameBucketZeroBody (cfg)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted {s : ℕ} (_ : Fin s) (_ : Fin 13 → Bool):=true
noncomputable def machine:=RepeatMachine.machine CompetitorSameBucketZeroBody.machine accepted
def bits (p m u : ℕ) : ℕ → ℕ → List Bool
  | _,0 => []
  | left,n+1 => CompetitorSameBucketZeroRow.bits p m left u u++bits p m u (left+1) n
def budget (p m u cap n : ℕ):=n*(CompetitorSameBucketZeroBody.budget p m u cap+3)+3

theorem driver_run (p m u left cap n total pos : ℕ) (out : List Bool)
    (hpos : pos+n=total) (hp : 2*(p+1)≤cap) (hc : 4*m+3≤cap) (hu : u+u<2^m) (hl : left+n<2^m) :
    ∃ actual,runFrom machine (n*(CompetitorSameBucketZeroBody.budget p m u cap+2)+total+3)
        (RepeatMachine.cfg 0 (cfg CompetitorSameBucketZeroBody.machine.start p m u left cap out) total (pos+1))=some actual ∧
      actual.steps≤n*(CompetitorSameBucketZeroBody.budget p m u cap+2)+total+3 ∧
      actual.final=RepeatMachine.cfg 3
        (cfg CompetitorSameBucketZeroBody.machine.start p m u (left+n) cap (out++bits p m u left n)) total 1 := by
  induction n generalizing left pos out with
  | zero =>
    have he : pos=total := by omega
    subst pos
    obtain ⟨actual,ha,af,ast⟩:=(RepeatMachine.exhaust CompetitorSameBucketZeroBody.machine accepted
      (cfg CompetitorSameBucketZeroBody.machine.start p m u left cap out) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨actual,by simpa [machine] using ha,by simpa using ast.le,by simpa [bits] using af⟩
  | succ n ih =>
    obtain ⟨one,ho,oh,ot,os⟩:=CompetitorSameBucketZeroBody.body_run p m u left cap out hp hc hu (by omega)
    have iteration:=RepeatMachine.iteration CompetitorSameBucketZeroBody.machine accepted
      (cfg CompetitorSameBucketZeroBody.machine.start p m u left cap out) total pos one rfl (by omega) ho
    simp only [accepted,if_true] at iteration
    have hend : RepeatMachine.cfg 0 one.final total (pos+2)=RepeatMachine.cfg 0
        (cfg CompetitorSameBucketZeroBody.machine.start p m u (left+1) cap
          (out++CompetitorSameBucketZeroRow.bits p m left u u)) total (pos+2) := by
      apply configuration_ext
      · rfl
      · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,oh]
      · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ot]
    rw [hend] at iteration
    obtain ⟨tail,ht,ts,tf⟩:=ih (left+1) (pos+1) (out++CompetitorSameBucketZeroRow.bits p m left u u)
      (by omega) (by omega)
    have htail : runFrom machine (n*(CompetitorSameBucketZeroBody.budget p m u cap+2)+total+3)
        (RepeatMachine.cfg 0
          (cfg CompetitorSameBucketZeroBody.machine.start p m u (left+1) cap
            (out++CompetitorSameBucketZeroRow.bits p m left u u)) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using ht
    rcases iteration with ⟨space,path⟩
    obtain ⟨actual,ha,af,ast,_⟩:=path.followedBy tail htail
    have bound : (one.steps+2)+(n*(CompetitorSameBucketZeroBody.budget p m u cap+2)+total+3)≤
        (n+1)*(CompetitorSameBucketZeroBody.budget p m u cap+2)+total+3 := by nlinarith
    have more:=runFrom_moreFuel machine _
      ((n+1)*(CompetitorSameBucketZeroBody.budget p m u cap+2)+total+3-
        ((one.steps+2)+(n*(CompetitorSameBucketZeroBody.budget p m u cap+2)+total+3))) _ actual ha
    rw [Nat.add_sub_of_le bound] at more
    refine ⟨actual,more,?_,?_⟩
    · rw [ast]; nlinarith
    · rw [af,tf]
      simp only [bits,List.append_assoc]
      rw [show left+1+n=left+(n+1) from by omega]

theorem grid_run (p m u left cap n : ℕ) (out : List Bool)
    (hp : 2*(p+1)≤cap) (hc : 4*m+3≤cap) (hu : u+u<2^m) (hl : left+n<2^m) :
    ∃ actual,runFrom machine (budget p m u cap n)
        (RepeatMachine.cfg 0 (cfg CompetitorSameBucketZeroBody.machine.start p m u left cap out) n 1)=some actual ∧
      actual.steps≤budget p m u cap n ∧
      actual.final=RepeatMachine.cfg 3
        (cfg CompetitorSameBucketZeroBody.machine.start p m u (left+n) cap (out++bits p m u left n)) n 1 := by
  obtain ⟨actual,ha,ast,af⟩:=driver_run p m u left cap n n 0 out (by omega) hp hc hu hl
  have cost : n*(CompetitorSameBucketZeroBody.budget p m u cap+2)+n+3=budget p m u cap n := by unfold budget; ring
  rw [cost] at ha ast
  exact ⟨actual,ha,ast,af⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroGrid
