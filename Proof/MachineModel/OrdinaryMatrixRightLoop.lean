import Proof.MachineModel.OrdinaryMatrixRightBucket

/-! The whole right-bucket traversal executes the repeatable bucket body
from the physical count driver, preserves aggregate output, and pays the
final driver rewind. Width guards apply to all visited boundary values. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightLoop
open LocalBitMultitape RecoveryExecution
open MatrixRightAdvance (Store)
open MatrixRightBucket (Params width fuel cfg)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cost (p : Params) := 2*fuel p+24*width p+4*p.I+33
noncomputable def machine := RepeatMachine.machine MatrixRightBucket.machine (fun _ _ => true)
def output (p : Params) : ℕ → ℕ → ℕ → List Bool
  | _,_,0 => []
  | a,inner,n+1 => MatrixRightBucket.output p a inner++output p (a+p.B) (inner+1) n

theorem driver_run (p : Params) (total n pos : ℕ) (v : Store) (hn : pos+n=total)
    (ha : v.a+n*p.B<2^width p) (hi : v.inner+n<2^p.I)
    (hu : v.upper.length ≤ 2*width p+1) (hr : v.record.length ≤ 4*width p+1)
    (hc : v.clone.length ≤ 4*width p+1) :
    ∃ final : Store,final.upper.length ≤ 2*width p+1 ∧ final.record.length ≤ 4*width p+1 ∧
      final.clone.length ≤ 4*width p+1 ∧ final.a=v.a+n*p.B ∧ final.inner=v.inner+n ∧
      final.out=v.out++output p v.a v.inner n ∧
      ∃ actual,runFrom machine (n*(cost p+2)+total+3)
        (RepeatMachine.cfg 0 (cfg MatrixRightBucket.machine.start p v) total (pos+1))=some actual ∧
        actual.steps ≤ n*(cost p+2)+total+3 ∧
        actual.final=RepeatMachine.cfg 3 (cfg MatrixRightBucket.machine.start p final) total 1 := by
  induction n generalizing pos v with
  | zero =>
    have hp : pos=total := by omega
    subst pos
    obtain ⟨r,hrun,hf,hs⟩ := (RepeatMachine.exhaust MatrixRightBucket.machine (fun _ _ => true)
      (cfg MatrixRightBucket.machine.start p v) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨v,hu,hr,hc,by omega,by omega,by simp [output],r,?_,?_,hf⟩
    · simpa only [machine,Nat.zero_mul,Nat.zero_add] using hrun
    · simpa using hs.le
  | succ n ih =>
    have ha1 : v.a+p.B<2^width p := by
      have hb : p.B ≤ (n+1)*p.B := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hi1 : v.inner+1<2^p.I := by omega
    obtain ⟨rank,record,clone,hrecord,hclone,body,hbody,hbf,hbs⟩ := MatrixRightBucket.bucket_run p v ha1 hi1 hu hr hc
    let state : Store :=
      {v with
        a := v.a+p.B
        b := p.B
        inner := v.inner+1
        rank := rank
        upper := frame (SignedSortKey.binary (width p) (v.a+p.B))
        record := record
        clone := clone
        out := v.out++MatrixRightBucket.output p v.a v.inner}
    have hstate : body.final=cfg 85 p state := hbf
    have hat : state.a+n*p.B<2^width p := by
      simpa only [state,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ha
    have hit : state.inner+n<2^p.I := by dsimp [state]; omega
    have hut : state.upper.length ≤ 2*width p+1 := by simp [state]
    obtain ⟨final,hfu,hfr,hfc,hfa,hfi,hfo,tail,htail,hts,htf⟩ := ih (pos+1) state (by omega) hat hit hut hrecord hclone
    have hp := RepeatMachine.iteration MatrixRightBucket.machine (fun _ _ => true)
      (cfg MatrixRightBucket.machine.start p v) total pos body rfl (by omega) hbody
    simp only [↓reduceIte] at hp
    have he : RepeatMachine.cfg 0 body.final total (pos+2)=
        RepeatMachine.cfg 0 (cfg MatrixRightBucket.machine.start p state) total (pos+2) := by
      rw [hstate]
      rfl
    rw [he] at hp
    rcases hp with ⟨space,hp⟩
    have htail' : runFrom machine (n*(cost p+2)+total+3)
        (RepeatMachine.cfg 0 (cfg MatrixRightBucket.machine.start p state) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    obtain ⟨actual,haRun,hf,hs,_⟩ := hp.followedBy tail htail'
    have hbnd : body.steps+2+(n*(cost p+2)+total+3) ≤ (n+1)*(cost p+2)+total+3 := by
      change body.steps ≤ cost p at hbs
      nlinarith only [hbs]
    have hm := runFrom_moreFuel machine _
      ((n+1)*(cost p+2)+total+3-(body.steps+2+(n*(cost p+2)+total+3))) _ actual haRun
    rw [Nat.add_sub_of_le hbnd] at hm
    refine ⟨final,hfu,hfr,hfc,?_,?_,?_,actual,hm,?_,hf.trans htf⟩
    · simpa only [state,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hfa
    · dsimp [state] at hfi
      omega
    · simpa only [state,output,List.append_assoc] using hfo
    · rw [hs]
      change body.steps ≤ cost p at hbs
      nlinarith only [hbs,hts]

theorem loop_run (p : Params) (total : ℕ) (v : Store)
    (ha : v.a+total*p.B<2^width p) (hi : v.inner+total<2^p.I)
    (hu : v.upper.length ≤ 2*width p+1) (hr : v.record.length ≤ 4*width p+1)
    (hc : v.clone.length ≤ 4*width p+1) :
    ∃ final : Store,final.upper.length ≤ 2*width p+1 ∧ final.record.length ≤ 4*width p+1 ∧
      final.clone.length ≤ 4*width p+1 ∧ final.a=v.a+total*p.B ∧ final.inner=v.inner+total ∧
      final.out=v.out++output p v.a v.inner total ∧
      ∃ actual,runFrom machine (total*(cost p+3)+3)
        (RepeatMachine.cfg 0 (cfg MatrixRightBucket.machine.start p v) total 1)=some actual ∧
        actual.steps ≤ total*(cost p+3)+3 ∧
        actual.final=RepeatMachine.cfg 3 (cfg MatrixRightBucket.machine.start p final) total 1 := by
  have h := driver_run p total total 0 v (by omega) ha hi hu hr hc
  have ht : total*(cost p+2)+total+3=total*(cost p+3)+3 := by ring
  simpa only [ht,Nat.zero_add] using h

end NearCubicWires.RepairOrdinary.MatrixRightLoop
