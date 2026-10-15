import Proof.Amplification.RecoveryBoundedNativeUnaryBodyRun

/-! The actual unary-equality literal loop is driven by the retained limit
sentinel. Every iteration reads the original value at its current offset. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  index : ℕ
  position : ℕ
  offset : ℕ
  flag : Bool
  out : List Bool
  stack : List Bool
def State.next (value : ℕ) (a : State) : State :=
  let negative:=RecoveryBoundedNativeUnaryFlag.negative value a.offset
  ⟨a.index+1,a.position+negative.toNat+1,a.offset+1,negative,
    a.out++RecoveryBoundedNativeLiteral.emitted a.index a.position negative,
    RecoveryBoundedNativeLiteralStack.stackWord (a.position+negative.toNat) a.stack⟩
def State.iterate (value : ℕ) : ℕ→State→State
  | 0,a=>a
  | count+1,a=>State.iterate value count (a.next value)
noncomputable def State.entry (C value : ℕ) (a : State) :=
  RecoveryBoundedNativeUnaryBody.entry a.index a.position C value a.offset a.flag a.out a.stack
noncomputable def machine:=RepeatMachine.machine RecoveryBoundedNativeUnaryBody.machine (fun _ _=>true)
noncomputable def configuration (phase : Fin 5) (C value : ℕ) (a : State) (total driver : ℕ) :=
  RepeatMachine.cfg phase (a.entry C value) total driver

private theorem cfg_data {t s : ℕ} (phase : Fin 5) (c d : Configuration t s) (total driver : ℕ)
    (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total driver=RepeatMachine.cfg phase d total driver := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

theorem loop_run (count W C value total : ℕ) (a : State)
    (htotal : a.offset+count=total) (hi : a.index+count ≤ W)
    (hp : a.position+2*count ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r, runFrom machine (count*(32*C+106)+total+3)
      (configuration 0 C value a total (a.offset+1))=some r ∧
      r.final=configuration 3 C value (a.iterate value count) total 1 ∧
      r.steps ≤ count*(32*C+106)+total+3 := by
  induction count generalizing a with
  | zero=>
    have hoff : a.offset=total := by omega
    obtain ⟨r,hr,rf,rs⟩:=(RepeatMachine.exhaust RecoveryBoundedNativeUnaryBody.machine (fun _ _=>true)
      (a.entry C value) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,rf,?_⟩
    · simpa only [machine,configuration,hoff,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [Nat.zero_mul,Nat.zero_add] using rs.le
  | succ count ih=>
    obtain ⟨first,hfirst,fs,fh,ft⟩:=RecoveryBoundedNativeUnaryBody.body_run
      a.index a.position W C value a.offset a.flag a.out a.stack (by omega) (by omega) hC
    have hiteration:=RepeatMachine.iteration RecoveryBoundedNativeUnaryBody.machine (fun _ _=>true)
      (a.entry C value) total a.offset first rfl (by omega) hfirst
    change Timed machine (first.steps+2) (configuration 0 C value a total (a.offset+1))
      (RepeatMachine.cfg 0 first.final total (a.offset+2)) at hiteration
    rw [cfg_data 0 first.final ((a.next value).entry C value) total (a.offset+2) fh ft] at hiteration
    have hnegative : (RecoveryBoundedNativeUnaryFlag.negative value a.offset).toNat ≤ 1 := by
      cases RecoveryBoundedNativeUnaryFlag.negative value a.offset <;> decide
    obtain ⟨last,hl,lf,ls⟩:=ih (a.next value)
      (by dsimp only [State.next]; omega)
      (by dsimp only [State.next]; omega)
      (by dsimp only [State.next]; omega)
    have he : a.offset+2=(a.next value).offset+1 := by rfl
    rw [he] at hiteration
    rcases hiteration with ⟨space,hprefix⟩
    obtain ⟨r,hr,rf,rs,_⟩:=hprefix.followedBy last hl
    have hbudget : first.steps+2+(count*(32*C+106)+total+3) ≤
        (count+1)*(32*C+106)+total+3 := by
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    have more:=runFrom_moreFuel machine _
      ((count+1)*(32*C+106)+total+3-(first.steps+2+(count*(32*C+106)+total+3))) _ r hr
    rw [Nat.add_sub_of_le hbudget] at more
    refine ⟨r,more,rf.trans lf,?_⟩
    rw [rs]
    omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryLoop
