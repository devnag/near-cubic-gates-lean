import Proof.Supplier.EquationScalarWidenValue
import Proof.PCP.VerifierDecodingRepeat

/-! The paid driver-controlled widening loop for one weight block. Source
and output cursors remain streaming; only the actual count driver rewinds. -/
namespace NearCubicWires.RepairOrdinary.EquationWidenLoop
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stream (p : ℕ) (values : List ℤ) : List Bool :=
  values.flatMap (fun z => frame (signMagnitude p z))
@[simp] theorem stream_nil (p : ℕ) : stream p []=[] := rfl
@[simp] theorem stream_cons (p : ℕ) (z : ℤ) (values : List ℤ) :
    stream p (z::values)=frame (signMagnitude p z)++stream p values := rfl

noncomputable def machine := RepeatMachine.machine EquationWiden.machine (fun _ _ => true)
noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos : ℕ)
    (out : List Bool) (total driver : ℕ) :=
  RepeatMachine.cfg phase (EquationWiden.cfg 0 source pos out) total driver

private theorem repeat_cfg_eq {t s : ℕ} (phase : Fin 5) (c d : Configuration t s)
    (total head : ℕ) (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total head=RepeatMachine.cfg phase d total head := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

theorem remaining (pre : List Bool) (values : List ℤ) (suffix out : List Bool)
    (p total pos : ℕ) (hn : pos+values.length=total)
    (hfit : ∀ z∈values,z.natAbs<2^p) :
    ∃ r,runFrom machine (values.length*(2*p+7)+total+3)
      (cfg 0 (pre++stream p values++suffix) pre.length out total (pos+1))=some r ∧
      r.final=cfg 3 (pre++stream p values++suffix) (pre.length+(stream p values).length)
        (out++stream (p+1) values) total 1 ∧
      r.steps ≤ values.length*(2*p+7)+total+3 := by
  induction values generalizing pre out pos with
  | nil =>
    have hp : pos=total := by simpa only [List.length_nil,Nat.add_zero] using hn
    subst pos
    have h := RepeatMachine.exhaust EquationWiden.machine (fun _ _ => true)
      (EquationWiden.cfg 0 (pre++suffix) pre.length out) total
    obtain ⟨r,hr,hf,hs⟩ := h.run (by
      simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,?_,?_⟩
    · simpa only [machine,cfg,stream_nil,List.append_nil,List.length_nil,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [cfg,stream_nil,List.append_nil,List.length_nil,Nat.add_zero] using hf
    · simp only [List.length_nil,Nat.zero_mul,Nat.zero_add]
      exact hs.le
  | cons z values ih =>
    obtain ⟨body,hb,bf,bs⟩ := EquationWiden.scalar_run pre (stream p values++suffix) out p z
      (hfit z (by simp))
    have hp := RepeatMachine.iteration EquationWiden.machine (fun _ _ => true)
      (EquationWiden.cfg 0 (pre++frame (signMagnitude p z)++(stream p values++suffix)) pre.length out)
      total pos body (by rfl) (by simp only [List.length_cons] at hn; omega) hb
    have he := repeat_cfg_eq 0 body.final
      (EquationWiden.cfg 0 (pre++frame (signMagnitude p z)++(stream p values++suffix))
        (pre.length+(frame (signMagnitude p z)).length) (out++frame (signMagnitude (p+1) z)))
      total (pos+2) (by rw [bf]; simp [EquationWiden.cfg,frame_length,signMagnitude_length]; omega)
      (by rw [bf]; rfl)
    change Timed machine (body.steps+2)
      (cfg 0 (pre++frame (signMagnitude p z)++(stream p values++suffix)) pre.length out total (pos+1))
      (RepeatMachine.cfg 0 body.final total (pos+2)) at hp
    rw [he] at hp
    obtain ⟨tail,ht,tf,ts⟩ := ih (pre++frame (signMagnitude p z))
      (out++frame (signMagnitude (p+1) z)) (pos+1)
      (by simp only [List.length_cons] at hn; omega)
      (by intro g hg; exact hfit g (by simp [hg]))
    have hmid : cfg 0 ((pre++frame (signMagnitude p z))++stream p values++suffix)
        (pre++frame (signMagnitude p z)).length (out++frame (signMagnitude (p+1) z)) total ((pos+1)+1)=
      RepeatMachine.cfg 0 (EquationWiden.cfg 0
        (pre++frame (signMagnitude p z)++(stream p values++suffix))
        (pre.length+(frame (signMagnitude p z)).length) (out++frame (signMagnitude (p+1) z)))
        total (pos+2) := by
      simp only [cfg,List.append_assoc,List.length_append,Nat.add_assoc]
    rw [hmid] at ht
    rcases hp with ⟨space,hp⟩
    obtain ⟨r,hr,hf,hs,_⟩ := hp.followedBy tail ht
    have htime : (body.steps+2)+(values.length*(2*p+7)+total+3) ≤
        (z::values).length*(2*p+7)+total+3 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have hm := runFrom_moreFuel machine _
      ((z::values).length*(2*p+7)+total+3-
        ((body.steps+2)+(values.length*(2*p+7)+total+3))) _ r hr
    rw [Nat.add_sub_of_le htime] at hm
    refine ⟨r,?_,?_,?_⟩
    · simpa only [stream_cons,List.append_assoc] using hm
    · rw [hf,tf]
      simp only [stream_cons,List.append_assoc,List.length_append,Nat.add_assoc]
    · rw [hs]
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem loop_run (pre : List Bool) (values : List ℤ) (suffix out : List Bool)
    (p : ℕ) (hfit : ∀ z∈values,z.natAbs<2^p) :
    ∃ r,runFrom machine (values.length*(2*p+8)+3)
      (cfg 0 (pre++stream p values++suffix) pre.length out values.length 1)=some r ∧
      r.final=cfg 3 (pre++stream p values++suffix) (pre.length+(stream p values).length)
        (out++stream (p+1) values) values.length 1 ∧
      r.steps ≤ values.length*(2*p+8)+3 := by
  have h := remaining pre values suffix out p values.length 0 (by omega) hfit
  have he : values.length*(2*p+7)+values.length+3=values.length*(2*p+8)+3 := by ring
  simpa only [he,Nat.zero_add] using h

end NearCubicWires.RepairOrdinary.EquationWidenLoop
