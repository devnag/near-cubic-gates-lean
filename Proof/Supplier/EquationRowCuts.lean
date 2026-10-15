import Proof.Supplier.EquationCut

/-! Execute the accepted two-cut emitter once per original equation, using
one physical G driver. No cut buffer, scalar workspace or cursor is free. -/
namespace NearCubicWires.RepairOrdinary.EquationRowCuts
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def stream (p : Nat) (cuts : List Cut) := cuts.flatMap (cutWord p)
def output (p : Nat) (odd : Bool) (cuts : List Cut) := cuts.flatMap (EquationCut.Ambient.output p odd)
def machine := RepeatMachine.machine EquationCut.Ambient.machine (fun _ _=>true)
def cfg (phase : Fin 5) (source out : List Bool) (pos C L p : Nat) (odd : Bool) (total driver : Nat) :=
  RepeatMachine.cfg phase (EquationCut.Ambient.entry C pos source out L p odd) total driver
def budget (G C : Nat) := G*(16*C+3)+3

@[simp] theorem stream_nil (p : Nat) : stream p []=[] := rfl
@[simp] theorem stream_cons (p : Nat) (c : Cut) (cuts : List Cut) :
    stream p (c::cuts)=cutWord p c++stream p cuts := rfl
@[simp] theorem output_nil (p : Nat) (odd : Bool) : output p odd []=[] := rfl
@[simp] theorem output_cons (p : Nat) (odd : Bool) (c : Cut) (cuts : List Cut) :
    output p odd (c::cuts)=EquationCut.Ambient.output p odd c++output p odd cuts := rfl

theorem output_literal (p : Nat) (odd : Bool) (cuts : List Cut) :
    output p odd cuts=(EquationRow.doubled odd cuts).flatMap (cutWord (p+1)) := by
  induction cuts with
  | nil => rfl
  | cons c cuts ih => simp [output,EquationCut.Ambient.output,EquationRow.doubled] at *; exact ih

private theorem repeat_cfg_eq {t s : Nat} (phase : Fin 5) (c d : Configuration t s)
    (total driver : Nat) (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total driver=RepeatMachine.cfg phase d total driver := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

theorem remaining (pre : List Bool) (cuts : List Cut) (suffix out : List Bool)
    (C L p : Nat) (odd : Bool) (total pos : Nat) (hn : pos+cuts.length=total)
    (hL : ∀ c∈cuts,(EquationCut.weights c).length=L)
    (hfit : ∀ c∈cuts,EquationRow.Fits p c) (hC : 128*(L+1)*(p+1) ≤ C) :
    ∃ r,runFrom machine (cuts.length*(16*C+2)+total+3)
      (cfg 0 (pre++stream p cuts++suffix) out pre.length C L p odd total (pos+1))=some r ∧
      r.final=cfg 3 (pre++stream p cuts++suffix) (out++output p odd cuts)
        (pre.length+(stream p cuts).length) C L p odd total 1 ∧
      r.steps ≤ cuts.length*(16*C+2)+total+3 := by
  induction cuts generalizing pre out pos with
  | nil =>
    have he : pos=total := by simpa only [List.length_nil,Nat.add_zero] using hn
    subst pos
    have h := RepeatMachine.exhaust EquationCut.Ambient.machine (fun _ _=>true)
      (EquationCut.Ambient.entry C pre.length (pre++suffix) out L p odd) total
    obtain ⟨r,hr,hf,hs⟩ := h.run (by
      simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨r,by simpa only [machine,cfg,stream_nil,List.append_nil,List.length_nil,Nat.zero_mul,Nat.zero_add] using hr,
      by simpa only [cfg,stream_nil,output_nil,List.append_nil,List.length_nil,Nat.add_zero] using hf,
      by simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using hs.le⟩
  | cons c cuts ih =>
    obtain ⟨body,hb,bh,bt,bs⟩ := EquationCut.Ambient.cut_run pre (stream p cuts++suffix) out C p odd c
      (hfit c (by simp)) (by rw [hL c (by simp)]; exact hC)
    rw [hL c (by simp)] at hb bt
    have hp := RepeatMachine.iteration EquationCut.Ambient.machine (fun _ _=>true)
      (EquationCut.Ambient.entry C pre.length (pre++cutWord p c++(stream p cuts++suffix)) out L p odd)
      total pos body (by rfl) (by simp only [List.length_cons] at hn; omega) hb
    have he := repeat_cfg_eq 0 body.final
      (EquationCut.Ambient.entry C (pre.length+(cutWord p c).length)
        (pre++cutWord p c++(stream p cuts++suffix)) (out++EquationCut.Ambient.output p odd c) L p odd)
      total (pos+2) bh bt
    change Timed machine (body.steps+2)
      (cfg 0 (pre++cutWord p c++(stream p cuts++suffix)) out pre.length C L p odd total (pos+1))
      (RepeatMachine.cfg 0 body.final total (pos+2)) at hp
    rw [he] at hp
    obtain ⟨tail,ht,tf,ts⟩ := ih (pre++cutWord p c) (out++EquationCut.Ambient.output p odd c) (pos+1)
      (by simp only [List.length_cons] at hn; omega)
      (by intro d hd; exact hL d (by simp [hd]))
      (by intro d hd; exact hfit d (by simp [hd]))
    have hmid : cfg 0 ((pre++cutWord p c)++stream p cuts++suffix)
        (out++EquationCut.Ambient.output p odd c) (pre++cutWord p c).length C L p odd total ((pos+1)+1)=
      RepeatMachine.cfg 0 (EquationCut.Ambient.entry C (pre.length+(cutWord p c).length)
        (pre++cutWord p c++(stream p cuts++suffix)) (out++EquationCut.Ambient.output p odd c) L p odd) total (pos+2) := by
      simp only [cfg,List.append_assoc,List.length_append,Nat.add_assoc]
    rw [hmid] at ht
    rcases hp with ⟨space,hp⟩
    obtain ⟨r,hr,hf,hs,_⟩ := hp.followedBy tail ht
    have htime : (body.steps+2)+(cuts.length*(16*C+2)+total+3) ≤
        (c::cuts).length*(16*C+2)+total+3 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      change body.steps ≤ 16*C at bs
      omega
    have hm := runFrom_moreFuel machine _
      ((c::cuts).length*(16*C+2)+total+3-((body.steps+2)+(cuts.length*(16*C+2)+total+3))) _ r hr
    rw [Nat.add_sub_of_le htime] at hm
    refine ⟨r,?_,?_,?_⟩
    · simpa only [stream_cons,List.append_assoc] using hm
    · rw [hf,tf]
      simp only [stream_cons,output_cons,List.append_assoc,List.length_append,Nat.add_assoc]
    · rw [hs]
      change body.steps ≤ 16*C at bs
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

/-- Exact22-tape all-cut pass, including the final physical G-driver rewind. -/
theorem loop_run (pre : List Bool) (cuts : List Cut) (suffix out : List Bool)
    (C L p : Nat) (odd : Bool)
    (hL : ∀ c∈cuts,(EquationCut.weights c).length=L)
    (hfit : ∀ c∈cuts,EquationRow.Fits p c) (hC : 128*(L+1)*(p+1) ≤ C) :
    ∃ r,runFrom machine (budget cuts.length C)
      (cfg 0 (pre++stream p cuts++suffix) out pre.length C L p odd cuts.length 1)=some r ∧
      r.final=cfg 3 (pre++stream p cuts++suffix) (out++output p odd cuts)
        (pre.length+(stream p cuts).length) C L p odd cuts.length 1 ∧ r.steps ≤ budget cuts.length C := by
  have h := remaining pre cuts suffix out C L p odd cuts.length 0 (by omega) hL hfit hC
  have he : cuts.length*(16*C+2)+cuts.length+3=budget cuts.length C := by unfold budget; ring
  simpa only [he,Nat.zero_add] using h

end
end NearCubicWires.RepairOrdinary.EquationRowCuts
