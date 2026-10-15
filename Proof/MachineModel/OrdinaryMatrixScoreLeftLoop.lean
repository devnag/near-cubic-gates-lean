import Proof.MachineModel.OrdinaryMatrixScoreLeftNext

/-! The remaining left assignments are enumerated by the actual retained
U-sentinel, beginning at head2 after assignment0. The assignment of row `n` is
its center-bit vector `φ(n)` (paper3 `alg:pullback`), written by the advance
from the id and the `φ` columns. All numeric obligations come from the literal
raw matrix request, including the d=0 case. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreLeftLoop
open LocalBitMultitape RecoveryExecution SignedSortKey MatrixScoreBatch
open MatrixScoreWeight (zeros)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def C (r : Request) := 4*((r.S+1)+r.M)+18
def bodyBudget (r : Request) := MatrixScoreLeftRecord.budget r.width r.p r.S (C r) r.M
structure State (r : Request) where
  work : Fin 12 → List Bool
  bounded : ∀ i,(work i).length≤C r
  returnCap : ℕ
  returnBound : returnCap≤bodyBudget r

def record (r : Request) (gate : Fin r.Gates) (n : ℕ) : List Bool :=
  StablePartition.recordBits (encode r.S r.M
    ((r.cuts.get gate).threshold-linearForm (r.cuts.get gate).leftWeights (r.phi n)) n)
def records (r : Request) (gate : Fin r.Gates) : ℕ → ℕ → List Bool
  | _,0 => []
  | n,k+1 => record r gate n++records r gate (n+1) k
noncomputable def data (r : Request) (gate : Fin r.Gates) (n : ℕ) (state : State r) (out : List Bool) :=
  RecoveryCalls.restarted MatrixScoreLeftNext.machine (MatrixScorePhiLayout.heads out.length)
    (MatrixScorePhiLayout.tapes (cutWord r.p (r.cuts.get gate)) (frame (binary r.width (r.phi n))) r.width (C r) (C r+1)
      (r.S+1) (2^r.S) r.M n r.U state.work (ZeroPadding.pad (C r) [true,true]) (zeros (C r)) out state.returnCap
      r.cols)
def accepted {s : ℕ} (_ : Fin s) (_ : Fin 28 → Bool) := true
noncomputable def machine := RepeatMachine.machine MatrixScoreLeftNext.machine accepted

theorem source_eq (r : Request) (gate : Fin r.Gates) :
    MatrixScoreCanonical.fields r.p (r.cuts.get gate).leftWeights++
      MatrixScoreCanonical.fields r.p (r.cuts.get gate).rightWeights++
      frame (signMagnitude r.p (r.cuts.get gate).threshold)++
      frame (signMagnitude r.p (r.cuts.get gate).coefficient)=cutWord r.p (r.cuts.get gate) := by
  simp [MatrixScoreCanonical.fields,cutWord,fields,List.flatMap_append,List.append_assoc]

theorem partial_fit (r : Request) (gate : Fin r.Gates) (n : ℕ) (sign : Bool) :
    part sign (r.cuts.get gate).leftWeights n+(r.cuts.get gate).threshold.natAbs<2^r.S := by
  have mem := List.get_mem r.cuts gate
  have hl := (r.lengths _ mem).1
  obtain ⟨hw,ht,_⟩ := r.fits _ mem
  have hp := part_bound (r.cuts.get gate).leftWeights n r.p sign
    (by intro z hz; exact hw z (List.mem_append_left _ hz))
  rw [hl] at hp
  have hlarge := score_bound r
  have hprod : (r.width+1)*2^r.p=r.width*2^r.p+2^r.p := by ring
  rw [hprod] at hlarge
  omega

theorem next_state_run (r : Request) (gate : Fin r.Gates) (n : ℕ) (state : State r) (out : List Bool)
    (hn : n+1<r.U) :
    ∃ next : State r,∃ actual,
      runFrom MatrixScoreLeftNext.machine (MatrixScoreLeftNext.budget r.width r.p r.S (C r) r.M r.d)
        (data r gate n state out)=some actual ∧
      actual.final.heads=(data r gate (n+1) next (out++record r gate (n+1))).heads ∧
      actual.final.tapes=(data r gate (n+1) next (out++record r gate (n+1))).tapes ∧
      actual.steps≤MatrixScoreLeftNext.budget r.width r.p r.S (C r) r.M r.d := by
  have mem := List.get_mem r.cuts gate
  obtain ⟨hl,hr⟩ := r.lengths _ mem
  obtain ⟨hweights,htheta,_⟩ := r.fits _ mem
  have hcommon := common_width r
  have hc : 4*(r.S+1)+5≤C r := by unfold C; omega
  have hm : 2*r.M≤C r := by unfold C; omega
  have hwl := r.widthLe
  have hphi : (r.cuts.get gate).leftWeights.length+r.cols.length+2 ≤ C r := by
    rw [hl,cols_length]; unfold C; omega
  have hid : n+1<2^r.M := hn.trans (by rw [hcommon]; exact Nat.pow_lt_pow_right (by decide) (by omega))
  have hrcap : state.returnCap≤MatrixScoreLeftRecord.budget (r.cuts.get gate).leftWeights.length r.p r.S (C r) r.M := by
    rw [hl]
    exact state.returnBound
  obtain ⟨work,hws,returnCap,hrb,actual,ha,ah,atapes,as⟩ := MatrixScoreLeftNext.next_run
    (r.cuts.get gate).leftWeights (r.cuts.get gate).rightWeights
    (frame (signMagnitude r.p (r.cuts.get gate).coefficient))
    r.p (r.phi n) r.S (C r) (C r+1) r.M n r.U state.returnCap (r.cuts.get gate).threshold state.work
    (ZeroPadding.pad (C r) [true,true]) (zeros (C r)) out r.cols (by omega)
    (by intro z hz; exact hweights z (List.mem_append_left _ hz)) htheta
    (by unfold Request.S; omega) hc hm (by omega) state.bounded
    (by simp only [ZeroPadding.pad_length,List.length_cons,List.length_nil]; omega)
    (by simp [zeros]) hrcap (by rw [hl]; exact phi_lt r n) hid (by rw [cols_length,hcommon]; omega)
    (by rw [hl]; exact cols_fit r) hphi
    (partial_fit r gate (r.phi (n+1)) true) (partial_fit r gate (r.phi (n+1)) false)
  simp only [hl,cols_length] at ha ah atapes as hrb
  rw [source_eq] at ha atapes
  let next : State r := ⟨work,hws,returnCap,hrb⟩
  exact ⟨next,actual,ha,ah,atapes,as⟩

theorem loop_run (r : Request) (gate : Fin r.Gates) (remaining n : ℕ) (state : State r) (out : List Bool)
    (hcount : n+remaining+1=r.U) :
    ∃ final : State r,∃ actual,
      runFrom machine (remaining*(MatrixScoreLeftNext.budget r.width r.p r.S (C r) r.M r.d+2)+r.U+3)
        (RepeatMachine.cfg 0 (data r gate n state out) r.U (n+2))=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (data r gate (n+remaining) final (out++records r gate (n+1) remaining)) r.U 1 ∧
      actual.steps≤remaining*(MatrixScoreLeftNext.budget r.width r.p r.S (C r) r.M r.d+2)+r.U+3 := by
  induction remaining generalizing n state out with
  | zero =>
    have hpos : n+2=r.U+1 := by omega
    obtain ⟨actual,hr,hf,hs⟩ := (RepeatMachine.exhaust MatrixScoreLeftNext.machine accepted (data r gate n state out) r.U).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨state,actual,?_,?_,?_⟩
    · simpa [machine,hpos] using hr
    · simpa [records] using hf
    · simpa using hs.le
  | succ remaining ih =>
    have hn : n+1<r.U := by omega
    obtain ⟨next,body,hb,bh,bt,bs⟩ := next_state_run r gate n state out hn
    have iteration := RepeatMachine.iteration MatrixScoreLeftNext.machine accepted (data r gate n state out) r.U (n+1)
      body rfl hn hb
    simp only [accepted,if_true] at iteration
    have hi : RepeatMachine.cfg 0 body.final r.U (n+1+2)=
        RepeatMachine.cfg 0 (data r gate (n+1) next (out++record r gate (n+1))) r.U (n+1+2) := by
      apply configuration_ext
      · rfl
      · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,bh]
      · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,bt]
    rw [hi] at iteration
    obtain ⟨final,tail,ht,htf,hts⟩ := ih (n+1) next (out++record r gate (n+1)) (by omega)
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨actual,ha,haf,has,_⟩ := hprefix.followedBy tail ht
    have hsmall : body.steps+2+(remaining*(MatrixScoreLeftNext.budget r.width r.p r.S (C r) r.M r.d+2)+r.U+3)≤
        (remaining+1)*(MatrixScoreLeftNext.budget r.width r.p r.S (C r) r.M r.d+2)+r.U+3 := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    have he := runFrom_moreFuel machine _
      (((remaining+1)*(MatrixScoreLeftNext.budget r.width r.p r.S (C r) r.M r.d+2)+r.U+3)-
        (body.steps+2+(remaining*(MatrixScoreLeftNext.budget r.width r.p r.S (C r) r.M r.d+2)+r.U+3))) _ actual ha
    rw [Nat.add_sub_of_le hsmall] at he
    refine ⟨final,actual,?_,?_,?_⟩
    · simpa only [Nat.add_assoc] using he
    · rw [haf,htf]
      simp only [records,List.append_assoc,Nat.add_assoc,Nat.add_comm 1 remaining]
    · rw [has]
      omega

end NearCubicWires.RepairOrdinary.MatrixScoreLeftLoop
