import Proof.MachineModel.OrdinaryMatrixBatchWorkspace
import Proof.MachineModel.OrdinaryMatrixScoreRetainedRanks
import Proof.MachineModel.OrdinaryMatrixScorePhiFields

/-! The shared score/rank call on the finite zero backing produced by the
gate caller's erase. This is the same ordinary 41-tape program. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreReusableRanks
open LocalBitMultitape SignedSortKey MatrixScoreBatch
open MatrixScoreLeftLoop (C State)
open MatrixScoreWeight (zeros)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def D (r : Request) := MatrixBatchCapacity.capacity (C r) r.U
def cold (r : Request) : State r := ⟨fun _ => [],by simp,0,Nat.zero_le _⟩
def fixed (i : Fin 42) : Bool := decide (i∈([1,6,15,16,17,18,19,22,23,25,27,28,29] : List (Fin 42)))
def capacities (r : Request) (i : Fin 42) := if fixed i then 0 else D r
/-- The per-gate fields: piece 0's 42-slot contract (`φ` columns at slot 27). -/
def fields (r : Request) (gate : Fin r.Gates) : Fin 42 → List Bool := MatrixScorePhiFields.fields r gate
noncomputable def input (r : Request) (gate : Fin r.Gates) :=
  ZeroPadding.config (capacities r) (MatrixScoreRetainedRanks.input r gate (cold r))

theorem input_fields (r : Request) (gate : Fin r.Gates) :
    (MatrixScoreRetainedRanks.input r gate (cold r)).tapes=fields r gate := by
  funext i
  fin_cases i <;> rfl
theorem input_heads (r : Request) (gate : Fin r.Gates) :
    (MatrixScoreRetainedRanks.input r gate (cold r)).heads=MatrixScoreRetainedRanks.retainedHeads := by
  funext i
  fin_cases i <;> rfl

theorem capacity_gap (r : Request) : MatrixScoreRawRanksBounds.capacity r+2≤D r := by
  have hu : 1≤r.U := Nat.one_le_two_pow
  have hc : 4*(r.d+r.p+1)≤C r+1 := by unfold C Request.S; rw [common_width]; omega
  have hs := Nat.pow_le_pow_left hc 2
  have hm := Nat.mul_le_mul_left r.U hs
  have hq : 1≤(r.d+r.p+1)^2 := by
    have hp : 0<(r.d+r.p+1)^2 := by positivity
    omega
  unfold D MatrixBatchCapacity.capacity MatrixScoreRawRanksBounds.capacity
  nlinarith [Nat.mul_le_mul_left ((r.d+r.p+1)^2) hu]

theorem small_bounds (r : Request) : C r+1≤D r ∧ r.U+2≤D r := by
  have hu : 1≤r.U := Nat.one_le_two_pow
  have hs : 1≤(C r+1)^2 := by
    have hp : 0<(C r+1)^2 := by positivity
    omega
  have hc : C r+1≤(C r+1)^2 := by nlinarith
  have hm := Nat.mul_le_mul_left ((C r+1)^2) hu
  have hn := Nat.mul_le_mul_left r.U hs
  unfold D MatrixBatchCapacity.capacity
  constructor <;> nlinarith

theorem budget_le (r : Request) (gate : Fin r.Gates) :
    MatrixScoreRetainedRanks.budget r gate≤MatrixScoreRawRanks.budget r gate := by
  have hb := MatrixScoreRawGateBounds.budget_le r gate
  have hs : MatrixScoreRetainedRanks.scoreBudget r≤MatrixScoreRawGate.budget r gate := by
    unfold MatrixScoreRetainedRanks.scoreBudget MatrixScoreRawGate.budget MatrixScoreRawGate.coreBudget
    omega
  unfold MatrixScoreRetainedRanks.budget MatrixScoreRawRanks.budget
  omega

theorem input_fits (r : Request) (gate : Fin r.Gates) : ∀ i,(fields r gate i).length≤D r := by
  obtain ⟨hc,hu⟩ := small_bounds r
  have hm := common_width r
  have hcap := (MatrixBatchCapacity.request_capacity r).1
  have hcut := MatrixScoreRawRanksBounds.input_fit r gate
  simp only [frame_length,gateWord,List.length_append] at hcut
  have hfield : (cutWord r.p (r.cuts.get gate)).length≤D r := by change _≤D r at hcap; omega
  have hwl := r.widthLe
  have hd : 2*r.width+2≤C r := by unfold C; omega
  have hw : 2*(r.S+1)+1≤C r := by unfold C; omega
  have hM : 2*r.M+1≤C r := by unfold C; omega
  have hcols : (MatrixScorePhi.columnsWord r.width r.cols).length≤D r := by
    rw [MatrixScorePhi.columnsWord_length,cols_length]
    have hU : 1≤r.U := Nat.one_le_two_pow
    have hwd : r.width+1≤C r+1 := by omega
    have hdd : r.d+1≤C r+1 := by unfold C; omega
    have hprod : r.d*(2*r.width+1)≤(C r+1)^2*2 := by nlinarith
    unfold D MatrixBatchCapacity.capacity
    nlinarith
  intro i
  fin_cases i
  all_goals first | exact hfield | exact hcols |
    (simp [fields,MatrixScorePhiFields.fields,MatrixScoreWeight.zeros,frame_length,binary_length,
      UnaryTemplate.tape] <;> omega)

theorem gate_run (r : Request) (gate : Fin r.Gates) :
    ∃ final : State r,∃ actual,
      runFrom MatrixScoreRetainedRanks.machine (MatrixScoreRetainedRanks.budget r gate) (input r gate)=some actual ∧
      actual.final.tapes 37=ZeroPadding.pad (D r) (MatrixScoreRawRanks.output r gate) ∧
      (∀ i : Fin 30,i≠24 → actual.final.tapes (i.castAdd 12)=
        ZeroPadding.pad (capacities r (i.castAdd 12)) (MatrixScoreRetainedRanks.finalFields r gate final i)) ∧
      actual.final.heads=MatrixScoreRetainedRanks.retainedHeads ∧
      (∀ i,(actual.final.tapes i).length≤D r) ∧
      actual.steps≤MatrixScoreRetainedRanks.budget r gate := by
  obtain ⟨final,base,hb,b36,bt,bh,bs⟩ := MatrixScoreRetainedRanks.gate_run r gate (cold r)
  obtain ⟨actual,ha,haf,has,_⟩ := ZeroPadding.run_config MatrixScoreRetainedRanks.machine
    (capacities r) _ _ base hb
  have hs := (budget_le r gate).trans_lt (MatrixScoreRawRanksBounds.budget_lt r gate)
  have hgap := capacity_gap r
  have hi : ∀ i,((MatrixScoreRetainedRanks.input r gate (cold r)).tapes i).length ≤ max (D r) (1+1) := by
    intro i
    rw [input_fields]
    exact (input_fits r gate i).trans (le_max_left _ _)
  have hh : ∀ i,(MatrixScoreRetainedRanks.input r gate (cold r)).heads i≤1 := by
    rw [input_heads]
    intro i
    simp only [MatrixScoreRetainedRanks.retainedHeads]
    split <;> omega
  have support := RecoveryTapeSupport.run_support MatrixScoreRetainedRanks.machine _ _ base hb (D r) 1 hh hi
  refine ⟨final,actual,ha,?_,?_,?_,?_,has.trans_le bs⟩
  · rw [haf]
    simp only [ZeroPadding.config,b36]
    rfl
  · intro i hn
    rw [haf]
    simpa only [ZeroPadding.config] using congrArg (ZeroPadding.pad (capacities r (i.castAdd 12))) (bt i hn)
  · rw [haf]
    funext i
    exact bh i
  · intro i
    rw [haf]
    simp only [ZeroPadding.config,ZeroPadding.pad_length]
    have hn := support i
    have hc : capacities r i≤D r := by unfold capacities; split <;> omega
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreReusableRanks
