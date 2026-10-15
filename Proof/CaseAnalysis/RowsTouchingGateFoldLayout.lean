import Proof.CaseAnalysis.RowsTouchingGateMath

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.GateFold
open LocalBitMultitape SupportScan ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word (xs : List Cell):=frame (xs.map Prod.fst)
noncomputable def machine:=CloseoutRowsDegreeLoop.machine Gate.machine
def cost (q w P : ℕ):=2*P+4*q+15+2*ScoreBlock.budget q q q w
def budget (q w P G : ℕ):=G*(cost q w P+3)+3
noncomputable def entry (q k w P C : ℕ) (records : List (List Cell)) (mask : List Cell)
    (initial : Gate.Store) (pre tail : List Bool) (j : ℕ) (_out : List Bool):=
  (⟨Gate.machine.start,Gate.heads (pre.length+((records.take j).flatMap word).length),
    Gate.data q k w P C (pre++records.flatMap word++tail) mask (Gate.states q k w P records initial j)⟩:
      Configuration 24 _)

theorem data_masks (q k w P C : ℕ) (source : List Bool) (xs ys : List Cell) (st : Gate.Store)
    (h:masks xs=masks ys):Gate.data q k w P C source xs st=Gate.data q k w P C source ys st:=by
  unfold Gate.data GateSummary.data
  rw [h]

theorem lookup_le (q m k : ℕ) (hm:m≤q) (hk:k≤q):
    Lookup.budget (PascalReady.width q) (q+1) m k≤Lookup.budget (PascalReady.width q) (q+1) q q:=by
  have hrow:=Nat.mul_le_mul_right (2*PascalReady.width q+7) hm
  have hfield:=Nat.mul_le_mul_right (2*(q+1)+4) hk
  unfold Lookup.budget FrameSeek.budget
  omega

theorem block_le (q m k w : ℕ) (hm:m≤q) (hk:k≤q):
    ScoreBlock.budget q m k w≤ScoreBlock.budget q q q w:=by
  have h:=lookup_le q m k hm hk
  unfold ScoreBlock.budget LookupReady.budget
  omega

theorem gate_le (q m k w P : ℕ) (hm:m≤q) (hk:k≤q):Gate.budget q m k w P≤cost q w P:=by
  have hfirst:=block_le q m k w hm hk
  have hsecond:=block_le q m (k-1) w hm (by omega)
  unfold Gate.budget cost
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.GateFold
