import Proof.MachineModel.OrdinaryMatrixCoordinatePair

/-! Execute loading and coordinate transposition as one bounded body, with
the original record stream and aggregate output preserved exactly. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoordinateTranspose
open LocalBitMultitape Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def fields : Machine 12 31 := Composition.machine load pair

theorem fields_run (w cap : ℕ) (a b pre suffix record clone rank out : List Bool)
    (ha : a.length=w) (hb : b.length=w) (hcap : 2*w ≤ cap)
    (hr : record.length ≤ 4*w+1) (hc : clone.length ≤ 4*w+1) (hk : rank.length ≤ 2*w+1) :
    ∃ actual : ExecutionReceipt 12 31,
      runFrom fields (64*w+42) (cfg fields.start w cap (pre++frame (a++b)++suffix)
        pre.length record clone rank out)=some actual ∧
      actual.final=cfg 30 w cap (pre++frame (a++b)++suffix) (pre.length+4*w+1)
        (frame (a++b)) (frame (a++b)) (frame b) (out++frame (b++a)) ∧
      actual.steps ≤ 64*w+42 := by
  obtain ⟨first,hfirst,hff,hfs⟩ := load_run w cap a b pre suffix record clone rank out ha hb hr hc hk
  obtain ⟨last,hl,hlf,hls⟩ := pair_run w cap a b (pre++frame (a++b)++suffix) out
    (pre.length+4*w+1) ha hb hcap
  have hi : Composition.restart first.final pair.start=
      cfg pair.start w cap (pre++frame (a++b)++suffix) (pre.length+4*w+1)
        (frame (a++b)) (frame (a++b)) (frame b) out := by rw [hff]; rfl
  rw [←hi] at hl
  have hj := Composition.run_join load pair (56*w+34) (8*w+7)
    (cfg load.start w cap (pre++frame (a++b)++suffix) pre.length record clone rank out)
    first last hfirst hl
  have htime : (56*w+34)+1+(8*w+7)=64*w+42 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_⟩
  · change Composition.rightConfig 21 last.final=_
    rw [hlf]
    rfl
  · change first.steps+1+last.steps ≤ _
    omega

end NearCubicWires.RepairOrdinary.MatrixCoordinateTranspose
