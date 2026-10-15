import Proof.Hierarchy.CompetitorPlaneTablePair

/-! One uniform bounded pair step for the actual p-fold machine. The packet
word is independent of accumulator values, and the invariant uses one
canonical zero-count view of the retained P/N bank between iterations. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorPlaneStream CompetitorPlanePacketPass CompetitorPlanePacketBanks
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zero (n : ℕ) : State n := ⟨fun _ => 0,fun _ => 0⟩
def canonical {n : ℕ} (state : State n) := cells (fun _ => 0) state
def TableContext {n : ℕ} (b w : ℕ) (state : State n) (ambient : Fin 34 → List Bool) := Context b w (canonical state) ambient
structure Plane (n : ℕ) where
  bit : ℕ
  positive : Fin n → ℕ
  negative : Fin n → ℕ
def Plane.Valid {n : ℕ} (b p : ℕ) (plane : Plane n) :=
  plane.bit<p ∧ (∀ i,plane.positive i<2^b) ∧ (∀ i,plane.negative i<2^b)
def Plane.word {n : ℕ} (b : ℕ) (plane : Plane n) := pairWord b plane.bit plane.positive plane.negative (zero n)
def Plane.apply {n : ℕ} (plane : Plane n) (state : State n) := pairState plane.bit plane.positive plane.negative state
def pairFuel (w n : ℕ) := 10*capacity w n+8*w+4*(n*w)+37

theorem count_independent {n : ℕ} (b : ℕ) (counts : Fin n → ℕ) (a c : State n) :
    countWords b (cells counts a)=countWords b (cells counts c) := by
  simp only [countWords,cells,List.flatMap_def,List.map_ofFn]
  rfl
theorem word_independent {n : ℕ} (b t : ℕ) (positive negative : Fin n → ℕ) (a c : State n) :
    pairWord b t positive negative a=pairWord b t positive negative c := by
  unfold pairWord CompetitorPlanePacketPair.word
  rw [count_independent b positive a c,
    count_independent b negative (advance false t positive a) (advance false t positive c)]

theorem context_recount {n : ℕ} (b w : ℕ) (a c : Fin n → ℕ) (state : State n)
    (ambient : Fin 34 → List Bool) (h : Context b w (cells a state) ambient) :
    Context b w (cells c state) ambient := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [← old_independent w a c state]
    simpa only [cells_length] using h.old
  · simpa only [cells_length] using h.width
  · simpa only [cells_length] using h.nativeWidth
  · simpa only [cells_length] using h.erase
  · simpa only [cells_length] using h.count
  · simpa only [CompetitorPlanePaddedEntry.count_length,cells_length] using h.byteCount
  · simpa only [cells_length] using h.driver
  · simpa only [cells_length] using h.reset
  · simpa only [cells_length] using h.support

theorem pair_budget {n : ℕ} (b w t : ℕ) (positive negative : Fin n → ℕ) (state : State n) :
    CompetitorPlanePacketPair.budget b w (CompetitorPlaneWidth.factor t)
      (cells positive state) (cells negative (advance false t positive state))=
        10*capacity w n+8*(t+1)+4*(n*b)+37 := by
  simp only [CompetitorPlanePacketPair.budget,CompetitorPlanePacketPass.budget,
    CompetitorPlanePacketDock.budget,CompetitorPlaneReusable.budget,CompetitorPlanePacketLoad.budget,
    CompetitorPlanePaddedEntry.count_length,cells_length,CompetitorPlaneWidth.factor_length]
  unfold capacity CompetitorPlaneReusable.capacity CompetitorPlanePaddedEntry.capacity
  ring

theorem pair_budget_le {n : ℕ} (b w t : ℕ) (positive negative : Fin n → ℕ) (state : State n)
    (hb : b≤w) (ht : t+1≤w) :
    CompetitorPlanePacketPair.budget b w (CompetitorPlaneWidth.factor t)
      (cells positive state) (cells negative (advance false t positive state))≤pairFuel w n := by
  rw [pair_budget]
  have hm := Nat.mul_le_mul_left n hb
  unfold pairFuel
  omega

theorem pair_fuel_polynomial (w n : ℕ) : pairFuel w n≤400000*(n+1)*(w+1)^2 := by
  have hw : w≤(w+1)^2 := by nlinarith
  have hn := Nat.mul_le_mul_left n hw
  have hu : 1≤(w+1)^2 := by nlinarith
  have hn1 := Nat.mul_le_mul_left n hu
  unfold pairFuel capacity CompetitorPlaneReusable.capacity CompetitorPlanePaddedEntry.capacity
    CompetitorPlaneSign.budget CompetitorPlaneEntry.readyBudget CompetitorPlaneEntry.budget
    planeBudget bodyBudget CompetitorPlane.capacity
  nlinarith [hn1]

theorem uniform_pair_run {n : ℕ} (pre suffix : List Bool) (b p j : ℕ) (plane : Plane n)
    (state : State n) (ambient : Fin 34 → List Bool)
    (hcontext : TableContext b (CompetitorPlaneWidth.width b p) state ambient)
    (hsource : ambient 32=pre++plane.word b++suffix)
    (hj : j<p) (hp : plane.Valid b p) (hs : Bounded b p (2*j) state) :
    ∃ r,runFrom CompetitorPlanePacketPair.machine (pairFuel (CompetitorPlaneWidth.width b p) n)
      (CompetitorPlanePacketDock.cfg CompetitorPlanePacketPair.machine.start pre.length ambient)=some r ∧
      r.final.heads=CompetitorPlanePacketDock.heads (pre.length+(plane.word b).length) ∧
      r.final.tapes 19=ZeroPadding.pad (capacity (CompetitorPlaneWidth.width b p) n)
        (oldWords (CompetitorPlaneWidth.width b p) (canonical (plane.apply state))) ∧
      r.final.tapes 32=ambient 32 ∧ TableContext b (CompetitorPlaneWidth.width b p) (plane.apply state) r.final.tapes ∧
      Bounded b p (2*(j+1)) (plane.apply state) ∧ r.steps≤pairFuel (CompetitorPlaneWidth.width b p) n := by
  have hctx := context_recount b (CompetitorPlaneWidth.width b p) (fun _ => 0) plane.positive state ambient hcontext
  have hsrc : ambient 32=pre++pairWord b plane.bit plane.positive plane.negative state++suffix := by
    rw [word_independent b plane.bit plane.positive plane.negative state (zero n)]
    exact hsource
  obtain ⟨r,hr,hh,h19,h32,hout,hbound,htime⟩ := table_pair_run pre suffix b p j plane.bit
    plane.positive plane.negative state ambient hctx hsrc hj hp.1 hp.2.1 hp.2.2 hs
  have hbit := hp.1
  have hfuel := pair_budget_le b (CompetitorPlaneWidth.width b p) plane.bit plane.positive plane.negative state
    (by unfold CompetitorPlaneWidth.width; omega) (by unfold CompetitorPlaneWidth.width; omega)
  have hmore := runFrom_moreFuel CompetitorPlanePacketPair.machine _
    (pairFuel (CompetitorPlaneWidth.width b p) n-
      CompetitorPlanePacketPair.budget b (CompetitorPlaneWidth.width b p) (CompetitorPlaneWidth.factor plane.bit)
        (cells plane.positive state) (cells plane.negative (advance false plane.bit plane.positive state))) _ r hr
  rw [Nat.add_sub_of_le hfuel] at hmore
  refine ⟨r,hmore,?_,?_,h32,?_,hbound,htime.trans hfuel⟩
  · rw [word_independent b plane.bit plane.positive plane.negative state (zero n)] at hh
    exact hh
  · rw [old_independent _ plane.negative (fun _ => 0)] at h19
    exact h19
  · exact context_recount b (CompetitorPlaneWidth.width b p) plane.negative (fun _ => 0)
      (plane.apply state) r.final.tapes hout

end NearCubicWires.RepairOrdinary.CompetitorPlaneTable
