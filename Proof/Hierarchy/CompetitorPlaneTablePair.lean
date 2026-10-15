import Proof.Hierarchy.CompetitorPlanePacketPair

/-! Indexed row-major accumulators discharge the concrete two-packet bank
handoff and every width premise. Counts may differ between the positive and
negative planes; both retain exactly the same n original cell positions. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorPlaneStream CompetitorPlanePacketPass CompetitorPlanePacketBanks
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State (n : ℕ) where
  positive : Fin n → ℕ
  negative : Fin n → ℕ
def cell {n : ℕ} (counts : Fin n → ℕ) (state : State n) (i : Fin n) : Cell :=
  ⟨counts i,state.positive i,state.negative i⟩
def cells {n : ℕ} (counts : Fin n → ℕ) (state : State n) := List.ofFn (cell counts state)
def advance {n : ℕ} (sign : Bool) (t : ℕ) (counts : Fin n → ℕ) (state : State n) : State n :=
  ⟨fun i => CompetitorPlane.nextPositive sign (state.positive i) (counts i) (CompetitorPlaneWidth.factor t),
    fun i => CompetitorPlane.nextNegative sign (state.negative i) (counts i) (CompetitorPlaneWidth.factor t)⟩
def Bounded {n : ℕ} (b p j : ℕ) (state : State n) :=
  ∀ i,state.positive i+state.negative i≤j*CompetitorPlaneWidth.unit b p
def pairState {n : ℕ} (t : ℕ) (positive negative : Fin n → ℕ) (state : State n) :=
  advance true t negative (advance false t positive state)

@[simp] theorem cells_length {n : ℕ} (counts : Fin n → ℕ) (state : State n) :
    (cells counts state).length=n := by simp [cells]
theorem old_independent {n : ℕ} (w : ℕ) (a b : Fin n → ℕ) (state : State n) :
    oldWords w (cells a state)=oldWords w (cells b state) := by
  simp only [oldWords,cells,List.flatMap_def,List.map_ofFn]
  rfl
theorem next_cells {n : ℕ} (sign : Bool) (t : ℕ) (counts : Fin n → ℕ) (state : State n) :
    nextCells sign (CompetitorPlaneWidth.factor t) (cells counts state)=cells counts (advance sign t counts state) := by
  simp only [nextCells,cells,List.map_ofFn]
  rfl

theorem advance_bounded {n : ℕ} (sign : Bool) (b p j t : ℕ) (counts : Fin n → ℕ) (state : State n)
    (ht : t<p) (hc : ∀ i,counts i<2^b) (hs : Bounded b p j state) :
    Bounded b p (j+1) (advance sign t counts state) := by
  intro i
  have hi := CompetitorPlaneWidth.bounded_update sign b p j t (cell counts state i) ht ⟨hc i,hs i⟩
  exact hi.2
theorem cells_valid {n : ℕ} (sign : Bool) (b p j t : ℕ) (counts : Fin n → ℕ) (state : State n)
    (hj : j<2*p) (ht : t<p) (hc : ∀ i,counts i<2^b) (hs : Bounded b p j state) :
    ∀ a∈cells counts state,a.Valid sign b (CompetitorPlaneWidth.width b p) (CompetitorPlaneWidth.factor t) := by
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact CompetitorPlaneWidth.cell_valid sign b p j t (cell counts state i) hj ht ⟨hc i,hs i⟩

def pairWord {n : ℕ} (b t : ℕ) (positive negative : Fin n → ℕ) (state : State n) :=
  CompetitorPlanePacketPair.word b (CompetitorPlaneWidth.factor t)
    (cells positive state) (cells negative (advance false t positive state))

theorem table_pair_run {n : ℕ} (pre suffix : List Bool) (b p j t : ℕ)
    (positive negative : Fin n → ℕ) (state : State n) (ambient : Fin 34 → List Bool)
    (hcontext : Context b (CompetitorPlaneWidth.width b p) (cells positive state) ambient)
    (hsource : ambient 32=pre++pairWord b t positive negative state++suffix)
    (hj : j<p) (ht : t<p) (hcP : ∀ i,positive i<2^b) (hcN : ∀ i,negative i<2^b)
    (hstate : Bounded b p (2*j) state) :
    ∃ r,runFrom CompetitorPlanePacketPair.machine
      (CompetitorPlanePacketPair.budget b (CompetitorPlaneWidth.width b p) (CompetitorPlaneWidth.factor t)
        (cells positive state) (cells negative (advance false t positive state)))
      (CompetitorPlanePacketDock.cfg CompetitorPlanePacketPair.machine.start pre.length ambient)=some r ∧
      r.final.heads=CompetitorPlanePacketDock.heads (pre.length+(pairWord b t positive negative state).length) ∧
      r.final.tapes 19=ZeroPadding.pad (capacity (CompetitorPlaneWidth.width b p) n)
        (oldWords (CompetitorPlaneWidth.width b p) (cells negative (pairState t positive negative state))) ∧
      r.final.tapes 32=ambient 32 ∧
      Context b (CompetitorPlaneWidth.width b p) (cells negative (pairState t positive negative state)) r.final.tapes ∧
      Bounded b p (2*(j+1)) (pairState t positive negative state) ∧
      r.steps≤CompetitorPlanePacketPair.budget b (CompetitorPlaneWidth.width b p) (CompetitorPlaneWidth.factor t)
        (cells positive state) (cells negative (advance false t positive state)) := by
  let w := CompetitorPlaneWidth.width b p
  let bits := CompetitorPlaneWidth.factor t
  have firstBound := advance_bounded false b p (2*j) t positive state ht hcP hstate
  have secondBound := advance_bounded true b p (2*j+1) t negative (advance false t positive state) ht hcN firstBound
  have hnext : oldWords w (cells negative (advance false t positive state))=
      newWords false w bits (cells positive state) := by
    rw [old_independent w negative positive,← next_cells]
    exact next_word false w bits (cells positive state)
  obtain ⟨r,hr,hh,h19,h32,hout,hs⟩ := CompetitorPlanePacketPair.pair_run pre suffix bits b w
    (cells positive state) (cells negative (advance false t positive state)) ambient hcontext hsource
    (by simp) hnext (by unfold w CompetitorPlaneWidth.width; omega)
    (by simp only [bits,CompetitorPlaneWidth.factor_length]; unfold w CompetitorPlaneWidth.width; omega)
    (cells_valid false b p (2*j) t positive state (by omega) ht hcP hstate)
    (cells_valid true b p (2*j+1) t negative (advance false t positive state) (by omega) ht hcN firstBound)
  refine ⟨r,hr,hh,?_,h32,?_,?_,hs⟩
  · rw [← next_word,next_cells,cells_length] at h19
    exact h19
  · simpa only [bits,next_cells,pairState] using hout
  · have he : 2*j+1+1=2*(j+1) := by omega
    rw [he] at secondBound
    exact secondBound

end NearCubicWires.RepairOrdinary.CompetitorPlaneTable
