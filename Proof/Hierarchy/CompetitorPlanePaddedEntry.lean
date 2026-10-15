import Proof.Hierarchy.CompetitorPlaneWidth

/-! The whole-plane caller reuses finite buffers of size O(n W²).
Transporting finite zero padding retains exact execution and all head resets;
the support proof charges one whole-plane buffer, never a buffer per cell. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlanePaddedEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding CompetitorPlaneStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (w n : ℕ) := CompetitorPlaneSign.budget w n+1
def input (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell) : Fin 30 → List Bool :=
  fun i => ZeroPadding.pad (capacity w xs.length) (CompetitorPlaneSign.input sign b w bits xs i)

theorem capacity_bounds (w n : ℕ) :
    2*w+1≤capacity w n ∧ n*(2*w)≤capacity w n ∧
    n+1≤capacity w n ∧ CompetitorPlane.capacity w≤capacity w n := by
  have hsmall : 2*w≤9000*(w+1)^2+3 := by nlinarith
  have hprod := Nat.mul_le_mul_left n hsmall
  unfold capacity CompetitorPlaneSign.budget CompetitorPlaneEntry.readyBudget CompetitorPlaneEntry.budget
    planeBudget bodyBudget CompetitorPlane.capacity
  constructor
  · nlinarith
  constructor
  · nlinarith [hprod]
  constructor <;> nlinarith

theorem count_length (b : ℕ) (xs : List Cell) : (countWords b xs).length=xs.length*b := by
  simp [countWords,countWord,List.length_flatMap]
theorem old_length (w : ℕ) (xs : List Cell) : (oldWords w xs).length=xs.length*(2*w) := by
  simp [oldWords,oldWord,CompetitorPlane.pairWord,List.length_flatMap,two_mul]

theorem input_support (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell)
    (hb : b≤w) (hbits : bits.length≤w) (i : Fin 30) :
    (CompetitorPlaneSign.input sign b w bits xs i).length≤capacity w xs.length := by
  obtain ⟨hword,hpairs,hn,hC⟩ := capacity_bounds w xs.length
  change xs.length*(2*w)≤capacity w xs.length at hpairs
  have hcounts : xs.length*b≤capacity w xs.length :=
    (Nat.mul_le_mul_left xs.length (by omega)).trans hpairs
  fin_cases i <;>
    simp [CompetitorPlaneSign.input,CompetitorPlaneEntry.readyInput,CompetitorPlaneEntry.input,
      CompetitorPlaneEntry.extendTapes,coldInput,Fin.addCases,count_length,old_length,CompareMachine.word] <;> omega

theorem padded_plane_run (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell)
    (hb : b≤w) (hbits : bits.length≤w) (hv : ∀ a∈xs,a.Valid sign b w bits) :
    ∃ out,ClockJoin.ReadyRun CompetitorPlaneSign.machine (CompetitorPlaneSign.budget w xs.length)
      (input sign b w bits xs) out ∧
      out 17=ZeroPadding.pad (capacity w xs.length) (newWords sign w bits xs) ∧
      (∀ i : Fin 30,i=0 ∨ i=9 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=27 ∨ i=29 →
        out i=input sign b w bits xs i) ∧
      (∀ i,(out i).length=capacity w xs.length) := by
  obtain ⟨produced,ready,h17,h18,h19,h0,h9,h20,h27,h29⟩ := CompetitorPlaneSign.run_plane sign b w bits xs hb hbits hv
  obtain ⟨base,hr,ht,hh,hs⟩ := ready
  have hend : base.steps+1≤capacity w xs.length := by unfold capacity; omega
  have support := RecoveryTapeSupport.run_support CompetitorPlaneSign.machine _ _ base hr
    (capacity w xs.length) 0 (by intro i; exact Nat.zero_le _) (by
      intro i
      exact (input_support sign b w bits xs hb hbits i).trans (Nat.le_max_left _ _))
  have hbound (i : Fin 30) : (base.final.tapes i).length≤capacity w xs.length := by
    simpa only [Nat.zero_add,max_eq_left hend] using support i
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config CompetitorPlaneSign.machine
    (fun _ => capacity w xs.length) _ _ base hr
  refine ⟨r.final.tapes,⟨r,hrun,rfl,?_,hsteps.trans_le hs⟩,?_,?_,?_⟩
  · intro i
    rw [hf]
    exact hh i
  · simp only [hf,ZeroPadding.config,ht,h17]
  · intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [hf,ZeroPadding.config,ht,h0,h9,h18,h19,h20,h27,h29,input,
        CompetitorPlaneSign.input,CompetitorPlaneEntry.readyInput,CompetitorPlaneEntry.input,
        CompetitorPlaneEntry.extendTapes,coldInput,Fin.addCases]
  · intro i
    rw [hf]
    simp only [ZeroPadding.config,ZeroPadding.pad_length,max_eq_left (hbound i)]

end NearCubicWires.RepairOrdinary.CompetitorPlanePaddedEntry
