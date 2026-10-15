import Proof.MachineModel.ClockBoundGuard

/-! Literal fixed-U bound-field consumer. Canonical B is rejected exactly
when B exceeds the generated dyadic cap, including the overwidth case. -/
namespace NearCubicWires.RepairOrdinary.ClockUniversalBound
open LocalBitMultitape SignedSortKey RadixSemantics ClockDyadicLedger
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def limitWord (N : ℕ) : List Bool := List.replicate (exponent N) false++[true]
@[simp] theorem limitWord_value (N : ℕ) : value (limitWord N)=limit N := by
  simp [limitWord,value_append,value,limit]
theorem limitWord_fits (N : ℕ) : (limitWord N).length≤width N := by
  simp [limitWord,width]
theorem boundWord_fits (N B : ℕ) (hB : B≤limit N) : (ClockBinary.word B).length≤width N := by
  have hwidth := (width_bounds N).1
  exact ClockBinary.length_bound B (width N) (by omega)

theorem decision (N B : ℕ) :
    ClockBoundGuard.accepted (width N) (ClockBinary.word B) (limitWord N)=decide (B≤limit N) := by
  rw [ClockBoundGuard.accepted_iff _ _ _ (limitWord_fits N)]
  simp only [ClockBinary.word_value,limitWord_value]
  have hiff : ((ClockBinary.word B).length≤width N ∧ B≤limit N) ↔ B≤limit N :=
    ⟨And.right,fun h => ⟨boundWord_fits N B h,h⟩⟩
  simp only [hiff]

def input (N B : ℕ) : Fin 12 → List Bool :=
  ClockBoundGuard.input (width N) (ClockBinary.word B) (limitWord N)

theorem bound_run (N B : ℕ) :
    ∃ r : ExecutionReceipt 12 21,
      run ClockBoundGuard.machine (16*(width N+1)) (input N B)=some r ∧
      r.final.tapes 11=[decide (B≤limit N)] ∧
      r.final.tapes 6=frame (binary (width N) (limit N)) ∧
      (B≤limit N → r.final.tapes 2=frame (binary (width N) B)) ∧
      r.final.tapes 0=List.replicate (width N) true ∧
      r.final.tapes 1=frame (ClockBinary.word B) ∧ r.final.tapes 5=frame (limitWord N) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps≤16*(width N+1) := by
  obtain ⟨r,hr,hf,hh,hs⟩ := ClockBoundGuard.guard_ready (width N) (ClockBinary.word B) (limitWord N)
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_,hh,hs⟩
  · simp [hf,ClockBoundGuard.output,decision]
  · simp [hf,ClockBoundGuard.output,ClockBoundGuard.normalized,
      ClockScalarFields.resize_binary _ _ (limitWord_fits N)]
  · intro hB
    simp [hf,ClockBoundGuard.output,ClockBoundGuard.normalized,
      ClockScalarFields.resize_binary _ _ (boundWord_fits N B hB)]
  · simp [hf,ClockBoundGuard.output]
  · simp [hf,ClockBoundGuard.output]
  · simp [hf,ClockBoundGuard.output]

end NearCubicWires.RepairOrdinary.ClockUniversalBound
