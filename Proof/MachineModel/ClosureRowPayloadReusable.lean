import Proof.MachineModel.ClosureRowPayload
import Proof.Amplification.RecoveryScratchErase

/-! The raw count reader returns a zeroed, bounded record buffer and a reusable
log, retaining the raw stream's append cursor. No literal-blank restoration
is requested. This is the output adapter for the external-row body.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.RowPayloadReusable
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open CloseoutRowsEstimatorCoefficients SignedSortKey

def keep : Fin 2 → Bool := ![true,false]
noncomputable def first := TapeEmbedding.machine 1 (MaskedReset.machine RowPayload.machine keep)
def eraseSlots : Fin 3 → Fin 4 := ![0,3,2]
theorem erase_injective : Function.Injective eraseSlots := by decide
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def machine := Composition.machine first last
def budget (b B : Nat) := 2*RowPayload.budget b+2+1+(2*B+4)

def heads (out : List Bool) : Fin 4 → Nat := ![0,out.length,0,0]
def input (word out : List Bool) (B R : Nat) : Fin 4 → List Bool :=
  ![ZeroPadding.pad B word,out,List.replicate R false,List.replicate B true]

theorem run (b : Nat) (q : CompetitorValidity.Estimate) (count den B R : Nat)
    (out : List Bool) (hb : RowPayload.budget b ≤ R) (hR : B+1 ≤ R)
    (hB : (Stream.recordWord b q count den).length ≤ B) :
    Step machine (budget b B) (heads out)
      (input (Stream.recordWord b q count den) out B R)
      (heads (out++binary b count)) (input [] (out++binary b count) B R) := by
  let word := Stream.recordWord b q count den
  have h := (RowPayload.run b q count den [] [] out).pad (![B,0] : Fin 2 → Nat)
  have hi : (fun i => ZeroPadding.pad (![B,0] i) (![[]++word++[],out] i)) =
      (![ZeroPadding.pad B word,out] : Fin 2 → List Bool) := by
    funext i; fin_cases i <;> simp [ZeroPadding.pad_zero]
  have ht : (fun i => ZeroPadding.pad (![B,0] i) (![[]++word++[],out++binary b count] i)) =
      (![ZeroPadding.pad B word,out++binary b count] : Fin 2 → List Bool) := by
    funext i; fin_cases i <;> simp [ZeroPadding.pad_zero]
  have h' := (h.congr_in rfl hi).congr rfl ht
  have reset := (h'.mask keep (by intro i; fin_cases i <;> simp [keep]) hb).embed
    (fun _ : Fin 1 => 0) (fun _ => List.replicate B true)
  have reset' : Step first (2*RowPayload.budget b+2) (heads out) (input word out B R)
      (heads (out++binary b count)) (input word (out++binary b count) B R) := by
    convert reset using 1 <;> (first | rfl | (funext i; fin_cases i <;> rfl))
  have erased := Step.of_ready (RecoveryScratchErase.erase_ready B R
    (fun _ : Fin 1 => ZeroPadding.pad B word)
    (by intro i; rw [ZeroPadding.pad_length,Nat.max_eq_left hB]))
  have erased' : Step (RecoveryScratchErase.resetMachine 1) (2*B+4)
      ![0,0,0] ![ZeroPadding.pad B word,List.replicate B true,List.replicate R false]
      ![0,0,0] ![List.replicate B false,List.replicate B true,List.replicate R false] := by
    convert erased using 1 <;>
      (first | rfl | (funext i; fin_cases i <;> simp [Fin.addCases,Nat.max_eq_left hR]))
  have docked := erased'.dock eraseSlots erase_injective
    (heads (out++binary b count)) (input word (out++binary b count) B R)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  have eh : dockH eraseSlots (heads (out++binary b count)) ![0,0,0] =
      heads (out++binary b count) :=
    dockH_existing _ _ _ (by intro i; fin_cases i <;> rfl)
  have et : install eraseSlots (input word (out++binary b count) B R)
      ![List.replicate B false,List.replicate B true,List.replicate R false] =
      input [] (out++binary b count) B R := by
    funext i
    fin_cases i
    · exact (install_slot _ erase_injective _ _ 0).trans (by simp [input,ZeroPadding.pad])
    · exact install_other _ _ _ _ (by decide)
    · exact install_slot _ erase_injective _ _ 2
    · exact install_slot _ erase_injective _ _ 1
  exact reset'.seq (docked.congr eh et)

theorem budget_le (b B : Nat) (h : RowPayload.budget b ≤ B) : budget b B ≤ 4*B+7 := by
  unfold budget
  omega

end NearCubicWires.P1Closure.RowPayloadReusable
