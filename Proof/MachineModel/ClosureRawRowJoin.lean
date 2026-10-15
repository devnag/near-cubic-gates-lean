import Proof.MachineModel.ClosureRowPayloadReusable

/-! Consume a real row-printing Step, then physically produce the raw scalar
required by the external-row loop and clear the bounded record buffer.
The program is fixed before the row, its coefficient, width, or answer.
Only the row producer's original input words and paid blank workspace enter.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.RawRowJoin
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open CloseoutRowsEstimatorCoefficients SignedSortKey

def caps {t : Nat} (port : Fin t) (B : Nat) (i : Fin t) := if i=port then B else 0
def padded {t : Nat} (port : Fin t) (B : Nat) (A : Fin t → List Bool) :=
  fun i => ZeroPadding.pad (caps port B i) (A i)
def bank {t : Nat} (A : Fin t → List Bool) (R B : Nat) (out : List Bool) :
    Fin (t+1+2) → List Bool :=
  Fin.addCases (Fin.addCases A (fun _ : Fin 1 => List.replicate R false))
    (![out,List.replicate B true] : Fin 2 → List Bool)
def heads (t : Nat) (out : List Bool) : Fin (t+1+2) → Nat :=
  Fin.addCases (Fin.addCases (fun _ : Fin t => 0) (fun _ : Fin 1 => 0))
    (![out.length,0] : Fin 2 → Nat)
def slots {t : Nat} (port : Fin t) : Fin 4 → Fin (t+1+2) :=
  ![(port.castAdd 1).castAdd 2,(0 : Fin 2).natAdd (t+1),
    ((0 : Fin 1).natAdd t).castAdd 2,(1 : Fin 2).natAdd (t+1)]

theorem injective {t : Nat} (port : Fin t) : Function.Injective (slots port) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hp := port.isLt
  fin_cases i <;> fin_cases j <;> simp [slots] at hv ⊢ <;> omega

noncomputable def first {t s : Nat} (p : Machine t s) :=
  TapeEmbedding.machine 2 (MaskedReset.machine p (fun _ => true))
noncomputable def last {t : Nat} (port : Fin t) :=
  RecoveryFocus.machine (slots port) RowPayloadReusable.machine
noncomputable def machine {t s : Nat} (p : Machine t s) (port : Fin t) :=
  Composition.machine (first p) (last port)
def budget (fuel b B : Nat) := 2*fuel+2+1+RowPayloadReusable.budget b B

theorem run {t s : Nat} (p : Machine t s) (port : Fin t)
    (fuel b B R : Nat) (q : CompetitorValidity.Estimate) (count den : Nat)
    (A Z : Fin t → List Bool) (H : Fin t → Nat) (out : List Bool)
    (printed : Step p fuel (fun _ => 0) A H Z)
    (hword : Z port = Stream.recordWord b q count den)
    (hf : fuel ≤ R) (hb : RowPayload.budget b ≤ B) (hR : B+1 ≤ R) :
    Step (machine p port) (budget fuel b B)
      (heads t out) (bank (padded port B A) R B out)
      (dockH (slots port) (heads t out) (RowPayloadReusable.heads (out++binary b count)))
      (install (slots port) (bank (padded port B Z) R B out)
        (RowPayloadReusable.input [] (out++binary b count) B R)) := by
  have firstRun := ((printed.pad (caps port B)).mask (fun _ => true)
    (by intros; rfl) hf).embed (![out.length,0] : Fin 2 → Nat)
      (![out,List.replicate B true] : Fin 2 → List Bool)
  have firstStep : Step (first p) (2*fuel+2)
      (heads t out) (bank (padded port B A) R B out)
      (heads t out) (bank (padded port B Z) R B out) := by
    exact firstRun
  have hB : (Stream.recordWord b q count den).length ≤ B := by
    rw [Stream.record_length]
    unfold RowPayload.budget at hb
    omega
  have read := RowPayloadReusable.run b q count den B R out (by omega) hR hB
  have ph : ∀ i, heads t out (slots port i) = RowPayloadReusable.heads out i := by
    intro i; fin_cases i <;> simp [heads,slots,RowPayloadReusable.heads,Fin.addCases]
  have pt : ∀ i, bank (padded port B Z) R B out (slots port i) =
      RowPayloadReusable.input (Stream.recordWord b q count den) out B R i := by
    intro i; fin_cases i <;>
      simp [bank,slots,padded,caps,RowPayloadReusable.input,Fin.addCases,hword]
  have readDock := read.dock (slots port) (injective port) (heads t out)
    (bank (padded port B Z) R B out) ph pt
  exact firstStep.seq readDock

theorem entry_buffer_blank {t : Nat} (port : Fin t) (B : Nat) (A : Fin t → List Bool)
    (h : A port = []) : padded port B A port = List.replicate B false := by
  simp [padded,caps,h,ZeroPadding.pad]

theorem exit_buffer_blank {t : Nat} (port : Fin t) (B R : Nat)
    (Z : Fin t → List Bool) (out next : List Bool) :
    install (slots port) (bank (padded port B Z) R B out)
      (RowPayloadReusable.input [] next B R) ((port.castAdd 1).castAdd 2) =
        List.replicate B false := by
  exact (install_slot _ (injective port) _ _ 0).trans
    (by simp [RowPayloadReusable.input,ZeroPadding.pad])

theorem exit_raw_word {t : Nat} (port : Fin t) (B R : Nat)
    (Z : Fin t → List Bool) (out next : List Bool) :
    install (slots port) (bank (padded port B Z) R B out)
      (RowPayloadReusable.input [] next B R) ((0 : Fin 2).natAdd (t+1)) = next :=
  install_slot _ (injective port) _ _ 1

theorem budget_le (fuel b B : Nat) (hb : RowPayload.budget b ≤ B) :
    budget fuel b B ≤ 2*fuel+4*B+10 := by
  have h := RowPayloadReusable.budget_le b B hb
  unfold budget
  omega

end NearCubicWires.P1Closure.RawRowJoin
