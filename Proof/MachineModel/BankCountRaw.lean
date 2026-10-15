import Proof.MachineModel.BankCountConsumer
import Proof.MachineModel.Layout

/-! The original incidence printer runs in the count-metadata bank. Its
actual count and table are retained; the twelve new private tapes are idle. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawOld (i : Fin 116) : Fin 128:=i.castAdd 12
theorem rawOld_injective : Function.Injective rawOld:=by
  intro i j h;exact Fin.ext (congrArg (fun x : Fin 128=>x.val) h)
noncomputable def raw:=RecoveryFocus.machine rawOld BankExecution.machine
noncomputable def afterHeads (H : Fin 128→ℕ) (pos : ℕ):=
  dockH rawOld H (BankExecution.changedHeads (H ∘ rawOld) pos 0 0)
noncomputable def afterTapes (A : Fin 128→List Bool) (C : ℕ) (table : List Bool) (M : ℕ):=
  install rawOld A (BankExecution.changedTapes (A ∘ rawOld) C table M)

theorem raw_run {B : ℕ} (ms : List (List (Fin B))) (C : ℕ) (hB : B≤C)
    (pre tail : List Bool) (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hh : ∀ j,H (rawOld (BankExecution.slots j))=Padded.heads pre.length 0 0 j)
    (ht : ∀ j,A (rawOld (BankExecution.slots j))=
      Padded.tapes C B (pre++stream (rawIndices ms)++tail) [] 0 j)
    (hsize : (rawRows ms).flatten.length≤C) (hcount : ms.length≤C)
    (hdh : H 104=0) (hlh : H 105=0)
    (hd : A 104=List.replicate C true) (hl : A 105=List.replicate (C+1) false) :
    Step raw (BankExecution.budget B C (rawIndices ms)) H A
      (afterHeads H (pre.length+(stream (rawIndices ms)).length))
      (afterTapes A C (rawRows ms).flatten ms.length) := by
  have base:=BankExecution.raw_run ms C hB pre tail (H ∘ rawOld) (A ∘ rawOld)
    hh ht hsize hcount hdh hlh hd hl
  obtain ⟨b,br,bh,bt,bs⟩:=base
  exact (Step.of_run br bh bt).dock rawOld rawOld_injective H A
    (by intro i;rfl) (by intro i;rfl)

theorem after_heads_old (H : Fin 128→ℕ) (pos : ℕ) (i : Fin 116) :
    afterHeads H pos (rawOld i)=BankExecution.changedHeads (H ∘ rawOld) pos 0 0 i:=
  dockH_slot rawOld rawOld_injective H _ i
theorem after_tapes_old (A : Fin 128→List Bool) (C : ℕ) (table : List Bool) (M : ℕ) (i : Fin 116) :
    afterTapes A C table M (rawOld i)=BankExecution.changedTapes (A ∘ rawOld) C table M i:=
  install_slot rawOld rawOld_injective A _ i
theorem rawOld_avoids (i : Fin 128) (hi : 116 ≤ i.val) : ∀ j,rawOld j≠i:=by
  intro j he
  have hv : j.val=i.val:=congrArg (fun x : Fin 128=>x.val) he
  have hj:=j.isLt
  omega
theorem after_heads_extra (H : Fin 128→ℕ) (pos : ℕ) (i : Fin 128) (hi : 116 ≤ i.val) :
    afterHeads H pos i=H i:=dockH_other rawOld H _ i (rawOld_avoids i hi)
theorem after_tapes_extra (A : Fin 128→List Bool) (C : ℕ) (table : List Bool) (M : ℕ)
    (i : Fin 128) (hi : 116 ≤ i.val) : afterTapes A C table M i=A i:=
  install_other rawOld A _ i (rawOld_avoids i hi)

end NearCubicWires.ExtIncidence.BankCount
