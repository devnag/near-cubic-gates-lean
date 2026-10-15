import Proof.MachineModel.TopDownWorkspaceSelectedOriginals
import Proof.CaseAnalysis.FinalEngineFuelSeam

/-! Direct reuse of the actual width/count prologue after selected admission.
The old parser bank is retained; only the original input, witness and true
length flag are aliased. All prologue work occurs in the selected fresh bank.
The prologue produces its envelope count, not the original PCPP clause count.
Its semantic width schedule uses PolynomialClock.ordinaryClock k. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntry
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.ProjectionNormalization
open WorkspaceGuardedWorker (entry reference)
open WorkspaceSelectedAdmission (originalTapes preFuel coldCutoff)
open WorkspaceSelectedProgram (finalBank lengthFlag)
open RecoveryRootRound
noncomputable section

/-- The logical prologue prefix fits in the caller's fresh bank. Its three
public words are physically aliased; every other logical port is fresh. -/
def slots {t m extra : Nat} (ht : 2≤t) (hspace : m≤extra) (i : Fin m) :
    Fin (t+1+1+extra) :=
  ⟨if i.val=0 then 0 else if i.val=1 then 1 else if i.val=216 then t+1 else t+2+i.val,
    by have := i.isLt;split_ifs <;>omega⟩

theorem slots_injective {t m extra : Nat} (ht : 2≤t) (hspace : m≤extra) :
    Function.Injective (slots ht hspace) := by
  intro i j he
  have hv:=congrArg Fin.val he
  dsimp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem flag_word {t extra : Nat} (A : Fin t → List Bool) (L : Nat) :
    finalBank A L extra ((Fin.last (t+1)).castAdd extra)=[true] := by
  change finalBank A L extra (((0 : Fin 1).natAdd (t+1)).castAdd extra)=[true]
  simp only [finalBank,Fin.addCases_left,Fin.addCases_right]

theorem input_at_slots {t m extra : Nat} (ht : 2≤t) (hspace : m≤extra)
    (A : Fin t → List Bool) (L : Nat) (x bits : List Bool)
    (hx : A ⟨0,by omega⟩=RepairOrdinary.frame x)
    (hb : A ⟨1,by omega⟩=RepairOrdinary.frame bits) :
    ∀i,finalBank A L extra (slots ht hspace i)=
      (C10SupplierCall.bank [] [] [] x bits (fun _=>[]) : Fin m → List Bool) i := by
  intro i
  by_cases h0:i.val=0
  · have he : slots ht hspace i=(((⟨0,by omega⟩ : Fin t).castAdd 1).castAdd 1).castAdd extra := by
      apply Fin.ext; simp only [slots,h0,if_true,Fin.val_castAdd]
    rw [he,WorkspaceSelectedProgram.finalBank_original]
    simpa only [C10SupplierCall.bank,C10SupplierCall.bankAt,h0,if_true] using hx
  by_cases h1:i.val=1
  · have he : slots ht hspace i=(((⟨1,by omega⟩ : Fin t).castAdd 1).castAdd 1).castAdd extra := by
      apply Fin.ext; simp [slots,h1]
    rw [he,WorkspaceSelectedProgram.finalBank_original]
    simpa [C10SupplierCall.bank,C10SupplierCall.bankAt,h1] using hb
  by_cases hf:i.val=216
  · have he : slots ht hspace i=(Fin.last (t+1)).castAdd extra := by
      apply Fin.ext; simp [slots,hf]
    rw [he,flag_word]
    simp [C10SupplierCall.bank,C10SupplierCall.bankAt,hf]
  · let j : Fin extra := ⟨i.val,by have:=i.isLt;omega⟩
    have he : slots ht hspace i=j.natAdd (t+1+1) := by
      apply Fin.ext; simp only [slots,h0,h1,hf,if_false,Fin.val_natAdd,j]
    rw [he]
    have blank : finalBank A L extra (j.natAdd (t+1+1))=[] := Fin.addCases_right j
    rw [blank]
    simp only [C10SupplierCall.bank,C10SupplierCall.bankAt,h0,h1,hf,if_false]
    split_ifs <;> rfl

def engineTapes (sources : EightSources) (k r D : Nat) : Nat :=
  CloseoutFinalC10SeedEngine.tapesOf
    (HierarchyPrefix.tapes k (CloseoutFinalC10SeedEngine.rp sources) (CloseoutFinalC10SeedEngine.rq sources)) r D

def size (sources : EightSources) (k r D : Nat) : Nat := 218+(60+(engineTapes sources k r D+23))+1

@[irreducible] def program (sources : EightSources) (k r D : Nat) :
    Σ s,Machine (size sources k r D) s :=
  ⟨_,C10PrologueUniform.prologueMachine (engineTapes sources k r D)
    (RecoveryFocus.machine (CloseoutFinalC10SeedEngine.bankSlots
      (HierarchyPrefix.tapes k (CloseoutFinalC10SeedEngine.rp sources) (CloseoutFinalC10SeedEngine.rq sources))
      r D (CloseoutFinalC10SeedEngine.readerIn sources k))
      (CloseoutFinalC10SeedEngine.engineMachine r D (CloseoutFinalC10SeedEngine.widthReader sources k)
        (CloseoutFinalC10SeedEngine.readerQ sources k) (C10PartsSchedule.thresholdFloor sources)))⟩

def output (sources : EightSources) (k r D n : Nat) (x bits : List Bool) (w : Nat→List Bool) :
    Fin (size sources k r D) → List Bool :=
  Fin.addCases (motive:=fun _=>List Bool)
    (C10SupplierCall.bank [] (VerifierDecoding.CompareMachine.word 0)
      (List.replicate (C10PartsSchedule.entryWidthSchedule sources k r n) true) x bits w)
    (fun _ : Fin 1 => VerifierDecoding.CompareMachine.word
      (2^CloseoutLanguage.clauseWidth D (C10PartsSchedule.widthAt sources k n)))

def outputHeads (sources : EightSources) (k r D : Nat) : Fin (size sources k r D) → Nat :=
  Fin.addCases (motive:=fun _=>Nat) (fun _ =>0) (fun _ : Fin 1=>1)

theorem local_run (sources : EightSources) (k r D : Nat) (hD : 1≤D)
    (n : Nat) (x : BitInput n) (bits : List Bool) :
    ∃ w,Step (program sources k r D).2 (C10EngineFuelSeam.enginePreFuel sources k r D n)
      (fun _=>0) (C10SupplierCall.bank [] [] [] (List.ofFn x) bits (fun _=>[]))
      (outputHeads sources k r D) (output sources k r D n (List.ofFn x) bits w) := by
  unfold program
  exact CloseoutFinalC10SeedEngine.prologue_at_schedule sources k r D hD
    (CloseoutFinalC10SeedEngine.widthReader sources k) (CloseoutFinalC10SeedEngine.readerIn sources k)
    (CloseoutFinalC10SeedEngine.readerQ sources k) (CloseoutFinalC10SeedEngine.readerIn_ne sources k)
    (CloseoutFinalC10SeedEngine.readerFuel sources k) (CloseoutFinalC10SeedEngine.width_reader sources k) n x bits

/-- Complete physical join from a selected admission bank. All old parser
ports other than input/witness are outside the prologue; the complete exit
is the displayed installation, with no implicit blank-bank replacement. -/
theorem run (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r extra : Nat)
    (hspace : size sources k r p.clauseDegree≤extra)
    (n : Nat) (x : BitInput n) (bits : List Bool)
    (A : Fin (originalTapes sources p k) → List Bool) (L : Nat)
    (originals : WorkspaceSelectedOriginals.Originals sources p k x bits A) :
    let ht : 2≤originalTapes sources p k := by
      dsimp [originalTapes,WorkspaceBoundedGateEntry.originalTapes,WorkspaceBoundedAdmission.tapes,HeaderDock.tapes]
      omega
    let port := slots ht hspace
    ∃ w,Step (RecoveryFocus.machine port (program sources k r p.clauseDegree).2)
      (C10EngineFuelSeam.enginePreFuel sources k r p.clauseDegree n) (fun _=>0) (finalBank A L extra)
      (dockH port (fun _=>0) (outputHeads sources k r p.clauseDegree))
      (install port (finalBank A L extra) (output sources k r p.clauseDegree n (List.ofFn x) bits w)) ∧
      ∀v,(∀i,port i≠v) →
        install port (finalBank A L extra) (output sources k r p.clauseDegree n (List.ofFn x) bits w) v=
          finalBank A L extra v := by
  intro ht port
  obtain ⟨w,hr⟩:=local_run sources k r p.clauseDegree p.hD n x bits
  have inp := input_at_slots ht hspace A L (List.ofFn x) bits originals.1 originals.2.1
  exact ⟨w,hr.dock port (slots_injective ht hspace) (fun _=>0) (finalBank A L extra)
    (fun _=>rfl) inp,fun v hv=>install_other port _ _ v hv⟩

/-- Existing exact fuel, with the fixed degree 2 and only its eventual onset
remaining. No poly(N) preprocessing is charged as a poly(width) operation. -/
theorem resource (sources : EightSources) (k r D : Nat) :
    ∃ onset,∀n,onset≤n → C10EngineFuelSeam.enginePreFuel sources k r D n≤(n+1)^2 := by
  simpa only [C10FuelRepin.polyFuel,one_mul] using
    C10EngineFuelSeam.enginePreFuel_le_polyFuel sources k r D 1 (by omega)

end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntry
