import Proof.MachineModel.TopDownWorkspaceGuarded

/-! Choose admission's fixed onset using k/clock alone, then build the actual
ordinary gate at that onset. The rejected branch is proved from the exact
admission receipt. The admitted continuation and whole Runtime stay explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceGuardedWorker
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal
open CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal.C10GuardedMachineConsumer
open RepairSource.CloseoutFinal.C10GuardedStageConsumer
open RepairSource.CloseoutFinal.C10Fusion
open RepairSource.CloseoutFinal.C10LengthGate
noncomputable section

/-- This datum selects only the semantic k/clock-dependent admission onset;
its dummy worker is never run by the constructed weak machine. -/
def reference (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) : WorkerData where
  k := k
  clock := clock
  tapes := 2
  states := 2
  worker := counter 0 0 1
  result := 1
  fuel := fun _ => 0
  onset := 0
  passed := fun _ _ _ => false

def legalOnset (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (coldCutoff : Nat) : Nat :=
  Classical.choose (C10LegalAdmission.passed_legal_eventually sources p (reference k clock) coldCutoff)

def onset (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (coldCutoff base : Nat) : Nat :=
  max (max base (Soundness.cutoff (constantsOf sources))) (legalOnset sources p k clock coldCutoff)

def input {t : Nat} (x bits : List Bool) : Fin t → List Bool :=
  fun i => if i.val=0 then RepairOrdinary.frame x else if i.val=1 then RepairOrdinary.frame bits else []

def entry {t : Nat} (lengthFlag : Fin t) (x bits : List Bool) : Fin t → List Bool :=
  exitTapes lengthFlag (input x bits) 0 true

/-- The finite control is constructed only after the final onset is selected. -/
def data (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (coldCutoff base : Nat)
    {t a b : Nat} (admission : Machine t a) (continuation : Machine t b)
    (inputTape lengthFlag admissionFlag result : Fin t)
    (preFuel bodyFuel : Nat → Nat) : WorkerData where
  k := k
  clock := clock
  tapes := t
  states := _
  worker := admittedWorker (onset sources p k clock coldCutoff base)
    admission continuation inputTape lengthFlag admissionFlag result
  result := result
  fuel := fun n => 4*onset sources p k clock coldCutoff base+5+preFuel n+bodyFuel n
  onset := onset sources p k clock coldCutoff base
  passed := C10LegalAdmission.passed sources p (reference k clock) coldCutoff

theorem legal_admission (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (coldCutoff base : Nat)
    {t a b : Nat} (admission : Machine t a) (continuation : Machine t b)
    (inputTape lengthFlag admissionFlag result : Fin t) (preFuel bodyFuel : Nat → Nat) :
    let W := data sources p k clock coldCutoff base admission continuation
      inputTape lengthFlag admissionFlag result preFuel bodyFuel
    ∀ s, W.onset ≤ s → ∀ (x : BitInput (2^s)) (guess : BitInput (2^s/16)),
      LegalWitness sources p W (2^s) x (List.ofFn guess) →
      W.passed (2^s) x (List.ofFn guess) = true := by
  intro W s hs x guess hlegal
  have h : legalOnset sources p k clock coldCutoff ≤ s :=
    (Nat.le_max_right _ _).trans hs
  exact Classical.choose_spec
    (C10LegalAdmission.passed_legal_eventually sources p (reference k clock) coldCutoff)
    s h x guess hlegal

/-- A physically rejecting run below the actual final finite gate. -/
theorem below_run {t a b : Nat} (C : Nat) (admission : Machine t a)
    (continuation : Machine t b) (inputTape lengthFlag admissionFlag result : Fin t)
    (hinput : inputTape.val=0) (hflag : lengthFlag ≠ inputTape)
    {n : Nat} (x : BitInput n) (bits : List Bool) (hn : n<C) :
    ∃ heads exit, Step (admittedWorker C admission continuation
      inputTape lengthFlag admissionFlag result) (2*n+3)
      (fun _ => 0) (input (List.ofFn x) bits) heads exit ∧
      readTapeBit (exit result) (heads result) = false := by
  have hT : input (List.ofFn x) bits inputTape = RepairOrdinary.frame (List.ofFn x) := by
    simp [input,hinput]
  have hread : ∀ j,j<2*n → j%2=0 →
      readTapeBit (input (List.ofFn x) bits inputTape) ((fun _ : Fin t => 0) inputTape+j)=true := by
    intro j hj he
    rw [hT]
    simpa only [Nat.zero_add,List.length_ofFn] using frame_short (List.ofFn x) j
      (by simpa only [List.length_ofFn] using hj) he
  have hstop : readTapeBit (input (List.ofFn x) bits inputTape)
      ((fun _ : Fin t => 0) inputTape+2*n)=false := by
    rw [hT]
    simpa only [Nat.zero_add,List.length_ofFn] using frame_stop (List.ofFn x)
  obtain ⟨r,hr,hfalse⟩ := gated_reject C inputTape lengthFlag result
    (admittedInner admission continuation admissionFlag result) hflag (fun _ => 0)
    (input (List.ofFn x) bits) n (by omega) hread hstop
  exact ⟨r.final.heads,r.final.tapes,Step.of_run hr rfl rfl,hfalse⟩

/-- Exact above-onset rejected path: run admission once and stop at its false
flag, keeping all its final heads and tapes except the decision bit. -/
theorem rejected_run {t a b : Nat} (C : Nat) (admission : Machine t a)
    (continuation : Machine t b) (inputTape lengthFlag admissionFlag result : Fin t)
    (hinput : inputTape.val=0) {n : Nat} (x : BitInput n) (bits : List Bool) (hn : C≤n)
    (preFuel : Nat) (H : Fin t → Nat) (A : Fin t → List Bool)
    (hpre : Step admission preFuel (fun _ => 0) (entry lengthFlag (List.ofFn x) bits) H A)
    (hfalse : readTapeBit (A admissionFlag) (H admissionFlag)=false) :
    Step (admittedWorker C admission continuation inputTape lengthFlag admissionFlag result)
      (4*C+5+preFuel) (fun _ => 0) (input (List.ofFn x) bits) H
      (exitTapes result A (H result) false) := by
  have inner := inner_reject admission continuation admissionFlag result preFuel
    (fun _ => 0) H (entry lengthFlag (List.ofFn x) bits) A hpre hfalse
  have hread : ∀ j,j<2*C → j%2=0 →
      readTapeBit (input (List.ofFn x) bits inputTape) ((fun _ : Fin t => 0) inputTape+j)=true := by
    intro j hj he
    rw [show input (List.ofFn x) bits inputTape = RepairOrdinary.frame (List.ofFn x) by
      simp [input,hinput]]
    simpa only [Nat.zero_add] using frame_short (List.ofFn x) j
      (by simpa only [List.length_ofFn] using (show j<2*n by omega)) he
  have whole := gated_pass C inputTape lengthFlag result
    (admittedInner admission continuation admissionFlag result) (fun _ => 0)
    (input (List.ofFn x) bits) hread (preFuel+1+1) H _ inner
  have hf : (4*C+1)+1+((preFuel+1+1)+1)=4*C+5+preFuel := by omega
  rw [hf] at whole
  exact whole

/-- The entire rejected field, against the actual chosen worker and budget.
The only physical input is the bounded admission receipt at the gate's exit. -/
theorem rejected (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (coldCutoff base : Nat)
    {t a b : Nat} (admission : Machine t a) (continuation : Machine t b)
    (inputTape lengthFlag admissionFlag result : Fin t) (preFuel bodyFuel : Nat → Nat)
    (ht : 2≤t) (hinput : inputTape.val=0) (hflag : lengthFlag ≠ inputTape)
    (hpre : ∀ n x bits,onset sources p k clock coldCutoff base ≤ n →
      ∃ H A,Step admission (preFuel n) (fun _ => 0) (entry lengthFlag (List.ofFn x) bits) H A ∧
        readTapeBit (A admissionFlag) (H admissionFlag)=
          C10LegalAdmission.passed sources p (reference k clock) coldCutoff n x bits) :
    let W := data sources p k clock coldCutoff base admission continuation
      inputTape lengthFlag admissionFlag result preFuel bodyFuel
    ∀ n x bits,n<W.onset ∨ W.passed n x bits=false →
      RejectedAt W.worker ht W.result W.fuel n x bits := by
  intro W n x bits hrej
  have hbank : (UAcceptanceCarrier.verifier W.worker ht W.result).inputTapes (List.ofFn x) bits =
      input (List.ofFn x) bits := UAcceptanceCarrier.inputTapes_eq _ _ _ _ _
  by_cases hn : n<onset sources p k clock coldCutoff base
  · obtain ⟨H,A,hr,hfalse⟩ := below_run _ admission continuation inputTape lengthFlag admissionFlag result
      hinput hflag x bits hn
    refine ⟨H,A,?_,hfalse⟩
    rw [hbank]
    exact hr.enlarge (by dsimp [W,data]; omega)
  · have hp : C10LegalAdmission.passed sources p (reference k clock) coldCutoff n x bits=false := by
      rcases hrej with hsmall|hfalse
      · exact (hn hsmall).elim
      · exact hfalse
    obtain ⟨H,A,hactual,hpassed⟩ := hpre n x bits (by omega)
    have hr := rejected_run (onset sources p k clock coldCutoff base)
      admission continuation inputTape lengthFlag admissionFlag result
      hinput x bits (by omega) (preFuel n) H A hactual (hpassed.trans hp)
    refine ⟨H,exitTapes result A (H result) false,?_,?_⟩
    · rw [hbank]
      exact hr.enlarge (by dsimp [W,data]; omega)
    · change readTapeBit (exitTapes result A (H result) false result) (H result)=false
      simp [exitTapes,MemoryTransition.read_write]

end
end NearCubicWires.P1TopDown.WorkspaceGuardedWorker
