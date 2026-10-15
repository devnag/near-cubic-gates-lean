import Proof.MachineModel.ClockInitialKey

/-! Fixed-U's scalar bound guard: normalize both fields, compare them, and
conjoin comparison with the physical B-field overflow bit. -/
namespace NearCubicWires.RepairOrdinary.ClockBoundGuard
open LocalBitMultitape ClockJoin RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def normalizeOutput (w : ℕ) (bits : List Bool) : Fin 5 → List Bool :=
  ![List.replicate w true,frame bits,frame (ClockNormalize.resize w bits),
    [decide (bits.length≤w)],List.replicate (2*w+1) false]
theorem normalize_ready (w : ℕ) (bits : List Bool) :
    ReadyRun ClockNormalize.machine (4*w+4) (ClockNormalize.input w bits) (normalizeOutput w bits) := by
  obtain ⟨r,hr,h0,h1,h2,h3,h4,hh,hs⟩ := ClockNormalize.normalize_run w bits
  refine ⟨r,hr,?_,hh,hs.le⟩
  funext i; fin_cases i <;> simp [normalizeOutput,h0,h1,h2,h3,h4]

def comparison : Machine 4 7 := Rewind.machine Compare.machine
def comparisonInput (a b : List Bool) : Fin 4 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (3+1) => List Bool) ![frame a,frame b,[]] (fun _ : Fin 1 => [])
theorem comparison_ready (a b : List Bool) (hw : a.length=b.length) :
    ReadyRun comparison (4*a.length+4) (comparisonInput a b)
      ![frame a,frame b,[decide (value a≤value b)],List.replicate (2*a.length+1) false] := by
  obtain ⟨base,hb,hf,hs,_⟩ := Compare.compare_run [] [] a b [] [] [] hw
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hb hf
  have hi : Compare.config (Compare.scanState true) (frame a) (frame b) 0 0 []=
      initialConfiguration Compare.machine ![frame a,frame b,[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at hb
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace Compare.machine _ _ base hb 0
  refine ⟨r,?_,?_,hh,by omega⟩
  · have htime : 2*base.steps+2=4*a.length+4 := by omega
    rw [htime] at hr
    exact hr
  · funext i; fin_cases i
    · simpa [hf,Compare.config] using ht 0
    · simpa [hf,Compare.config] using ht 1
    · simpa [hf,Compare.config] using ht 2
    · simpa [hs] using hcounter

def conjunction : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==1
  rule := fun s bits => if s.val=0 then
    some ⟨1,![none,none,some (bits 0 && bits 1)],fun _ => .stay⟩ else none
theorem conjunction_ready (a b : Bool) :
    ReadyRun conjunction 1 ![[a],[b],[]] ![[a],[b],[a && b]] := by
  let c : Configuration 3 2 := ⟨1,fun _ => 0,![[a],[b],[a && b]]⟩
  have he : step conjunction (initialConfiguration conjunction ![[a],[b],[]])=some c := by
    simp [step,conjunction,initialConfiguration,Configuration.scanned,readTapeBit]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [applyAction,c,writeTapeBit]
  have hp := Prefix.step (by simp [Configuration.tapeCells,initialConfiguration,Fin.sum_univ_succ] :
      (initialConfiguration conjunction ![[a],[b],[]]).tapeCells≤3)
    (by rfl : conjunction.halted conjunction.start=false) he
    (Prefix.refl c (by simp [c,Configuration.tapeCells,Fin.sum_univ_succ]))
  obtain ⟨r,hr,hf,hs,_⟩ := hp.run (by rfl) (by simp [c,Configuration.tapeCells,Fin.sum_univ_succ])
  exact ⟨r,hr,by rw [hf],by rw [hf]; intro i; rfl,hs.le⟩

def normalized (w : ℕ) (bits : List Bool) : List Bool := ClockNormalize.resize w bits
def cmp (w : ℕ) (a b : List Bool) : Bool := decide (value (normalized w a)≤value (normalized w b))
def accepted (w : ℕ) (a b : List Bool) : Bool := decide (a.length≤w) && cmp w a b
def input (w : ℕ) (a b : List Bool) : Fin 12 → List Bool :=
  ![List.replicate w true,frame a,[],[],[],frame b,[],[],[],[],[],[]]
def afterLeft (w : ℕ) (a b : List Bool) : Fin 12 → List Bool :=
  ![List.replicate w true,frame a,frame (normalized w a),[decide (a.length≤w)],List.replicate (2*w+1) false,
    frame b,[],[],[],[],[],[]]
def afterRight (w : ℕ) (a b : List Bool) : Fin 12 → List Bool :=
  ![List.replicate w true,frame a,frame (normalized w a),[decide (a.length≤w)],List.replicate (2*w+1) false,
    frame b,frame (normalized w b),[decide (b.length≤w)],List.replicate (2*w+1) false,[],[],[]]
def afterCompare (w : ℕ) (a b : List Bool) : Fin 12 → List Bool :=
  ![List.replicate w true,frame a,frame (normalized w a),[decide (a.length≤w)],List.replicate (2*w+1) false,
    frame b,frame (normalized w b),[decide (b.length≤w)],List.replicate (2*w+1) false,
    [cmp w a b],List.replicate (2*w+1) false,[]]
def output (w : ℕ) (a b : List Bool) : Fin 12 → List Bool :=
  ![List.replicate w true,frame a,frame (normalized w a),[decide (a.length≤w)],List.replicate (2*w+1) false,
    frame b,frame (normalized w b),[decide (b.length≤w)],List.replicate (2*w+1) false,
    [cmp w a b],List.replicate (2*w+1) false,[accepted w a b]]

def rightLayout : Fin 12 ≃ Fin 12 where
  toFun := ![0,5,6,7,8,1,2,3,4,9,10,11]
  invFun := ![0,5,6,7,8,1,2,3,4,9,10,11]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def compareLayout : Fin 12 ≃ Fin 12 where
  toFun := ![2,6,9,10,0,1,3,4,5,7,8,11]
  invFun := ![4,5,0,6,7,8,1,9,10,2,3,11]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def conjunctionLayout : Fin 12 ≃ Fin 12 where
  toFun := ![3,9,11,0,1,2,4,5,6,7,8,10]
  invFun := ![3,4,5,0,6,7,8,9,10,1,11,2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def leftPhase : Machine 12 6 := ClockJoin.lifted (e:=7) (Equiv.refl _) ClockNormalize.machine
def rightPhase : Machine 12 6 := ClockJoin.lifted (e:=7) rightLayout ClockNormalize.machine
def comparePhase : Machine 12 7 := ClockJoin.lifted (e:=8) compareLayout comparison
def conjunctionPhase : Machine 12 2 := ClockJoin.lifted (e:=9) conjunctionLayout conjunction
def machine : Machine 12 21 := Composition.machine
  (Composition.machine (Composition.machine leftPhase rightPhase) comparePhase) conjunctionPhase

theorem left_phase (w : ℕ) (a b : List Bool) : ReadyRun leftPhase (4*w+4) (input w a b) (afterLeft w a b) := by
  let extra : Fin 7 → List Bool := ![frame b,[],[],[],[],[],[]]
  have hl := ClockJoin.lift (Equiv.refl (Fin 12)) ClockNormalize.machine (4*w+4) _ _ extra (normalize_ready w a)
  have hi : data (Equiv.refl (Fin 12)) (ClockNormalize.input w a) extra=input w a b := by
    funext i; fin_cases i <;> rfl
  have ho : data (Equiv.refl (Fin 12)) (normalizeOutput w a) extra=afterLeft w a b := by
    funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact hl
theorem right_phase (w : ℕ) (a b : List Bool) : ReadyRun rightPhase (4*w+4) (afterLeft w a b) (afterRight w a b) := by
  let extra : Fin 7 → List Bool := ![frame a,frame (normalized w a),[decide (a.length≤w)],
    List.replicate (2*w+1) false,[],[],[]]
  have hl := ClockJoin.lift rightLayout ClockNormalize.machine (4*w+4) _ _ extra (normalize_ready w b)
  have hi : data rightLayout (ClockNormalize.input w b) extra=afterLeft w a b := by
    funext i; fin_cases i <;> rfl
  have ho : data rightLayout (normalizeOutput w b) extra=afterRight w a b := by
    funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact hl
theorem compare_phase (w : ℕ) (a b : List Bool) : ReadyRun comparePhase (4*w+4) (afterRight w a b) (afterCompare w a b) := by
  have h := comparison_ready (normalized w a) (normalized w b) (by simp [normalized])
  simp only [normalized,ClockNormalize.resize_length] at h
  let extra : Fin 8 → List Bool := ![List.replicate w true,frame a,[decide (a.length≤w)],
    List.replicate (2*w+1) false,frame b,[decide (b.length≤w)],List.replicate (2*w+1) false,[]]
  have hl := ClockJoin.lift compareLayout comparison (4*w+4) _ _ extra h
  have hi : data compareLayout (comparisonInput (normalized w a) (normalized w b)) extra=afterRight w a b := by
    funext i; fin_cases i <;> rfl
  have ho : data compareLayout
      ![frame (normalized w a),frame (normalized w b),[cmp w a b],List.replicate (2*w+1) false]
      extra=afterCompare w a b := by funext i; fin_cases i <;> rfl
  change ReadyRun _ _ (data compareLayout (comparisonInput (normalized w a) (normalized w b)) extra)
    (data compareLayout ![frame (normalized w a),frame (normalized w b),[cmp w a b],List.replicate (2*w+1) false] extra) at hl
  rw [hi,ho] at hl
  exact hl
theorem conjunction_phase (w : ℕ) (a b : List Bool) : ReadyRun conjunctionPhase 1 (afterCompare w a b) (output w a b) := by
  let extra : Fin 9 → List Bool := ![List.replicate w true,frame a,frame (normalized w a),List.replicate (2*w+1) false,
    frame b,frame (normalized w b),[decide (b.length≤w)],List.replicate (2*w+1) false,List.replicate (2*w+1) false]
  have hl := ClockJoin.lift conjunctionLayout conjunction 1 _ _ extra (conjunction_ready (decide (a.length≤w)) (cmp w a b))
  have hi : data conjunctionLayout ![[decide (a.length≤w)],[cmp w a b],[]] extra=afterCompare w a b := by
    funext i; fin_cases i <;> rfl
  have ho : data conjunctionLayout ![[decide (a.length≤w)],[cmp w a b],[accepted w a b]] extra=output w a b := by
    funext i; fin_cases i <;> rfl
  dsimp only [accepted] at ho
  rw [hi,ho] at hl
  exact hl

theorem guard_ready (w : ℕ) (a b : List Bool) : ReadyRun machine (16*(w+1)) (input w a b) (output w a b) := by
  have hnorm := ClockJoin.join leftPhase rightPhase _ _ _ _ _ (left_phase w a b) (right_phase w a b)
  have hcmp := ClockJoin.join (Composition.machine leftPhase rightPhase) comparePhase _ _ _ _ _ hnorm (compare_phase w a b)
  have h := ClockJoin.join (Composition.machine (Composition.machine leftPhase rightPhase) comparePhase)
    conjunctionPhase _ _ _ _ _ hcmp (conjunction_phase w a b)
  exact ClockJoin.enlarge machine _ _ _ _ h (by omega)

theorem accepted_iff (w : ℕ) (a b : List Bool) (hb : b.length≤w) :
    accepted w a b=decide (a.length≤w ∧ value a≤value b) := by
  by_cases ha : a.length≤w
  · simp [accepted,cmp,normalized,ha,ClockScalarFields.resize_value w a ha,ClockScalarFields.resize_value w b hb]
  · simp [accepted,ha]

theorem guard_run (w : ℕ) (a b : List Bool) (hb : b.length≤w) :
    ∃ r : ExecutionReceipt 12 21,
      run machine (16*(w+1)) (input w a b)=some r ∧
      r.final.tapes 11=[decide (a.length≤w ∧ value a≤value b)] ∧
      r.final.tapes 0=List.replicate w true ∧ r.final.tapes 1=frame a ∧ r.final.tapes 5=frame b ∧
      (∀ i,r.final.heads i=0) ∧ r.steps≤16*(w+1) := by
  obtain ⟨r,hr,hf,hh,hs⟩ := guard_ready w a b
  exact ⟨r,hr,by simp [hf,output,accepted_iff w a b hb],by simp [hf,output],by simp [hf,output],
    by simp [hf,output],hh,hs⟩

end NearCubicWires.RepairOrdinary.ClockBoundGuard
