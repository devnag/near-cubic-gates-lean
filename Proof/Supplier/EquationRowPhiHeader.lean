import Proof.Supplier.EquationHeaderCounts
import Proof.Amplification.RecoveryScratchErase
import Proof.MachineModel.OrdinaryMatrixCoefficientHeaders
import Proof.MachineModel.Runs

namespace NearCubicWires.RepairOrdinary.EquationRowPhiHeader
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- A focused stage entered from zero-padded ambient tapes. -/
theorem padStage {u a b t : ℕ} (P : Machine u a) (sl : Fin t → Fin u) (hinj : Function.Injective sl)
    (Q : Machine t b) (fp fq : ℕ) (c : Configuration u a) (r : ExecutionReceipt u a)
    (hp : runFrom P fp c=some r) (entry : Configuration t b) (s : ExecutionReceipt t b)
    (hq : runFrom Q fq entry=some s) (hstart : entry.control=Q.start) (cap : Fin t → ℕ)
    (hh : ∀ i, r.final.heads (sl i)=entry.heads i)
    (ht : ∀ i, r.final.tapes (sl i)=ZeroPadding.pad (cap i) (entry.tapes i)) :
    ∃ res : ExecutionReceipt u (a+b),
      runFrom (Composition.machine P (RecoveryFocus.machine sl Q)) (fp+1+fq)
        (Composition.leftConfig b c)=some res ∧
      (∀ i, res.final.heads (sl i)=s.final.heads i) ∧
      (∀ i, res.final.tapes (sl i)=ZeroPadding.pad (cap i) (s.final.tapes i)) ∧
      (∀ j, RecoveryFocus.pick sl j=none →
        res.final.heads j=r.final.heads j ∧ res.final.tapes j=r.final.tapes j) ∧
      res.steps=r.steps+1+s.steps := by
  obtain ⟨s',hs',hsf,hss,_⟩ := ZeroPadding.run_config Q cap fq entry s hq
  obtain ⟨res,hres,rh,rt,ro,rs⟩ := MatrixCoefficientHeaders.stage P sl hinj Q fp fq c r hp
    (ZeroPadding.config cap entry) s' hs' hstart hh ht
  refine ⟨res,hres,?_,?_,ro,?_⟩
  · intro i; rw [rh i, hsf]; rfl
  · intro i; rw [rt i, hsf]; rfl
  · rw [rs, hss]

/-! ### Stage 1: erase bank 24 (`replicate (2d+1) true`) with driver bank 26 and recording bank 31. -/

def eraseSlots : Fin 3 → Fin 126 := ![54,56,61]
theorem erase_injective : Function.Injective eraseSlots := by decide
noncomputable def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
def driverLength (d p : ℕ) := (2*d+1)*(p+1)
def eraseBudget (d p : ℕ) := 2*driverLength d p+4

def eraseInput (d p cap : ℕ) : Fin 3 → List Bool :=
  ![List.replicate (2*d+1) true,List.replicate (driverLength d p) true,List.replicate cap false]
def eraseOutput (d p cap : ℕ) : Fin 3 → List Bool :=
  ![List.replicate (driverLength d p) false,List.replicate (driverLength d p) true,
    List.replicate (max cap (driverLength d p+1)) false]

theorem erase_ready (d p cap : ℕ) :
    RecoveryRootRound.ReadyRun (RecoveryScratchErase.resetMachine 1) (eraseBudget d p)
      (eraseInput d p cap) (eraseOutput d p cap) := by
  have hb : ∀ i : Fin 1, ((fun _ : Fin 1 => List.replicate (2*d+1) true) i).length ≤ driverLength d p := by
    intro _; simp only [List.length_replicate, driverLength]; nlinarith
  have h := RecoveryScratchErase.erase_ready (driverLength d p) cap
    (fun _ : Fin 1 => List.replicate (2*d+1) true) hb
  have hi : Fin.addCases (m := 1+1) (n := 1) (motive := fun _ => List Bool)
      (Fin.addCases (m := 1) (n := 1) (motive := fun _ => List Bool)
        (fun _ : Fin 1 => List.replicate (2*d+1) true)
        (fun _ : Fin 1 => List.replicate (driverLength d p) true))
      (fun _ : Fin 1 => List.replicate cap false)=eraseInput d p cap := by
    funext i; fin_cases i <;> rfl
  have ho : Fin.addCases (m := 1+1) (n := 1) (motive := fun _ => List Bool)
      (Fin.addCases (m := 1) (n := 1) (motive := fun _ => List Bool)
        (fun _ : Fin 1 => List.replicate (driverLength d p) false)
        (fun _ : Fin 1 => List.replicate (driverLength d p) true))
      (fun _ : Fin 1 => List.replicate (max cap (driverLength d p+1)) false)=eraseOutput d p cap := by
    funext i; fin_cases i <;> rfl
  rw [hi,ho] at h
  exact h

theorem erase_stage {a : ℕ} (P : Machine 126 a) (fp : ℕ) (c : Configuration 126 a)
    (r : ExecutionReceipt 126 a) (hp : runFrom P fp c=some r) (d p cap : ℕ)
    (h54 : r.final.tapes 54=List.replicate (2*d+1) true) (h56 : r.final.tapes 56=List.replicate (driverLength d p) true)
    (h61 : r.final.tapes 61=List.replicate cap false) (hcap : driverLength d p+1 ≤ cap)
    (hh54 : r.final.heads 54=0) (hh56 : r.final.heads 56=0) (hh61 : r.final.heads 61=0) :
    ∃ res : ExecutionReceipt 126 (a+4),
      runFrom (Composition.machine P erase) (fp+1+eraseBudget d p) (Composition.leftConfig 4 c)=some res ∧
      res.final.tapes 54=List.replicate (driverLength d p) false ∧ res.final.heads 54=0 ∧
      res.final.tapes 56=List.replicate (driverLength d p) true ∧ res.final.heads 56=0 ∧
      res.final.tapes 61=List.replicate cap false ∧ res.final.heads 61=0 ∧
      (∀ j, RecoveryFocus.pick eraseSlots j=none →
        res.final.heads j=r.final.heads j ∧ res.final.tapes j=r.final.tapes j) ∧
      res.steps=r.steps+1+eraseBudget d p := by
  obtain ⟨s,hs,st,sh,ss⟩ := erase_ready d p cap
  have hcapmax : max cap (driverLength d p+1)=cap := max_eq_left hcap
  obtain ⟨res,hres,rh,rt,ro,rs⟩ := padStage P eraseSlots erase_injective _ fp _ c r hp
    (initialConfiguration (RecoveryScratchErase.resetMachine 1) (eraseInput d p cap)) s hs rfl (fun _ => 0)
    (by intro i; fin_cases i <;> simp [initialConfiguration,eraseSlots,hh54,hh56,hh61])
    (by
      intro i
      fin_cases i
      · simpa [initialConfiguration,eraseSlots,eraseInput] using h54
      · simpa [initialConfiguration,eraseSlots,eraseInput] using h56
      · simpa [initialConfiguration,eraseSlots,eraseInput] using h61)
  have t0 := rt 0
  have t1 := rt 1
  have t2 := rt 2
  simp only [st,ZeroPadding.pad_zero] at t0 t1 t2
  refine ⟨res,hres,?_,?_,?_,?_,?_,?_,ro,?_⟩
  · simpa [eraseSlots,eraseOutput] using t0
  · simpa [eraseSlots,sh] using rh 0
  · simpa [eraseSlots,eraseOutput] using t1
  · simpa [eraseSlots,sh] using rh 1
  · simpa [eraseSlots,eraseOutput,hcapmax] using t2
  · simpa [eraseSlots,sh] using rh 2
  · rw [rs,ss]

/-! ### Stage 2: append `natWord d` with sixteen all-false work tapes. -/

/-- Local 0: the first header program's retained `replicate d true` (tape 62); locals 1..16: the
all-false banks 5,7,9,11,13,15,16,17,19,21,23,24(erased),25,27,29,31; local 17: the output. -/
def appendSlots : Fin 18 → Fin 126 := ![62,35,37,39,41,43,45,46,47,49,51,53,54,55,57,59,61,110]
theorem append_injective : Function.Injective appendSlots := by decide
noncomputable def append := RecoveryFocus.machine appendSlots EquationHeaderAppend.machine

/-- Zero-padding capacities: the current lengths of the sixteen all-false work tapes. -/
def appendCap (A : Fin 126 → List Bool) (i : Fin 18) : ℕ :=
  if i.val=0 ∨ i.val=17 then 0 else (A (appendSlots i)).length

theorem append_stage {a : ℕ} (P : Machine 126 a) (fp : ℕ) (c : Configuration 126 a)
    (r : ExecutionReceipt 126 a) (hp : runFrom P fp c=some r) (d : ℕ) (out : List Bool)
    (h62 : r.final.tapes 62=List.replicate d true) (hh62 : r.final.heads 62=0)
    (h110 : r.final.tapes 110=out) (hh110 : r.final.heads 110=out.length)
    (hz : ∀ i : Fin 18, i.val≠0 → i.val≠17 →
      r.final.tapes (appendSlots i)=List.replicate (r.final.tapes (appendSlots i)).length false ∧
      r.final.heads (appendSlots i)=0) :
    ∃ res : ExecutionReceipt 126 (a+_),
      runFrom (Composition.machine P append) (fp+1+EquationHeaderAppend.budget d)
        (Composition.leftConfig _ c)=some res ∧
      res.final.tapes 110=out++natWord d ∧ res.final.heads 110=(out++natWord d).length ∧
      res.final.tapes 35=ZeroPadding.pad (r.final.tapes 35).length (List.replicate d true) ∧
      res.final.heads 35=0 ∧
      (∀ j, RecoveryFocus.pick appendSlots j=none →
        res.final.heads j=r.final.heads j ∧ res.final.tapes j=r.final.tapes j) ∧
      res.steps ≤ r.steps+1+EquationHeaderAppend.budget d := by
  obtain ⟨s,hs,st,sh,s1,sh1,ss⟩ := EquationHeaderAppend.append_run d out
  obtain ⟨res,hres,rh,rt,ro,rs⟩ := padStage P appendSlots append_injective _ fp _ c r hp
    (EquationHeaderAppend.entry d out) s hs rfl (appendCap r.final.tapes)
    (by
      intro i
      by_cases h0 : i.val=0
      · have : i=0 := Fin.ext h0
        subst this
        simpa [EquationHeaderAppend.entry,EquationHeaderAppend.heads,appendSlots] using hh62
      · by_cases h17 : i.val=17
        · have : i=17 := Fin.ext h17
          subst this
          simpa [EquationHeaderAppend.entry,EquationHeaderAppend.heads,appendSlots] using hh110
        · have hi : i≠17 := fun he => h17 (congrArg Fin.val he)
          rw [(hz i h0 h17).2]
          simp [EquationHeaderAppend.entry,EquationHeaderAppend.heads,hi])
    (by
      intro i
      by_cases h0 : i.val=0
      · have : i=0 := Fin.ext h0
        subst this
        simpa [EquationHeaderAppend.entry,EquationHeaderAppend.tapes,appendCap,appendSlots] using h62
      · by_cases h17 : i.val=17
        · have : i=17 := Fin.ext h17
          subst this
          simpa [EquationHeaderAppend.entry,EquationHeaderAppend.tapes,appendCap,appendSlots] using h110
        · have hi0 : i≠0 := fun he => h0 (congrArg Fin.val he)
          have hi : i≠17 := fun he => h17 (congrArg Fin.val he)
          have hc : appendCap r.final.tapes i=(r.final.tapes (appendSlots i)).length := by
            simp [appendCap,h0,h17]
          rw [hc]
          simp only [EquationHeaderAppend.entry,EquationHeaderAppend.tapes,hi0,hi,ite_false]
          exact (MatrixCoefficientHeaders.pad_nil_self _ (hz i h0 h17).1).symm)
  have r17 := rt 17
  have r1 := rt 1
  rw [st] at r17
  rw [s1] at r1
  refine ⟨res,hres,?_,?_,?_,?_,ro,?_⟩
  · simpa [appendCap,appendSlots] using r17
  · simpa [appendSlots,sh] using rh 17
  · simpa [appendCap,appendSlots] using r1
  · simpa [appendSlots,sh1] using rh 1
  · rw [rs]; omega

/-! ### Stage 3: a five-tape column writer (count, output, three scratch tapes). -/

/-- Local 0: the appended count copy (tape 35); local 1: the output; locals 2..4: three blank
extras whose final all-false contents fit back inside their allocated capacity. -/
def writerSlots : Fin 5 → Fin 126 := ![35,110,111,112,113]
theorem writer_injective : Function.Injective writerSlots := by decide

theorem pad_replicate_false (C k : ℕ) (h : k ≤ C) :
    ZeroPadding.pad C (List.replicate k false)=List.replicate C false := by
  simp only [ZeroPadding.pad,List.length_replicate]
  rw [← List.replicate_add]
  congr 1
  omega

theorem writer_stage {a sw : ℕ} (P : Machine 126 a) (fp : ℕ) (c : Configuration 126 a)
    (r : ExecutionReceipt 126 a) (hp : runFrom P fp c=some r) (W : Machine 5 sw) (fw d C L : ℕ)
    (out w : List Bool)
    (hW : ExtDecompositionBatch.Step W fw ![0,out.length,0,0,0]
      ![List.replicate d true,out,[],[],[]] ![0,(out++w).length,0,0,0]
      ![List.replicate d true,out++w,List.replicate (2*d+1) false,List.replicate (2*d) false,
        List.replicate d false])
    (h35 : r.final.tapes 35=ZeroPadding.pad L (List.replicate d true)) (hh35 : r.final.heads 35=0)
    (h110 : r.final.tapes 110=out) (hh110 : r.final.heads 110=out.length)
    (hx : ∀ i : Fin 3, r.final.tapes (writerSlots (i.natAdd 2))=List.replicate C false ∧
      r.final.heads (writerSlots (i.natAdd 2))=0) (hC : 2*d+1 ≤ C) :
    ∃ res : ExecutionReceipt 126 (a+sw),
      runFrom (Composition.machine P (RecoveryFocus.machine writerSlots W)) (fp+1+fw)
        (Composition.leftConfig sw c)=some res ∧
      res.final.tapes 110=out++w ∧ res.final.heads 110=(out++w).length ∧
      (∀ i : Fin 3, res.final.tapes (writerSlots (i.natAdd 2))=List.replicate C false ∧
        res.final.heads (writerSlots (i.natAdd 2))=0) ∧
      (∀ j, RecoveryFocus.pick writerSlots j=none →
        res.final.heads j=r.final.heads j ∧ res.final.tapes j=r.final.tapes j) ∧
      res.steps ≤ r.steps+1+fw := by
  obtain ⟨s,hs,sh,st,ss⟩ := hW
  have x0 := hx 0
  have x1 := hx 1
  have x2 := hx 2
  obtain ⟨res,hres,rh,rt,ro,rs⟩ := padStage P writerSlots writer_injective W fp fw c r hp
    ⟨W.start,![0,out.length,0,0,0],![List.replicate d true,out,[],[],[]]⟩ s hs rfl ![L,0,C,C,C]
    (by
      intro i
      fin_cases i
      · simpa [writerSlots] using hh35
      · simpa [writerSlots] using hh110
      · simpa [writerSlots] using x0.2
      · simpa [writerSlots] using x1.2
      · simpa [writerSlots] using x2.2)
    (by
      intro i
      fin_cases i
      · simpa [writerSlots] using h35
      · simpa [writerSlots] using h110
      · simpa [writerSlots,ZeroPadding.pad] using x0.1
      · simpa [writerSlots,ZeroPadding.pad] using x1.1
      · simpa [writerSlots,ZeroPadding.pad] using x2.1)
  refine ⟨res,hres,?_,?_,?_,ro,?_⟩
  · simpa [writerSlots,st] using rt 1
  · simpa [writerSlots,sh] using rh 1
  · intro i
    fin_cases i
    · refine ⟨?_,?_⟩
      · simpa [writerSlots,st,pad_replicate_false C (2*d+1) hC] using rt 2
      · simpa [writerSlots,sh] using rh 2
    · refine ⟨?_,?_⟩
      · simpa [writerSlots,st,pad_replicate_false C (2*d) (by omega)] using rt 3
      · simpa [writerSlots,sh] using rh 3
    · refine ⟨?_,?_⟩
      · simpa [writerSlots,st,pad_replicate_false C d (by omega)] using rt 4
      · simpa [writerSlots,sh] using rh 4
  · rw [rs]; omega

end NearCubicWires.RepairOrdinary.EquationRowPhiHeader
