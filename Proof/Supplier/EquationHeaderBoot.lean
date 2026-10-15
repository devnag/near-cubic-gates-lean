import Proof.Supplier.EquationHeaderRead

/-! Read the physical odd-coordinate flag and reset the three parsed count
drivers. The entry remains the original framed row word and blank scratch. -/
namespace NearCubicWires.RepairOrdinary.EquationHeaderBoot
open LocalBitMultitape RecoveryExecution
open RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boot : Machine 34 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ bs => some ⟨1,
    fun i => if i=33 then some (bs 1) else none,
    fun i => if i=1 then .right else if i=12 ∨ i=22 ∨ i=32 then .left else .stay⟩

def afterHeads (h : Fin 34 → ℕ) (i : Fin 34) :=
  if i=1 then h i+1 else if i=12 ∨ i=22 ∨ i=32 then h i-1 else h i
def afterTapes (h : Fin 34 → ℕ) (a : Fin 34 → List Bool) (i : Fin 34) :=
  if i=33 then writeTapeBit (a i) (h i) (readTapeBit (a 1) (h 1)) else a i

theorem boot_run (h : Fin 34 → ℕ) (a : Fin 34 → List Bool) :
    ∃ actual,runFrom boot 1 ⟨0,h,a⟩=some actual ∧
      actual.final.heads=afterHeads h ∧ actual.final.tapes=afterTapes h a ∧ actual.steps=1 := by
  let final : Configuration 34 2 := ⟨1,afterHeads h,afterTapes h a⟩
  have hs : step boot ⟨0,h,a⟩=some final := by
    simp only [step,boot]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      simp only [applyAction,afterHeads,final]
      split_ifs <;> rfl
    · funext i
      simp only [applyAction,afterTapes,final,Configuration.scanned]
      split_ifs <;> rfl
  obtain ⟨actual,ha,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨actual,ha,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,ht⟩

noncomputable def first := TapeEmbedding.machine 1 EquationHeaderRead.machine
noncomputable def machine := Composition.machine first boot
def input (d p g : ℕ) (odd : Bool) (suffix : List Bool) : Fin 34 → List Bool :=
  fun i => if i=0 then frame (EquationHeaderRead.word d p g (odd::suffix)) else []
def budget (d p g : ℕ) (odd : Bool) (suffix : List Bool) :=
  EquationHeaderRead.budget d p g (odd::suffix)+2

theorem headers_run (d p g : ℕ) (odd : Bool) (suffix : List Bool) : ∃ actual,
    run machine (budget d p g odd suffix) (input d p g odd suffix)=some actual ∧
    actual.final.tapes 0=frame (EquationHeaderRead.word d p g (odd::suffix)) ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 1=EquationHeaderRead.word d p g (odd::suffix) ∧
      actual.final.heads 1=(EquationHeaderRead.header d p g).length+1 ∧
    actual.final.tapes 12=UnaryTemplate.tape d ∧ actual.final.heads 12=0 ∧
    actual.final.tapes 22=UnaryTemplate.tape p ∧ actual.final.heads 22=0 ∧
    actual.final.tapes 32=UnaryTemplate.tape g ∧ actual.final.heads 32=0 ∧
    actual.final.tapes 33=[odd] ∧ actual.final.heads 33=0 ∧
    actual.steps ≤ budget d p g odd suffix := by
  obtain ⟨base,hb,bt0,bh0,bt1,bh1,bd,bdh,bp,bph,bg,bgh,bs⟩ :=
    EquationHeaderRead.headers_run d p g (odd::suffix)
  let prepared := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) base
  have he := TapeEmbedding.run_embed EquationHeaderRead.machine (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => []) _ _ base hb
  have oldT (i : Fin 33) : prepared.final.tapes (i.castAdd 1)=base.final.tapes i := by
    change (Fin.addCases (m := 33) (n := 1) (motive := fun _ => List Bool)
      base.final.tapes (fun _ => [])) (i.castAdd 1)=_
    rw [Fin.addCases_left]
  have oldH (i : Fin 33) : prepared.final.heads (i.castAdd 1)=base.final.heads i := by
    change (Fin.addCases (m := 33) (n := 1) (motive := fun _ => ℕ)
      base.final.heads (fun _ => 0)) (i.castAdd 1)=_
    rw [Fin.addCases_left]
  have freshT : prepared.final.tapes 33=[] := rfl
  have freshH : prepared.final.heads 33=0 := rfl
  obtain ⟨last,hl,lh,lt,ls⟩ := boot_run prepared.final.heads prepared.final.tapes
  have hj := Composition.run_join first boot _ _ _ prepared last he hl
  have hi : Composition.leftConfig 2 (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => [])
      (initialConfiguration EquationHeaderRead.machine (EquationHeaderRead.input d p g (odd::suffix))))=
      initialConfiguration machine (input d p g odd suffix) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hj
  have keepT (i : Fin 33) : last.final.tapes (i.castAdd 1)=base.final.tapes i := by
    rw [lt]
    have hn : i.castAdd 1 ≠ (33 : Fin 34) := by
      intro h
      have hv : i.val=33 := congrArg Fin.val h
      have hil := i.isLt
      omega
    simpa only [afterTapes,hn,ite_false] using oldT i
  have readOdd : readTapeBit (prepared.final.tapes 1) (prepared.final.heads 1)=odd := by
    have t : prepared.final.tapes 1=EquationHeaderRead.word d p g (odd::suffix) := (oldT 1).trans bt1
    have h : prepared.final.heads 1=(EquationHeaderRead.header d p g).length := (oldH 1).trans bh1
    rw [t,h]
    simp [EquationHeaderRead.word,readTapeBit]
  refine ⟨Composition.joinedReceipt prepared last,?_,keepT 0 |>.trans bt0,?_,keepT 1 |>.trans bt1,?_,
    keepT 12 |>.trans bd,?_,keepT 22 |>.trans bp,?_,keepT 32 |>.trans bg,?_,?_,?_,?_⟩
  · simpa only [budget,machine,run,Nat.add_assoc,Nat.reduceAdd] using hj
  · change last.final.heads 0=0
    rw [lh]
    change prepared.final.heads 0=0
    exact (oldH 0).trans bh0
  · change last.final.heads 1=_
    rw [lh]
    change prepared.final.heads 1+1=_
    exact congrArg (fun n : ℕ => n+1) ((oldH 1).trans bh1)
  · change last.final.heads 12=0
    rw [lh]
    change prepared.final.heads 12-1=0
    have h : prepared.final.heads 12=1 := (oldH 12).trans bdh
    omega
  · change last.final.heads 22=0
    rw [lh]
    change prepared.final.heads 22-1=0
    have h : prepared.final.heads 22=1 := (oldH 22).trans bph
    omega
  · change last.final.heads 32=0
    rw [lh]
    change prepared.final.heads 32-1=0
    have h : prepared.final.heads 32=1 := (oldH 32).trans bgh
    omega
  · change last.final.tapes 33=[odd]
    rw [lt]
    simp only [afterTapes,ite_true,freshT,freshH,readOdd]
    rfl
  · change last.final.heads 33=0
    rw [lh]
    change prepared.final.heads 33=0
    exact freshH
  · change base.steps+1+last.steps ≤ _
    rw [ls]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.EquationHeaderBoot
