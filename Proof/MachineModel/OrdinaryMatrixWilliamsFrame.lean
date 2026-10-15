import Proof.MachineModel.OrdinaryMatrixMarksAppend

/-! Serialize the actual header and two raw Boolean matrices into the one
canonical ordinary input frame, with retained physical length sentinels. -/
namespace NearCubicWires.RepairOrdinary.MatrixWilliamsFrame
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (header left right : List Bool) (n a b c : ℕ) (out : List Bool) : Configuration 6 s :=
  ⟨q,![1,a,1,b,c,out.length],![UnaryTemplate.tape header.length,header,UnaryTemplate.tape n,left,right,out]⟩
def input (header left right : List Bool) (n : ℕ) : Fin 6 → List Bool :=
  ![UnaryTemplate.tape header.length,header,UnaryTemplate.tape n,left,right,[]]
def boot : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,
    fun i => if i=0 ∨ i=2 then .right else .stay⟩ else none

theorem boot_run (header left right : List Bool) (n : ℕ) : ∃ actual,
    run boot 1 (input header left right n)=some actual ∧
    actual.final=cfg 1 header left right n 0 0 0 [] ∧ actual.steps=1 := by
  have hs : step boot (initialConfiguration boot (input header left right n))=
      some (cfg 1 header left right n 0 0 0 []) := by
    simp [step,boot,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem focus_append {s : ℕ} (slots : Fin 3 → Fin 6) (inj : Function.Injective slots)
    (c : Configuration 6 s) (bits out : List Bool)
    (hh : ∀ j,c.heads (slots j)=(![1,0,out.length] : Fin 3 → ℕ) j)
    (ht : ∀ j,c.tapes (slots j)=(![UnaryTemplate.tape bits.length,bits,out] : Fin 3 → List Bool) j) :
    ∃ actual,
      runFrom (RecoveryFocus.machine slots MatrixMarksAppend.machine) (3*bits.length+4)
        (Composition.restart c (RecoveryFocus.machine slots MatrixMarksAppend.machine).start)=some actual ∧
      actual.final=RecoveryFocus.config slots c.heads c.tapes
        (MatrixMarksAppend.cfg 5 bits.length 1 bits bits.length (out++marks bits)) ∧
      actual.steps=3*bits.length+4 := by
  obtain ⟨base,hb,bf,bs⟩ := MatrixMarksAppend.append_run bits [] [] out
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hb bf
  obtain ⟨actual,hr,rf,rs⟩ := RecoveryFocus.run_config slots inj MatrixMarksAppend.machine
    c.heads c.tapes _ _ base hb
  have hi : RecoveryFocus.config slots c.heads c.tapes
      (MatrixMarksAppend.cfg MatrixMarksAppend.machine.start bits.length 1 bits 0 out)=
      Composition.restart c (RecoveryFocus.machine slots MatrixMarksAppend.machine).start := by
    apply WilliamsSourceCrop.focus_same
    · intro j; exact hh j
    · intro j; exact ht j
  rw [hi] at hr
  exact ⟨actual,hr,by rw [rf,bf],rs.trans bs⟩

def headerSlots : Fin 3 → Fin 6 := ![0,1,5]
noncomputable def headerCall := RecoveryFocus.machine headerSlots MatrixMarksAppend.machine

theorem header_run (header left right : List Bool) (n : ℕ) : ∃ actual,
    runFrom headerCall (3*header.length+4) (cfg headerCall.start header left right n 0 0 0 ([]))=some actual ∧
    actual.final=cfg 5 header left right n header.length 0 0 (marks header) ∧ actual.steps=3*header.length+4 := by
  let entry := cfg headerCall.start header left right n 0 0 0 ([])
  obtain ⟨actual,hr,rf,rs⟩ := focus_append headerSlots (by decide) entry header ([])
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [entry,cfg,headerSlots])
  have pick (i : Fin 6) : RecoveryFocus.pick headerSlots i=
      (![some 0,some 1,none,none,none,some 2] : Fin 6 → Option (Fin 3)) i := by
    fin_cases i <;> first | decide | exact RecoveryFocus.pick_slot headerSlots (by decide) 0 | exact RecoveryFocus.pick_slot headerSlots (by decide) 1 | exact RecoveryFocus.pick_slot headerSlots (by decide) 2
  refine ⟨actual,hr,?_,rs⟩
  rw [rf]
  apply configuration_ext
  · rfl
  · funext i; simp only [RecoveryFocus.config,pick]
    fin_cases i <;> simp [entry,cfg,MatrixMarksAppend.cfg]
  · funext i; simp only [RecoveryFocus.config,pick]
    fin_cases i <;> simp [entry,cfg,MatrixMarksAppend.cfg]

def leftSlots : Fin 3 → Fin 6 := ![2,3,5]
noncomputable def leftCall := RecoveryFocus.machine leftSlots MatrixMarksAppend.machine

theorem left_run (header left right : List Bool) (n : ℕ) (hn : left.length=n) : ∃ actual,
    runFrom leftCall (3*left.length+4) (cfg leftCall.start header left right n header.length 0 0 (marks header))=some actual ∧
    actual.final=cfg 5 header left right n header.length left.length 0 (marks header++marks left) ∧ actual.steps=3*left.length+4 := by
  let entry := cfg leftCall.start header left right n header.length 0 0 (marks header)
  obtain ⟨actual,hr,rf,rs⟩ := focus_append leftSlots (by decide) entry left (marks header)
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [entry,cfg,leftSlots,hn])
  have pick (i : Fin 6) : RecoveryFocus.pick leftSlots i=
      (![none,none,some 0,some 1,none,some 2] : Fin 6 → Option (Fin 3)) i := by
    fin_cases i <;> first | decide | exact RecoveryFocus.pick_slot leftSlots (by decide) 0 | exact RecoveryFocus.pick_slot leftSlots (by decide) 1 | exact RecoveryFocus.pick_slot leftSlots (by decide) 2
  refine ⟨actual,hr,?_,rs⟩
  rw [rf]
  apply configuration_ext
  · rfl
  · funext i; simp only [RecoveryFocus.config,pick]
    fin_cases i <;> simp [entry,cfg,MatrixMarksAppend.cfg]
  · funext i; simp only [RecoveryFocus.config,pick]
    fin_cases i <;> simp [entry,cfg,MatrixMarksAppend.cfg,hn]

def rightSlots : Fin 3 → Fin 6 := ![2,4,5]
noncomputable def rightCall := RecoveryFocus.machine rightSlots MatrixMarksAppend.machine

theorem right_run (header left right : List Bool) (n : ℕ) (hn : right.length=n) : ∃ actual,
    runFrom rightCall (3*right.length+4) (cfg rightCall.start header left right n header.length left.length 0 (marks header++marks left))=some actual ∧
    actual.final=cfg 5 header left right n header.length left.length right.length (marks header++marks left++marks right) ∧ actual.steps=3*right.length+4 := by
  let entry := cfg rightCall.start header left right n header.length left.length 0 (marks header++marks left)
  obtain ⟨actual,hr,rf,rs⟩ := focus_append rightSlots (by decide) entry right (marks header++marks left)
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [entry,cfg,rightSlots,hn])
  have pick (i : Fin 6) : RecoveryFocus.pick rightSlots i=
      (![none,none,some 0,none,some 1,some 2] : Fin 6 → Option (Fin 3)) i := by
    fin_cases i <;> first | decide | exact RecoveryFocus.pick_slot rightSlots (by decide) 0 | exact RecoveryFocus.pick_slot rightSlots (by decide) 1 | exact RecoveryFocus.pick_slot rightSlots (by decide) 2
  refine ⟨actual,hr,?_,rs⟩
  rw [rf]
  apply configuration_ext
  · rfl
  · funext i; simp only [RecoveryFocus.config,pick]
    fin_cases i <;> simp [entry,cfg,MatrixMarksAppend.cfg,List.append_assoc]
  · funext i; simp only [RecoveryFocus.config,pick]
    fin_cases i <;> simp [entry,cfg,MatrixMarksAppend.cfg,List.append_assoc,hn]

def close : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun i => if i=5 then some false else none,
    fun i => if i=5 then .right else .stay⟩ else none

theorem close_step (header left right : List Bool) (n a b c : ℕ) (out : List Bool) :
    step close (cfg close.start header left right n a b c out)=
      some (cfg 1 header left right n a b c (out++[false])) := by
  simp [step,close,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem close_run (header left right : List Bool) (n : ℕ) : ∃ actual,
    runFrom close 1 (cfg close.start header left right n header.length left.length right.length
      (marks header++marks left++marks right))=some actual ∧
    actual.final=cfg 1 header left right n header.length left.length right.length (frame (header++left++right)) ∧
    actual.steps=1 := by
  have he : marks header++marks left++marks right++[false]=frame (header++left++right) := by
    rw [←marks_append,←marks_append]
    simpa only [List.append_nil,RepairOrdinary.frame] using (Streaming.frame_append (header++left++right) []).symm
  have hs := close_step header left right n header.length left.length right.length (marks header++marks left++marks right)
  rw [he] at hs
  exact (Timed.single (by rfl) hs).run (by rfl)

noncomputable def first := Composition.machine boot headerCall
noncomputable def second := Composition.machine first leftCall
noncomputable def third := Composition.machine second rightCall
noncomputable def raw := Composition.machine third close
noncomputable def machine := Rewind.machine raw

theorem raw_run (header left right : List Bool) (n : ℕ) (hl : left.length=n) (hr : right.length=n) :
    ∃ actual,run raw (3*header.length+6*n+18) (input header left right n)=some actual ∧
    actual.final.tapes=![UnaryTemplate.tape header.length,header,UnaryTemplate.tape n,left,right,frame (header++left++right)] ∧
    actual.steps=3*header.length+6*n+18 := by
  obtain ⟨a,ha,af,as⟩ := boot_run header left right n
  obtain ⟨b,hb,bf,bs⟩ := header_run header left right n
  have hi : cfg headerCall.start header left right n 0 0 0 []=Composition.restart a.final headerCall.start := by rw [af]; rfl
  rw [hi] at hb
  have h1 := Composition.run_join boot headerCall _ _ _ a b ha hb
  let ab := Composition.joinedReceipt a b
  obtain ⟨c,hc,cf,cs⟩ := left_run header left right n hl
  have hi2 : cfg leftCall.start header left right n header.length 0 0 (marks header)=Composition.restart ab.final leftCall.start := by
    change _=Composition.restart (Composition.rightConfig 2 b.final) _
    rw [bf]; rfl
  rw [hi2] at hc
  have h2 := Composition.run_join first leftCall _ _ _ ab c h1 hc
  let abc := Composition.joinedReceipt ab c
  obtain ⟨d,hd,df,ds⟩ := right_run header left right n hr
  have hi3 : cfg rightCall.start header left right n header.length left.length 0 (marks header++marks left)=Composition.restart abc.final rightCall.start := by
    change _=Composition.restart (Composition.rightConfig (2+6) c.final) _
    rw [cf]; rfl
  rw [hi3] at hd
  have h3 := Composition.run_join second rightCall _ _ _ abc d h2 hd
  let abcd := Composition.joinedReceipt abc d
  obtain ⟨e,he,ef,es⟩ := close_run header left right n
  have hi4 : cfg close.start header left right n header.length left.length right.length (marks header++marks left++marks right)=
      Composition.restart abcd.final close.start := by
    change _=Composition.restart (Composition.rightConfig (2+6+6) d.final) _
    rw [df]; rfl
  rw [hi4] at he
  have h4 := Composition.run_join third close _ _ _ abcd e h3 he
  have ht : (((1+1+(3*header.length+4))+1+(3*left.length+4))+1+(3*right.length+4))+1+1=3*header.length+6*n+18 := by omega
  rw [ht] at h4
  refine ⟨Composition.joinedReceipt abcd e,h4,?_,?_⟩
  · change e.final.tapes=_
    rw [ef]; rfl
  · change a.steps+1+b.steps+1+c.steps+1+d.steps+1+e.steps=_
    omega

def resetInput (header left right : List Bool) (n : ℕ) : Fin 7 → List Bool :=
  Fin.addCases (m := 6) (n := 1) (motive := fun _ => List Bool) (input header left right n) (fun _ => [])

theorem frame_run (header left right : List Bool) (n : ℕ) (hl : left.length=n) (hr : right.length=n) :
    ∃ actual,run machine (6*header.length+12*n+38) (resetInput header left right n)=some actual ∧
    (∀ i : Fin 6,actual.final.tapes (i.castAdd 1)=
      (![UnaryTemplate.tape header.length,header,UnaryTemplate.tape n,left,right,frame (header++left++right)] : Fin 6 → List Bool) i) ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps=6*header.length+12*n+38 := by
  obtain ⟨base,hb,bt,bs⟩ := raw_run header left right n hl hr
  obtain ⟨actual,ha,atapes,ah,as,_⟩ := Rewind.reset_run raw _ _ base hb
  have ht : 2*base.steps+2=6*header.length+12*n+38 := by omega
  rw [ht] at ha as
  exact ⟨actual,ha,fun i => (atapes i).trans (congrFun bt i),ah,as⟩

end NearCubicWires.RepairOrdinary.MatrixWilliamsFrame
