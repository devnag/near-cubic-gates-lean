import Proof.Supplier.EquationRowAllocate
import Proof.Supplier.EquationRowPhiHeader
import Proof.Supplier.EquationIdentityColumns

namespace NearCubicWires.RepairOrdinary.EquationRowPrepare
open LocalBitMultitape RecoveryExecution RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 126) : Prop := i=34 ∨ i=38 ∨ i=40
instance (i : Fin 126) : Decidable (selected i) := inferInstanceAs (Decidable (i=34 ∨ i=38 ∨ i=40))
def boot : Machine 126 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun _ => none,fun i => if selected i then .right else .stay⟩
def afterHeads (h : Fin 126 → ℕ) (i : Fin 126) := if selected i then h i+1 else h i

theorem boot_run (h : Fin 126 → ℕ) (a : Fin 126 → List Bool) :
    ∃ actual,runFrom boot 1 ⟨0,h,a⟩=some actual ∧
      actual.final.heads=afterHeads h ∧ actual.final.tapes=a ∧ actual.steps=1 := by
  let final : Configuration 126 2 := ⟨1,afterHeads h,a⟩
  have hs : step boot ⟨0,h,a⟩=some final := by
    simp only [step,boot]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      simp only [applyAction,afterHeads,final]
      split_ifs <;> rfl
    · rfl
  obtain ⟨actual,ha,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨actual,ha,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,ht⟩

noncomputable def first := TapeEmbedding.machine 15 EquationHeaderCold.machine
noncomputable def allocated := Composition.machine first EquationRowAllocate.machine
noncomputable def booted := Composition.machine allocated boot
noncomputable def erased := Composition.machine booted EquationRowPhiHeader.erase
noncomputable def appended := Composition.machine erased EquationRowPhiHeader.append
noncomputable def machine := Composition.machine appended
  (RecoveryFocus.machine EquationRowPhiHeader.writerSlots EquationIdentityColumns.machine)
def input (d p g : ℕ) (odd : Bool) (suffix : List Bool) : Fin 126 → List Bool :=
  fun i => if i=0 then frame (EquationHeaderRead.word d p g (odd::suffix)) else []
def capacity (d p : ℕ) := 128*(2*d+1)*(p+1)
def bank (j : Fin 32) : Fin 126 := (EquationHeaderCold.bank j).castAdd 15
def bankHead (j : Fin 32) := if selected (bank j) then 1 else 0
def budget (d p g : ℕ) (odd : Bool) (suffix : List Bool) :=
  EquationHeaderCold.budget d p g odd suffix+2*capacity d p+7+
    (1+EquationRowPhiHeader.eraseBudget d p)+(1+EquationHeaderAppend.budget d)+
    (1+EquationIdentityColumns.budget d)
/-- The φ part of the output header for the identity instance. -/
def phiHeader (d : ℕ) : List Bool := natWord d++EquationIdentityColumns.word d
/-- Banks the cut loop reads, untouched by the φ header stages. -/
def retained (j : Fin 32) : Prop := j=3 ∨ j=4 ∨ j=8 ∨ j=10 ∨ j=30
instance (j : Fin 32) : Decidable (retained j) := inferInstanceAs (Decidable (j=3 ∨ j=4 ∨ j=8 ∨ j=10 ∨ j=30))

theorem prepare_run (d p g : ℕ) (odd : Bool) (suffix : List Bool) : ∃ actual,
    run machine (budget d p g odd suffix) (input d p g odd suffix)=some actual ∧
    actual.final.tapes 0=frame (EquationHeaderRead.word d p g (odd::suffix)) ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 1=EquationHeaderRead.word d p g (odd::suffix) ∧
      actual.final.heads 1=(EquationHeaderRead.header d p g).length+1 ∧
    actual.final.tapes 110=EquationHeaderRead.header d (p+1) (2*g)++phiHeader d ∧
      actual.final.heads 110=(EquationHeaderRead.header d (p+1) (2*g)++phiHeader d).length ∧
    (∀ j,retained j →
      actual.final.tapes (bank j)=EquationCountCapacity.data8 d p g odd j ∧ actual.final.heads (bank j)=bankHead j) ∧
    (∀ i : Fin 15,actual.final.tapes (i.natAdd 111)=EquationRowAllocate.extra (capacity d p) i ∧
      actual.final.heads (i.natAdd 111)=0) ∧ actual.steps ≤ budget d p g odd suffix := by
  obtain ⟨base,hb,bt0,bh0,bt1,bh1,btOut,bhOut,fields,b62,bh62,bs⟩ :=
    EquationHeaderCold.cold_counts d p g odd suffix
  let prepared := TapeEmbedding.receipt (fun _ : Fin 15 => 0) (fun _ : Fin 15 => []) base
  have he := TapeEmbedding.run_embed EquationHeaderCold.machine (fun _ : Fin 15 => 0)
    (fun _ : Fin 15 => []) _ _ base hb
  obtain ⟨alloc,ha,old,fresh,ast⟩ := EquationRowAllocate.allocate_run base.final (capacity d p)
    (by
      have h := (fields 30 (by decide) (by decide) (by decide)).1
      change base.final.tapes 60=List.replicate ((2*d+1)*(p+1)*128) true at h
      simpa only [capacity,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h)
    (fields 30 (by decide) (by decide) (by decide)).2
  have ha' : runFrom EquationRowAllocate.machine (2*capacity d p+4)
      (Composition.restart prepared.final EquationRowAllocate.machine.start)=some alloc := ha
  have hj := Composition.run_join first EquationRowAllocate.machine _ _ _ prepared alloc he ha'
  obtain ⟨last,hl,lh,lt,ls⟩ := boot_run alloc.final.heads alloc.final.tapes
  have hw := Composition.run_join allocated boot _ _ _ (Composition.joinedReceipt prepared alloc) last hj hl
  have hinB : Composition.leftConfig _ (Composition.leftConfig _
      (TapeEmbedding.config (fun _ : Fin 15 => 0) (fun _ : Fin 15 => [])
        (initialConfiguration EquationHeaderCold.machine (EquationHeaderCold.input d p g odd suffix))))=
      initialConfiguration booted (input d p g odd suffix) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hinB] at hw
  let B := Composition.joinedReceipt (Composition.joinedReceipt prepared alloc) last
  have keepT (i : Fin 111) : B.final.tapes (i.castAdd 15)=base.final.tapes i := by
    change last.final.tapes _=_
    rw [lt]
    exact (old i).1
  have keepH (i : Fin 111) : B.final.heads (i.castAdd 15)=
      if selected (i.castAdd 15) then base.final.heads i+1 else base.final.heads i := by
    change last.final.heads _=_
    rw [lh]
    simp only [afterHeads,(old i).2]
  have bankT (j : Fin 32) (h12 : j≠12) (h14 : j≠14) (h20 : j≠20) :
      B.final.tapes (bank j)=EquationCountCapacity.data8 d p g odd j :=
    (keepT (EquationHeaderCold.bank j)).trans (fields j h12 h14 h20).1
  have bankH (j : Fin 32) (h12 : j≠12) (h14 : j≠14) (h20 : j≠20) :
      B.final.heads (bank j)=bankHead j := by
    change B.final.heads ((EquationHeaderCold.bank j).castAdd 15)=_
    rw [keepH,(fields j h12 h14 h20).2]
    rfl
  have freshT (i : Fin 15) : B.final.tapes (i.natAdd 111)=EquationRowAllocate.extra (capacity d p) i := by
    change last.final.tapes (i.natAdd 111)=_
    rw [lt]
    exact (fresh i).1
  have freshH (i : Fin 15) : B.final.heads (i.natAdd 111)=0 := by
    change last.final.heads (i.natAdd 111)=0
    rw [lh]
    have hn : ¬selected (i.natAdd 111) := by
      intro h
      rcases h with h|h|h <;> have hv := congrArg Fin.val h <;> simp only [Fin.val_natAdd] at hv <;> norm_num at hv <;> omega
    simp only [afterHeads,hn,ite_false,(fresh i).2]
  -- stage 1: erase bank 24
  have c31 : (2*d+1)*(p+1)+1 ≤ (2*d+1)*(p+1)*(2*128+3)+2 := by nlinarith
  obtain ⟨E,hE,e54,eh54,_,_,e61,eh61,eo,es⟩ := EquationRowPhiHeader.erase_stage booted _ _ B hw d p
    ((2*d+1)*(p+1)*(2*128+3)+2) (bankT 24 (by decide) (by decide) (by decide))
    (bankT 26 (by decide) (by decide) (by decide)) (bankT 31 (by decide) (by decide) (by decide)) c31
    (bankH 24 (by decide) (by decide) (by decide)) (bankH 26 (by decide) (by decide) (by decide))
    (bankH 31 (by decide) (by decide) (by decide))
  have eT (i : Fin 126) (hi : RecoveryFocus.pick EquationRowPhiHeader.eraseSlots i=none) :
      E.final.tapes i=B.final.tapes i := (eo i hi).2
  have eH (i : Fin 126) (hi : RecoveryFocus.pick EquationRowPhiHeader.eraseSlots i=none) :
      E.final.heads i=B.final.heads i := (eo i hi).1
  -- stage 2: append natWord d
  have zero (j : Fin 32) (n : ℕ) (h12 : j≠12) (h14 : j≠14) (h20 : j≠20)
      (hv : EquationCountCapacity.data8 d p g odd j=List.replicate n false)
      (hi : RecoveryFocus.pick EquationRowPhiHeader.eraseSlots (bank j)=none) (hb : bankHead j=0) :
      E.final.tapes (bank j)=List.replicate (E.final.tapes (bank j)).length false ∧
        E.final.heads (bank j)=0 := by
    rw [eT _ hi,eH _ hi,bankT j h12 h14 h20,bankH j h12 h14 h20,hv,hb]
    exact ⟨by simp,rfl⟩
  have cellH (i : Fin 111) (hs : ¬selected (i.castAdd 15)) :
      B.final.heads (i.castAdd 15)=base.final.heads i := by
    rw [keepH]; simp only [hs,ite_false]
  obtain ⟨A,hA,a110,ah110,a35,ah35,ao,as⟩ := EquationRowPhiHeader.append_stage erased _ _ E hE d
    (EquationHeaderRead.header d (p+1) (2*g))
    (by rw [eT 62 (by decide)]; exact (keepT 62).trans b62)
    (by rw [eH 62 (by decide)]; exact (cellH 62 (by decide)).trans bh62)
    (by rw [eT 110 (by decide)]; exact (keepT 110).trans btOut)
    (by rw [eH 110 (by decide)]; exact (cellH 110 (by decide)).trans bhOut)
    (by
      intro i h0 h17
      fin_cases i
      all_goals first
        | (exfalso; revert h0; decide)
        | (exfalso; revert h17; decide)
        | skip
      · exact zero 5 _ (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      · exact zero 7 _ (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      · exact zero 9 _ (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      · exact zero 11 _ (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      · exact zero 13 _ (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      · exact zero 15 _ (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      · exact zero 16 1 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      · exact zero 17 1 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      · exact zero 19 _ (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      · exact zero 21 _ (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      · exact zero 23 _ (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      · change E.final.tapes 54=List.replicate (E.final.tapes 54).length false ∧ E.final.heads 54=0
        rw [e54]; exact ⟨by simp,eh54⟩
      · exact zero 25 _ (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      · exact zero 27 _ (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      · exact zero 29 _ (by decide) (by decide) (by decide) rfl (by decide) (by decide)
      · change E.final.tapes 61=List.replicate (E.final.tapes 61).length false ∧ E.final.heads 61=0
        rw [e61]; exact ⟨by simp,eh61⟩)
  have aT (i : Fin 126) (hi : RecoveryFocus.pick EquationRowPhiHeader.appendSlots i=none) :
      A.final.tapes i=E.final.tapes i := (ao i hi).2
  have aH (i : Fin 126) (hi : RecoveryFocus.pick EquationRowPhiHeader.appendSlots i=none) :
      A.final.heads i=E.final.heads i := (ao i hi).1
  -- stage 3: identity columns
  have hC : 2*d+1 ≤ capacity d p := by unfold capacity; nlinarith
  obtain ⟨W,hW,w110,wh110,wx,wo,ws⟩ := EquationRowPhiHeader.writer_stage appended _ _ A hA
    EquationIdentityColumns.machine (EquationIdentityColumns.budget d) d (capacity d p)
    (E.final.tapes 35).length (EquationHeaderRead.header d (p+1) (2*g)++natWord d)
    (EquationIdentityColumns.word d)
    (EquationIdentityColumns.write_run d (EquationHeaderRead.header d (p+1) (2*g)++natWord d))
    a35 ah35 a110 ah110
    (by
      intro i
      fin_cases i
      · change A.final.tapes 111=_ ∧ A.final.heads 111=0
        rw [aT 111 (by decide),eT 111 (by decide),aH 111 (by decide),eH 111 (by decide)]
        exact ⟨(freshT 0).trans (by simp [EquationRowAllocate.extra]),freshH 0⟩
      · change A.final.tapes 112=_ ∧ A.final.heads 112=0
        rw [aT 112 (by decide),eT 112 (by decide),aH 112 (by decide),eH 112 (by decide)]
        exact ⟨(freshT 1).trans (by simp [EquationRowAllocate.extra]),freshH 1⟩
      · change A.final.tapes 113=_ ∧ A.final.heads 113=0
        rw [aT 113 (by decide),eT 113 (by decide),aH 113 (by decide),eH 113 (by decide)]
        exact ⟨(freshT 2).trans (by simp [EquationRowAllocate.extra]),freshH 2⟩)
    hC
  have wT (i : Fin 126) (hw : RecoveryFocus.pick EquationRowPhiHeader.writerSlots i=none)
      (ha : RecoveryFocus.pick EquationRowPhiHeader.appendSlots i=none)
      (he : RecoveryFocus.pick EquationRowPhiHeader.eraseSlots i=none) :
      W.final.tapes i=B.final.tapes i := ((wo i hw).2.trans (aT i ha)).trans (eT i he)
  have wH (i : Fin 126) (hw : RecoveryFocus.pick EquationRowPhiHeader.writerSlots i=none)
      (ha : RecoveryFocus.pick EquationRowPhiHeader.appendSlots i=none)
      (he : RecoveryFocus.pick EquationRowPhiHeader.eraseSlots i=none) :
      W.final.heads i=B.final.heads i := ((wo i hw).1.trans (aH i ha)).trans (eH i he)
  refine ⟨W,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hn : (((EquationHeaderCold.budget d p g odd suffix+1+(2*capacity d p+4))+1+1)+1+
        EquationRowPhiHeader.eraseBudget d p)+1+EquationHeaderAppend.budget d+1+
        EquationIdentityColumns.budget d=budget d p g odd suffix := by unfold budget; omega
    rw [← hn]
    exact hW
  · rw [wT 0 (by decide) (by decide) (by decide)]; exact (keepT 0).trans bt0
  · rw [wH 0 (by decide) (by decide) (by decide)]
    exact (cellH 0 (by decide)).trans bh0
  · rw [wT 1 (by decide) (by decide) (by decide)]; exact (keepT 1).trans bt1
  · rw [wH 1 (by decide) (by decide) (by decide)]
    exact (cellH 1 (by decide)).trans bh1
  · rw [w110]; simp only [phiHeader,List.append_assoc]
  · rw [wh110]; simp only [phiHeader,List.append_assoc]
  · intro j hj
    have h12 : j≠12 := by rcases hj with h|h|h|h|h <;> subst h <;> decide
    have h14 : j≠14 := by rcases hj with h|h|h|h|h <;> subst h <;> decide
    have h20 : j≠20 := by rcases hj with h|h|h|h|h <;> subst h <;> decide
    have hw : RecoveryFocus.pick EquationRowPhiHeader.writerSlots (bank j)=none := by
      rcases hj with h|h|h|h|h <;> subst h <;> decide
    have ha : RecoveryFocus.pick EquationRowPhiHeader.appendSlots (bank j)=none := by
      rcases hj with h|h|h|h|h <;> subst h <;> decide
    have he : RecoveryFocus.pick EquationRowPhiHeader.eraseSlots (bank j)=none := by
      rcases hj with h|h|h|h|h <;> subst h <;> decide
    exact ⟨(wT _ hw ha he).trans (bankT j h12 h14 h20),(wH _ hw ha he).trans (bankH j h12 h14 h20)⟩
  · intro i
    fin_cases i
    · exact ⟨(wx 0).1.trans (by simp [EquationRowAllocate.extra]),(wx 0).2⟩
    · exact ⟨(wx 1).1.trans (by simp [EquationRowAllocate.extra]),(wx 1).2⟩
    · exact ⟨(wx 2).1.trans (by simp [EquationRowAllocate.extra]),(wx 2).2⟩
    · exact ⟨(wT _ (by decide) (by decide) (by decide)).trans (freshT _),
        (wH _ (by decide) (by decide) (by decide)).trans (freshH _)⟩
    · exact ⟨(wT _ (by decide) (by decide) (by decide)).trans (freshT _),
        (wH _ (by decide) (by decide) (by decide)).trans (freshH _)⟩
    · exact ⟨(wT _ (by decide) (by decide) (by decide)).trans (freshT _),
        (wH _ (by decide) (by decide) (by decide)).trans (freshH _)⟩
    · exact ⟨(wT _ (by decide) (by decide) (by decide)).trans (freshT _),
        (wH _ (by decide) (by decide) (by decide)).trans (freshH _)⟩
    · exact ⟨(wT _ (by decide) (by decide) (by decide)).trans (freshT _),
        (wH _ (by decide) (by decide) (by decide)).trans (freshH _)⟩
    · exact ⟨(wT _ (by decide) (by decide) (by decide)).trans (freshT _),
        (wH _ (by decide) (by decide) (by decide)).trans (freshH _)⟩
    · exact ⟨(wT _ (by decide) (by decide) (by decide)).trans (freshT _),
        (wH _ (by decide) (by decide) (by decide)).trans (freshH _)⟩
    · exact ⟨(wT _ (by decide) (by decide) (by decide)).trans (freshT _),
        (wH _ (by decide) (by decide) (by decide)).trans (freshH _)⟩
    · exact ⟨(wT _ (by decide) (by decide) (by decide)).trans (freshT _),
        (wH _ (by decide) (by decide) (by decide)).trans (freshH _)⟩
    · exact ⟨(wT _ (by decide) (by decide) (by decide)).trans (freshT _),
        (wH _ (by decide) (by decide) (by decide)).trans (freshH _)⟩
    · exact ⟨(wT _ (by decide) (by decide) (by decide)).trans (freshT _),
        (wH _ (by decide) (by decide) (by decide)).trans (freshH _)⟩
    · exact ⟨(wT _ (by decide) (by decide) (by decide)).trans (freshT _),
        (wH _ (by decide) (by decide) (by decide)).trans (freshH _)⟩
  · have hB : B.steps ≤ EquationHeaderCold.budget d p g odd suffix+1+(2*capacity d p+4)+1+1 := by
      change (base.steps+1+alloc.steps)+1+last.steps ≤ _
      rw [ast,ls]
      omega
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.EquationRowPrepare
