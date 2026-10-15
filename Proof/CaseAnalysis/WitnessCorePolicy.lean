import Proof.CaseAnalysis.WitnessCoefficientPolicy
import Proof.CaseAnalysis.ScheduleCoreWidth
import Proof.PCP.PCPPNativeTemplateRaw
import Proof.PCP.PCPSerializerCapacityFocus

/-! One policy from the actual retained cache arity and actual clause-bit
count. The cache template stays at head one. Existing width arithmetic with
copies=1 supplies q0, then the exact coefficient-bit policy is produced once. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CorePolicy
open LocalBitMultitape RecoveryRootRound RepairSource
open CloseoutSchedule ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev W (D : ℕ):=Width.tapes D
def tapes (D : ℕ):=W D+26
def templateSlots (D : ℕ) (i : Fin 5) : Fin (tapes D):=⟨i.val,by dsimp [tapes,W,Width.tapes,Clause.tapes];omega⟩
def widthSlots (D : ℕ) (i : Fin (W D)) : Fin (tapes D):=
  ⟨if i.val=0 then 1 else 5+i.val,by dsimp only [tapes];split_ifs <;> omega⟩
def q0Slot (D : ℕ):=widthSlots D (Width.outputSlot D)
def clauseSlot (D : ℕ) : Fin (tapes D):=⟨5,by dsimp [tapes,W,Width.tapes,Clause.tapes];omega⟩
def policySlots (D : ℕ) (i : Fin 21) : Fin (tapes D):=
  if i.val=0 then q0Slot D else if i.val=16 then clauseSlot D
  else ⟨W D+5+i.val,by dsimp only [tapes];omega⟩
def capSlot (D : ℕ):=policySlots D 19
def heads (D : ℕ) (i : Fin (tapes D)) : ℕ:=if i.val=0 then 1 else 0
def input (D core cb : ℕ) (i : Fin (tapes D)) : List Bool:=
  if i.val=0 then UnaryTemplate.tape core else if i.val=5 then List.replicate cb true else []
def template (D : ℕ):=RecoveryFocus.machine (templateSlots D) PCPPNativeTemplateRaw.machine
def width (D : ℕ):=RecoveryFocus.machine (widthSlots D) (Width.machine D 1)
def policy (D copies : ℕ) (delta : ℚ):=RecoveryFocus.machine (policySlots D) (CoefficientBits.machine delta copies)
def first (D : ℕ):=Composition.machine (template D) (width D)
def machine (D copies : ℕ) (delta : ℚ):=Composition.machine (first D) (policy D copies delta)
def entry (D copies core cb : ℕ) (delta : ℚ):=
  (⟨(machine D copies delta).start,heads D,input D core cb⟩ : Configuration (tapes D) _)
def q0 (D core : ℕ):=core+CloseoutLanguage.clauseWidth D core+1
def budget (D copies core cb : ℕ) (delta : ℚ):=
  (4*core+16)+1+Width.budget D 1 core+1+CoefficientBits.budget delta copies (q0 D core) cb

theorem template_injective (D : ℕ) : Function.Injective (templateSlots D):=by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (tapes D)=>x.val) h)
theorem width_injective (D : ℕ) : Function.Injective (widthSlots D):=by
  intro i j h
  have hv:=congrArg Fin.val h
  dsimp only [widthSlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem q0_val (D : ℕ) : (q0Slot D).val=W D+3:=by
  simp [q0Slot,widthSlots,Width.outputSlot,Width.scaleSlots,W,Width.tapes,Clause.tapes]
  omega
theorem policy_val (D : ℕ) (i : Fin 21) : (policySlots D i).val=
    if i.val=0 then W D+3 else if i.val=16 then 5 else W D+5+i.val:=by
  unfold policySlots
  split_ifs
  · exact q0_val D
  all_goals rfl
theorem policy_injective (D : ℕ) : Function.Injective (policySlots D):=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [policy_val,policy_val] at hv
  have hW:36 ≤ W D:=by dsimp [W,Width.tapes,Clause.tapes];omega
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem template_outside (D : ℕ) (i : Fin (tapes D)) (hi : 5 ≤ i.val) :
    ∀ j,templateSlots D j≠i:=by
  intro j h
  have hv:=congrArg Fin.val h
  change j.val=i.val at hv
  omega
theorem width_outside (D : ℕ) (i : Fin (tapes D)) (hi : i.val=0 ∨ i.val=5 ∨ W D+5 ≤ i.val) :
    ∀ j,widthSlots D j≠i:=by
  intro j h
  have hv:=congrArg Fin.val h
  dsimp only [widthSlots] at hv
  split_ifs at hv <;> rcases hi with hi|hi|hi <;> omega
theorem policy_nonzero (D : ℕ) (i : Fin 21) : (policySlots D i).val≠0:=by
  rw [policy_val]
  split_ifs <;> omega

theorem policy_run (D copies core cb : ℕ) (delta : ℚ) (hD : 1 ≤ D) : ∃ result,
    runFrom (machine D copies delta) (budget D copies core cb delta) (entry D copies core cb delta)=some result ∧
      result.steps ≤ budget D copies core cb delta ∧ result.final.heads=heads D ∧
      result.final.tapes (templateSlots D 0)=UnaryTemplate.tape core ∧
      result.final.tapes (q0Slot D)=List.replicate (q0 D core) true ∧
      result.final.tapes (clauseSlot D)=List.replicate cb true ∧
      result.final.tapes (capSlot D)=List.replicate
        (natBitLength (CloseoutXor.cap delta (q0 D core) copies*max 1 (2*2^cb))) true:=by
  obtain ⟨t,ht,ts,t0,t1,_,_,th⟩:=PCPPNativeTemplateRaw.template_run core
  obtain ⟨f,hf,_,fs,fh,ft,fa⟩:=RecoveryFocus.dock (templateSlots D) (template_injective D)
    PCPPNativeTemplateRaw.machine _ (heads D) (input D core cb) (PCPPNativeTemplateRaw.entry core)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl) t ht
  have fheads:f.final.heads=heads D:=by
    funext i
    by_cases hi:i.val<5
    · let j : Fin 5:=⟨i.val,hi⟩
      have he:i=templateSlots D j:=Fin.ext rfl
      rw [he,fh,th]
      simp only [PCPPNativeTemplateRaw.heads,heads,templateSlots,Fin.ext_iff,Fin.val_zero]
      rfl
    · exact (fa i (template_outside D i (by omega))).1
  have fblank (i : Fin (tapes D)) (hi : 6 ≤ i.val) : f.final.tapes i=[]:=by
    rw [(fa i (template_outside D i (by omega))).2]
    simp only [input,if_neg (show i.val≠0 by omega),if_neg (show i.val≠5 by omega)]
  obtain ⟨wo,hw,wq⟩:=Width.width_run D 1 core hD
  have winput:∀ i,f.final.tapes (widthSlots D i)=Width.input D core i:=by
    intro i
    by_cases hi:i.val=0
    · have he:i=⟨0,by dsimp [W,Width.tapes,Clause.tapes];omega⟩:=Fin.ext hi
      rw [he]
      exact (ft 1).trans t1
    · rw [Width.input,if_neg hi]
      exact fblank _ (by simp [widthSlots,hi];omega)
  obtain ⟨w,wr,wh,wt,ws⟩:=hw.focus_at (widthSlots D) (width_injective D) (heads D) f.final.tapes winput
    (by intro i;unfold heads widthSlots;split_ifs <;> simp_all)
  have wjoined:runFrom (width D) (Width.budget D 1 core)
      (Composition.restart f.final (width D).start)=some w:=by
    change runFrom (width D) _ ⟨_,f.final.heads,f.final.tapes⟩=some w
    rw [fheads]
    exact wr
  have wq0:w.final.tapes (q0Slot D)=List.replicate (q0 D core) true:=by
    change w.final.tapes (widthSlots D (Width.outputSlot D))=_
    rw [wt,install_slot _ (width_injective D),wq]
    simp only [CloseoutLanguage.coreWidth,one_mul,q0]
  have wcb:w.final.tapes (clauseSlot D)=List.replicate cb true:=by
    rw [wt,install_other _ _ _ _ (width_outside D _ (Or.inr (Or.inl rfl))),
      (fa _ (template_outside D _ (by simp [clauseSlot]))).2]
    rfl
  have wblank (i : Fin (tapes D)) (hi : W D+5 ≤ i.val) : w.final.tapes i=[]:=by
    rw [wt,install_other _ _ _ _ (width_outside D i (Or.inr (Or.inr hi)))]
    apply fblank
    have hW:36 ≤ W D:=by dsimp [W,Width.tapes,Clause.tapes];omega
    omega
  obtain ⟨po,hp,pq,pc,pb⟩:=CoefficientBits.policy_run delta copies (q0 D core) cb
  have pinput:∀ i,w.final.tapes (policySlots D i)=CoefficientBits.input (q0 D core) cb i:=by
    intro i
    by_cases h0:i.val=0
    · simpa only [policySlots,if_pos h0,CoefficientBits.input] using wq0
    by_cases h16:i.val=16
    · simpa only [policySlots,if_neg h0,if_pos h16,CoefficientBits.input] using wcb
    rw [CoefficientBits.input,if_neg h0,if_neg h16]
    exact wblank _ (by rw [policy_val,if_neg h0,if_neg h16];omega)
  obtain ⟨p,pr,ph,pt,ps⟩:=hp.focus_at (policySlots D) (policy_injective D) (heads D) w.final.tapes pinput
    (by intro i;simp only [heads,if_neg (policy_nonzero D i)])
  have pjoined:runFrom (policy D copies delta) (CoefficientBits.budget delta copies (q0 D core) cb)
      (Composition.restart (Composition.joinedReceipt f w).final (policy D copies delta).start)=some p:=by
    change runFrom (policy D copies delta) _ ⟨_,w.final.heads,w.final.tapes⟩=some p
    rw [wh]
    exact pr
  have hfirst:=Composition.run_join (template D) (width D) _ _ _ f w hf wjoined
  have hall:=Composition.run_join (first D) (policy D copies delta) _ _ _
    (Composition.joinedReceipt f w) p hfirst pjoined
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt f w) p,hall,?_,ph,?_,?_,?_,?_⟩
  · change f.steps+1+w.steps+1+p.steps ≤ budget D copies core cb delta
    rw [fs,ts]
    unfold budget
    omega
  · change p.final.tapes (templateSlots D 0)=_
    rw [pt,install_other _ _ _ _ (by
      intro i hi;have hv:=congrArg Fin.val hi;exact policy_nonzero D i hv),wt,
      install_other _ _ _ _ (width_outside D _ (Or.inl rfl))]
    exact (ft 0).trans t0
  · change p.final.tapes (policySlots D 0)=_
    rw [pt,install_slot _ (policy_injective D)]
    exact pq
  · change p.final.tapes (policySlots D 16)=_
    rw [pt,install_slot _ (policy_injective D)]
    exact pc
  · change p.final.tapes (policySlots D 19)=_
    rw [pt,install_slot _ (policy_injective D)]
    exact pb

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.CorePolicy
