import Proof.MachineModel.OrdinarySourceSATLiftRequestPrint

namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.RequestMoves
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem focus_existing {t u s : ℕ} (slot : Fin t → Fin u)
    (heads : Fin u → ℕ) (data : Fin u → List Bool) (c : Configuration t s)
    (hh : ∀ i,heads (slot i)=c.heads i) (ht : ∀ i,data (slot i)=c.tapes i) :
    RecoveryFocus.config slot heads data c=⟨c.control,heads,data⟩ := by
  apply configuration_ext
  · rfl
  · funext i
    cases hp : RecoveryFocus.pick slot i with
    | none => simp [RecoveryFocus.config,hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slot hp
      simpa only [RecoveryFocus.config,hp] using (hh j).symm.trans (congrArg heads he)
  · exact install_existing slot data c.tapes ht

theorem focus_other {t u s : ℕ} (slot : Fin t → Fin u)
    (heads : Fin u → ℕ) (data : Fin u → List Bool) (c : Configuration t s)
    (i : Fin u) (hi : ∀ j,slot j≠i) :
    (RecoveryFocus.config slot heads data c).heads i=heads i ∧
      (RecoveryFocus.config slot heads data c).tapes i=data i := by
  classical
  have hp : RecoveryFocus.pick slot i=none := by
    unfold RecoveryFocus.pick
    exact dif_neg (by rintro ⟨j,hj⟩; exact hi j hj)
  simp [RecoveryFocus.config,hp]

theorem focused_run {t u s budget : ℕ} (slot : Fin t → Fin u) (inj : Function.Injective slot)
    (machine : Machine t s) (heads : Fin u → ℕ) (data : Fin u → List Bool)
    (source : Configuration t s) (base : ExecutionReceipt t s)
    (h : runFrom machine budget source=some base)
    (hh : ∀ i,heads (slot i)=source.heads i) (ht : ∀ i,data (slot i)=source.tapes i) :
    ∃ r,runFrom (RecoveryFocus.machine slot machine) budget ⟨source.control,heads,data⟩=some r ∧
      r.final=RecoveryFocus.config slot heads data base.final ∧ r.steps=base.steps := by
  obtain ⟨r,hr,hf,hs⟩ := RecoveryFocus.run_config slot inj machine heads data budget source base h
  rw [focus_existing slot heads data source hh ht] at hr
  exact ⟨r,hr,hf,hs⟩

theorem print_run {t : ℕ} (outSlot : Fin t) (bits out : List Bool)
    (heads : Fin t → ℕ) (data : Fin t → List Bool)
    (hh : heads outSlot=out.length) (ht : data outSlot=out) :
    ∃ r,runFrom (RecoveryFocus.machine (fun _ : Fin 1 => outSlot) (HierarchyFixedWord.raw bits))
      bits.length ⟨(HierarchyFixedWord.raw bits).start,heads,data⟩=some r ∧
      r.steps=bits.length ∧ r.final.heads outSlot=(out++bits).length ∧
      r.final.tapes outSlot=out++bits ∧
      ∀ i,i≠outSlot → r.final.heads i=heads i ∧ r.final.tapes i=data i := by
  obtain ⟨base,hb,hbh,hbt,hbs⟩ := RequestPrint.run bits out
  have inj : Function.Injective (fun _ : Fin 1 => outSlot) := fun _ _ _ => Subsingleton.elim _ _
  obtain ⟨r,hr,hf,hs⟩ := focused_run (fun _ : Fin 1 => outSlot) inj _ heads data _ base hb
    (fun _ => hh) (fun _ => ht)
  have hp : RecoveryFocus.pick (fun _ : Fin 1 => outSlot) outSlot=some 0 :=
    RecoveryFocus.pick_slot _ inj 0
  refine ⟨r,hr,hs.trans hbs,?_,?_,?_⟩
  · have h := congrFun hbh 0
    simpa only [hf,RecoveryFocus.config,hp] using h
  · have h := congrFun hbt 0
    simpa only [hf,RecoveryFocus.config,hp] using h
  · intro i hi
    rw [hf]
    exact focus_other _ heads data base.final i (fun _ => Ne.symm hi)

theorem scale_run {t : ℕ} (slot : Fin 2 → Fin t) (inj : Function.Injective slot)
    (k n : ℕ) (out : List Bool) (heads : Fin t → ℕ) (data : Fin t → List Bool)
    (hh : heads (slot 0)=0) (ho : heads (slot 1)=out.length)
    (ht : data (slot 0)=List.replicate n true) (hw : data (slot 1)=out) :
    ∃ r,runFrom (RecoveryFocus.machine slot (RequestScale.machine k)) ((k+2)*n+1)
      ⟨(RequestScale.machine k).start,heads,data⟩=some r ∧ r.steps=(k+2)*n+1 ∧
      r.final.heads (slot 0)=n ∧ r.final.tapes (slot 0)=List.replicate n true ∧
      r.final.heads (slot 1)=(out++List.replicate (k*n) true).length ∧
      r.final.tapes (slot 1)=out++List.replicate (k*n) true ∧
      ∀ i,(∀ j,slot j≠i) → r.final.heads i=heads i ∧ r.final.tapes i=data i := by
  obtain ⟨base,hb,hbf,hbs⟩ := RequestScale.run k n out
  obtain ⟨r,hr,hf,hs⟩ := focused_run slot inj _ heads data _ base hb
    (by intro i; fin_cases i <;> assumption) (by intro i; fin_cases i <;> assumption)
  refine ⟨r,hr,hs.trans hbs,?_,?_,?_,?_,?_⟩
  · simp only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot _ inj,hbf,RequestScale.cfg]
    rfl
  · simp only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot _ inj,hbf,RequestScale.cfg]
    rfl
  · simp only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot _ inj,hbf,RequestScale.cfg]
    rfl
  · simp only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot _ inj,hbf,RequestScale.cfg]
    rfl
  · intro i hi
    rw [hf]
    exact focus_other slot heads data base.final i hi

end NearCubicWires.RepairSource.OrdinarySourceSATLift.RequestMoves
