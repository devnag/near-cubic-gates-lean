import Proof.PCP.PCPPNativeClauseDrivers

/-! Dock physical raw-count drivers into the original clause bank.
Every other clause scratch tape starts empty. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseDriverEntry
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 10→Fin 58 := ![52,21,49,54,53,55,56,51,28,57]
theorem slots_injective : Function.Injective slots := by decide
abbrev supplied (i : Fin 52) : Prop := i=21 ∨ i=49 ∨ i=51 ∨ i=28
noncomputable def target (source : List Bool) (pos stride p n C base accumulator : ℕ) (out : List Bool) (M : ℕ) :=
  PCPPNativeClauseCold.templateInput source pos stride p n C base accumulator out M
noncomputable def heads (source : List Bool) (pos stride p n C base accumulator : ℕ) (out : List Bool) (M : ℕ)
    (i : Fin 58) : ℕ :=
  if hi : i.val<52 then if i.val=51 then 0 else (target source pos stride p n C base accumulator out M).heads ⟨i.val,hi⟩ else 0
noncomputable def input (source : List Bool) (pos stride p n C base accumulator : ℕ) (out : List Bool) (M : ℕ)
    (i : Fin 58) : List Bool :=
  if hi : i.val<52 then if supplied ⟨i.val,hi⟩ then [] else (target source pos stride p n C base accumulator out M).tapes ⟨i.val,hi⟩
  else if i=52 then List.replicate C true else if i=53 then List.replicate M true else []
noncomputable def machine := RecoveryFocus.machine slots PCPPNativeClauseDrivers.machine
noncomputable def entry (source : List Bool) (pos stride p n C base accumulator : ℕ) (out : List Bool) (M : ℕ) :=
  (⟨machine.start,heads source pos stride p n C base accumulator out M,
    input source pos stride p n C base accumulator out M⟩ : Configuration 58 _)

theorem initial_fields (source : List Bool) (pos stride p n C base accumulator : ℕ) (out : List Bool) (M : ℕ)
    (j : Fin 10) :
    heads source pos stride p n C base accumulator out M (slots j)=0 ∧
    input source pos stride p n C base accumulator out M (slots j)=PCPPNativeClauseDrivers.input C M j := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

theorem initial_other (source : List Bool) (pos stride p n C base accumulator : ℕ) (out : List Bool) (M : ℕ)
    (i : Fin 52) (hi : ¬supplied i) :
    heads source pos stride p n C base accumulator out M (i.castAdd 6)=
      (target source pos stride p n C base accumulator out M).heads i ∧
    input source pos stride p n C base accumulator out M (i.castAdd 6)=
      (target source pos stride p n C base accumulator out M).tapes i := by
  have h51 : i.val≠51 := by intro h; exact hi (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  simp [heads,input,Fin.val_castAdd,i.isLt,h51,hi]

theorem slots_away (i : Fin 52) (hi : ¬supplied i) : ∀ j,slots j≠i.castAdd 6 := by
  have h21 : i≠21:=fun h=>hi (Or.inl h)
  have h49 : i≠49:=fun h=>hi (Or.inr (Or.inl h))
  have h51 : i≠51:=fun h=>hi (Or.inr (Or.inr (Or.inl h)))
  have h28 : i≠28:=fun h=>hi (Or.inr (Or.inr (Or.inr h)))
  have hil:=i.isLt
  intro j hj
  have hv:=congrArg Fin.val hj
  fin_cases j
  all_goals norm_num [slots] at hv
  all_goals omega

theorem prepare_run (source : List Bool) (pos stride p n C base accumulator : ℕ) (out : List Bool) (M : ℕ) :
    ∃ result,runFrom machine (PCPPNativeClauseDrivers.budget C M)
      (entry source pos stride p n C base accumulator out M)=some result ∧
      result.steps=PCPPNativeClauseDrivers.budget C M ∧
      ∀ i : Fin 52,result.final.heads (i.castAdd 6)=(target source pos stride p n C base accumulator out M).heads i ∧
        result.final.tapes (i.castAdd 6)=(target source pos stride p n C base accumulator out M).tapes i := by
  obtain ⟨a,ar,as,a1h,a1,a2h,a2,a7h,a7,a8h,a8⟩:=PCPPNativeClauseDrivers.drivers_run C M
  obtain ⟨b,br,_,bs,bh,bt,other⟩:=RecoveryFocus.dock slots slots_injective PCPPNativeClauseDrivers.machine _
    (heads source pos stride p n C base accumulator out M) (input source pos stride p n C base accumulator out M)
    (initialConfiguration PCPPNativeClauseDrivers.machine (PCPPNativeClauseDrivers.input C M))
    (fun j=>(initial_fields source pos stride p n C base accumulator out M j).1)
    (fun j=>(initial_fields source pos stride p n C base accumulator out M j).2) a ar
  refine ⟨b,br,bs.trans as,?_⟩
  intro i
  by_cases hi : supplied i
  · rcases hi with rfl|rfl|rfl|rfl
    · exact ⟨(bh 1).trans a1h,(bt 1).trans (a1.trans (by change List.replicate C true=ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C true)); simp))⟩
    · exact ⟨(bh 2).trans a2h,(bt 2).trans (a2.trans (by change List.replicate C true=ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C true)); simp))⟩
    · exact ⟨(bh 7).trans a7h,(bt 7).trans (a7.trans (PCPPNativeClauseCold.template_count source pos stride p n C base accumulator out M).symm)⟩
    · exact ⟨(bh 8).trans a8h,(bt 8).trans (a8.trans (ZeroPadding.pad_zero _).symm)⟩
  · have keep:=other (i.castAdd 6) (slots_away i hi)
    have original:=initial_other source pos stride p n C base accumulator out M i hi
    exact ⟨keep.1.trans original.1,keep.2.trans original.2⟩

end NearCubicWires.RepairOrdinary.PCPPNativeClauseDriverEntry
