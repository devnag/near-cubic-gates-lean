import Proof.CaseAnalysis.RowsRawLoad

/-! One reused packet field load in the ambient bank. The packet cursor
advances, and the native target and shared log return to their original heads. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPacketField
open LocalBitMultitape RecoveryExecution RecoveryRootRound CloseoutRowsRawLoad
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (source : List Bool) (pos C D : ℕ) : Configuration 3 4 :=
  ⟨0,![pos,0,0],![source,List.replicate C false,List.replicate D false]⟩
def output (source bits : List Bool) (pos C D : ℕ) : Configuration 3 4 :=
  ⟨3,![pos,0,0],![source,ZeroPadding.pad C bits,List.replicate D false]⟩

theorem padded_run (pre bits tail : List Bool) (C D : ℕ) (hD : bits.length ≤ D) :
    ∃ r,runFrom CloseoutRowsRawLoad.machine (3*bits.length+2)
      (input (pre++frame bits++tail) pre.length C D)=some r ∧
      r.final=output (pre++frame bits++tail) bits (pre.length+2*bits.length+1) C D ∧
      r.steps=3*bits.length+2 := by
  obtain ⟨base,hb,bf,bs⟩ := field_run pre bits tail
  obtain ⟨r,hr,rf,rs,_⟩ := ZeroPadding.run_config CloseoutRowsRawLoad.machine
    (![0,C,D] : Fin 3→ℕ) _ _ base hb
  have hi : ZeroPadding.config (![0,C,D] : Fin 3→ℕ)
      (scan 0 (pre++frame bits++tail) pre.length [])=input (pre++frame bits++tail) pre.length C D := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,scan,input,ZeroPadding.pad]
  rw [hi] at hr
  refine ⟨r,hr,?_,rs.trans bs⟩
  rw [rf,bf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [ZeroPadding.config,reset,output,ZeroPadding.pad,
      Nat.add_sub_of_le hD]

noncomputable def program {t : ℕ} (source target log : Fin t) :=
  RecoveryFocus.machine ![source,target,log] CloseoutRowsRawLoad.machine

theorem field_load {t : ℕ} (source target log : Fin t)
    (hst : source≠target) (hsl : source≠log) (htl : target≠log)
    (pre bits tail : List Bool) (C D : ℕ) (hD : bits.length ≤ D)
    (heads : Fin t→ℕ) (data : Fin t→List Bool)
    (hs : heads source=pre.length) (ht : heads target=0) (hl : heads log=0)
    (ds : data source=pre++frame bits++tail) (dt : data target=List.replicate C false)
    (dl : data log=List.replicate D false) :
    ∃ r,runFrom (program source target log) (3*bits.length+2)
      ⟨(program source target log).start,heads,data⟩=some r ∧
      r.final.heads=Function.update heads source (pre.length+2*bits.length+1) ∧
      r.final.tapes=Function.update data target (ZeroPadding.pad C bits) ∧
      r.steps=3*bits.length+2 := by
  have hinj : Function.Injective (![source,target,log] : Fin 3→Fin t) := by
    intro i j he; fin_cases i <;> fin_cases j <;> simp_all
  have hpS : RecoveryFocus.pick ![source,target,log] source=some 0 := RecoveryFocus.pick_slot _ hinj 0
  have hpT : RecoveryFocus.pick ![source,target,log] target=some 1 := RecoveryFocus.pick_slot _ hinj 1
  have hpL : RecoveryFocus.pick ![source,target,log] log=some 2 := RecoveryFocus.pick_slot _ hinj 2
  obtain ⟨base,hb,bf,bs⟩ := padded_run pre bits tail C D hD
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config ![source,target,log] hinj CloseoutRowsRawLoad.machine heads data _ _ base hb
  have hi : RecoveryFocus.config ![source,target,log] heads data
      (input (pre++frame bits++tail) pre.length C D)=⟨0,heads,data⟩ := by
    apply WilliamsSourceCrop.focus_same ![source,target,log] (⟨0,heads,data⟩ : Configuration t 4)
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [rf,bf]
    funext i
    by_cases hi : i=source
    · subst i
      simp [RecoveryFocus.config,hpS,output]
    · by_cases ht' : i=target
      · subst i
        simp [RecoveryFocus.config,hpT,output,hi,ht]
      · by_cases hl' : i=log
        · subst i
          simp [RecoveryFocus.config,hpL,output,hi,hl]
        · have hp : RecoveryFocus.pick ![source,target,log] i=none := by
            unfold RecoveryFocus.pick
            exact dif_neg (by rintro ⟨j,hj⟩; fin_cases j <;> simp_all)
          simp [RecoveryFocus.config,hp,hi]
  · rw [rf,bf]
    funext i
    by_cases hi : i=target
    · subst i
      simp [RecoveryFocus.config,hpT,output]
    · by_cases hs' : i=source
      · subst i
        simp [RecoveryFocus.config,hpS,output,hi,ds]
      · by_cases hl' : i=log
        · subst i
          simp [RecoveryFocus.config,hpL,output,hi,dl]
        · have hp : RecoveryFocus.pick ![source,target,log] i=none := by
            unfold RecoveryFocus.pick
            exact dif_neg (by rintro ⟨j,hj⟩; fin_cases j <;> simp_all)
          simp [RecoveryFocus.config,hp,hi]

end NearCubicWires.RepairOrdinary.CloseoutRowsPacketField
