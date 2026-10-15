import Proof.PCP.PCPPNativeCanonicalStackPop

/-! Paid current-word restoration for the actual DFS return. The existing
pop machine writes over the previous same-width code, and its selected
rewind restores that code's head while retaining the stack's live boundary. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalStack
open LocalBitMultitape RecoveryExecution
open StablePartition.Workspace (overlay)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def popMachine := PCPStackReady.machine
def popInput (bits pre old : List Bool) (z R : ℕ) : Configuration 3 6 :=
  ⟨popMachine.start,![pre.length+(frame bits).length,0,0],
    ![pre++(frame bits).reverse++List.replicate z false,old,List.replicate R false]⟩

theorem pop_restore (bits pre old : List Bool) (z R : ℕ)
    (hb:old.length≤2*bits.length+1) (hR:2*bits.length+2≤R) :
    ∃ r,runFrom popMachine (4*bits.length+6) (popInput bits pre old z R)=some r ∧
      r.final.tapes=![pre++List.replicate (2*bits.length+1+z) false,frame bits,List.replicate R false] ∧
      r.final.heads=![pre.length,0,0] ∧ r.steps=4*bits.length+6 := by
  obtain ⟨raw,hr,hf,hs⟩:=pop_run old bits pre [] z
  have hb':overlay (frame bits) old=frame bits:=by
    have hlen:old.length≤(frame bits).length:=by simpa only [frame_length] using hb
    rw [overlay,List.drop_eq_nil_of_le hlen,List.append_nil]
  have hhead:∀ i,PCPStackReady.selected i=true → raw.final.heads i≤raw.steps:=by
    intro i hi
    have he:i=1:=by simpa [PCPStackReady.selected] using hi
    subst i
    rw [hf,hs]
    change (frame bits).length≤2*bits.length+2
    rw [frame_length]
    omega
  obtain ⟨base,hrun,hfinal,hsteps,_⟩:=MaskedReset.reset_run machine PCPStackReady.selected _ _ raw hr hhead
  have he:2*raw.steps+2=4*bits.length+6:=by omega
  rw [he] at hrun hsteps
  let caps:Fin 3→ℕ:=![0,0,R]
  obtain ⟨r,hp,hpf,hps,_⟩:=ZeroPadding.run_config popMachine caps _ _ base hrun
  have hi:ZeroPadding.config caps (Rewind.recording
      (cfg old 0 (pre++(frame bits).reverse++List.replicate z false) (pre.length+(frame bits).length) []) 0)=
      popInput bits pre old z R:=by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i
      · exact ZeroPadding.pad_zero _
      · change ZeroPadding.pad 0 (overlay [] old)=old
        simp only [overlay,List.length_nil,List.drop_zero,List.nil_append,ZeroPadding.pad_zero]
      · rfl
  rw [hi] at hp
  refine ⟨r,hp,?_,?_,hps.trans hsteps⟩
  · rw [hpf,hfinal,hf,hs]
    funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · change ZeroPadding.pad 0 (overlay ([]++frame bits) old)=frame bits
      rw [List.nil_append,hb',ZeroPadding.pad_zero]
    · change ZeroPadding.pad R (List.replicate (2*bits.length+2) false)=_
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega
  · rw [hpf,hfinal,hf]
    funext i
    fin_cases i <;> rfl

theorem pop_padded (bits pre old : List Bool) (C R : ℕ)
    (hb:old.length≤2*bits.length+1) (hC:pre.length+2*bits.length+1≤C) (hR:2*bits.length+2≤R) :
    ∃ r,runFrom popMachine (4*bits.length+6)
      ⟨popMachine.start,![pre.length+(frame bits).length,0,0],
        ![ZeroPadding.pad C (pre++(frame bits).reverse),old,List.replicate R false]⟩=some r ∧
      r.final.tapes=![ZeroPadding.pad C pre,frame bits,List.replicate R false] ∧
      r.final.heads=![pre.length,0,0] ∧ r.steps=4*bits.length+6 := by
  obtain ⟨r,hr,ht,hh,hs⟩:=pop_restore bits pre old (C-(pre.length+2*bits.length+1)) R hb hR
  have hi:popInput bits pre old (C-(pre.length+2*bits.length+1)) R=
      (⟨popMachine.start,![pre.length+(frame bits).length,0,0],
        ![ZeroPadding.pad C (pre++(frame bits).reverse),old,List.replicate R false]⟩ : Configuration 3 6):=by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i
      · simp only [popInput,ZeroPadding.pad,List.length_append,List.length_reverse,frame_length,List.append_assoc]
        congr 2
      · rfl
      · rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,hh,hs⟩
  rw [ht]
  funext i;fin_cases i
  · change pre++List.replicate (2*bits.length+1+(C-(pre.length+2*bits.length+1))) false=ZeroPadding.pad C pre
    unfold ZeroPadding.pad
    congr 2
    omega
  · rfl
  · rfl

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalStack
