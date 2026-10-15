import Proof.CaseAnalysis.WitnessFamilyBank
import Proof.CaseAnalysis.RowsCircuitCopy

/-! The paid coefficient-width and original family-frame copies use the
already allocated banks. Only their two destination tapes change; the
logical streams and the actual source policy are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyReload
open LocalBitMultitape RecoveryRootRound
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def widthSlots : Fin 4 → Fin 3243 := ![3241,149,720,721]
def rawSlots : Fin 4 → Fin 3243 := ![3242,3064,2530,2531]
def widthCopy:=RecoveryFocus.machine widthSlots RecoveryBoundedTapeCopy.machine
def rawCopy:=RecoveryFocus.machine rawSlots RecoveryBoundedTapeCopy.machine
def copies:=Composition.machine widthCopy rawCopy
def output (P H b : ℕ) (bits : List Bool) (base : Fin 3243 → List Bool):=
  Function.update (Function.update base 149 (ZeroPadding.pad P (List.replicate b true)))
    3064 (ZeroPadding.pad H (frame bits))
def copyBudget (P H : ℕ):=2*P+2*H+9

theorem copies_run (P H b : ℕ) (bits : List Bool) (heads : Fin 3243 → ℕ) (base : Fin 3243 → List Bool)
    (hb : b ≤ P) (hbits : 2*bits.length+1 ≤ H)
    (hw : ∀ i,heads (widthSlots i)=0) (hr : ∀ i,heads (rawSlots i)=0)
    (tw : ∀ i,base (widthSlots i)=CloseoutRowsMetadataCopy.input (List.replicate b true) P i)
    (tr : ∀ i,base (rawSlots i)=CloseoutRowsMetadataCopy.input (frame bits) H i) :
    ∃ r,runFrom copies (copyBudget P H) ⟨copies.start,heads,base⟩=some r ∧
      r.steps ≤ copyBudget P H ∧ r.final.heads=heads ∧ r.final.tapes=output P H b bits base:=by
  obtain ⟨a,ha,ah,atapes,as⟩:=CloseoutRowsCircuitCopy.copy_focus widthSlots (by decide) P
    (List.replicate b true) (by simpa using hb) heads base hw tw
  let middle:=Function.update base 149 (ZeroPadding.pad P (List.replicate b true))
  have nextInput (i : Fin 4):middle (rawSlots i)=CloseoutRowsMetadataCopy.input (frame bits) H i:=by
    have hn:rawSlots i≠149:=by fin_cases i <;> decide
    simpa only [middle,Function.update_of_ne hn] using tr i
  obtain ⟨c,hc,ch,ct,cs⟩:=CloseoutRowsCircuitCopy.copy_focus rawSlots (by decide) H
    (frame bits) (by simpa only [frame_length] using hbits) heads middle hr nextInput
  have next:runFrom rawCopy (2*H+4) ⟨rawCopy.start,a.final.heads,a.final.tapes⟩=some c:=by
    rw [ah,atapes];exact hc
  obtain ⟨r,run,rs,rh,rt⟩:=joined widthCopy rawCopy (2*P+4) (2*H+4) heads base a c ha next as.le cs.le
  have he:(2*P+4)+1+(2*H+4)=copyBudget P H:=by unfold copyBudget;omega
  rw [he] at run rs
  exact ⟨r,run,rs,rh.trans ch,rt.trans ct⟩

def prime : Machine 3243 2 where
  descriptionBits:=0
  start:=0
  halted:=fun state=>state.val==1
  rule:=fun state _=>if state.val=0 then
    some ⟨1,fun i=>if i=724 then some false else none,fun _=>.stay⟩ else none

theorem prime_run (heads : Fin 3243 → ℕ) (base : Fin 3243 → List Bool)
    (hh : heads 724=0) (ht : base 724=[]) :
    ∃ r,runFrom prime 1 ⟨0,heads,base⟩=some r ∧ r.steps=1 ∧
      r.final.heads=heads ∧ r.final.tapes=Function.update base 724 [false]:=by
  have hs:step prime ⟨0,heads,base⟩=
      some (⟨1,heads,Function.update base 724 [false]⟩ : Configuration 3243 2):=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi:i=724
      · subst i;simp [applyAction,hh,ht,writeTapeBit]
      · simp [applyAction,hi]
  obtain ⟨r,run,rf,rs⟩:=(RecoveryExecution.Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,run,rs,by rw [rf],by rw [rf]⟩

def machine:=Composition.machine copies prime
def budget (P H : ℕ):=copyBudget P H+2

theorem reload_run (P H b : ℕ) (bits : List Bool) (heads : Fin 3243 → ℕ) (base : Fin 3243 → List Bool)
    (hb : b ≤ P) (hbits : 2*bits.length+1 ≤ H)
    (hw : ∀ i,heads (widthSlots i)=0) (hr : ∀ i,heads (rawSlots i)=0)
    (tw : ∀ i,base (widthSlots i)=CloseoutRowsMetadataCopy.input (List.replicate b true) P i)
    (tr : ∀ i,base (rawSlots i)=CloseoutRowsMetadataCopy.input (frame bits) H i)
    (h724 : heads 724=0) (t724 : base 724=[]) :
    ∃ r,runFrom machine (budget P H) ⟨machine.start,heads,base⟩=some r ∧
      r.steps ≤ budget P H ∧ r.final.heads=heads ∧
      r.final.tapes=Function.update (output P H b bits base) 724 [false]:=by
  obtain ⟨a,ha,as,ah,atapes⟩:=copies_run P H b bits heads base hb hbits hw hr tw tr
  obtain ⟨c,hc,cs,ch,ct⟩:=prime_run heads (output P H b bits base) h724 (by
    simpa only [output,Function.update_of_ne (show (724 : Fin 3243)≠3064 by decide),
      Function.update_of_ne (show (724 : Fin 3243)≠149 by decide)] using t724)
  have next:runFrom prime 1 ⟨prime.start,a.final.heads,a.final.tapes⟩=some c:=by
    rw [ah,atapes];exact hc
  obtain ⟨r,run,rs,rh,rt⟩:=joined copies prime (copyBudget P H) 1 heads base a c ha next as cs.le
  have he:copyBudget P H+1+1=budget P H:=by unfold budget;omega
  rw [he] at run rs
  exact ⟨r,run,rs,rh.trans ch,rt.trans ct⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyReload
