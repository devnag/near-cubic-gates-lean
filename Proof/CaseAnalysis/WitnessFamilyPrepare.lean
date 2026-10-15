import Proof.CaseAnalysis.WitnessFamilyReload

/-! Whole-family preparation: the two paid erase sweeps, both retained
field copies and the initial false verdict are one actual execution.
The incoming source policy, zero mass store and stream cursors survive. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyPrepare
open LocalBitMultitape RecoveryRootRound
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def bank:=TapeEmbedding.machine 2 FamilyBank.machine
def machine:=Composition.machine bank FamilyReload.machine
def heads (base : Fin 3241 → ℕ) : Fin 3243 → ℕ:=Fin.addCases (m:=3241) (n:=2) (motive:=fun _=>ℕ) base (fun _=>0)
def tapes (b : ℕ) (bits : List Bool) (base : Fin 3241 → List Bool) : Fin 3243 → List Bool:=
  Fin.addCases (m:=3241) (n:=2) (motive:=fun _=>List Bool) base ![List.replicate b true,frame bits]
def output (P H b : ℕ) (bits : List Bool) (base : Fin 3241 → List Bool):=
  Function.update (FamilyReload.output P H b bits (tapes b bits (FamilyBank.output P H base))) 724 [false]
def budget (P H : ℕ):=4*P+4*H+21

theorem prepare_run (P H b : ℕ) (bits : List Bool) (baseHeads : Fin 3241 → ℕ) (base : Fin 3241 → List Bool)
    (hb : b ≤ P) (hbits : 2*bits.length+1 ≤ H)
    (hh : ∀ i,FamilyBank.parser i=true ∨ FamilyBank.family i=true ∨
      i=720 ∨ i=721 ∨ i=2530 ∨ i=2531 → baseHeads i=0)
    (hp : ∀ i,FamilyBank.parser i=true → base i=[])
    (hf : ∀ i,FamilyBank.family i=true → base i=[])
    (hpdriver : base 720=List.replicate P true) (hplog : base 721=[])
    (hfdriver : base 2530=List.replicate H true) (hflog : base 2531=[])
    (h724 : baseHeads 724=0) (t724 : base 724=[]) :
    ∃ r,runFrom machine (budget P H) ⟨machine.start,heads baseHeads,tapes b bits base⟩=some r ∧
      r.steps ≤ budget P H ∧ r.final.heads=heads baseHeads ∧ r.final.tapes=output P H b bits base:=by
  obtain ⟨a,ha,as,ah,atapes⟩:=FamilyBank.bank_run P H baseHeads base hh hp hf hpdriver hplog hfdriver hflog
  have first:=TapeEmbedding.run_embed FamilyBank.machine (fun _ : Fin 2=>0)
    (![List.replicate b true,frame bits] : Fin 2→List Bool) _ _ a ha
  let old:=TapeEmbedding.receipt (fun _ : Fin 2=>0) (![List.replicate b true,frame bits] : Fin 2→List Bool) a
  have oldh:old.final.heads=heads baseHeads:=by
    change Fin.addCases (m:=3241) (n:=2) (motive:=fun _=>ℕ) a.final.heads (fun _ : Fin 2=>0)=_
    rw [ah];rfl
  have oldt:old.final.tapes=tapes b bits (FamilyBank.output P H base):=by
    change Fin.addCases (m:=3241) (n:=2) (motive:=fun _=>List Bool) a.final.tapes (![List.replicate b true,frame bits] : Fin 2→List Bool)=_
    rw [atapes];rfl
  let prepared:=tapes b bits (FamilyBank.output P H base)
  have widthHeads (i : Fin 4):heads baseHeads (FamilyReload.widthSlots i)=0:=by
    fin_cases i
    · rfl
    · exact hh 149 (Or.inl (by decide))
    · exact hh 720 (Or.inr (Or.inr (Or.inl rfl)))
    · exact hh 721 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have rawHeads (i : Fin 4):heads baseHeads (FamilyReload.rawSlots i)=0:=by
    fin_cases i
    · rfl
    · exact hh 3064 (Or.inr (Or.inl (by decide)))
    · exact hh 2530 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact hh 2531 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have widthTapes (i : Fin 4):prepared (FamilyReload.widthSlots i)=CloseoutRowsMetadataCopy.input (List.replicate b true) P i:=by
    fin_cases i
    · rfl
    · rfl
    · exact hpdriver
    · rfl
  have rawTapes (i : Fin 4):prepared (FamilyReload.rawSlots i)=CloseoutRowsMetadataCopy.input (frame bits) H i:=by
    fin_cases i
    · rfl
    · rfl
    · exact hfdriver
    · rfl
  obtain ⟨last,lastRun,ls,lh,lt⟩:=FamilyReload.reload_run P H b bits (heads baseHeads) prepared
    hb hbits widthHeads rawHeads widthTapes rawTapes h724 t724
  have next:runFrom FamilyReload.machine (FamilyReload.budget P H)
      ⟨FamilyReload.machine.start,old.final.heads,old.final.tapes⟩=some last:=by
    rw [oldh,oldt];exact lastRun
  obtain ⟨r,run,rs,rh,rt⟩:=joined bank FamilyReload.machine (FamilyBank.budget P H) (FamilyReload.budget P H)
    (heads baseHeads) (tapes b bits base) old last first next as ls
  have he:FamilyBank.budget P H+1+FamilyReload.budget P H=budget P H:=by
    unfold FamilyBank.budget FamilyReload.budget FamilyReload.copyBudget budget;omega
  rw [he] at run rs
  exact ⟨r,run,rs,rh.trans lh,rt.trans lt⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyPrepare
