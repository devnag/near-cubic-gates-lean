import Proof.CaseAnalysis.WitnessSelectedErase
import Proof.CaseAnalysis.CloseoutWitnessFamilyRun

/-! The two existing erase drivers allocate the whole family's private
workspace once. The retained source policy, mass accumulator and logical
streams are outside both sweeps. Their capacities remain independent. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyBank
open LocalBitMultitape
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def parser (i : Fin 3241) : Bool:=decide
  ((i.val<724 ∧ i.val≠720 ∧ i.val≠721 ∧ i.val≠722) ∨ (819 ≤ i.val ∧ i.val<826))
def family (i : Fin 3241) : Bool:=decide (i.val=722 ∨
  (827 ≤ i.val ∧ i.val≠2501 ∧ i.val≠2515 ∧ i.val≠2525 ∧ i.val≠2526 ∧
    i.val≠2530 ∧ i.val≠2531 ∧ i.val≠3034 ∧ i.val≠3035 ∧ i.val≠3059 ∧ i.val≠3238))
def first:=SelectedErase.machine parser 720 721
def second:=SelectedErase.machine family 2530 2531
def machine:=Composition.machine first second
def output (P H : ℕ) (base : Fin 3241→List Bool):=
  SelectedErase.output family 2531 H (SelectedErase.output parser 721 P base)
def budget (P H : ℕ):=2*P+2*H+9

theorem disjoint (i : Fin 3241) (h : family i=true) : parser i=false:=by
  apply Bool.eq_false_iff.mpr
  intro hp
  simp only [parser,family,decide_eq_true_eq] at h hp
  omega

theorem bank_run (P H : ℕ) (heads : Fin 3241→ℕ) (base : Fin 3241→List Bool)
    (hh : ∀ i,parser i=true ∨ family i=true ∨ i=720 ∨ i=721 ∨ i=2530 ∨ i=2531 → heads i=0)
    (hp : ∀ i,parser i=true → base i=[]) (hf : ∀ i,family i=true → base i=[])
    (hpdriver : base 720=List.replicate P true) (hplog : base 721=[])
    (hfdriver : base 2530=List.replicate H true) (hflog : base 2531=[]) :
    ∃ r,runFrom machine (budget P H) ⟨machine.start,heads,base⟩=some r ∧
      r.steps≤budget P H ∧ r.final.heads=heads ∧ r.final.tapes=output P H base:=by
  obtain ⟨a,ha,as,ah,atapes⟩:=SelectedErase.erase_run parser 720 721 (by decide) (by decide) (by decide)
    P heads base (by
      intro i hi
      rcases hi with h|h|h
      · exact hh i (Or.inl h)
      · exact hh i (Or.inr (Or.inr (Or.inl h)))
      · exact hh i (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    (by intro i hi;rw [hp i hi];simp) hpdriver hplog
  let middle:=SelectedErase.output parser 721 P base
  have fresh (i : Fin 3241) (hi : family i=true):middle i=[]:=by
    have hn:i≠721:=by intro he;subst i;change false=true at hi;cases hi
    simp only [middle,SelectedErase.output,disjoint i hi,if_neg hn]
    exact hf i hi
  obtain ⟨b,hb,bs,bh,bt⟩:=SelectedErase.erase_run family 2530 2531 (by decide) (by decide) (by decide)
    H heads middle (by
      intro i hi
      rcases hi with h|h|h
      · exact hh i (Or.inr (Or.inl h))
      · exact hh i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact hh i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    (by intro i hi;rw [fresh i hi];simp)
    (by change (if false then _ else if (2530 : Fin 3241)=721 then _ else base 2530)=_;exact hfdriver)
    (by change (if false then _ else if (2531 : Fin 3241)=721 then _ else base 2531)=_;exact hflog)
  have next:runFrom second (2*H+4) ⟨second.start,a.final.heads,a.final.tapes⟩=some b:=by
    rw [ah,atapes];exact hb
  obtain ⟨r,run,rs,rh,rt⟩:=joined first second (2*P+4) (2*H+4) heads base a b ha next as bs
  have he:(2*P+4)+1+(2*H+4)=budget P H:=by unfold budget;omega
  rw [he] at run rs
  exact ⟨r,run,rs,rh.trans bh,rt.trans bt⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyBank
