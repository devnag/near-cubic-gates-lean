import Proof.CaseAnalysis.RecoveryGrammarScalarAdd

/-! Focus the paid scalar update on the existing grammar cold bank and
its already allocated scratch, rewind log and erase driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarAdvance
open LocalBitMultitape RecoveryRootRound
open private install_eq from Proof.Amplification.RecoveryRowLookupCell
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bank (B : ℕ) (cold : Fin 33→List Bool) : Fin 37→List Bool:=
  Fin.addCases (m:=33) (n:=4) (motive:=fun _ : Fin 37=>List Bool) cold ![List.replicate B false,List.replicate B false,List.replicate B true,List.replicate (B+1) false]
def slots (destination source : Fin 33) : Fin 6→Fin 37:=
  ![destination.castAdd 4,source.castAdd 4,33,34,35,36]

theorem injective (destination source : Fin 33) (hne : destination≠source) :
    Function.Injective (slots destination source) := by
  have hd:=destination.isLt
  have hs:=source.isLt
  have hn : destination.val≠source.val:=fun h=>hne (Fin.ext h)
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all [slots,Fin.ext_iff] <;> omega

noncomputable def add (destination source : Fin 33):=
  RecoveryFocus.machine (slots destination source) RecoveryBoundedGrammarScalarAdd.machine

theorem bank_update (B : ℕ) (cold : Fin 33→List Bool) (destination : Fin 33) (bits : List Bool) :
    Function.update (bank B cold) (destination.castAdd 4) bits=bank B (Function.update cold destination bits) := by
  funext i
  refine Fin.addCases (m:=33) (n:=4) (motive:=fun i=>
    Function.update (bank B cold) (destination.castAdd 4) bits i=bank B (Function.update cold destination bits) i)
    (fun j=>?_) (fun j=>?_) i
  · simp [bank,Function.update,Fin.ext_iff]
  · have he : j.natAdd 33≠destination.castAdd 4 := by
      intro h
      have hv:=congrArg Fin.val h
      have hd:=destination.isLt
      change 33+j.val=destination.val at hv
      omega
    rw [Function.update_of_ne he]
    simp only [bank,Fin.addCases_right]

theorem add_ready (destination source : Fin 33) (hne : destination≠source)
    (a b B : ℕ) (cold : Fin 33→List Bool)
    (ha : cold destination=RecoveryBoundedGrammarScalarAdd.unary B a)
    (hb : cold source=RecoveryBoundedGrammarScalarAdd.unary B b) (hB : a+b+2≤B) :
    ClockJoin.ReadyRun (add destination source) (RecoveryBoundedGrammarScalarAdd.budget a b B)
      (bank B cold) (bank B (Function.update cold destination (RecoveryBoundedGrammarScalarAdd.unary B (a+b)))) := by
  have hin : ∀ j,bank B cold (slots destination source j)=RecoveryBoundedGrammarScalarAdd.input a b B j := by
    intro j
    fin_cases j <;> simp [bank,slots,RecoveryBoundedGrammarScalarAdd.input,ha,hb,Fin.addCases]
  have run:=(RecoveryBoundedGrammarScalarAdd.ready a b B hB).focus
    (slots destination source) (injective destination source hne) (bank B cold) hin
  have hout : install (slots destination source) (bank B cold) (RecoveryBoundedGrammarScalarAdd.input (a+b) b B)=
      Function.update (bank B cold) (destination.castAdd 4) (RecoveryBoundedGrammarScalarAdd.unary B (a+b)) := by
    apply install_eq (slots destination source) (injective destination source hne)
    · intro j
      have h0 : destination.castAdd 4=slots destination source 0:=rfl
      rw [h0]
      by_cases hj : j=0
      · subst j
        rw [Function.update_self]
        rfl
      · rw [Function.update_of_ne ((injective destination source hne).ne hj)]
        have keep : RecoveryBoundedGrammarScalarAdd.input (a+b) b B j=
            RecoveryBoundedGrammarScalarAdd.input a b B j := by
          fin_cases j <;> simp_all [RecoveryBoundedGrammarScalarAdd.input]
        exact keep.trans (hin j).symm
    · intro i hi
      exact (Function.update_of_ne (Ne.symm (hi 0)) _ _).symm
  rw [hout,bank_update] at run
  exact run

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarAdvance
