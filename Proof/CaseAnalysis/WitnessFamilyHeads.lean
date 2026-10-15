import Proof.CaseAnalysis.WitnessFamilyInput

/-! The cold family entry has only the retained native-domain head at one.
All private work and all initially empty output streams start at zero. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyHeads
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads:=FamilyDock.heads (SumDock.heads [] [] [])

theorem shape (i : Fin 3241) : heads i=if i.val=2501 then 1 else 0:=by
  dsimp only [heads,FamilyDock.heads,FamilyDock.coreHeads,FamilyLoad.heads,SumDock.heads,
    SumDock.coreHeads,TermRound.heads,TermCommit.heads,TermMass.heads,TermRead.heads]
  refine Fin.addCases (m:=3064) (n:=177) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=3063) (n:=1) ?_ ?_ j
    · intro j
      refine Fin.addCases (m:=3061) (n:=2) ?_ ?_ j
      · intro j
        refine Fin.addCases (m:=2533) (n:=528) ?_ ?_ j
        · intro j
          refine Fin.addCases (m:=2532) (n:=1) ?_ ?_ j
          · intro j
            refine Fin.addCases (m:=827) (n:=1705) ?_ ?_ j
            · intro j
              have hn:j.val≠2501:=by omega
              simp only [Fin.val_castAdd,if_neg hn]
              refine Fin.addCases (m:=826) (n:=1) ?_ ?_ j
              · intro j
                refine Fin.addCases (m:=725) (n:=101) ?_ ?_ j
                · intro j
                  refine Fin.addCases (m:=720) (n:=5) ?_ ?_ j
                  · intro j;simp
                  · intro j;fin_cases j <;> rfl
                · intro j;simp
              · intro j;simp
            · intro j
              simp only [Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd]
              simp only [TermEnvironment.heads,List.length_nil,ite_self]
              split_ifs <;> omega
          · intro j
            have hn:2532+j.val≠2501:=by omega
            simp only [Fin.val_castAdd,Fin.val_natAdd,if_neg hn]
            simp
        · intro j
          have hn:2533+j.val≠2501:=by omega
          simp only [Fin.val_castAdd,Fin.val_natAdd,if_neg hn]
          simp only [Fin.addCases_left,Fin.addCases_right]
          refine Fin.addCases (m:=510) (n:=18) ?_ ?_ j
          · intro k;simp [SumCountStream.heads]
          · intro k;simp [SumCountStream.heads,SumCountStream.extraHeads]
      · intro j
        have hn:3061+j.val≠2501:=by omega
        simp only [Fin.val_castAdd,Fin.val_natAdd,if_neg hn]
        fin_cases j <;> rfl
    · intro j
      have hn:3063+j.val≠2501:=by omega
      simp only [Fin.val_castAdd,Fin.val_natAdd,if_neg hn]
      simp
  · intro j
    have hn:3064+j.val≠2501:=by omega
    simp only [Fin.val_natAdd,if_neg hn]
    simp

theorem private_heads (i : Fin 3241) (hi : FamilyBank.parser i=true ∨ FamilyBank.family i=true ∨
    i=720 ∨ i=721 ∨ i=2530 ∨ i=2531) : heads i=0:=by
  rw [shape]
  have hn:i.val≠2501:=by
    intro hv
    have he:i=2501:=Fin.ext hv
    subst i
    simp only [FamilyBank.parser,FamilyBank.family] at hi
    rcases hi with h|h|h|h|h|h <;> contradiction
  rw [if_neg hn]

end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyHeads
