import Proof.CaseAnalysis.RecoveryCountScalarDock

/-! The original row-packet printer reads the retained grammar scalars
directly. Its sole count update is also the next grammar candidate. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountPacketBank
open LocalBitMultitape RecoveryRootRound
open RecoveryBoundedCountBank
open RecoveryBoundedRowPacketAppend (values)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nextExtra (B count : ℕ) (extra : Fin 12→List Bool):=
  Function.update extra 1 (RecoveryBoundedGrammarScalarAdd.unary B (count+1))

theorem metadata_next (q bound row C B count : ℕ) (extra : Fin 12→List Bool) :
    RecoveryBoundedGrammarCold.metadata q bound row C B (nextExtra B count extra)=
      Function.update (RecoveryBoundedGrammarCold.metadata q bound row C B extra) 22
        (RecoveryBoundedGrammarScalarAdd.unary B (count+1)) := by
  funext i
  fin_cases i <;> simp [RecoveryBoundedGrammarCold.metadata,nextExtra,Function.update,Fin.addCases]

theorem projection (q bound C count Q clauses B P node total : ℕ) (fields : Fin 78→List Bool)
    (out stack packet source : List Bool) (proj : Fin 37→List Bool) (extra : Fin 12→List Bool)
    (bd cd : List Bool)
    (hcount : extra 1=RecoveryBoundedGrammarScalarAdd.unary B count)
    (hQ : extra 3=RecoveryBoundedGrammarScalarAdd.unary B Q)
    (hclauses : extra 4=RecoveryBoundedGrammarScalarAdd.unary B clauses)
    (hR : extra 5=RecoveryBoundedGrammarScalarAdd.unary B (q+1)) :
    (fun j=>data B P (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) proj total
      (RecoveryBoundedGrammarCold.metadata q bound 0 C B extra) bd cd (packetSlots j))=
    RecoveryBoundedCountPacketCanonical.padded B P
      (RecoveryBoundedGrammarBank.ready fields node B out stack packet source)
      (values C (OuterPCPRecovery.boundedCircuitFieldLimit q bound) q count Q clauses) := by
  funext i
  fin_cases i <;> simp [packetSlots,packetSources,data,extras,
    RecoveryBoundedFixedRestart.data,RecoveryBoundedFixedContinue.data,
    RecoveryBoundedFixedContinue.padded,RecoveryBoundedFixedContinue.capacity,
    RecoveryBoundedCountPacketCanonical.padded,RecoveryBoundedCountPacketCanonical.capacity,
    RecoveryBoundedCountPacketCanonical.data,RecoveryBoundedGrammarCold.metadata,
    RecoveryBoundedGrammarCold.numbers,RecoveryBoundedRowPacketAppend.values,
    RecoveryBoundedGrammarScalarAdd.unary,hcount,hQ,hclauses,hR,ZeroPadding.pad_zero,Fin.addCases]

theorem projection_heads (out stack : List Bool) (bp cp : ℕ) :
    (fun j=>heads out stack bp cp (packetSlots j))=RecoveryBoundedCountPacketCanonical.heads out stack := by
  funext i
  fin_cases i <;> rfl

theorem install_bank (B P total count : ℕ) (A nextA : Fin 78→List Bool) (proj : Fin 37→List Bool)
    (cold : Fin 33→List Bool) (bd cd : List Bool) (localNext : Fin 88→List Bool)
    (hn : ∀ j,data B P nextA proj total (Function.update cold 22 (RecoveryBoundedGrammarScalarAdd.unary B (count+1)))
      bd cd (packetSlots j)=localNext j) :
    install packetSlots (data B P A proj total cold bd cd) localNext=
      data B P nextA proj total (Function.update cold 22 (RecoveryBoundedGrammarScalarAdd.unary B (count+1))) bd cd := by
  apply HierarchyWidth.install_eq packetSlots packet_injective
  · exact hn
  · intro i
    refine Fin.addCases (m:=116) (n:=36) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=78) (n:=38) (fun k=>?_) (fun k=>?_) j
      · intro hi
        exact False.elim (hi (k.castAdd 10) (by
          simp only [packetSlots,Fin.addCases_left]
          apply Fin.ext;rfl))
      · intro _
        simp only [data,Fin.addCases_left,RecoveryBoundedFixedRestart.data,
          RecoveryBoundedFixedContinue.data,Fin.addCases_right]
    · refine Fin.addCases (m:=1) (n:=35) (fun k=>?_) (fun k=>?_) j
      · intro _
        simp only [data,extras,Fin.addCases_right,Fin.addCases_left]
      · refine Fin.addCases (m:=33) (n:=2) (fun k=>?_) (fun k=>?_) k
        · intro hi
          have hk : k≠22 := by
            intro he
            subst k
            exact hi 81 rfl
          simp only [data,extras,Fin.addCases_right,Fin.addCases_left,Function.update_of_ne hk]
        · intro _
          simp only [data,extras,Fin.addCases_right]

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountPacketBank
