import Proof.CaseAnalysis.RecoveryCountGrammarEntry
import Proof.CaseAnalysis.RecoveryGrammarScans

/-! One shared original count bank: rows0..115 and grammar's disjoint
extras116..151. The outer repeat adds its one driver on152. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountBank
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def grammarSlots : Fin 114→Fin 152:=Fin.addCases (m:=78) (n:=36)
  (fun j=>j.castAdd 74) (fun j=>j.natAdd 116)
def rowSlots (j : Fin 116) : Fin 152:=j.castAdd 36
def packetSources : Fin 10→Fin 152:=![137,122,135,139,141,142,133,119,127,143]
def packetSlots : Fin 88→Fin 152:=Fin.addCases (m:=78) (n:=10)
  (fun j=>j.castAdd 74) packetSources
def extras (B : ℕ) (cold : Fin 33→List Bool) (boundDriver candidateDriver : List Bool) : Fin 36→List Bool:=
  Fin.addCases (m:=1) (n:=35) (fun _=>List.replicate B false)
    (Fin.addCases (m:=33) (n:=2) cold ![boundDriver,candidateDriver])
def extraHeads (boundPos candidatePos : ℕ) : Fin 36→ℕ:=
  Fin.addCases (m:=1) (n:=35) (fun _=>0)
    (Fin.addCases (m:=33) (n:=2) (fun _=>0) ![boundPos,candidatePos])
def data (B P : ℕ) (A : Fin 78→List Bool) (proj : Fin 37→List Bool) (rowTotal : ℕ)
    (cold : Fin 33→List Bool) (boundDriver candidateDriver : List Bool) : Fin 152→List Bool:=
  Fin.addCases (m:=116) (n:=36) (RecoveryBoundedFixedRestart.data P A proj rowTotal)
    (extras B cold boundDriver candidateDriver)
def heads (out stack : List Bool) (boundPos candidatePos : ℕ) : Fin 152→ℕ:=
  Fin.addCases (m:=116) (n:=36) (RecoveryBoundedFixedRestart.nextHeads out stack)
    (extraHeads boundPos candidatePos)

theorem grammar_injective : Function.Injective grammarSlots := by
  intro i j he
  revert he
  refine Fin.addCases (m:=78) (n:=36) (fun a=>?_) (fun a=>?_) i <;>
    refine Fin.addCases (m:=78) (n:=36) (fun b=>?_) (fun b=>?_) j
  · intro he
    simp only [grammarSlots,Fin.addCases_left] at he
    exact congrArg (fun k : Fin 78=>k.castAdd 36) (Fin.ext (congrArg (fun k : Fin 152=>k.val) he))
  · intro he
    have hv:=congrArg Fin.val he
    simp only [grammarSlots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · intro he
    have hv:=congrArg Fin.val he
    simp only [grammarSlots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · intro he
    have hv:=congrArg Fin.val he
    simp only [grammarSlots,Fin.addCases_right,Fin.val_natAdd] at hv
    exact congrArg (fun k : Fin 36=>k.natAdd 78) (Fin.ext (by omega))

theorem row_injective : Function.Injective rowSlots := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 152=>k.val) he)

theorem packetSources_injective : Function.Injective packetSources:=by decide
theorem packetSources_high (j : Fin 10) : 116 ≤ (packetSources j).val := by
  fin_cases j <;> decide
theorem packet_injective : Function.Injective packetSlots := by
  intro i j he
  revert he
  refine Fin.addCases (m:=78) (n:=10) (fun a=>?_) (fun a=>?_) i <;>
    refine Fin.addCases (m:=78) (n:=10) (fun b=>?_) (fun b=>?_) j
  · intro he
    simp only [packetSlots,Fin.addCases_left] at he
    exact congrArg (fun k : Fin 78=>k.castAdd 10) (Fin.ext (congrArg (fun k : Fin 152=>k.val) he))
  · intro he
    have hv:=congrArg Fin.val he
    simp only [packetSlots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd] at hv
    have hb:=packetSources_high b
    omega
  · intro he
    have hv:=congrArg Fin.val he
    simp only [packetSlots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd] at hv
    have ha:=packetSources_high a
    omega
  · intro he
    simp only [packetSlots,Fin.addCases_right] at he
    exact congrArg (fun k : Fin 10=>k.natAdd 78) (packetSources_injective he)

theorem row_data (B P : ℕ) (A : Fin 78→List Bool) (proj : Fin 37→List Bool) (total : ℕ)
    (cold : Fin 33→List Bool) (bd cd : List Bool) (j : Fin 116) :
    data B P A proj total cold bd cd (rowSlots j)=RecoveryBoundedFixedRestart.data P A proj total j := by
  simp only [data,rowSlots,Fin.addCases_left]
theorem row_heads (out stack : List Bool) (bp cp : ℕ) (j : Fin 116) :
    heads out stack bp cp (rowSlots j)=RecoveryBoundedFixedRestart.nextHeads out stack j := by
  simp only [heads,rowSlots,Fin.addCases_left]

theorem grammar_data (fields : Fin 78→List Bool) (node B P bound count total : ℕ)
    (out stack packet source : List Bool) (proj : Fin 37→List Bool) (cold : Fin 33→List Bool) :
    (fun j=>data B P (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) proj total cold
      (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (bound+1)))
      (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+1))) (grammarSlots j))=
    RecoveryBoundedGrammarCold.scanData
      (RecoveryBoundedGrammarCold.data fields node B P out stack packet source cold) B bound count := by
  funext i
  fin_cases i <;> simp [grammarSlots,data,extras,RecoveryBoundedFixedRestart.data,
    RecoveryBoundedFixedContinue.data,RecoveryBoundedFixedContinue.padded,RecoveryBoundedFixedContinue.capacity,
    RecoveryBoundedGrammarCold.scanData,RecoveryBoundedGrammarDriver.data,RecoveryBoundedGrammarCold.data,
    RecoveryBoundedGrammarContinue.bank,RecoveryBoundedGrammarContinue.stackCapacity,
    RecoveryBoundedGrammarWorker.resultData,Fin.addCases]

theorem grammar_heads (out stack : List Bool) (bp cp : ℕ) :
    (fun j=>heads out stack bp cp (grammarSlots j))=
      RecoveryBoundedGrammarCold.scanHeads (RecoveryBoundedGrammarCold.heads out stack) bp cp := by
  funext i
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountBank
