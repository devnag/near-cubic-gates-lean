import Proof.CaseAnalysis.CommonProgramTwoAliases
import Proof.CaseAnalysis.CommonPortBankAt

/-! Match the five literal Case2 input words and empty work at its actual
shared-bank boundary. The sixth shared port is its initially empty result. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose CloseoutLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def twoInput (p : Parameters) (word description address : List Bool) (R B : ℕ) : Fin (tn p)→List Bool:=
  CloseoutCaseTwo.DirectInput.input (source p) (selectedPCPP p.sources) p.k p.D p.copies
    word description address R B

theorem two_local_first (p : Parameters) (j : Fin 5) :
    twoLocal p (j.castAdd 1)=CloseoutCaseTwo.DirectInput.ports
      (source p) (selectedPCPP p.sources) p.k p.D p.copies j:=Fin.addCases_left j

theorem two_input_fields (p : Parameters) (word description address : List Bool) (R B : ℕ) (j : Fin 5) :
    twoInput p word description address R B (twoLocal p (j.castAdd 1))=
      CloseoutCaseTwo.DirectInput.words word description address R B j:=by
  exact (congrArg (twoInput p word description address R B) (two_local_first p j)).trans
    (CloseoutCaseTwo.DirectInput.input_port (source p) (selectedPCPP p.sources) p.k p.D p.copies
      word description address R B j)

theorem two_input_empty (p : Parameters) (word description address : List Bool) (R B : ℕ)
    (i : Fin (tn p)) (hi : ∀ j,twoLocal p j≠i) : twoInput p word description address R B i=[]:=by
  have hb : 5 ≤ i.val:=by
    by_contra! hb
    exact hi ((⟨i.val,hb⟩ : Fin 5).castAdd 1)
      ((two_local_first p ⟨i.val,hb⟩).trans (Fin.ext rfl))
  exact CloseoutCaseTwo.DirectInput.input_empty (source p) (selectedPCPP p.sources) p.k p.D p.copies
    word description address R B i hb

theorem two_input_output (p : Parameters) (word description address : List Bool) (R B : ℕ) :
    twoInput p word description address R B (twoLocal p 5)=[]:=by
  apply CloseoutCaseTwo.DirectInput.input_empty (source p) (selectedPCPP p.sources) p.k p.D p.copies
  change 5 ≤ 140+CloseoutCaseTwo.Execution.foldTapes (source p) (selectedPCPP p.sources) p.k p.D p.copies
  omega

theorem two_entry (p : Parameters) (word description address : List Bool) (R B : ℕ)
    (A : Fin (tapes p)→List Bool)
    (fields : ∀ j,A (((twoShared p j).castAdd (tn p)).castAdd 2)=
      twoInput p word description address R B (twoLocal p j))
    (fresh : ∀ i : Fin (tn p),A ((i.natAdd (n3 p)).castAdd 2)=[]) (i : Fin (tn p)) :
    A (twoSlot p i)=twoInput p word description address R B i:=by
  exact CloseoutCommonPortBank.input_at (twoLocal p) (twoShared p)
    (fun z=>A (z.castAdd 2)) (twoInput p word description address R B) fields fresh
    (two_input_empty p word description address R B) i

theorem two_entry_heads (p : Parameters) (H : Fin (tapes p)→ℕ)
    (fields : ∀ j,H (((twoShared p j).castAdd (tn p)).castAdd 2)=0)
    (fresh : ∀ i : Fin (tn p),H ((i.natAdd (n3 p)).castAdd 2)=0) (i : Fin (tn p)) :
    H (twoSlot p i)=0:=by
  cases hp : RecoveryFocus.pick (twoLocal p) i with
  | none =>simp only [twoSlot,twoBank,CloseoutCommonPortBank.slot,hp,fresh]
  | some j =>simpa only [twoSlot,twoBank,CloseoutCommonPortBank.slot,hp] using fields j

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
