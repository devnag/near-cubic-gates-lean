import Proof.CaseAnalysis.CommonProgramSource

/-! The physical finite-search sentinel is zero. A positive common onset
therefore agrees exactly with the language's active/inactive definition. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces CloseoutLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def index (p : Parameters) (n : ℕ):=selectedIndex (widthAt p.sources p.k p.clock p.copies p.D) n
def length (p : Parameters) (n : ℕ):=CloseoutSchedule.Framed.selectedLength
  (widthAt p.sources p.k p.clock p.copies p.D) n
def selectedWord (p : Parameters) (M : OrdinaryWeakMachine) (n : ℕ):=
  (p.sources.hierarchy (fun n=>n^(p.k+2)) p.clock).output M (2^index p n)
def target (p : Parameters) (M : OrdinaryWeakMachine):=
  language p.sources p.k p.clock M p.degree p.copies p.D p.onset

theorem active_iff (p : Parameters) (n : ℕ) (honset : 1 ≤ p.onset) :
    p.onset ≤ length p n ↔ 1 ≤ index p n ∧ p.onset ≤ 2^index p n:=by
  change (p.onset ≤ if index p n=0 then 0 else 2^index p n) ↔ _
  by_cases hz:index p n=0
  · rw [if_pos hz,hz]
    omega
  · rw [if_neg hz]
    omega

theorem active_length (p : Parameters) (n : ℕ) (honset : 1 ≤ p.onset)
    (live : p.onset ≤ length p n) : length p n=2^index p n:=by
  have hs:=((active_iff p n honset).mp live).1
  have hz : index p n≠0:=by omega
  exact if_neg hz

theorem inactive_target (p : Parameters) (M : OrdinaryWeakMachine) (n : ℕ) (x : BitInput n)
    (honset : 1 ≤ p.onset) (inactive : ¬p.onset ≤ length p n) : target p M n x=false:=
  if_neg (fun h=>inactive ((active_iff p n honset).mpr h))

theorem active_target (p : Parameters) (M : OrdinaryWeakMachine) (n : ℕ) (x : BitInput n)
    (honset : 1 ≤ p.onset) (live : p.onset ≤ length p n) : target p M n x=
      core (globalPCP p) (selectedPCPP p.sources) (selectedAmplifier p.sources.amplification p.degree)
        (selectedWord p M n) p.copies (clauseWidth p.D (R p ⟨2^index p n,selectedWord p M n⟩)) n x:=
  if_pos ((active_iff p n honset).mp live)

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
