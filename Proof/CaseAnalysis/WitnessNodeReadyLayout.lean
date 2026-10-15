import Proof.CaseAnalysis.WitnessNodeBody
import Proof.MachineModel.OrdinaryMaskedReset
import Proof.PCP.PCPSerializerTapeSupport

/-! One recorded reset surrounds the complete node body. Its descriptor
cursor remains live; every local head resets. The fixed polynomial capacity
also bounds every local tape, including arbitrary rejected node codes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeReady
open LocalBitMultitape RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 748) : Bool:=decide (i≠747)
def pads (cap : ℕ) (i : Fin 748) : ℕ:=if i=747 then 0 else cap
noncomputable def machine:=MaskedReset.machine NodeBody.machine selected
def capacity (w : ℕ):=113000000000000000000*w^24
def budget (w : ℕ) (bits : List Bool):=2*NodeBody.budget w bits+2
noncomputable def entry (cap w : ℕ) (left right bits out : List Bool):=
  ZeroPadding.config (Rewind.Workspace.capacities 748 cap)
    (Rewind.recording (ZeroPadding.config (pads cap) (NodeBody.entry w left right bits [] out)) 0)

theorem budget_bound (w : ℕ) (bits : List Bool) (hw : bits.length+1 ≤ w) :
    budget w bits ≤ capacity w:=by
  have hp: (bits.length+1)^24 ≤ w^24:=Nat.pow_le_pow_left hw 24
  have hself:w ≤ w^24:=Nat.le_self_pow (by decide) _
  unfold budget NodeBody.budget NodeGuard.budget NodeFields.budget capacity
  omega

theorem input_length (w : ℕ) (left right bits out : List Bool)
    (hl : left.length=w) (hr : right.length=w) (hw : bits.length+1 ≤ w)
    (i : Fin 748) (hi : i≠747) :
    ((NodeBody.entry w left right bits [] out).tapes i).length ≤ 2*w+3:=by
  have fields (j : Fin 668) : (NodeFields.input bits j).length ≤ 2*w+3:=by
    refine Fin.addCases (m:=122) (n:=546) ?_ ?_ j
    · intro k
      simp only [NodeFields.input,Fin.addCases_left,CompetitorWitnessTriple.input]
      split_ifs <;> simp only [frame_length,List.length_nil] <;> omega
    · intro k
      simp only [NodeFields.input,Fin.addCases_right,List.length_nil]
      omega
  have guard (j : Fin 746) : (NodeGuard.input w left right bits j).length ≤ 2*w+3:=by
    refine Fin.addCases (m:=668) (n:=78) ?_ ?_ j
    · intro a
      simpa only [NodeGuard.input,NodeGuard.base,Fin.addCases_left] using fields a
    · intro k
      refine Fin.addCases (m:=4) (n:=74) ?_ ?_ k
      · intro a
        simp only [NodeGuard.input,NodeGuard.base,Fin.addCases_right,Fin.addCases_left]
        fin_cases a <;> simp [NodeGuard.shared,hl,hr]
        omega
      · intro a
        simp only [NodeGuard.input,NodeGuard.base,Fin.addCases_right,List.length_nil]
        omega
  revert hi
  refine Fin.addCases (m:=746) (n:=2) ?_ ?_ i
  · intro j _
    simpa only [NodeBody.entry,Composition.leftConfig,TapeEmbedding.config,Fin.addCases_left,
      initialConfiguration] using guard j
  · intro j hi
    fin_cases j
    · change ([] : List Bool).length ≤ _
      simp
    · exact False.elim (hi rfl)

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeReady
