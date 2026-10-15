import Proof.Hierarchy.CompetitorCrossRequestHeaders
import Proof.MachineModel.OrdinaryMatrixPacketDimensions

/-! Original framed Request to actual raw d,p,M=d+3 and unary U=2^d.
The copied p fields feed the exact width sum; the U template feeds U². -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossRequestDimensions
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (r : Request) : Fin 46 → List Bool := fun i => if i.val=0 then MatrixScoreBatch.physicalInput r else []
def headerSlots (i : Fin 24) : Fin 46 := i.castAdd 22
def dSlots : Fin 5 → Fin 46 := ![12,24,25,26,27]
def pSlots : Fin 5 → Fin 46 := ![22,28,29,30,31]
def powerSlots (i : Fin 15) : Fin 46 := if i.val=0 then 24 else ⟨i.val+31,by omega⟩
theorem header_injective : Function.Injective headerSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 46 => k.val) h)
theorem power_injective : Function.Injective powerSlots := by decide
noncomputable def headers := RecoveryFocus.machine headerSlots CompetitorCrossRequestHeaders.machine
noncomputable def dCopy := RecoveryFocus.machine dSlots MatrixTemplateCopy.resetMachine
noncomputable def pCopy := RecoveryFocus.machine pSlots MatrixTemplateCopy.resetMachine
noncomputable def power := RecoveryFocus.machine powerSlots CompetitorCrossRequestHeaders.powerMachine
noncomputable def machine := Composition.machine headers (Composition.machine dCopy (Composition.machine pCopy power))
def budget (r : Request) := CompetitorCrossRequestHeaders.budget r+1+
  ((4*r.d+12)+1+((4*r.p+12)+1+CompetitorCrossRequestHeaders.powerBudget r.d))

theorem dimensions_run (r : Request) : ∃ out,ClockJoin.ReadyRun machine (budget r) (input r) out ∧
    out 0=MatrixScoreBatch.physicalInput r ∧ out 24=List.replicate r.d true ∧
    out 28=List.replicate r.p true ∧ out 29=List.replicate r.p true ∧
    out 33=List.replicate (r.d+3) true ∧ out 44=UnaryTemplate.tape r.U := by
  obtain ⟨a,ha,ha0,ha12,ha22⟩ := CompetitorCrossRequestHeaders.headers_run r
  have hh := bounded_focus headerSlots header_injective _ _ _ ha (input r)
    (by intro i;fin_cases i <;> rfl)
  let atapes := install headerSlots (input r) a
  have fresh (i : Fin 46) (hi : 24 ≤ i.val) : atapes i=[] := by
    rw [show atapes i=install headerSlots (input r) a i from rfl]
    rw [install_other _ _ _ _ (by
      intro j hj
      have hv := congrArg Fin.val hj
      change j.val=i.val at hv
      omega)]
    simp [input,show i.val≠0 by omega]
  have hd := bounded_focus dSlots (by decide) _ _ _ (MatrixPacketDimensions.copy_ready r.d) atapes (by
    intro i
    fin_cases i
    · exact (install_slot headerSlots header_injective _ a 12).trans ha12
    all_goals exact fresh _ (by decide))
  let btapes := install dSlots atapes (MatrixPacketDimensions.copied r.d)
  have hp := bounded_focus pSlots (by decide) _ _ _ (MatrixPacketDimensions.copy_ready r.p) btapes (by
    intro i
    fin_cases i
    · exact (install_other dSlots _ _ _ (by decide)).trans
        ((install_slot headerSlots header_injective _ a 22).trans ha22)
    all_goals exact (install_other dSlots _ _ _ (by decide)).trans (fresh _ (by decide)))
  let ctapes := install pSlots btapes (MatrixPacketDimensions.copied r.p)
  obtain ⟨pow,hpow,p0,p2,p13⟩ := CompetitorCrossRequestHeaders.power_run r.d
  have hpower := bounded_focus powerSlots power_injective _ _ _ hpow ctapes (by
    intro i
    fin_cases i
    · exact (install_other pSlots _ _ _ (by decide)).trans (install_slot dSlots (by decide) _ _ 1)
    all_goals
      exact (install_other pSlots _ _ _ (by decide)).trans
        ((install_other dSlots _ _ _ (by decide)).trans (fresh _ (by decide))))
  let out := install powerSlots ctapes pow
  have htail := ClockJoin.join _ _ _ _ _ _ _ hp hpower
  have hrest := ClockJoin.join _ _ _ _ _ _ _ hd htail
  refine ⟨out,ClockJoin.join _ _ _ _ _ _ _ hh hrest,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other powerSlots _ _ _ (by decide)).trans
      ((install_other pSlots _ _ _ (by decide)).trans
        ((install_other dSlots _ _ _ (by decide)).trans ((install_slot headerSlots header_injective _ a 0).trans ha0)))
  · exact (install_slot powerSlots power_injective _ pow 0).trans p0
  · exact (install_other powerSlots _ _ _ (by decide)).trans (install_slot pSlots (by decide) _ _ 1)
  · exact (install_other powerSlots _ _ _ (by decide)).trans (install_slot pSlots (by decide) _ _ 2)
  · exact (install_slot powerSlots power_injective _ pow 2).trans p2
  · exact (install_slot powerSlots power_injective _ pow 13).trans p13

end NearCubicWires.RepairOrdinary.CompetitorCrossRequestDimensions
