import Proof.CaseAnalysis.CaseTwoXorStep

/-! A restored physical block contributes its returned bit to one extra
accumulator tape. The block's original tapes all survive the XOR transition. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.XorBody
open LocalBitMultitape RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old {t : ℕ} (i : Fin t) : Fin (t+1):=i.castAdd 1
def slots {t : ℕ} (bitSlot : Fin t) : Fin 2→Fin (t+1):=![Fin.last t,old bitSlot]
theorem old_injective (t : ℕ) : Function.Injective (@old t):=by
  intro i j h;exact Fin.ext (congrArg (fun x : Fin (t+1)=>x.val) h)
theorem old_away (t : ℕ) : ∀ i : Fin t,old i≠Fin.last t:=by
  intro i he
  have hv:=congrArg Fin.val he
  have hi:=i.isLt
  change i.val=t at hv
  omega
theorem slots_injective {t : ℕ} (bitSlot : Fin t) : Function.Injective (slots bitSlot):=by
  intro i j he
  fin_cases i <;>fin_cases j <;>try rfl
  · exact (old_away t bitSlot he.symm).elim
  · exact (old_away t bitSlot he).elim
def input {t : ℕ} (native : Fin t→List Bool) (parity : Bool) : Fin (t+1)→List Bool:=
  Fin.addCases native (fun _=>[parity])
noncomputable def first {t s : ℕ} (p : Machine t s):=RecoveryFocus.machine old p
noncomputable def last {t : ℕ} (bitSlot : Fin t):=RecoveryFocus.machine (slots bitSlot) XorStep.machine
noncomputable def machine {t s : ℕ} (p : Machine t s) (bitSlot : Fin t):=
  Composition.machine (first p) (last bitSlot)
theorem ready {t s : ℕ} (p : Machine t s) (bitSlot : Fin t) (fuel : ℕ)
    (native out : Fin t→List Bool) (parity bit : Bool)
    (hp : ClockJoin.ReadyRun p fuel native out) (hb : out bitSlot=[bit]) :
    ∃ result,ClockJoin.ReadyRun (machine p bitSlot) (fuel+2) (input native parity) result ∧
      result (Fin.last t)=[xor parity bit] ∧ ∀ i,result (old i)=out i:=by
  have firstReady:=hp.focus old (old_injective t) (input native parity) (by
    intro i;exact Fin.addCases_left i)
  let middle:=install old (input native parity) out
  have lastReady:=(XorStep.ready parity bit).focus (slots bitSlot) (slots_injective bitSlot) middle (by
    intro i
    fin_cases i
    · change middle (Fin.last t)=[parity]
      change install old (input native parity) out (Fin.last t)=[parity]
      rw [install_other old _ _ _ (old_away t)]
      exact Fin.addCases_right 0
    · change middle (old bitSlot)=[bit]
      exact (install_slot old (old_injective t) _ _ bitSlot).trans hb)
  have whole:=ClockJoin.join (first p) (last bitSlot) fuel 1 _ _ _ firstReady lastReady
  have hcost : fuel+1+1=fuel+2:=by omega
  rw [hcost] at whole
  refine ⟨_,whole,?_,?_⟩
  · exact install_slot (slots bitSlot) (slots_injective bitSlot) _ _ 0
  · intro i
    by_cases hi : i=bitSlot
    · subst i
      exact (install_slot (slots bitSlot) (slots_injective bitSlot) _ _ 1).trans hb.symm
    · have outside : ∀ j,slots bitSlot j≠old i:=by
        intro j he
        fin_cases j
        · exact old_away t i he.symm
        · exact hi (old_injective t he).symm
      rw [install_other (slots bitSlot) _ _ _ outside]
      exact install_slot old (old_injective t) _ _ i

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.XorBody
