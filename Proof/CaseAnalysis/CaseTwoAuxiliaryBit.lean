import Proof.CaseAnalysis.CaseTwoAuxiliaryLookup

/-! One complete original auxiliary-bit call, including construction of the
honest input, the imported honest machine, its reset, and the final lookup. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.AuxiliaryBit
open LocalBitMultitape RepairRepresentation SourceInterfaces RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (a : PointwisePCPPAlgorithm)
def tapes:=HonestCall.tapes a+3
def honestSlots (j : Fin (HonestCall.tapes a)) : Fin (tapes a):=j.castAdd 3
def indexSlot : Fin (tapes a):=Fin.natAdd (HonestCall.tapes a) (0 : Fin 3)
def outputSlot : Fin (tapes a):=Fin.natAdd (HonestCall.tapes a) (1 : Fin 3)
def logSlot : Fin (tapes a):=Fin.natAdd (HonestCall.tapes a) (2 : Fin 3)
def lookupSlots : Fin 4→Fin (tapes a):=![indexSlot a,honestSlots a (HonestCall.outputSlot a),outputSlot a,logSlot a]
theorem honest_injective : Function.Injective (honestSlots a):=by
  intro i j he;apply Fin.ext;exact congrArg (fun x : Fin (tapes a)=>x.val) he
theorem lookup_injective : Function.Injective (lookupSlots a):=by
  intro i j he
  have hv:=congrArg Fin.val he
  have hb:=(HonestCall.outputSlot a).isLt
  fin_cases i <;>fin_cases j <;>first | rfl | (simp [lookupSlots,indexSlot,outputSlot,logSlot,honestSlots] at hv <;>omega)
def honest:=RecoveryFocus.machine (honestSlots a) (HonestCall.machine a)
def lookup:=RecoveryFocus.machine (lookupSlots a) UnaryLookup.machine
def machine:=Composition.machine (honest a) (lookup a)
def input (request : PCPPRequest a.minimumArity) (u : BitInput request.arity) (index : ℕ) : Fin (tapes a)→List Bool:=
  Fin.addCases (m:=HonestCall.tapes a) (n:=3) (HonestCall.input a request u) ![List.replicate index true,[],[]]
def budget (request : PCPPRequest a.minimumArity) (u : BitInput request.arity) (index : ℕ):=
  HonestCall.budget a request u+1+(2*index+4)

theorem bit_run (request : PCPPRequest a.minimumArity) (u : BitInput request.arity)
    (i : Fin (a.output request).auxiliaryBits) : ∃ out,
    ClockJoin.ReadyRun (machine a) (budget a request u i.val) (input a request u i.val) out ∧
      out (outputSlot a)=[(a.output request).honestAuxiliary u i]:=by
  obtain ⟨table,ht,word,_,_⟩:=HonestCall.honest_run a request u
  have firstReady:=ht.focus (honestSlots a) (honest_injective a) (input a request u i.val)
    (by intro j;exact Fin.addCases_left j)
  let middle:=install (honestSlots a) (input a request u i.val) table
  have fresh (j : Fin 3) : middle (j.natAdd (HonestCall.tapes a))=
      ![List.replicate i.val true,[],[]] j:=by
    have ha:∀ k,honestSlots a k≠j.natAdd (HonestCall.tapes a):=by
      intro k he
      have hv:=congrArg Fin.val he
      have hk:=k.isLt
      simp only [honestSlots,Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    exact (install_other _ _ _ _ ha).trans (Fin.addCases_right j)
  obtain ⟨bit,hb,bitValue⟩:=UnaryLookup.auxiliary_ready ((a.output request).honestAuxiliary u) i
  have lastReady:=hb.focus (lookupSlots a) (lookup_injective a) middle (by
    intro j;fin_cases j
    · exact fresh 0
    · exact (install_slot (honestSlots a) (honest_injective a) _ _ _).trans word
    · exact fresh 1
    · exact fresh 2)
  exact ⟨_,ClockJoin.join _ _ _ _ _ _ _ firstReady lastReady,
    (install_slot (lookupSlots a) (lookup_injective a) _ _ 2).trans bitValue⟩

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.AuxiliaryBit
