import Proof.CaseAnalysis.RecoveryAddressPrep

/-! Enclose the address handoff beside both child results, the saved constant,
and the actual address word/count. The original selector bank is retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNodeAddress
open LocalBitMultitape RepairRepresentation RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool) : Fin 51→ℕ:=
  Fin.addCases (m:=48) (n:=3) (motive:=fun _=>ℕ) (RecoveryBoundedConstant.heads out) ![0,0,1]
def data (index base C D value limit total L : ℕ) (out source : List Bool) (secondIndex : ℕ)
    (savedFirst savedSecond savedConstant address : List Bool) (count : ℕ) : Fin 51→List Bool:=
  Fin.addCases (m:=48) (n:=3) (motive:=fun _=>List Bool)
    (RecoveryBoundedConstant.data index base C D value limit total L out source secondIndex index savedFirst savedSecond)
    ![savedConstant,address,CompareMachine.word count]
def before (index base C D limit total L : ℕ) (flag : Bool) (out source : List Bool) (secondIndex : ℕ)
    (savedFirst savedSecond address : List Bool) (count : ℕ) (i : Fin 51):=
  if i=1 then List.replicate C false else if i=29 then ZeroPadding.pad C [flag]
    else data index base C D 1 limit total L out source secondIndex savedFirst savedSecond (List.replicate C false) address count i
def fixedData (index C D limit total L : ℕ) (out source : List Bool) (secondIndex : ℕ)
    (savedFirst savedSecond address : List Bool) (count : ℕ):=
  data index 0 C D 0 limit total L out source secondIndex savedFirst savedSecond [] address count

theorem data_override (index base C D value limit total L : ℕ) (out source : List Bool) (secondIndex : ℕ)
    (savedFirst savedSecond savedConstant address : List Bool) (count : ℕ) :
    data index base C D value limit total L out source secondIndex savedFirst savedSecond savedConstant address count=
      fun i=>if i=25 then List.replicate base true else if i=34 then ZeroPadding.pad C (List.replicate value true)
        else if i=48 then savedConstant else fixedData index C D limit total L out source secondIndex savedFirst savedSecond address count i := by
  funext i
  fin_cases i <;> rfl

theorem before_constant (index base C D limit total L : ℕ) (flag : Bool) (out source : List Bool) (secondIndex : ℕ)
    (savedFirst savedSecond address : List Bool) (count : ℕ) :
    before index base C D limit total L flag out source secondIndex savedFirst savedSecond address count=
      Fin.addCases (m:=48) (n:=3) (motive:=fun _=>List Bool)
        (RecoveryBoundedConstant.afterUnary index base C D limit total L flag out source secondIndex index savedFirst savedSecond)
        ![List.replicate C false,address,CompareMachine.word count] := by
  funext i
  fin_cases i <;> rfl

def prepareSlots : Fin 10→Fin 51:=![25,48,46,1,41,34,32,22,23,29]
noncomputable def prepare:=RecoveryFocus.machine prepareSlots RecoveryBoundedAddressPrep.machine

theorem prepare_install (index base C D limit total L : ℕ) (flag : Bool) (out source : List Bool) (secondIndex : ℕ)
    (savedFirst savedSecond address : List Bool) (count : ℕ) :
    install prepareSlots (before index base C D limit total L flag out source secondIndex savedFirst savedSecond address count)
      (RecoveryBoundedAddressPrep.output base index C)=
      data index (base+1) C D 0 limit total L out source secondIndex savedFirst savedSecond
        (ZeroPadding.pad C (List.replicate base true)) address count := by
  apply HierarchyWidth.install_eq prepareSlots (by decide)
  · intro j;fin_cases j <;> rfl
  · intro i hi
    have h1 : i≠1:=fun h=>hi 3 h.symm
    have h29 : i≠29:=fun h=>hi 9 h.symm
    have h25 : i≠25:=fun h=>hi 0 h.symm
    have h34 : i≠34:=fun h=>hi 5 h.symm
    have h48 : i≠48:=fun h=>hi 1 h.symm
    simp only [before,if_neg h1,if_neg h29,data_override,if_neg h25,if_neg h34,if_neg h48]

theorem prepare_run (index base C D limit total L : ℕ) (flag : Bool) (out source : List Bool) (secondIndex : ℕ)
    (savedFirst savedSecond address : List Bool) (count : ℕ) (ha : base+1 ≤ C) (hi : index+1 ≤ C) :
    ∃ r,runFrom prepare (4*C+4*base+4*index+29)
      ⟨prepare.start,heads out,before index base C D limit total L flag out source secondIndex savedFirst savedSecond address count⟩=some r ∧
      r.steps=4*C+4*base+4*index+29 ∧ r.final.heads=heads out ∧
      r.final.tapes=data index (base+1) C D 0 limit total L out source secondIndex savedFirst savedSecond
        (ZeroPadding.pad C (List.replicate base true)) address count := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryBoundedAddressPrep.prepare_ready base index C flag ha hi).focus_at
    prepareSlots (by decide) (heads out)
    (before index base C D limit total L flag out source secondIndex savedFirst savedSecond address count)
    (by intro j;fin_cases j <;> rfl) (by intro j;fin_cases j <;> rfl)
  exact ⟨r,hr,rs,rh,rt.trans (prepare_install index base C D limit total L flag out source secondIndex savedFirst savedSecond address count)⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedNodeAddress
