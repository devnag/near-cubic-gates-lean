import Proof.CaseAnalysis.CaseTwoLiteralFields

/-! One original clause packet and its actual occurrence-position bit
produce the unsigned variable index. Both original literal templates are
split by the existing native worker, then the existing selector copies the
selected raw index. The packet survives for the paid cache clear. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.LiteralIndices
open LocalBitMultitape RepairRepresentation SourceInterfaces RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def fieldsSlots (i : Fin 32) : Fin 41:=i.castAdd 9
def leftSlots : Fin 4→Fin 41:=![20,32,33,34]
def rightSlots : Fin 4→Fin 41:=![30,35,36,37]
def selectSlots : Fin 5→Fin 41:=![38,32,35,39,40]
def fields:=RecoveryFocus.machine fieldsSlots LiteralFields.machine
def left:=RecoveryFocus.machine leftSlots LiteralFields.split
def right:=RecoveryFocus.machine rightSlots LiteralFields.split
def select:=RecoveryFocus.machine selectSlots PCPPNativeClauseOffset.machine
def machine:=Composition.machine (Composition.machine (Composition.machine fields left) right) select
def input (C a b : ℕ) (position : Bool) (i : Fin 41):=
  if i=0 then ZeroPadding.pad C (natListWord [a,b]) else if i=38 then [position] else []
def selected {n : ℕ} (left right : Literal n) (position : Bool):=
  if position then LiteralFields.index right else LiteralFields.index left
def budget {n : ℕ} (left right : Literal n) (position : Bool):=
  LiteralFields.budget (literalIndex left) (literalIndex right)+1+
    LiteralFields.splitBudget (LiteralFields.index left) (LiteralFields.negative left)+1+
    LiteralFields.splitBudget (LiteralFields.index right) (LiteralFields.negative right)+1+
    (2*selected left right position+6)
theorem fields_injective : Function.Injective fieldsSlots:=by
  intro i j he;apply Fin.ext;exact congrArg (fun x : Fin 41=>x.val) he
theorem above_fields (i : Fin 41) (hi : 32 ≤ i.val) : ∀ j,fieldsSlots j≠i:=by
  intro j he
  have hv:=congrArg Fin.val he
  have hj:=j.isLt
  simp only [fieldsSlots,Fin.val_castAdd] at hv
  omega

theorem indices_run {n : ℕ} (C : ℕ) (L R : Literal n) (position : Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget L R position)
      (input C (literalIndex L) (literalIndex R) position) out ∧
      out 39=List.replicate (selected L R position) true ∧
      out 0=ZeroPadding.pad C (natListWord [literalIndex L,literalIndex R]):=by
  let initial:=input C (literalIndex L) (literalIndex R) position
  obtain ⟨parsed,hp,pl,pr,pkeep⟩:=LiteralFields.fields_run C (literalIndex L) (literalIndex R)
  have parsedReady:=hp.focus fieldsSlots fields_injective initial (by
    intro j
    by_cases hj : j=0
    · subst j;rfl
    · have hn : j.val≠0:=fun he=>hj (Fin.ext he)
      have hx : fieldsSlots j≠38:=fun he=>by
        have hv:=congrArg Fin.val he
        have hlt:=j.isLt
        simp only [fieldsSlots,Fin.val_castAdd] at hv
        omega
      have hz : fieldsSlots j≠0:=by
        intro he
        exact hn (congrArg (fun x : Fin 41=>x.val) he)
      change (if fieldsSlots j=0 then _ else if fieldsSlots j=38 then _ else [])=
        (if j.val=0 then _ else [])
      simp only [hz,hx,hn,if_false])
  let A:=install fieldsSlots initial parsed
  have fresh (i : Fin 41) (hi : 32 ≤ i.val) : A i=initial i:=install_other _ _ _ _ (above_fields i hi)
  obtain ⟨leftOut,hl,leftIndex⟩:=LiteralFields.literal_run L
  have leftReady:=hl.focus leftSlots (by decide) A (by
    intro j;fin_cases j
    · exact (install_slot fieldsSlots fields_injective initial parsed 20).trans pl
    all_goals rw [fresh _ (by decide)];rfl)
  let B:=install leftSlots A leftOut
  obtain ⟨rightOut,hr,rightIndex⟩:=LiteralFields.literal_run R
  have rightReady:=hr.focus rightSlots (by decide) B (by
    intro j;fin_cases j
    · change B 30=UnaryTemplate.tape (literalIndex R)
      rw [show B 30=A 30 from install_other _ _ _ _ (by decide)]
      exact (install_slot fieldsSlots fields_injective initial parsed 30).trans pr
    all_goals
      rw [show B _=A _ from install_other _ _ _ _ (by decide),fresh _ (by decide)]
      rfl)
  let D:=install rightSlots B rightOut
  obtain ⟨selector,hsel,selTape,selHead,selSteps⟩:=
    PCPPNativeClauseOffset.ready_run position (LiteralFields.index L) (LiteralFields.index R)
  have selectBase:ClockJoin.ReadyRun PCPPNativeClauseOffset.machine _ _ _:=
    ⟨selector,hsel,selTape,selHead,selSteps.le⟩
  have selectReady:=selectBase.focus
    selectSlots (by decide) D (by
    intro j;fin_cases j
    · change D 38=[position]
      rw [show D 38=B 38 from install_other _ _ _ _ (by decide),
        show B 38=A 38 from install_other _ _ _ _ (by decide),fresh 38 (by decide)]
      rfl
    · change D 32=List.replicate (LiteralFields.index L) true
      rw [show D 32=B 32 from install_other _ _ _ _ (by decide)]
      exact (install_slot leftSlots (by decide) A leftOut 1).trans leftIndex
    · exact (install_slot rightSlots (by decide) B rightOut 1).trans rightIndex
    all_goals
      rw [show D _=B _ from install_other _ _ _ _ (by decide),
        show B _=A _ from install_other _ _ _ _ (by decide),fresh _ (by decide)]
      rfl)
  have joined:=ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ parsedReady leftReady) rightReady
  have whole:=ClockJoin.join _ _ _ _ _ _ _ joined selectReady
  refine ⟨_,whole,?_,?_⟩
  · exact install_slot selectSlots (by decide) D _ 3
  · rw [install_other selectSlots _ _ 0 (by decide),
      show D 0=B 0 from install_other _ _ _ _ (by decide),
      show B 0=A 0 from install_other _ _ _ _ (by decide)]
    exact (install_slot fieldsSlots fields_injective initial parsed 0).trans pkeep

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.LiteralIndices
