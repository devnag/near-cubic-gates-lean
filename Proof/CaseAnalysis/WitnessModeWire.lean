import Proof.CaseAnalysis.WitnessModeDivide

/-! The original actual native arity alone produces the exact natural
wire cap. The binary arity and the reusable domain template are retained
for the enclosing sum and circuit guards. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ModeWire
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open ProjectionNormalization VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (e : ℕ):=47+ModeDivide.tapes e
def dimensionSlots (e : ℕ) (i : Fin 47) : Fin (tapes e):=i.castAdd (ModeDivide.tapes e)
def divideSlots (e : ℕ) (i : Fin (ModeDivide.tapes e)) : Fin (tapes e):=
  ⟨if i.val=0 then 45 else if i.val=1 then 36 else 47+i.val,by
    dsimp only [tapes];split_ifs <;> have hi:=i.isLt <;> dsimp [ModeDivide.tapes] at * <;> omega⟩
def valueSlot (e : ℕ):=divideSlots e (ModeDivide.valueSlot e)
def first (e : ℕ):=RecoveryFocus.machine (dimensionSlots e) ModeDimensions.machine
def second (e den : ℕ):=RecoveryFocus.machine (divideSlots e) (ModeDivide.machine e den)
def machine (e den : ℕ):=Composition.machine (first e) (second e den)
def input (e R : ℕ) (i : Fin (tapes e)):=if i.val=0 then List.replicate R true else []
def budget (e den R : ℕ):=ModeDimensions.budget R+1+ModeDivide.budget e den (R^3) (logScale R)

theorem dimension_injective (e : ℕ) : Function.Injective (dimensionSlots e):=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (tapes e)=>k.val) h)
theorem divide_injective (e : ℕ) : Function.Injective (divideSlots e):=by
  intro i j h
  have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  dsimp only [divideSlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem divide_outside (e : ℕ) (i : Fin 47) (h36 : i.val≠36) (h45 : i.val≠45) :
    ∀ j,divideSlots e j≠dimensionSlots e i:=by
  intro j h
  have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  have hi:=i.isLt
  dsimp only [divideSlots,dimensionSlots,Fin.val_castAdd] at hv
  split_ifs at hv <;> omega

theorem wire_run (e den R : ℕ) (hd : 0<den) (hR : 0<R) : ∃ output,
    ClockJoin.ReadyRun (machine e den) (budget e den R) (input e R) output ∧
      output (dimensionSlots e 1)=List.replicate R true ∧
      output (dimensionSlots e 3)=UnaryTemplate.tape R ∧
      output (dimensionSlots e 5)=frame (binary (natBitLength R) R) ∧
      output (dimensionSlots e 8)=CompareMachine.word (natBitLength R) ∧
      output (valueSlot e)=List.replicate (R^3/(den*logScale R^e)) true:=by
  obtain ⟨d,hdRun,d1,d3,d5,d8,d36,d45⟩:=ModeDimensions.dimensions_run R hR
  have hdf:=hdRun.focus (dimensionSlots e) (dimension_injective e) (input e R) (by intro i;rfl)
  let bank:=install (dimensionSlots e) (input e R) d
  have old (i : Fin 47) : bank (dimensionSlots e i)=d i:=
    install_slot _ (dimension_injective e) _ _ _
  have fresh (i : Fin (tapes e)) (hi : 47 ≤ i.val) : bank i=[]:=by
    rw [show bank=install (dimensionSlots e) _ _ by rfl,
      install_other _ _ _ _ (by
        intro j h
        have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
        change j.val=i.val at hv
        omega)]
    simp only [input,if_neg (show i.val≠0 by omega)]
  obtain ⟨w,hw,_,_,_,wv⟩:=ModeDivide.divide_run e den (R^3) (logScale R) hd (logScale_pos R)
  have hwf:=hw.focus (divideSlots e) (divide_injective e) bank (by
    intro i
    by_cases h0:i.val=0
    · have he:i=⟨0,by dsimp [ModeDivide.tapes];omega⟩:=Fin.ext h0
      rw [he];exact (old 45).trans d45
    by_cases h1:i.val=1
    · have he:i=⟨1,by dsimp [ModeDivide.tapes];omega⟩:=Fin.ext h1
      rw [he];exact (old 36).trans d36
    rw [ModeDivide.input,if_neg h0,if_neg h1]
    exact fresh _ (by simp only [divideSlots,if_neg h0,if_neg h1];omega))
  have keep (i : Fin 47) (h36 : i.val≠36) (h45 : i.val≠45) :
      install (divideSlots e) bank w (dimensionSlots e i)=d i:=by
    rw [install_other _ _ _ _ (divide_outside e i h36 h45)]
    exact old i
  refine ⟨_,ClockJoin.join (first e) (second e den) _ _ _ _ _ hdf hwf,
    (keep 1 (by decide) (by decide)).trans d1,
    (keep 3 (by decide) (by decide)).trans d3,
    (keep 5 (by decide) (by decide)).trans d5,
    (keep 8 (by decide) (by decide)).trans d8,?_⟩
  rw [valueSlot,install_slot _ (divide_injective e)]
  exact wv

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ModeWire
