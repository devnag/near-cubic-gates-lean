import Proof.CaseAnalysis.WitnessModeWire
import Proof.CaseAnalysis.WitnessDescriptionPolicy
import Proof.CaseAnalysis.WitnessTermPolicy
import Proof.CaseAnalysis.WitnessMass

/-! The complete legal-family policy uses the actual source fields once.
The original wire, description, term and mass workers share their produced
values directly; each policy and the zero accumulator remain available. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.LegalPolicy
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open CompetitorSumFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev M (e : ℕ):=ModeWire.tapes e
def tapes (e : ℕ):=M e+256
def modeSlots (e : ℕ) (i : Fin (M e)) : Fin (tapes e):=i.castAdd 256
def termSlots (e : ℕ) (i : Fin 44) : Fin (tapes e):=⟨M e+i.val,by dsimp only [tapes];omega⟩
def wireSlot (e : ℕ):=modeSlots e (ModeWire.valueSlot e)
def descriptionSlots (e : ℕ) (i : Fin 93) : Fin (tapes e):=
  if i.val=0 then termSlots e 0 else if i.val=34 then wireSlot e
  else if i.val=76 then modeSlots e (ModeWire.dimensionSlots e 1)
  else ⟨M e+44+i.val,by dsimp only [tapes];omega⟩
def massSlots (e : ℕ) (i : Fin 119) : Fin (tapes e):=
  if i.val=0 then termSlots e 42 else ⟨M e+137+i.val,by dsimp only [tapes];omega⟩
def input (e R q0 cb b : ℕ) (i : Fin (tapes e)):=
  if i.val=0 then List.replicate R true else if i.val=M e then List.replicate q0 true
  else if i.val=M e+16 then List.replicate cb true else if i.val=M e+138 then List.replicate b true else []
def mode (e den : ℕ):=RecoveryFocus.machine (modeSlots e) (ModeWire.machine e den)
def terms (e : ℕ) (delta : ℚ) (copies : ℕ):=RecoveryFocus.machine (termSlots e) (TermPolicy.machine delta copies)
def description (e : ℕ) (sym : Bool):=RecoveryFocus.machine (descriptionSlots e) (DescriptionPolicy.machine sym)
def mass (e : ℕ):=RecoveryFocus.machine (massSlots e) MassCold.machine
def first (e den : ℕ) (delta : ℚ) (copies : ℕ):=Composition.machine (mode e den) (terms e delta copies)
def second (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool):=
  Composition.machine (first e den delta copies) (description e sym)
def machine (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool):=
  Composition.machine (second e den delta copies sym) (mass e)
def W (e den R : ℕ):=R^3/(den*logScale R^e)
def T (delta : ℚ) (copies q0 cb : ℕ):=(2*2^cb)*xorTermBound delta q0 copies
def budget (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool) (R q0 cb b : ℕ):=
  ModeWire.budget e den R+1+TermPolicy.budget delta copies q0 cb+1+
    DescriptionPolicy.budget sym R q0 (W e den R)+1+MassCold.budget (T delta copies q0 cb) b
def project (e : ℕ) (bank : Fin (tapes e)→List Bool) (i : Fin 94):=bank (massSlots e (MassCold.nativeSlots i))

theorem mode_injective (e : ℕ) : Function.Injective (modeSlots e):=by
  intro i j h;exact Fin.ext (congrArg (fun k : Fin (tapes e)=>k.val) h)
theorem term_injective (e : ℕ) : Function.Injective (termSlots e):=by
  intro i j h
  have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  dsimp only [termSlots] at hv
  exact Fin.ext (by omega)
theorem wire_val (e : ℕ) : (wireSlot e).val=58+2*e:=by
  simp only [wireSlot,modeSlots,Fin.val_castAdd,ModeWire.valueSlot,ModeWire.divideSlots,ModeDivide.valueSlot,
    if_neg (show 11+2*e≠0 by omega),if_neg (show 11+2*e≠1 by omega)]
  omega
theorem description_val (e : ℕ) (i : Fin 93) : (descriptionSlots e i).val=
    if i.val=0 then M e else if i.val=34 then 58+2*e else if i.val=76 then 1 else M e+44+i.val:=by
  unfold descriptionSlots
  split_ifs
  · rfl
  · exact wire_val e
  all_goals rfl
theorem description_injective (e : ℕ) : Function.Injective (descriptionSlots e):=by
  intro i j h
  have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  rw [description_val,description_val] at hv
  have he:M e=60+2*e:=by dsimp [M,ModeWire.tapes,ModeDivide.tapes];omega
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem mass_val (e : ℕ) (i : Fin 119) : (massSlots e i).val=if i.val=0 then M e+42 else M e+137+i.val:=by
  unfold massSlots;split_ifs <;> rfl
theorem mass_injective (e : ℕ) : Function.Injective (massSlots e):=by
  intro i j h
  have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  rw [mass_val,mass_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem mode_outside (e : ℕ) (i : Fin (tapes e)) (hi : M e ≤ i.val) : ∀ j,modeSlots e j≠i:=by
  intro j h;have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  change j.val=i.val at hv;omega
theorem term_outside (e : ℕ) (i : Fin (tapes e)) (hi : i.val<M e ∨ M e+44 ≤ i.val) : ∀ j,termSlots e j≠i:=by
  intro j h;have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  dsimp only [termSlots] at hv
  rcases hi with hi|hi <;> omega
theorem description_outside (e : ℕ) (i : Fin (tapes e))
    (hi : i.val≠M e ∧ i.val≠58+2*e ∧ i.val≠1 ∧ (i.val<M e+44 ∨ M e+137 ≤ i.val)) :
    ∀ j,descriptionSlots e j≠i:=by
  intro j h;have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  rw [description_val] at hv
  split_ifs at hv <;> rcases hi.2.2.2 with ht|ht <;> omega
theorem mass_outside (e : ℕ) (i : Fin (tapes e)) (hi : i.val≠M e+42 ∧ i.val<M e+137) :
    ∀ j,massSlots e j≠i:=by
  intro j h;have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  rw [mass_val] at hv
  split_ifs at hv <;> omega

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.LegalPolicy
