import Proof.CaseAnalysis.WitnessSourceFields
import Proof.CaseAnalysis.CapacityPower

/-! Actual source metadata supplies the exact distinct-variable count V
and actual clause-bit driver. All template copies and the V sum are paid;
the same PCPP output is retained without any source serialization. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SourceCounts
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 34) : Fin 42:=i.castAdd 8
theorem old_injective : Function.Injective old:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 42=>k.val) h)
def copySlots : Fin 3→Fin 3→Fin 42:=![![10,34,35],![20,36,37],![30,38,39]]
def sumSlots : Fin 4→Fin 42:=![34,36,40,41]
def copyResult (n : ℕ) : Fin 3→List Bool:=
  ![UnaryTemplate.tape n,List.replicate n true,List.replicate (n+2) false]
noncomputable def copied (i : Fin 3) (n : ℕ) (ambient : Fin 42→List Bool):=
  install (copySlots i) ambient (copyResult n)
noncomputable def field:=RecoveryFocus.machine old SourceFields.machine
noncomputable def copy (i : Fin 3):=RecoveryFocus.machine (copySlots i) (UWalkUnary.machine false false)
noncomputable def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def first:=Composition.machine field (copy 0)
noncomputable def second:=Composition.machine first (copy 1)
noncomputable def third:=Composition.machine second (copy 2)
noncomputable def machine:=Composition.machine third sum
def input (source : List Bool) (i : Fin 42):=if i.val=0 then source else []
def budget (a b c : ℕ):=
  SourceFields.budget a b c+1+(2*a+6)+1+(2*b+6)+1+(2*c+6)+1+(2*(a+b)+6)

theorem copy_run (n : ℕ) : ClockJoin.ReadyRun (UWalkUnary.machine false false) (2*n+6)
    ![UnaryTemplate.tape n,[],[]] (copyResult n):=by
  simpa [UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,copyResult,
    RepairSource.CloseoutCapacity.Power.template_source] using
    UWalkUnary.ready false false (n+2) n
theorem copied_slot (i : Fin 3) (n : ℕ) (ambient : Fin 42→List Bool) (j : Fin 3) :
    copied i n ambient (copySlots i j)=copyResult n j:=
  install_slot _ (by fin_cases i <;> decide) _ _ _
theorem copied_other (i j : Fin 3) (hij : i≠j) (n : ℕ) (ambient : Fin 42→List Bool) (l : Fin 3) :
    copied i n ambient (copySlots j l)=ambient (copySlots j l):=by
  apply install_other
  exact (by decide : ∀ i j : Fin 3,i≠j → ∀ l k : Fin 3,copySlots i k≠copySlots j l) i j hij l
theorem copied_outside (i : Fin 3) (n : ℕ) (ambient : Fin 42→List Bool) (j : Fin 42)
    (hj : j=0 ∨ 40 ≤ j.val) : copied i n ambient j=ambient j:=by
  apply install_other
  intro k h
  have hv:=congrArg (fun x : Fin 42=>x.val) h
  have hb:(copySlots i k).val<40 ∧ (copySlots i k).val≠0:=by fin_cases i <;> fin_cases k <;> decide
  rcases hj with rfl|hj <;> omega
theorem copy_at (i : Fin 3) (n : ℕ) (ambient : Fin 42→List Bool)
    (h0 : ambient (copySlots i 0)=UnaryTemplate.tape n)
    (h1 : ambient (copySlots i 1)=[]) (h2 : ambient (copySlots i 2)=[]) :
    ClockJoin.ReadyRun (copy i) (2*n+6) ambient (copied i n ambient):=by
  exact (copy_run n).focus (copySlots i) (by fin_cases i <;> decide) ambient
    (by intro j;fin_cases j <;> assumption)

theorem counts_run (a b c : ℕ) (tail : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget a b c) (input (SourceFields.word a b c tail)) output ∧
      output 0=SourceFields.word a b c tail ∧ output 40=List.replicate (a+b) true ∧
      output 38=List.replicate c true:=by
  obtain ⟨out,ho,h0,ht⟩:=SourceFields.fields_run a b c tail
  have hf:=ho.focus old old_injective (input (SourceFields.word a b c tail))
    (by intro j;fin_cases j <;> rfl)
  let b0:=install old (input (SourceFields.word a b c tail)) out
  have b0old (j : Fin 34) : b0 (old j)=out j:=install_slot _ old_injective _ _ _
  have b0blank (j : Fin 42) (hj : 34 ≤ j.val) : b0 j=[]:=by
    rw [show b0=install old _ out by rfl,install_other _ _ _ _ (by
      intro k h;have hv:=congrArg (fun x : Fin 42=>x.val) h;change k.val=j.val at hv;omega)]
    simp only [input,if_neg (show j.val≠0 by omega)]
  have b0template (j : Fin 3) : b0 (copySlots j 0)=UnaryTemplate.tape (![a,b,c] j):=by
    have he:copySlots j 0=old ((SourceFields.outputSlot j).castAdd 1):=by fin_cases j <;> rfl
    rw [he,b0old]
    exact ht j
  have h1:=copy_at 0 a b0 (b0template 0) (b0blank 34 (by decide)) (b0blank 35 (by decide))
  let b1:=copied 0 a b0
  have h2:=copy_at 1 b b1
    (by rw [show b1=copied 0 a b0 by rfl,copied_other 0 1 (by decide)];exact b0template 1)
    (by rw [show b1=copied 0 a b0 by rfl,copied_other 0 1 (by decide)];exact b0blank 36 (by decide))
    (by rw [show b1=copied 0 a b0 by rfl,copied_other 0 1 (by decide)];exact b0blank 37 (by decide))
  let b2:=copied 1 b b1
  have h3:=copy_at 2 c b2
    (by rw [show b2=copied 1 b b1 by rfl,copied_other 1 2 (by decide),
        show b1=copied 0 a b0 by rfl,copied_other 0 2 (by decide)];exact b0template 2)
    (by rw [show b2=copied 1 b b1 by rfl,copied_other 1 2 (by decide),
        show b1=copied 0 a b0 by rfl,copied_other 0 2 (by decide)];exact b0blank 38 (by decide))
    (by rw [show b2=copied 1 b b1 by rfl,copied_other 1 2 (by decide),
        show b1=copied 0 a b0 by rfl,copied_other 0 2 (by decide)];exact b0blank 39 (by decide))
  let b3:=copied 2 c b2
  have b3left:b3 34=List.replicate a true:=by
    change copied 2 c b2 (copySlots 0 1)=_
    rw [copied_other 2 0 (by decide)]
    change copied 1 b b1 (copySlots 0 1)=_
    rw [copied_other 1 0 (by decide)]
    exact copied_slot 0 a b0 1
  have b3right:b3 36=List.replicate b true:=by
    change copied 2 c b2 (copySlots 1 1)=_
    rw [copied_other 2 1 (by decide)]
    exact copied_slot 1 b b1 1
  have b3blank (j : Fin 42) (hj : 40 ≤ j.val) : b3 j=[]:=by
    rw [show b3=copied 2 c b2 by rfl,copied_outside _ _ _ _ (Or.inr hj),
      show b2=copied 1 b b1 by rfl,copied_outside _ _ _ _ (Or.inr hj),
      show b1=copied 0 a b0 by rfl,copied_outside _ _ _ _ (Or.inr hj)]
    exact b0blank j (by omega)
  have hs:=(ClockUnarySum.sum_ready a b).focus sumSlots (by decide) b3 (by
    intro j;fin_cases j
    · exact b3left
    · exact b3right
    all_goals exact b3blank _ (by decide))
  have hall:=ClockJoin.join third sum _ _ _ _ _
    (ClockJoin.join second (copy 2) _ _ _ _ _
      (ClockJoin.join first (copy 1) _ _ _ _ _ (ClockJoin.join field (copy 0) _ _ _ _ _ hf h1) h2) h3) hs
  refine ⟨_,hall,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide),show b3=copied 2 c b2 by rfl,
      copied_outside _ _ _ _ (Or.inl rfl),show b2=copied 1 b b1 by rfl,
      copied_outside _ _ _ _ (Or.inl rfl),show b1=copied 0 a b0 by rfl,
      copied_outside _ _ _ _ (Or.inl rfl)]
    exact (b0old 0).trans h0
  · exact install_slot sumSlots (by decide) _ _ 2
  · rw [install_other _ _ _ _ (by decide)]
    exact copied_slot 2 c b2 1

end NearCubicWires.RepairOrdinary.CloseoutWitness.SourceCounts
