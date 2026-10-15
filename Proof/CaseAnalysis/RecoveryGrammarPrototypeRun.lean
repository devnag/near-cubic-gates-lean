import Proof.CaseAnalysis.RecoveryGrammarPrototype

/-! The fifteen-field grammar prototype has one fixed physical print order.
Its seven nonempty fields are copied from actual retained raw scalars. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarPrototype
open LocalBitMultitape Composition RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (C index value limit upper : ℕ) (i : Fin 78) : List Bool:=
  if i=1 then List.replicate index true
  else if i=22 then List.replicate C true
  else if i=35 then RepairSource.VerifierDecoding.CompareMachine.word limit
  else if i=41 then List.replicate value true
  else if i=42 then List.replicate C true
  else if i=44 then List.replicate index true
  else if i=72 then RepairSource.VerifierDecoding.CompareMachine.word upper else []
def packet (C index value limit upper : ℕ):=
  field false index++field false C++field true limit++field false value++
    field false C++field false index++List.replicate 8 false++field true upper

theorem packet_original (C index value limit upper : ℕ) :
    packet C index value limit upper=RecoveryBoundedRowReload.word (fields C index value limit upper) := by
  simp [packet,RecoveryBoundedRowReload.word,RecoveryBoundedRowReload.ports,
    CloseoutRowsPacketLoad.stream,fields,field,header,RepairSource.VerifierDecoding.CompareMachine.word,
    frame,List.append_assoc]

noncomputable def first:=Composition.machine (scalarField 79 false) (scalarField 83 false)
noncomputable def second:=Composition.machine first (scalarField 80 true)
noncomputable def third:=Composition.machine second (scalarField 81 false)
noncomputable def fourth:=Composition.machine third (scalarField 83 false)
noncomputable def fifth:=Composition.machine fourth (scalarField 79 false)
noncomputable def sixth:=Composition.machine fifth (write (List.replicate 8 false))
noncomputable def machine:=Composition.machine sixth (scalarField 82 true)
def budget (C index value limit upper : ℕ):=
  fieldBudget false index+1+fieldBudget false C+1+fieldBudget true limit+1+fieldBudget false value+
    1+fieldBudget false C+1+fieldBudget false index+1+8+1+fieldBudget true upper

theorem packet_run (C index value limit upper B : ℕ) (out : List Bool)
    (H : Fin 84→ℕ) (A : Fin 84→List Bool)
    (hH : ∀ i∈([79,80,81,82,83] : List (Fin 84)),H i=0) (hHl : H 73=0)
    (hIndex : A 79=List.replicate index true) (hLimit : A 80=List.replicate limit true)
    (hValue : A 81=List.replicate value true) (hUpper : A 82=List.replicate upper true)
    (hC : A 83=List.replicate C true) (hAl : A 73=List.replicate B false)
    (bIndex : 2*index+4≤B) (bLimit : 2*limit+4≤B) (bValue : 2*value+4≤B)
    (bUpper : 2*upper+4≤B) (bC : 2*C+4≤B) :
    Appends machine (budget C index value limit upper) H A out
      (out++RecoveryBoundedRowReload.word (fields C index value limit upper)) := by
  have p0:=field_run 79 false index B out H A (by decide) (by decide)
    (hH 79 (by simp)) hHl hIndex hAl bIndex
  have p1:=field_run 83 false C B (out++field false index) H A (by decide) (by decide)
    (hH 83 (by simp)) hHl hC hAl bC
  have p2:=field_run 80 true limit B ((out++field false index)++field false C) H A (by decide) (by decide)
    (hH 80 (by simp)) hHl hLimit hAl bLimit
  have p3:=field_run 81 false value B (((out++field false index)++field false C)++field true limit)
    H A (by decide) (by decide) (hH 81 (by simp)) hHl hValue hAl bValue
  have p4:=field_run 83 false C B ((((out++field false index)++field false C)++field true limit)++field false value)
    H A (by decide) (by decide) (hH 83 (by simp)) hHl hC hAl bC
  have p5:=field_run 79 false index B (((((out++field false index)++field false C)++field true limit)++field false value)++field false C)
    H A (by decide) (by decide) (hH 79 (by simp)) hHl hIndex hAl bIndex
  have p6:=write_run (List.replicate 8 false)
    ((((((out++field false index)++field false C)++field true limit)++field false value)++field false C)++field false index) H A
  have p7:=field_run 82 true upper B
    (((((((out++field false index)++field false C)++field true limit)++field false value)++field false C)++field false index)++List.replicate 8 false)
    H A (by decide) (by decide) (hH 82 (by simp)) hHl hUpper hAl bUpper
  have whole:=((((((p0.join p1).join p2).join p3).join p4).join p5).join p6).join p7
  change Appends machine (budget C index value limit upper) H A out _ at whole
  rw [←packet_original]
  simpa only [packet,List.append_assoc] using whole

theorem packet_length (C index value limit upper : ℕ) :
    (RecoveryBoundedRowReload.word (fields C index value limit upper)).length=
      4*C+4*index+2*value+2*limit+2*upper+19 := by
  rw [←packet_original]
  simp only [packet,field,header,Bool.false_eq_true,↓reduceIte,List.nil_append,
    List.length_append,frame_length,List.length_replicate,List.length_cons,List.length_nil]
  omega

theorem budget_eq (C index value limit upper : ℕ) :
    budget C index value limit upper=8*C+8*index+4*value+4*limit+4*upper+82 := by
  simp only [budget,fieldBudget,header,Bool.false_eq_true,↓reduceIte,List.length_cons,List.length_nil]
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarPrototype
