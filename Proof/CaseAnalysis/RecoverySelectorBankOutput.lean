import Proof.CaseAnalysis.RecoverySelectorBudget

/-! The complete selector returns a reusable bank. This identifies every
original scalar and scratch tape; only the consumed outer stack has a
bounded false suffix before the already paid padding is applied. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorFinish
open LocalBitMultitape SourceInterfaces RepairRepresentation
open RecoveryBoundedSelectorLoop RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def foldPickData : Fin 43→Option (Fin 35):=![some 0,none,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,none,some 32,some 33,none,none,some 1,none,none,none,some 31,none,some 34]
theorem fold_pick (i : Fin 43) : RecoveryFocus.pick foldSlots i=foldPickData i := by
  fin_cases i
  · change RecoveryFocus.pick foldSlots (0 : Fin 43)=some (0 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 0
  · change RecoveryFocus.pick foldSlots (1 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(1 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (2 : Fin 43)=some (2 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 2
  · change RecoveryFocus.pick foldSlots (3 : Fin 43)=some (3 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 3
  · change RecoveryFocus.pick foldSlots (4 : Fin 43)=some (4 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 4
  · change RecoveryFocus.pick foldSlots (5 : Fin 43)=some (5 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 5
  · change RecoveryFocus.pick foldSlots (6 : Fin 43)=some (6 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 6
  · change RecoveryFocus.pick foldSlots (7 : Fin 43)=some (7 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 7
  · change RecoveryFocus.pick foldSlots (8 : Fin 43)=some (8 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 8
  · change RecoveryFocus.pick foldSlots (9 : Fin 43)=some (9 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 9
  · change RecoveryFocus.pick foldSlots (10 : Fin 43)=some (10 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 10
  · change RecoveryFocus.pick foldSlots (11 : Fin 43)=some (11 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 11
  · change RecoveryFocus.pick foldSlots (12 : Fin 43)=some (12 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 12
  · change RecoveryFocus.pick foldSlots (13 : Fin 43)=some (13 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 13
  · change RecoveryFocus.pick foldSlots (14 : Fin 43)=some (14 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 14
  · change RecoveryFocus.pick foldSlots (15 : Fin 43)=some (15 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 15
  · change RecoveryFocus.pick foldSlots (16 : Fin 43)=some (16 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 16
  · change RecoveryFocus.pick foldSlots (17 : Fin 43)=some (17 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 17
  · change RecoveryFocus.pick foldSlots (18 : Fin 43)=some (18 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 18
  · change RecoveryFocus.pick foldSlots (19 : Fin 43)=some (19 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 19
  · change RecoveryFocus.pick foldSlots (20 : Fin 43)=some (20 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 20
  · change RecoveryFocus.pick foldSlots (21 : Fin 43)=some (21 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 21
  · change RecoveryFocus.pick foldSlots (22 : Fin 43)=some (22 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 22
  · change RecoveryFocus.pick foldSlots (23 : Fin 43)=some (23 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 23
  · change RecoveryFocus.pick foldSlots (24 : Fin 43)=some (24 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 24
  · change RecoveryFocus.pick foldSlots (25 : Fin 43)=some (25 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 25
  · change RecoveryFocus.pick foldSlots (26 : Fin 43)=some (26 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 26
  · change RecoveryFocus.pick foldSlots (27 : Fin 43)=some (27 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 27
  · change RecoveryFocus.pick foldSlots (28 : Fin 43)=some (28 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 28
  · change RecoveryFocus.pick foldSlots (29 : Fin 43)=some (29 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 29
  · change RecoveryFocus.pick foldSlots (30 : Fin 43)=some (30 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 30
  · change RecoveryFocus.pick foldSlots (31 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(31 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (32 : Fin 43)=some (32 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 32
  · change RecoveryFocus.pick foldSlots (33 : Fin 43)=some (33 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 33
  · change RecoveryFocus.pick foldSlots (34 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(34 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (35 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(35 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (36 : Fin 43)=some (1 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 1
  · change RecoveryFocus.pick foldSlots (37 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(37 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (38 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(38 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (39 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(39 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (40 : Fin 43)=some (31 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 31
  · change RecoveryFocus.pick foldSlots (41 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(41 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (42 : Fin 43)=some (34 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 34

def folded (base : ℕ) (out : List Bool) (refs : List ℕ):=
  RecoveryBoundedNativeFoldLoop.State.iterate false refs.reverse ⟨base,0,0,out⟩

theorem fold_output_heads (base C total : ℕ) (out pre : List Bool) (refs : List ℕ) :
    (foldOutput base C total out pre refs).heads=
      Fin.addCases (m:=34) (n:=1) (motive:=fun _=>ℕ)
        (RecoveryBoundedNativeFold.heads (folded base out refs).out pre.length) (fun _=>1) := by
  change (Fin.addCases (m:=34) (n:=1) (motive:=fun _=>ℕ)
    (RecoveryBoundedNativeFold.heads (folded base out refs).out
      (pre++RecoveryBoundedNativeUnaryLoop.stackWords ([] : List ℕ).reverse).length) (fun _=>1))=_
  simp only [List.reverse_nil,RecoveryBoundedNativeUnaryLoop.stackWords,List.flatMap_nil,List.append_nil]

theorem fold_output_data (base C total : ℕ) (out pre : List Bool) (refs : List ℕ) :
    (foldOutput base C total out pre refs).tapes=
      fun j=>ZeroPadding.pad (foldCaps C j)
        (Fin.addCases (m:=34) (n:=1) (motive:=fun _=>List Bool)
          (RecoveryBoundedNativeFold.data 0 (folded base out refs).acc C false (folded base out refs).out
            (pre++List.replicate (folded base out refs).erased false) [])
          (fun _=>CompareMachine.word total) j) := by
  change (fun j=>ZeroPadding.pad (foldCaps C j)
    (Fin.addCases (m:=34) (n:=1) (motive:=fun _=>List Bool)
      (RecoveryBoundedNativeFold.data 0 (folded base out refs).acc C false (folded base out refs).out
        (pre++RecoveryBoundedNativeUnaryLoop.stackWords ([] : List ℕ).reverse++
          List.replicate (folded base out refs).erased false) [])
      (fun _=>CompareMachine.word total) j))=_
  simp only [List.reverse_nil,RecoveryBoundedNativeUnaryLoop.stackWords,List.flatMap_nil,List.append_nil]

def afterData (index base C D value limit total erased : ℕ) (out source pre : List Bool) (i : Fin 43) :=
  if i=40 then pre++List.replicate erased false else data index base C D value limit total out source pre i

def mergedHeads (out result stack pre : List Bool) (pos : ℕ) (i : Fin 43) :=
  match foldPickData i with
  | some j=>Fin.addCases (m:=34) (n:=1) (motive:=fun _=>ℕ)
      (RecoveryBoundedNativeFold.heads result pre.length) (fun _=>1) j
  | none=>heads out stack pos i

section
variable (out result stack pre : List Bool) (pos : ℕ)
private theorem head_port_0 : mergedHeads out result stack pre pos 0=heads result pre pos 0 := by rfl
private theorem head_port_1 : mergedHeads out result stack pre pos 1=heads result pre pos 1 := by
  change (0 : ℕ)=0
  rfl
private theorem head_port_2 : mergedHeads out result stack pre pos 2=heads result pre pos 2 := by rfl
private theorem head_port_3 : mergedHeads out result stack pre pos 3=heads result pre pos 3 := by rfl
private theorem head_port_4 : mergedHeads out result stack pre pos 4=heads result pre pos 4 := by rfl
private theorem head_port_5 : mergedHeads out result stack pre pos 5=heads result pre pos 5 := by rfl
private theorem head_port_6 : mergedHeads out result stack pre pos 6=heads result pre pos 6 := by rfl
private theorem head_port_7 : mergedHeads out result stack pre pos 7=heads result pre pos 7 := by rfl
private theorem head_port_8 : mergedHeads out result stack pre pos 8=heads result pre pos 8 := by rfl
private theorem head_port_9 : mergedHeads out result stack pre pos 9=heads result pre pos 9 := by rfl
private theorem head_port_10 : mergedHeads out result stack pre pos 10=heads result pre pos 10 := by rfl
private theorem head_port_11 : mergedHeads out result stack pre pos 11=heads result pre pos 11 := by rfl
private theorem head_port_12 : mergedHeads out result stack pre pos 12=heads result pre pos 12 := by rfl
private theorem head_port_13 : mergedHeads out result stack pre pos 13=heads result pre pos 13 := by rfl
private theorem head_port_14 : mergedHeads out result stack pre pos 14=heads result pre pos 14 := by rfl
private theorem head_port_15 : mergedHeads out result stack pre pos 15=heads result pre pos 15 := by rfl
private theorem head_port_16 : mergedHeads out result stack pre pos 16=heads result pre pos 16 := by rfl
private theorem head_port_17 : mergedHeads out result stack pre pos 17=heads result pre pos 17 := by rfl
private theorem head_port_18 : mergedHeads out result stack pre pos 18=heads result pre pos 18 := by rfl
private theorem head_port_19 : mergedHeads out result stack pre pos 19=heads result pre pos 19 := by rfl
private theorem head_port_20 : mergedHeads out result stack pre pos 20=heads result pre pos 20 := by rfl
private theorem head_port_21 : mergedHeads out result stack pre pos 21=heads result pre pos 21 := by rfl
private theorem head_port_22 : mergedHeads out result stack pre pos 22=heads result pre pos 22 := by rfl
private theorem head_port_23 : mergedHeads out result stack pre pos 23=heads result pre pos 23 := by rfl
private theorem head_port_24 : mergedHeads out result stack pre pos 24=heads result pre pos 24 := by rfl
private theorem head_port_25 : mergedHeads out result stack pre pos 25=heads result pre pos 25 := by rfl
private theorem head_port_26 : mergedHeads out result stack pre pos 26=heads result pre pos 26 := by rfl
private theorem head_port_27 : mergedHeads out result stack pre pos 27=heads result pre pos 27 := by rfl
private theorem head_port_28 : mergedHeads out result stack pre pos 28=heads result pre pos 28 := by rfl
private theorem head_port_29 : mergedHeads out result stack pre pos 29=heads result pre pos 29 := by rfl
private theorem head_port_30 : mergedHeads out result stack pre pos 30=heads result pre pos 30 := by rfl
private theorem head_port_31 : mergedHeads out result stack pre pos 31=heads result pre pos 31 := by
  change (0 : ℕ)=0
  rfl
private theorem head_port_32 : mergedHeads out result stack pre pos 32=heads result pre pos 32 := by rfl
private theorem head_port_33 : mergedHeads out result stack pre pos 33=heads result pre pos 33 := by rfl
private theorem head_port_34 : mergedHeads out result stack pre pos 34=heads result pre pos 34 := by
  change (0 : ℕ)=0
  rfl
private theorem head_port_35 : mergedHeads out result stack pre pos 35=heads result pre pos 35 := by
  change (1 : ℕ)=1
  rfl
private theorem head_port_36 : mergedHeads out result stack pre pos 36=heads result pre pos 36 := by rfl
private theorem head_port_37 : mergedHeads out result stack pre pos 37=heads result pre pos 37 := by
  change (pos : ℕ)=pos
  rfl
private theorem head_port_38 : mergedHeads out result stack pre pos 38=heads result pre pos 38 := by
  change (0 : ℕ)=0
  rfl
private theorem head_port_39 : mergedHeads out result stack pre pos 39=heads result pre pos 39 := by
  change (0 : ℕ)=0
  rfl
private theorem head_port_40 : mergedHeads out result stack pre pos 40=heads result pre pos 40 := by rfl
private theorem head_port_41 : mergedHeads out result stack pre pos 41=heads result pre pos 41 := by
  change (0 : ℕ)=0
  rfl
private theorem head_port_42 : mergedHeads out result stack pre pos 42=heads result pre pos 42 := by rfl
theorem heads_install : mergedHeads out result stack pre pos=heads result pre pos := by
  funext i
  fin_cases i
  · exact head_port_0 out result stack pre pos
  · exact head_port_1 out result stack pre pos
  · exact head_port_2 out result stack pre pos
  · exact head_port_3 out result stack pre pos
  · exact head_port_4 out result stack pre pos
  · exact head_port_5 out result stack pre pos
  · exact head_port_6 out result stack pre pos
  · exact head_port_7 out result stack pre pos
  · exact head_port_8 out result stack pre pos
  · exact head_port_9 out result stack pre pos
  · exact head_port_10 out result stack pre pos
  · exact head_port_11 out result stack pre pos
  · exact head_port_12 out result stack pre pos
  · exact head_port_13 out result stack pre pos
  · exact head_port_14 out result stack pre pos
  · exact head_port_15 out result stack pre pos
  · exact head_port_16 out result stack pre pos
  · exact head_port_17 out result stack pre pos
  · exact head_port_18 out result stack pre pos
  · exact head_port_19 out result stack pre pos
  · exact head_port_20 out result stack pre pos
  · exact head_port_21 out result stack pre pos
  · exact head_port_22 out result stack pre pos
  · exact head_port_23 out result stack pre pos
  · exact head_port_24 out result stack pre pos
  · exact head_port_25 out result stack pre pos
  · exact head_port_26 out result stack pre pos
  · exact head_port_27 out result stack pre pos
  · exact head_port_28 out result stack pre pos
  · exact head_port_29 out result stack pre pos
  · exact head_port_30 out result stack pre pos
  · exact head_port_31 out result stack pre pos
  · exact head_port_32 out result stack pre pos
  · exact head_port_33 out result stack pre pos
  · exact head_port_34 out result stack pre pos
  · exact head_port_35 out result stack pre pos
  · exact head_port_36 out result stack pre pos
  · exact head_port_37 out result stack pre pos
  · exact head_port_38 out result stack pre pos
  · exact head_port_39 out result stack pre pos
  · exact head_port_40 out result stack pre pos
  · exact head_port_41 out result stack pre pos
  · exact head_port_42 out result stack pre pos
end

theorem endBank_heads (index base C D value limit total pos : ℕ) (out source pre : List Bool) (refs : List ℕ) :
    (endBank index base C D value limit total pos out source pre refs).heads=
      heads (folded base out refs).out pre pos := by
  simp only [endBank,RecoveryFocus.config,fold_pick,fold_output_heads]
  funext i
  fin_cases i
  all_goals first | (change (0 : ℕ)=0; rfl) | (change (1 : ℕ)=1; rfl) |
    (change (pos : ℕ)=pos; rfl) |
    (change (folded base out refs).out.length=(folded base out refs).out.length; rfl) |
    (change pre.length=pre.length; rfl)

theorem endBank_tapes (index base C D value limit total pos : ℕ) (out source pre : List Bool) (refs : List ℕ)
    (hC : 1 ≤ C) :
    (endBank index base C D value limit total pos out source pre refs).tapes=
      afterData index (folded base out refs).acc C D value limit total (folded base out refs).erased
        (folded base out refs).out source pre := by
  simp only [endBank,RecoveryFocus.config,fold_pick,fold_output_data]
  funext i
  fin_cases i
  all_goals first | rfl | exact ZeroPadding.pad_zero _ | exact pad_false C hC

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorFinish
