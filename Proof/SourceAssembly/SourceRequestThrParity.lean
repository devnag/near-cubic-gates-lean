import Proof.SourceAssembly.SourceCircuitFrame

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

namespace NearCubicWires.SourceRequest.Gen.ParityQuery
open SourceAssemblyParityQuery (slots slots_inj arity_eq)

/-- The generic prefix: only the q-templates (`ParityPrep`) are produced; the bitmap is given. -/
def machine:=RecoveryFocus.machine slots SourceAssemblyParityPrep.machine
def input (q Q : Nat) (bm : List Bool) : Fin 137→List Bool:=fun i=>
  if i=3 then ZeroPadding.pad Q bm else if i=13 then UnaryTemplate.tape q else []
def budget (q Q : Nat) (bm : List Bool):=SourceAssemblyParityPrep.budget q

theorem run (q Q : Nat) (bm : List Bool) :
    ∃ A,Step machine (budget q Q bm) (fun _=>0) (input q Q bm) (fun _=>0) A ∧
      A 3=ZeroPadding.pad Q bm ∧
      A 131=frame (natWord q) ∧A 133=List.replicate (Capacity.value q) false ∧
      A 135=CompareMachine.word q ∧A 101=List.replicate (Capacity.value q) true ∧
      A 13=UnaryTemplate.tape q := by
  obtain ⟨B,hb,b0,b41,b43,b45,b11⟩:=SourceAssemblyParityPrep.run q
  have selected : ∀ i,input q Q bm (slots i)=SourceAssemblyParityPrep.input q i := by
    intro i
    by_cases hi:i=0
    · subst i
      simp only [input,slots,if_true]
      rw [if_neg (by decide)]
      exact arity_eq q
    · have hv : (slots i).val=90+i.val := by simp [slots,hi]
      have h3 : slots i≠3 := fun e => by have := congrArg Fin.val e; rw [hv] at this; simp at this; omega
      have h13 : slots i≠13 := fun e => by have := congrArg Fin.val e; rw [hv] at this; simp at this; omega
      simp only [input,h3,h13,if_false,SourceAssemblyParityPrep.input,hi]
  obtain ⟨s,hs,st,sh,ss⟩:=hb.focus slots slots_inj (input q Q bm) selected
  have stepB : Step machine (SourceAssemblyParityPrep.budget q)
      (fun _=>0) (input q Q bm) (fun _=>0) (install slots (input q Q bm) B):=⟨s,hs,funext sh,st,ss⟩
  refine ⟨install slots (input q Q bm) B,stepB,?_,?_,?_,?_,?_,?_⟩
  · rw [install_other slots _ B 3 (by decide)]; simp [input]
  · exact (install_slot slots slots_inj _ B 41).trans b41
  · exact (install_slot slots slots_inj _ B 43).trans b43
  · exact (install_slot slots slots_inj _ B 45).trans b45
  · exact (install_slot slots slots_inj _ B 11).trans b11
  · exact (install_slot slots slots_inj _ B 0).trans (b0.trans (arity_eq q).symm)

end NearCubicWires.SourceRequest.Gen.ParityQuery

namespace NearCubicWires.SourceRequest.Gen.SymmetricQuery
open SourceAssemblySymmetricQuery (slots slots_inj last capacity_fit)

def first:=TapeEmbedding.machine 4 Gen.ParityQuery.machine

def machine:=Composition.machine first last

def input (q Q : Nat) (bm : List Bool) : Fin 141→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (Gen.ParityQuery.input q Q bm) (fun _ : Fin 4=>[])

def budget (q Q : Nat) (bm : List Bool):=
  Gen.ParityQuery.budget q Q bm+1+SourceAssemblySymmetricCold.budget q

def bitmap (q Q : Nat) (bm : List Bool):=ZeroPadding.pad Q bm

def finalHeads (q Q : Nat) (bm : List Bool):=
  dockH slots (fun _=>0) (SourceAssemblySymmetricCold.heads q (bitmap q Q bm) q)

end NearCubicWires.SourceRequest.Gen.SymmetricQuery

namespace NearCubicWires.SourceRequest.Gen.SymmetricHeaderQuery
open SourceAssemblySymmetricHeaderQuery (slots slots_inj fresh slots_fresh last)

def first:=TapeEmbedding.machine 25 Gen.SymmetricQuery.machine

def machine:=Composition.machine first last

def input (q Q : Nat) (bm : List Bool) : Fin 166→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (Gen.SymmetricQuery.input q Q bm) (fun _ : Fin 25=>[])

def count (q Q : Nat) (bm : List Bool):=
  (SourceAssemblySymmetricScan.selected (Gen.SymmetricQuery.bitmap q Q bm) q).length

def beforeHeads (q Q : Nat) (bm : List Bool) : Fin 166→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (Gen.SymmetricQuery.finalHeads q Q bm) (fun _ : Fin 25=>0)

def finalHeads (q Q : Nat) (bm : List Bool):=dockH slots (beforeHeads q Q bm) (fun _=>0)

def budget (q Q : Nat) (bm : List Bool):=
  Gen.SymmetricQuery.budget q Q bm+1+
    SourceAssemblySymmetricHeader.budget (count q Q bm)

theorem selected_heads (q Q : Nat) (bm : List Bool) (i : Fin 26) :
    beforeHeads q Q bm (slots i)=SourceAssemblySymmetricHeader.heads i := by
  by_cases hi:i=3
  · subst i
    change beforeHeads q Q bm ((140 : Fin 141).castAdd 25)=1
    rw [beforeHeads,Fin.addCases_left]
    change dockH SourceAssemblySymmetricQuery.slots _ _
      (SourceAssemblySymmetricQuery.slots 7)=1
    rw [dockH_slot _ SourceAssemblySymmetricQuery.slots_inj]
    rfl
  · rw [slots_fresh i hi]
    simp only [beforeHeads,Fin.addCases_right,SourceAssemblySymmetricHeader.heads,hi,if_false]

end NearCubicWires.SourceRequest.Gen.SymmetricHeaderQuery

namespace NearCubicWires.SourceRequest.Gen.ThresholdHeader

open NearCubicWires.SourceRequest.Gen.SymmetricQuery in
open SourceAssemblySymmetricQuery (slots slots_inj last capacity_fit) in
theorem selected_run (q Q : Nat) (bm : List Bool) :
    ∃ A,Step machine (budget q Q bm) (fun _=>0) (input q Q bm) (finalHeads q Q bm) A ∧
      A 3=bitmap q Q bm ∧A 131=frame (natWord q) ∧A 135=CompareMachine.word q ∧
      A 140=CompareMachine.word (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 101=List.replicate (Capacity.value q) true := by
  obtain ⟨A,ha,h3,h131,h133,h135,h101,h13⟩:=Gen.ParityQuery.run q Q bm
  let bank : Fin 141→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 4=>[])
  have stepA : Step first (Gen.ParityQuery.budget q Q bm)
      (fun _=>0) (input q Q bm) (fun _=>0) bank :=
    ((ha.embed (fun _ : Fin 4=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl).congr
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have selected : ∀ i,bank (slots i)=SourceAssemblySymmetricCold.input
      q (Capacity.value q) (bitmap q Q bm) i := by
    intro i;fin_cases i
    · exact h13
    · rfl
    · exact h131
    · rfl
    · rfl
    · exact h133
    · exact h3
    · rfl
    · exact h135
  have hb:=SourceAssemblySymmetricCold.run q (Capacity.value q)
    (bitmap q Q bm) (capacity_fit q)
  let out:=SourceAssemblySymmetricCold.words q (Capacity.value q) (bitmap q Q bm) q
  have lastStep:=hb.dock slots slots_inj (fun _=>0) bank (by intro i;rfl) selected
  refine ⟨install slots bank out,stepA.seq lastStep,?_,?_,?_,?_,?_⟩
  · exact install_slot slots slots_inj bank out 6
  · exact install_slot slots slots_inj bank out 2
  · exact install_slot slots slots_inj bank out 8
  · exact install_slot slots slots_inj bank out 7
  · exact (install_other slots bank out 101 (by decide)).trans h101

open NearCubicWires.SourceRequest.Gen.SymmetricHeaderQuery in
open SourceAssemblySymmetricHeaderQuery (slots slots_inj fresh slots_fresh last) in
theorem run (q Q : Nat) (bm : List Bool) :
    ∃ A,Step machine (budget q Q bm) (fun _=>0) (input q Q bm) (finalHeads q Q bm) A ∧
      A 3=Gen.SymmetricQuery.bitmap q Q bm ∧A 131=frame (natWord q) ∧
      A 135=CompareMachine.word q ∧A 140=CompareMachine.word (count q Q bm) ∧
      A 101=List.replicate (Capacity.value q) true ∧A 161=natWord (count q Q bm) ∧
      A 164=frame (natWord (count q Q bm)) := by
  obtain ⟨A,ha,h3,h131,h135,h140,h101⟩:=selected_run q Q bm
  let bank : Fin 166→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 25=>[])
  have firstStep : Step first (Gen.SymmetricQuery.budget q Q bm)
      (fun _=>0) (input q Q bm) (beforeHeads q Q bm) bank :=
    (ha.embed (fun _ : Fin 25=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  obtain ⟨B,hb,_top,header,framed,driver⟩:=SourceAssemblySymmetricHeader.run (count q Q bm)
  have selected : ∀ i,bank (slots i)=SourceAssemblySymmetricHeader.input (count q Q bm) i := by
    intro i
    by_cases hi:i=3
    · subst i;exact h140
    · rw [slots_fresh i hi]
      simp only [bank,Fin.addCases_right,SourceAssemblySymmetricHeader.input,hi,if_false]
  have lastStep:=hb.dock slots slots_inj (beforeHeads q Q bm) bank (selected_heads q Q bm) selected
  refine ⟨_,firstStep.seq lastStep,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other slots bank B 3 (by decide)).trans h3
  · exact (install_other slots bank B 131 (by decide)).trans h131
  · exact (install_other slots bank B 135 (by decide)).trans h135
  · exact (install_slot slots slots_inj bank B 3).trans driver
  · exact (install_other slots bank B 101 (by decide)).trans h101
  · exact (install_slot slots slots_inj bank B 21).trans header
  · exact (install_slot slots slots_inj bank B 24).trans framed

end NearCubicWires.SourceRequest.Gen.ThresholdHeader

namespace NearCubicWires.SourceRequest.Gen.ThresholdCache
open SourceAssemblyThresholdCache (slots last)

def first:=TapeEmbedding.machine 4 Gen.SymmetricHeaderQuery.machine

def machine:=Composition.machine first last

def input (q Q : Nat) (bm : List Bool) : Fin 170→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (Gen.SymmetricHeaderQuery.input q Q bm) (fun _ : Fin 4=>[])

def beforeHeads (q Q : Nat) (bm : List Bool) : Fin 170→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (Gen.SymmetricHeaderQuery.finalHeads q Q bm) (fun _ : Fin 4=>0)

def finalHeads (q Q : Nat) (bm : List Bool):=dockH slots (beforeHeads q Q bm) SourceAssemblyThresholdBitmap.readyHeads

def budget (q Q : Nat) (bm : List Bool):=
  Gen.SymmetricHeaderQuery.budget q Q bm+1+SourceAssemblyThresholdBitmap.budget q

def bits (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) := bm

theorem bits_length (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) : (bits q Q bm hbm).length=q:=hbm

theorem before_heads (q Q : Nat) (bm : List Bool) (i : Fin 7) :
    beforeHeads q Q bm (slots i)=SourceAssemblyThresholdBitmap.heads q i := by
  fin_cases i
  · change Gen.SymmetricHeaderQuery.finalHeads q Q bm 3=q
    rw [Gen.SymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 3 (by decide)]
    change Gen.SymmetricHeaderQuery.beforeHeads q Q bm ((3 : Fin 141).castAdd 25)=_
    rw [Gen.SymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_slot _ SourceAssemblySymmetricQuery.slots_inj _ _ 6
  · change Gen.SymmetricHeaderQuery.finalHeads q Q bm 135=1
    rw [Gen.SymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 135 (by decide)]
    change Gen.SymmetricHeaderQuery.beforeHeads q Q bm ((135 : Fin 141).castAdd 25)=_
    rw [Gen.SymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_slot _ SourceAssemblySymmetricQuery.slots_inj _ _ 8
  · change Gen.SymmetricHeaderQuery.finalHeads q Q bm 101=0
    rw [Gen.SymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 101 (by decide)]
    change Gen.SymmetricHeaderQuery.beforeHeads q Q bm ((101 : Fin 141).castAdd 25)=0
    rw [Gen.SymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_other _ _ _ 101 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl

theorem run (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) :
    ∃ A,Step machine (budget q Q bm) (fun _=>0) (input q Q bm) (finalHeads q Q bm) A ∧
      A 131=frame (natWord q) ∧A 101=List.replicate (Capacity.value q) true ∧
      A 140=CompareMachine.word (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 161=natWord (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 164=frame (natWord (Gen.SymmetricHeaderQuery.count q Q bm)) ∧
      A 166=frame (weights (bits q Q bm hbm)) ∧A 167=frame (bits q Q bm hbm) := by
  obtain ⟨A,ha,h3,h131,h135,h140,h101,h161,h164⟩:=Gen.ThresholdHeader.run q Q bm
  let bank : Fin 170→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 4=>[])
  have firstStep : Step first (Gen.SymmetricHeaderQuery.budget q Q bm)
      (fun _=>0) (input q Q bm) (beforeHeads q Q bm) bank :=
    (ha.embed (fun _ : Fin 4=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have selected : ∀ i,bank (slots i)=SourceAssemblyThresholdBitmap.input Q q (bits q Q bm hbm) i := by
    intro i;fin_cases i
    · exact h3
    · exact h135
    · exact h101
    · rfl
    · rfl
    · rfl
    · rfl
  obtain ⟨k,_hk,raw⟩:=SourceAssemblyThresholdBitmap.run Q q (bits q Q bm hbm) (bits_length q Q bm hbm)
  have lastStep:=raw.dock slots (by decide) (beforeHeads q Q bm) bank (before_heads q Q bm) selected
  refine ⟨_,firstStep.seq lastStep,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other slots bank _ 131 (by decide)).trans h131
  · exact install_slot slots (by decide) bank _ 2
  · exact (install_other slots bank _ 140 (by decide)).trans h140
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact (install_other slots bank _ 164 (by decide)).trans h164
  · exact install_slot slots (by decide) bank _ 3
  · exact install_slot slots (by decide) bank _ 4

end NearCubicWires.SourceRequest.Gen.ThresholdCache

namespace NearCubicWires.SourceRequest.Gen.ThresholdQuery
open SourceAssemblyThresholdQuery (slots slots_inj oldSlots last)

def first:=TapeEmbedding.machine 33 Gen.ThresholdCache.machine

def machine:=Composition.machine first last

def input (q Q : Nat) (bm : List Bool) : Fin 203→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (Gen.ThresholdCache.input q Q bm) (fun _ : Fin 33=>[])

def beforeHeads (q Q : Nat) (bm : List Bool) : Fin 203→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (Gen.ThresholdCache.finalHeads q Q bm) (fun _ : Fin 33=>0)

def finalHeads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q):=
  dockH slots (beforeHeads q Q bm) (SourceAssemblyThresholdCold.heads q
    (Gen.ThresholdCache.bits q Q bm hbm) (Gen.SymmetricHeaderQuery.count q Q bm))

def budget (q Q : Nat) (bm : List Bool):=
  Gen.ThresholdCache.budget q Q bm+1+
    SourceAssemblyThresholdCold.budget q (Gen.SymmetricHeaderQuery.count q Q bm)

theorem count_le (q Q : Nat) (bm : List Bool) : Gen.SymmetricHeaderQuery.count q Q bm≤q := by
  exact (List.length_filter_le _ _).trans List.length_range.le

theorem old_heads (q Q : Nat) (bm : List Bool) (i : Fin 5) :
    Gen.ThresholdCache.finalHeads q Q bm (oldSlots i)=0 := by
  fin_cases i
  · exact dockH_slot _ (by decide) _ _ 2
  · change Gen.ThresholdCache.finalHeads q Q bm 131=0
    rw [Gen.ThresholdCache.finalHeads,dockH_other _ _ _ 131 (by decide)]
    change Gen.SymmetricHeaderQuery.finalHeads q Q bm 131=0
    rw [Gen.SymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 131 (by decide)]
    change Gen.SymmetricHeaderQuery.beforeHeads q Q bm ((131 : Fin 141).castAdd 25)=0
    rw [Gen.SymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_slot _ SourceAssemblySymmetricQuery.slots_inj _ _ 2
  · exact dockH_slot _ (by decide) _ _ 3
  · exact dockH_slot _ (by decide) _ _ 4
  · change Gen.ThresholdCache.finalHeads q Q bm 140=0
    rw [Gen.ThresholdCache.finalHeads,dockH_other _ _ _ 140 (by decide)]
    change Gen.SymmetricHeaderQuery.finalHeads q Q bm 140=0
    exact dockH_slot _ SourceAssemblySymmetricHeaderQuery.slots_inj _ _ 3

theorem selected_heads (q Q : Nat) (bm : List Bool) (i : Fin 33) : beforeHeads q Q bm (slots i)=0 := by
  by_cases h22:i=22
  · subst i;exact old_heads q Q bm 0
  by_cases h26:i=26
  · subst i;exact old_heads q Q bm 1
  by_cases h27:i=27
  · subst i;exact old_heads q Q bm 2
  by_cases h28:i=28
  · subst i;exact old_heads q Q bm 3
  by_cases h32:i=32
  · subst i;exact old_heads q Q bm 4
  simp only [slots,h22,h26,h27,h28,h32,if_false,beforeHeads,Fin.addCases_right]

theorem run_retained (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) :
    ∃ A,Step machine (budget q Q bm) (fun _=>0) (input q Q bm) (finalHeads q Q bm hbm) A ∧
      A 199=SourceAssemblyThresholdLoop.outputs q
        (Gen.ThresholdCache.bits q Q bm hbm) (Gen.SymmetricHeaderQuery.count q Q bm) 0 ∧
      A 200=SourceAssemblyThresholdLoop.outputs q
        (Gen.ThresholdCache.bits q Q bm hbm) (Gen.SymmetricHeaderQuery.count q Q bm) 1 ∧
      A 140=CompareMachine.word (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 161=natWord (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 164=frame (natWord (Gen.SymmetricHeaderQuery.count q Q bm)) ∧
      A 201=List.replicate (Capacity.value q) false ∧A 101=List.replicate (Capacity.value q) true ∧ A 131=frame (natWord q) := by
  obtain ⟨A,ha,h131,h101,h140,h161,h164,h166,h167⟩:=Gen.ThresholdCache.run q Q bm hbm
  let bank : Fin 203→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 33=>[])
  have firstStep : Step first (Gen.ThresholdCache.budget q Q bm)
      (fun _=>0) (input q Q bm) (beforeHeads q Q bm) bank :=
    (ha.embed (fun _ : Fin 33=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have selected : ∀ i,bank (slots i)=SourceAssemblyThresholdCold.input q
      (Gen.SymmetricHeaderQuery.count q Q bm) (Gen.ThresholdCache.bits q Q bm hbm) i := by
    intro i
    by_cases h22:i=22
    · subst i;exact h101
    by_cases h26:i=26
    · subst i;exact h131
    by_cases h27:i=27
    · subst i;exact h166
    by_cases h28:i=28
    · subst i;exact h167
    by_cases h32:i=32
    · subst i;exact h140
    simp only [slots,h22,h26,h27,h28,h32,if_false,bank,Fin.addCases_right,SourceAssemblyThresholdCold.input]
  have raw:=SourceAssemblyThresholdCold.run q (Gen.SymmetricHeaderQuery.count q Q bm)
    (Gen.ThresholdCache.bits q Q bm hbm) (count_le q Q bm)
    (Gen.ThresholdCache.bits_length q Q bm hbm)
  have lastStep:=raw.dock slots slots_inj (beforeHeads q Q bm) bank (selected_heads q Q bm) selected
  refine ⟨_,firstStep.seq lastStep,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact install_slot slots slots_inj bank _ 29
  · exact install_slot slots slots_inj bank _ 30
  · exact install_slot slots slots_inj bank _ 32
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact (install_other slots bank _ 164 (by decide)).trans h164
  · exact install_slot slots slots_inj bank _ 31
  · exact install_slot slots slots_inj bank _ 22

  · exact install_slot slots slots_inj bank _ 26

end NearCubicWires.SourceRequest.Gen.ThresholdQuery

namespace NearCubicWires.SourceRequest.Gen.ThresholdTopQuery
open SourceAssemblyThresholdTopQuery (slots last)

def first:=TapeEmbedding.machine 3 Gen.ThresholdQuery.machine

def machine:=Composition.machine first last

def input (q Q : Nat) (bm : List Bool) : Fin 206→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (Gen.ThresholdQuery.input q Q bm) (fun _ : Fin 3=>[])

def beforeHeads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) : Fin 206→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (Gen.ThresholdQuery.finalHeads q Q bm hbm) (fun _ : Fin 3=>0)

def finalHeads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q):=
  dockH slots (beforeHeads q Q bm hbm) (SourceAssemblyThresholdTop.H
    (SourceAssemblyThresholdTop.finalOut (Gen.SymmetricHeaderQuery.count q Q bm)))

def budget (q Q : Nat) (bm : List Bool):=
  Gen.ThresholdQuery.budget q Q bm+1+
    SourceAssemblyThresholdTop.budget (Gen.SymmetricHeaderQuery.count q Q bm)

theorem selected_heads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) (i : Fin 6) :
    beforeHeads q Q bm hbm (slots i)=SourceAssemblyThresholdTop.inputHeads i := by
  fin_cases i
  · change Gen.ThresholdQuery.finalHeads q Q bm hbm 164=0
    rw [Gen.ThresholdQuery.finalHeads,dockH_other _ _ _ 164 (by decide)]
    change Gen.ThresholdCache.finalHeads q Q bm 164=0
    rw [Gen.ThresholdCache.finalHeads,dockH_other _ _ _ 164 (by decide)]
    change Gen.SymmetricHeaderQuery.finalHeads q Q bm 164=0
    exact dockH_slot _ SourceAssemblySymmetricHeaderQuery.slots_inj _ _ 24
  · rfl
  · rfl
  · rfl
  · change Gen.ThresholdQuery.finalHeads q Q bm hbm (SourceAssemblyThresholdQuery.slots 32)=1
    rw [Gen.ThresholdQuery.finalHeads,dockH_slot _ SourceAssemblyThresholdQuery.slots_inj _ _ 32]
    rfl
  · change Gen.ThresholdQuery.finalHeads q Q bm hbm (SourceAssemblyThresholdQuery.slots 31)=0
    rw [Gen.ThresholdQuery.finalHeads,dockH_slot _ SourceAssemblyThresholdQuery.slots_inj _ _ 31]
    rfl

theorem run_retained (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) :
    ∃ A,Step machine (budget q Q bm) (fun _=>0) (input q Q bm) (finalHeads q Q bm hbm) A ∧
      A 199=SourceAssemblyThresholdLoop.outputs q
        (Gen.ThresholdCache.bits q Q bm hbm) (Gen.SymmetricHeaderQuery.count q Q bm) 0 ∧
      A 200=SourceAssemblyThresholdLoop.outputs q
        (Gen.ThresholdCache.bits q Q bm hbm) (Gen.SymmetricHeaderQuery.count q Q bm) 1 ∧
      A 140=CompareMachine.word (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 161=natWord (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 204=frame (SourceAssemblyThresholdTop.payload (Gen.SymmetricHeaderQuery.count q Q bm)) ∧
      A 101=List.replicate (Capacity.value q) true ∧ A 131=frame (natWord q) := by
  obtain ⟨A,ha,h199,h200,h140,h161,h164,h201,h101,h131⟩:=Gen.ThresholdQuery.run_retained q Q bm hbm
  let bank : Fin 206→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 3=>[])
  have firstStep : Step first (Gen.ThresholdQuery.budget q Q bm)
      (fun _=>0) (input q Q bm) (beforeHeads q Q bm hbm) bank :=
    (ha.embed (fun _ : Fin 3=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  let n:=Gen.SymmetricHeaderQuery.count q Q bm
  have hn:n≤q:=Gen.ThresholdQuery.count_le q Q bm
  have hlen:2*(natWord n).length+1≤Capacity.value q := by
    have hh:natBitLength n≤n+1:=Nat.add_le_add_right (Nat.log_le_self 2 n) 1
    rw [DecompositionSource.natWord_length];unfold Capacity.value;nlinarith
  have selected : ∀ i,bank (slots i)=SourceAssemblyThresholdTop.input n (Capacity.value q) i := by
    intro i;fin_cases i
    · exact h164
    · rfl
    · rfl
    · rfl
    · exact h140
    · exact h201
  have lastStep:=(SourceAssemblyThresholdTop.run n (Capacity.value q) hlen).dock slots (by decide)
    (beforeHeads q Q bm hbm) bank (selected_heads q Q bm hbm) selected
  refine ⟨_,firstStep.seq lastStep,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other slots bank _ 199 (by decide)).trans h199
  · exact (install_other slots bank _ 200 (by decide)).trans h200
  · exact install_slot slots (by decide) bank _ 4
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact (install_slot slots (by decide) bank _ 2).trans (SourceAssemblyThresholdTop.final_exact n)
  · exact (install_other slots bank _ 101 (by decide)).trans h101

  · exact (install_other slots bank _ 131 (by decide)).trans h131

end NearCubicWires.SourceRequest.Gen.ThresholdTopQuery

namespace NearCubicWires.SourceRequest.Gen.ThresholdReady
open SourceAssemblyThresholdReady (slots last)

def streams (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) : Fin 3→List Bool:=
  ![SourceAssemblyThresholdLoop.outputs q (Gen.ThresholdCache.bits q Q bm hbm)
      (Gen.SymmetricHeaderQuery.count q Q bm) 0,
    SourceAssemblyThresholdLoop.outputs q (Gen.ThresholdCache.bits q Q bm hbm)
      (Gen.SymmetricHeaderQuery.count q Q bm) 1,
    frame (SourceAssemblyThresholdTop.payload (Gen.SymmetricHeaderQuery.count q Q bm))]

def first:=TapeEmbedding.machine 4 Gen.ThresholdTopQuery.machine

def machine:=Composition.machine first last

def input (q Q : Nat) (bm : List Bool) : Fin 210→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (Gen.ThresholdTopQuery.input q Q bm) (fun _ : Fin 4=>[])

def beforeHeads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) : Fin 210→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (Gen.ThresholdTopQuery.finalHeads q Q bm hbm) (fun _ : Fin 4=>0)

def finalHeads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q):=
  dockH slots (beforeHeads q Q bm hbm) (fun _=>0)

def budget (q Q : Nat) (bm : List Bool):=
  Gen.ThresholdTopQuery.budget q Q bm+1+2*Capacity.value q+2

theorem before_heads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) (i : Fin 5) :
    beforeHeads q Q bm hbm (slots i)=SourceAssemblyClear.join
      (fun j=>(streams q Q bm hbm j).length) 0 0 i := by
  fin_cases i
  · change Gen.ThresholdTopQuery.finalHeads q Q bm hbm 199=_
    rw [Gen.ThresholdTopQuery.finalHeads,dockH_other _ _ _ 199 (by decide)]
    change Gen.ThresholdQuery.finalHeads q Q bm hbm (SourceAssemblyThresholdQuery.slots 29)=_
    rw [Gen.ThresholdQuery.finalHeads,dockH_slot _ SourceAssemblyThresholdQuery.slots_inj _ _ 29]
    rfl
  · change Gen.ThresholdTopQuery.finalHeads q Q bm hbm 200=_
    rw [Gen.ThresholdTopQuery.finalHeads,dockH_other _ _ _ 200 (by decide)]
    change Gen.ThresholdQuery.finalHeads q Q bm hbm (SourceAssemblyThresholdQuery.slots 30)=_
    rw [Gen.ThresholdQuery.finalHeads,dockH_slot _ SourceAssemblyThresholdQuery.slots_inj _ _ 30]
    rfl
  · change Gen.ThresholdTopQuery.finalHeads q Q bm hbm (SourceAssemblyThresholdTopQuery.slots 2)=_
    rw [Gen.ThresholdTopQuery.finalHeads,dockH_slot SourceAssemblyThresholdTopQuery.slots (by decide) _ _ 2]
    change (SourceAssemblyThresholdTop.finalOut _ 0).length=_
    rw [SourceAssemblyThresholdTop.final_exact]
    rfl
  · change Gen.ThresholdTopQuery.finalHeads q Q bm hbm 101=0
    rw [Gen.ThresholdTopQuery.finalHeads,dockH_other _ _ _ 101 (by decide)]
    change Gen.ThresholdQuery.finalHeads q Q bm hbm (SourceAssemblyThresholdQuery.slots 22)=0
    rw [Gen.ThresholdQuery.finalHeads,dockH_slot _ SourceAssemblyThresholdQuery.slots_inj _ _ 22]
    rfl
  · rfl

theorem run_retained (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) :
    ∃ A,Step machine (budget q Q bm) (fun _=>0) (input q Q bm) (finalHeads q Q bm hbm) A ∧
      A 199=streams q Q bm hbm 0 ∧A 200=streams q Q bm hbm 1 ∧A 204=streams q Q bm hbm 2 ∧
      A 140=CompareMachine.word (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 161=natWord (Gen.SymmetricHeaderQuery.count q Q bm) ∧
      A 207=[] ∧A 208=[] ∧A 209=[] ∧ A 131=frame (natWord q) := by
  obtain ⟨A,ha,h199,h200,h140,h161,h204,h101,h131⟩:=Gen.ThresholdTopQuery.run_retained q Q bm hbm
  let bank : Fin 210→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 4=>[])
  have firstStep : Step first (Gen.ThresholdTopQuery.budget q Q bm)
      (fun _=>0) (input q Q bm) (beforeHeads q Q bm hbm) bank :=
    (ha.embed (fun _ : Fin 4=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have hlen : ∀ i,(streams q Q bm hbm i).length≤Capacity.value q := by
    intro i;fin_cases i
    · exact SourceAssemblyThresholdBounds.outputs_bound _ _ _
        (Gen.ThresholdQuery.count_le q Q bm) (Gen.ThresholdCache.bits_length q Q bm hbm) 0
    · exact SourceAssemblyThresholdBounds.outputs_bound _ _ _
        (Gen.ThresholdQuery.count_le q Q bm) (Gen.ThresholdCache.bits_length q Q bm hbm) 1
    · exact SourceAssemblyThresholdBounds.top_bound _ _ (Gen.ThresholdQuery.count_le q Q bm)
  have selected : ∀ i,bank (slots i)=SourceAssemblyClear.join (streams q Q bm hbm)
      (List.replicate (Capacity.value q) true) [] i := by
    intro i;fin_cases i
    · exact h199
    · exact h200
    · exact h204
    · exact h101
    · rfl
  have raw:=SourceAssemblyClear.raw_rewind (streams q Q bm hbm) (fun i=>(streams q Q bm hbm i).length)
    (Capacity.value q) hlen
  have lastStep:=raw.dock slots (by decide) (beforeHeads q Q bm hbm) bank (before_heads q Q bm hbm) selected
  refine ⟨_,(firstStep.seq lastStep).enlarge (by unfold budget;omega),?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact install_slot slots (by decide) bank _ 0
  · exact install_slot slots (by decide) bank _ 1
  · exact install_slot slots (by decide) bank _ 2
  · exact (install_other slots bank _ 140 (by decide)).trans h140
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact install_other slots bank _ 207 (by decide)
  · exact install_other slots bank _ 208 (by decide)
  · exact install_other slots bank _ 209 (by decide)

  · exact (install_other slots bank _ 131 (by decide)).trans h131

end NearCubicWires.SourceRequest.Gen.ThresholdReady

namespace NearCubicWires.SourceRequest.Gen.ThresholdPhysical
open SourceAssemblyThresholdPhysical (gates gates_length gates_native gates_support native slots slots_inj writer)

def machine:=Composition.machine Gen.ThresholdReady.machine writer

def finalHeads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q):=
  dockH slots (Gen.ThresholdReady.finalHeads q Q bm hbm)
    (SourceAssemblySymmetricAssemble.H
      (SourceAssemblyThresholdTop.payload (Gen.SymmetricHeaderQuery.count q Q bm))
      (gates q (Gen.SymmetricHeaderQuery.count q Q bm)
        (Gen.ThresholdCache.bits q Q bm hbm)) 3)

def budget (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q):=
  Gen.ThresholdReady.budget q Q bm+1+
    SourceAssemblySymmetricAssemble.budget
      (SourceAssemblyThresholdTop.payload (Gen.SymmetricHeaderQuery.count q Q bm))
      (gates q (Gen.SymmetricHeaderQuery.count q Q bm)
        (Gen.ThresholdCache.bits q Q bm hbm))

theorem selected_heads (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) (i : Fin 8) :
    Gen.ThresholdReady.finalHeads q Q bm hbm (slots i)=
      SourceAssemblySymmetricAssemble.H
        (SourceAssemblyThresholdTop.payload (Gen.SymmetricHeaderQuery.count q Q bm))
        (gates q (Gen.SymmetricHeaderQuery.count q Q bm)
          (Gen.ThresholdCache.bits q Q bm hbm)) 0 i := by
  fin_cases i
  · change Gen.ThresholdReady.finalHeads q Q bm hbm 161=0
    rw [Gen.ThresholdReady.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change Gen.ThresholdTopQuery.finalHeads q Q bm hbm 161=0
    rw [Gen.ThresholdTopQuery.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change Gen.ThresholdQuery.finalHeads q Q bm hbm 161=0
    rw [Gen.ThresholdQuery.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change Gen.ThresholdCache.finalHeads q Q bm 161=0
    rw [Gen.ThresholdCache.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change Gen.SymmetricHeaderQuery.finalHeads q Q bm 161=0
    exact dockH_slot _ SourceAssemblySymmetricHeaderQuery.slots_inj _ _ 21
  · exact dockH_slot _ (by decide) _ _ 2
  · exact dockH_slot _ (by decide) _ _ 0
  · exact dockH_slot _ (by decide) _ _ 1
  · change Gen.ThresholdReady.finalHeads q Q bm hbm 140=1
    rw [Gen.ThresholdReady.finalHeads,dockH_other _ _ _ 140 (by decide)]
    change Gen.ThresholdTopQuery.finalHeads q Q bm hbm 140=1
    exact dockH_slot _ (by decide) _ _ 4
  · exact dockH_other _ _ _ 207 (by decide)
  · exact dockH_other _ _ _ 208 (by decide)
  · exact dockH_other _ _ _ 209 (by decide)

theorem run_retained (q Q : Nat) (bm : List Bool)
    (hbm : bm.length = q) :
    ∃ A,Step machine (budget q Q bm hbm) (fun _=>0)
      (Gen.ThresholdReady.input q Q bm) (finalHeads q Q bm hbm) A ∧
      A 207=native q (Gen.SymmetricHeaderQuery.count q Q bm)
        (Gen.ThresholdCache.bits q Q bm hbm) ∧
      A 208=CloseoutRowsTupleSeek.supportWord (gates q (Gen.SymmetricHeaderQuery.count q Q bm)
        (Gen.ThresholdCache.bits q Q bm hbm)) ∧ A 131=frame (natWord q) := by
  obtain ⟨A,ha,h199,h200,h204,h140,h161,h207,h208,h209,h131⟩:=Gen.ThresholdReady.run_retained q Q bm hbm
  let n:=Gen.SymmetricHeaderQuery.count q Q bm
  let bits:=Gen.ThresholdCache.bits q Q bm hbm
  have selected : ∀ i,A (slots i)=SourceAssemblySymmetricAssemble.A
      (SourceAssemblyThresholdTop.payload n) (gates q n bits) 0 i := by
    intro i;fin_cases i
    · change A 161=natWord (gates q n bits).length
      rw [gates_length];exact h161
    · exact h204
    · exact h199.trans (gates_native _ _ _).symm
    · exact h200.trans (gates_support _ _ _).symm
    · change A 140=CompareMachine.word (gates q n bits).length
      rw [gates_length];exact h140
    · exact h207
    · exact h208
    · exact h209
  have lastStep:=(SourceAssemblySymmetricAssemble.run
      (SourceAssemblyThresholdTop.payload n) (gates q n bits)).dock slots slots_inj
        (Gen.ThresholdReady.finalHeads q Q bm hbm) A (selected_heads q Q bm hbm) selected
  exact ⟨_,ha.seq lastStep,install_slot slots slots_inj A _ 5,install_slot slots slots_inj A _ 6,
    (install_other slots A _ 131 (by decide)).trans h131⟩

end NearCubicWires.SourceRequest.Gen.ThresholdPhysical

namespace NearCubicWires.SourceRequest.Gen.ThresholdCanonical
open SourceAssemblyThresholdPhysical (native gates slots slots_inj)
open SupplierPipeline CompilerSemantics

/-- The generic chain's native word is the THR parity circuit of the support whose bitmap it reads. -/
theorem native_eq {q : Nat} (S : Finset (Fin q)) (Q : Nat) :
    native q (Gen.SymmetricHeaderQuery.count q Q (SourceAssemblySymmetricMeaning.bitmap S))
      (SourceAssemblySymmetricMeaning.bitmap S)
      = PacketProduction.thrWord (normalizedThresholdParityCircuit S) := by
  unfold Gen.SymmetricHeaderQuery.count
  rw [show Gen.SymmetricQuery.bitmap q Q (SourceAssemblySymmetricMeaning.bitmap S)
      = ZeroPadding.pad Q (SourceAssemblySymmetricMeaning.bitmap S) from rfl,
    SourceAssemblySymmetricMeaning.count_eq]
  exact SourceAssemblyThresholdCanonical.bytes_eq S

theorem bitmap_length {q : Nat} (S : Finset (Fin q)) :
    (SourceAssemblySymmetricMeaning.bitmap S).length = q := by
  simp [SourceAssemblySymmetricMeaning.bitmap]

theorem native_head {q : Nat} (S : Finset (Fin q)) (Q : Nat) :
    Gen.ThresholdPhysical.finalHeads q Q (SourceAssemblySymmetricMeaning.bitmap S)
      (bitmap_length S) 207
      = (PacketProduction.thrWord (normalizedThresholdParityCircuit S)).length := by
  change Gen.ThresholdPhysical.finalHeads q Q _ (bitmap_length S) (slots 5)=_
  rw [Gen.ThresholdPhysical.finalHeads,dockH_slot _ slots_inj _ _ 5]
  change (native q (Gen.SymmetricHeaderQuery.count q Q (SourceAssemblySymmetricMeaning.bitmap S))
    (SourceAssemblySymmetricMeaning.bitmap S)).length=_
  rw [native_eq]

end NearCubicWires.SourceRequest.Gen.ThresholdCanonical

namespace NearCubicWires.SourceRequest.Gen.CircuitFrame
open RepairSource.ProjectionNormalization SupplierPipeline CompilerSemantics

theorem threshold_forward : CursorRestore.NoLeft Gen.ThresholdPhysical.machine 207 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (SourceAssemblyCircuitFrame.fresh_forward _ (1 : Fin 4))
      (EquationRowCuts.unselected_forward _ _ 207 (by decide)))
    (CursorRestore.focus_forward _ SourceAssemblyThresholdPhysical.slots_inj _ 5
      SourceAssemblyCircuitFrame.assembler_forward)

def machine:=AppendOutputFrame.machine Gen.ThresholdPhysical.machine 207

theorem run {q : Nat} (S : Finset (Fin q)) (Q : Nat) :
    let c:=normalizedThresholdParityCircuit S
    let bm:=SourceAssemblySymmetricMeaning.bitmap S
    ∃ A,Step machine (2*Gen.ThresholdPhysical.budget q Q bm (Gen.ThresholdCanonical.bitmap_length S)+
        4*(PacketProduction.thrWord c).length+7) (fun _=>0)
      (AppendOutputFrame.input (Gen.ThresholdReady.input q Q bm)) (fun _=>0) A ∧
      A 212=frame (PacketProduction.thrWord c) ∧
      A 207=PacketProduction.thrWord c ∧
      A 208=CloseoutRowsTupleSeek.supportWord (SourceAssemblyThresholdPhysical.gates q S.card bm) ∧
      A 131=frame (natWord q) := by
  intro c bm
  have hbm : bm.length = q := Gen.ThresholdCanonical.bitmap_length S
  obtain ⟨A,⟨source,hr,rh,rt,rs⟩,hn,hs,h131⟩:=Gen.ThresholdPhysical.run_retained q Q bm hbm
  have hn' : A 207=PacketProduction.thrWord c :=
    hn.trans (Gen.ThresholdCanonical.native_eq S Q)
  obtain ⟨s,sr,st,sh,sk,ss⟩:=PCPPNativeFrame.frame_run
    Gen.ThresholdPhysical.machine 207 threshold_forward
    (Gen.ThresholdPhysical.budget q Q bm hbm) (Gen.ThresholdReady.input q Q bm) source hr
    (PacketProduction.thrWord c)
    (by rw [rt];exact hn') (by rw [rh];exact Gen.ThresholdCanonical.native_head S Q)
  have hcount : Gen.SymmetricHeaderQuery.count q Q bm = S.card :=
    SourceAssemblySymmetricMeaning.count_eq S Q
  refine ⟨s.final.tapes,(Step.of_run sr (funext sh) rfl).enlarge (by omega),st,?_,?_,?_⟩
  · exact (sk 207).trans (by rw [rt];exact hn')
  · exact (sk 208).trans (by rw [rt,hs,hcount];rfl)
  · exact (sk 131).trans (by rw [rt];exact h131)

end NearCubicWires.SourceRequest.Gen.CircuitFrame

end
