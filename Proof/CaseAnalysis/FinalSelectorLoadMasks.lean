import Proof.CaseAnalysis.FinalSelectorCellSetter
import Proof.MachineModel.UWalkUnary
import Proof.CaseAnalysis.RowsEstimatorPad

/-! A.4 cold start, part 5: the LOADER, first group of ports.

Working down the port chart of `RepairCloseoutFinalSelectorColdPorts`, this
file physically writes the three seed masks (ports 1, 2, 3) and the two
single-cell scalars (ports 29, 32) of the selector's 35-tape entry bank.
Every stage is an accepted worker docked by `RecoveryFocus`; the only newly
built machine in the whole group is the one-cell writer `setOne`.

The bank is `Fin 96`: the selector's 36 tapes at 0-35, the paid drivers at
36-40, and per-group scratch above that (this group owns 41-44).  The group
is stated over an ARBITRARY ambient bank `A` satisfying `MaskReady`, and
returns `mask_untouched`: every other selector tape is left exactly as it
was.  That is what lets the groups be sequenced. -/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalSelector
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- A worker with all heads at zero, docked into the ambient bank. -/
theorem dock_ready {t u s n : ℕ} (p : Machine t s) (slots : Fin t→Fin u)
    (hi:Function.Injective slots) (A : Fin u→List Bool) (inp out : Fin t→List Bool)
    (h:Step p n (fun _=>0) inp (fun _=>0) out) (hin:∀ k,A (slots k)=inp k):
    Step (RecoveryFocus.machine slots p) n (fun _=>0) A (fun _=>0) (install slots A out):=by
  have focused:=h.focus slots hi (fun _=>0) A
  have heads:dockH slots (fun _=>0) (fun _ : Fin t=>0)=(fun _ : Fin u=>0):=by
    funext i;unfold dockH;split <;> rfl
  exact focused.congr_in heads (install_existing slots A inp hin) |>.congr heads rfl

/-- The `ClockJoin` flavour of a heads-at-zero receipt. -/
theorem step_of_clock {t s n : ℕ} {p : Machine t s} {inp out : Fin t→List Bool}
    (h:ClockJoin.ReadyRun p n inp out):Step p n (fun _=>0) inp (fun _=>0) out:=by
  obtain ⟨r,hr,ht,hh,hs⟩:=h
  refine ⟨r,?_,funext hh,ht,hs⟩
  change run p n inp=some r at hr
  exact hr

/-! ### Slot maps -/

def u1Slots : Fin 3→Fin 96:=![36,41,42]
def u2Slots : Fin 3→Fin 96:=![36,3,43]
def padSlots : Fin 4→Fin 96:=![1,2,41,44]
def oneSlot : Fin 1→Fin 96:=![2]
def remSlot : Fin 1→Fin 96:=![3]
def flagSlot : Fin 1→Fin 96:=![29]
def carrySlot : Fin 1→Fin 96:=![32]

noncomputable def u1:=RecoveryFocus.machine u1Slots (UWalkUnary.machine false false)
noncomputable def u2:=RecoveryFocus.machine u2Slots (UWalkUnary.machine false false)
noncomputable def padStage:=RecoveryFocus.machine padSlots (CloseoutRowsEstimator.Pad.machine 2)
noncomputable def oneStage:=RecoveryFocus.machine oneSlot setOne
noncomputable def remStage:=RecoveryFocus.machine remSlot LookupReadBit.clear
noncomputable def flagStage:=RecoveryFocus.machine flagSlot LookupReadBit.clear
noncomputable def carryStage:=RecoveryFocus.machine carrySlot LookupReadBit.clear
noncomputable def maskMachine:=Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine u1 u2) padStage) oneStage)
    remStage) flagStage) carryStage
def maskBudget (q : ℕ):=6*q+26

/-- What the ambient bank must supply: the raw unary q driver, blank mask and
scalar ports, and blank group scratch. -/
structure MaskReady (q : ℕ) (A : Fin 96→List Bool) : Prop where
  count : A 36=CompareMachine.word q
  m1 : A 1=[]
  m2 : A 2=[]
  m3 : A 3=[]
  m29 : A 29=[]
  m32 : A 32=[]
  w41 : A 41=[]
  w42 : A 42=[]
  w43 : A 43=[]
  w44 : A 44=[]

/-! ### Worker receipts, all heads at zero -/

theorem walk_step (q : ℕ):
    Step (UWalkUnary.machine false false) (2*q+6) (fun _=>0) (UWalkUnary.input 0 q) (fun _=>0)
      (UWalkUnary.result false false 0 q):=step_of_clock (UWalkUnary.ready false false 0 q)

theorem pad_step (q : ℕ):
    Step (CloseoutRowsEstimator.Pad.machine 2) (2*q+4) (fun _=>0)
      (CloseoutRowsEstimator.Pad.input (fun _ : Fin 2=>[]) q) (fun _=>0)
      (CloseoutRowsEstimator.Pad.output (fun _ : Fin 2=>[]) q):=
  Step.of_ready (CloseoutRowsEstimator.Pad.ready (fun _ : Fin 2=>[]) q)

theorem walk_source (q : ℕ):UWalkUnary.source 0 q=CompareMachine.word q:=ZeroPadding.pad_zero _
theorem walk_in0 (q : ℕ):UWalkUnary.input 0 q 0=CompareMachine.word q:=walk_source q
theorem walk_in1 (q : ℕ):UWalkUnary.input 0 q 1=[]:=rfl
theorem walk_in2 (q : ℕ):UWalkUnary.input 0 q 2=[]:=rfl
theorem walk_out0 (q : ℕ):UWalkUnary.result false false 0 q 0=CompareMachine.word q:=walk_source q
theorem walk_out1 (q : ℕ):UWalkUnary.result false false 0 q 1=List.replicate q true:=rfl
theorem pad_in0 (q : ℕ):CloseoutRowsEstimator.Pad.input (fun _ : Fin 2=>[]) q 0=[]:=rfl
theorem pad_in1 (q : ℕ):CloseoutRowsEstimator.Pad.input (fun _ : Fin 2=>[]) q 1=[]:=rfl
theorem pad_in2 (q : ℕ):CloseoutRowsEstimator.Pad.input (fun _ : Fin 2=>[]) q 2=List.replicate q true:=rfl
theorem pad_in3 (q : ℕ):CloseoutRowsEstimator.Pad.input (fun _ : Fin 2=>[]) q 3=[]:=rfl
theorem pad_out0 (q : ℕ):CloseoutRowsEstimator.Pad.output (fun _ : Fin 2=>[]) q 0=List.replicate q false:=rfl
theorem pad_out1 (q : ℕ):CloseoutRowsEstimator.Pad.output (fun _ : Fin 2=>[]) q 1=List.replicate q false:=rfl

/-! ### The banks after each docked stage -/

noncomputable def B1 (q : ℕ) (A : Fin 96→List Bool) : Fin 96→List Bool:=
  install u1Slots A (UWalkUnary.result false false 0 q)
noncomputable def B2 (q : ℕ) (A : Fin 96→List Bool) : Fin 96→List Bool:=
  install u2Slots (B1 q A) (UWalkUnary.result false false 0 q)
noncomputable def B3 (q : ℕ) (A : Fin 96→List Bool) : Fin 96→List Bool:=
  install padSlots (B2 q A) (CloseoutRowsEstimator.Pad.output (fun _ : Fin 2=>[]) q)
noncomputable def B4 (q : ℕ) (A : Fin 96→List Bool) : Fin 96→List Bool:=
  install oneSlot (B3 q A) (fun _=>List.ofFn (fun i : Fin q=>decide (i.val=0)))
noncomputable def B5 (q : ℕ) (A : Fin 96→List Bool) : Fin 96→List Bool:=
  install remSlot (B4 q A) (fun _=>List.ofFn (fun i : Fin q=>decide (0 < i.val)))
noncomputable def B6 (q : ℕ) (A : Fin 96→List Bool) : Fin 96→List Bool:=
  install flagSlot (B5 q A) (fun _=>[false])
noncomputable def B7 (q : ℕ) (A : Fin 96→List Bool) : Fin 96→List Bool:=
  install carrySlot (B6 q A) (fun _=>[false])

theorem B1_at (q : ℕ) (A : Fin 96→List Bool) (i : Fin 96) (h:∀ k,u1Slots k≠i):B1 q A i=A i:=
  install_other u1Slots _ _ i h
theorem B2_at (q : ℕ) (A : Fin 96→List Bool) (i : Fin 96) (h:∀ k,u2Slots k≠i):B2 q A i=B1 q A i:=
  install_other u2Slots _ _ i h
theorem B3_at (q : ℕ) (A : Fin 96→List Bool) (i : Fin 96) (h:∀ k,padSlots k≠i):B3 q A i=B2 q A i:=
  install_other padSlots _ _ i h
theorem B4_at (q : ℕ) (A : Fin 96→List Bool) (i : Fin 96) (h:∀ k,oneSlot k≠i):B4 q A i=B3 q A i:=
  install_other oneSlot _ _ i h
theorem B5_at (q : ℕ) (A : Fin 96→List Bool) (i : Fin 96) (h:∀ k,remSlot k≠i):B5 q A i=B4 q A i:=
  install_other remSlot _ _ i h
theorem B6_at (q : ℕ) (A : Fin 96→List Bool) (i : Fin 96) (h:∀ k,flagSlot k≠i):B6 q A i=B5 q A i:=
  install_other flagSlot _ _ i h
theorem B7_at (q : ℕ) (A : Fin 96→List Bool) (i : Fin 96) (h:∀ k,carrySlot k≠i):B7 q A i=B6 q A i:=
  install_other carrySlot _ _ i h

/-! ### Stage entry ports -/

theorem B1_36 (q : ℕ) (A : Fin 96→List Bool):B1 q A 36=CompareMachine.word q:=by
  rw [show (36 : Fin 96)=u1Slots 0 from by decide,B1,install_slot u1Slots (by decide)]
  exact walk_out0 q
theorem B1_41 (q : ℕ) (A : Fin 96→List Bool):B1 q A 41=List.replicate q true:=by
  rw [show (41 : Fin 96)=u1Slots 1 from by decide,B1,install_slot u1Slots (by decide)]
  exact walk_out1 q
theorem B2_3 (q : ℕ) (A : Fin 96→List Bool):B2 q A 3=List.replicate q true:=by
  rw [show (3 : Fin 96)=u2Slots 1 from by decide,B2,install_slot u2Slots (by decide)]
  exact walk_out1 q
theorem B2_41 (q : ℕ) (A : Fin 96→List Bool):B2 q A 41=List.replicate q true:=by
  rw [B2_at q A 41 (by decide),B1_41]
theorem B3_2 (q : ℕ) (A : Fin 96→List Bool):B3 q A 2=List.replicate q false:=by
  rw [show (2 : Fin 96)=padSlots 1 from by decide,B3,install_slot padSlots (by decide)]
  exact pad_out1 q
theorem B4_3 (q : ℕ) (A : Fin 96→List Bool):B4 q A 3=List.replicate q true:=by
  rw [B4_at q A 3 (by decide),B3_at q A 3 (by decide),B2_3]

/-! ### The docked stages -/

theorem s1in0 (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):
    A (u1Slots 0)=UWalkUnary.input 0 q 0:=by rw [walk_in0];exact h.count
theorem s1in1 (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):
    A (u1Slots 1)=UWalkUnary.input 0 q 1:=by rw [walk_in1];exact h.w41
theorem s1in2 (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):
    A (u1Slots 2)=UWalkUnary.input 0 q 2:=by rw [walk_in2];exact h.w42

theorem stage1 (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):
    Step u1 (2*q+6) (fun _=>0) A (fun _=>0) (B1 q A):=
  dock_ready (UWalkUnary.machine false false) u1Slots (by decide) A
    (UWalkUnary.input 0 q) (UWalkUnary.result false false 0 q) (walk_step q) (by
      intro k
      fin_cases k
      · exact s1in0 q A h
      · exact s1in1 q A h
      · exact s1in2 q A h)

theorem s2in0 (q : ℕ) (A : Fin 96→List Bool):B1 q A (u2Slots 0)=UWalkUnary.input 0 q 0:=by
  rw [walk_in0];exact B1_36 q A
theorem s2in1 (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):
    B1 q A (u2Slots 1)=UWalkUnary.input 0 q 1:=by
  rw [walk_in1,B1_at q A _ (by decide)];exact h.m3
theorem s2in2 (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):
    B1 q A (u2Slots 2)=UWalkUnary.input 0 q 2:=by
  rw [walk_in2,B1_at q A _ (by decide)];exact h.w43

theorem stage2 (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):
    Step u2 (2*q+6) (fun _=>0) (B1 q A) (fun _=>0) (B2 q A):=
  dock_ready (UWalkUnary.machine false false) u2Slots (by decide) (B1 q A)
    (UWalkUnary.input 0 q) (UWalkUnary.result false false 0 q) (walk_step q) (by
      intro k
      fin_cases k
      · exact s2in0 q A
      · exact s2in1 q A h
      · exact s2in2 q A h)

theorem s3in0 (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):
    B2 q A (padSlots 0)=CloseoutRowsEstimator.Pad.input (fun _ : Fin 2=>[]) q 0:=by
  rw [pad_in0,B2_at q A _ (by decide),B1_at q A _ (by decide)];exact h.m1
theorem s3in1 (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):
    B2 q A (padSlots 1)=CloseoutRowsEstimator.Pad.input (fun _ : Fin 2=>[]) q 1:=by
  rw [pad_in1,B2_at q A _ (by decide),B1_at q A _ (by decide)];exact h.m2
theorem s3in2 (q : ℕ) (A : Fin 96→List Bool):
    B2 q A (padSlots 2)=CloseoutRowsEstimator.Pad.input (fun _ : Fin 2=>[]) q 2:=by
  rw [pad_in2];exact B2_41 q A
theorem s3in3 (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):
    B2 q A (padSlots 3)=CloseoutRowsEstimator.Pad.input (fun _ : Fin 2=>[]) q 3:=by
  rw [pad_in3,B2_at q A _ (by decide),B1_at q A _ (by decide)];exact h.w44

theorem stage3 (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):
    Step padStage (2*q+4) (fun _=>0) (B2 q A) (fun _=>0) (B3 q A):=
  dock_ready (CloseoutRowsEstimator.Pad.machine 2) padSlots (by decide) (B2 q A)
    (CloseoutRowsEstimator.Pad.input (fun _ : Fin 2=>[]) q)
    (CloseoutRowsEstimator.Pad.output (fun _ : Fin 2=>[]) q) (pad_step q) (by
      intro k
      fin_cases k
      · exact s3in0 q A h
      · exact s3in1 q A h
      · exact s3in2 q A
      · exact s3in3 q A h)

theorem stage4 (q : ℕ) (hq:0<q) (A : Fin 96→List Bool):
    Step oneStage 1 (fun _=>0) (B3 q A) (fun _=>0) (B4 q A):=
  dock_ready setOne oneSlot (fun a b _=>Subsingleton.elim a b) (B3 q A)
    (fun _=>List.replicate q false) (fun _=>List.ofFn (fun i : Fin q=>decide (i.val=0)))
    (set_one_hot_step q hq) (by intro k;fin_cases k;exact B3_2 q A)

theorem stage5 (q : ℕ) (hq:0<q) (A : Fin 96→List Bool):
    Step remStage 1 (fun _=>0) (B4 q A) (fun _=>0) (B5 q A):=
  dock_ready LookupReadBit.clear remSlot (fun a b _=>Subsingleton.elim a b) (B4 q A)
    (fun _=>List.replicate q true) (fun _=>List.ofFn (fun i : Fin q=>decide (0 < i.val)))
    (set_remaining_step q hq) (by intro k;fin_cases k;exact B4_3 q A)

theorem s6in (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):B5 q A (flagSlot 0)=[]:=by
  rw [B5_at q A _ (by decide),B4_at q A _ (by decide),B3_at q A _ (by decide),
    B2_at q A _ (by decide),B1_at q A _ (by decide)]
  exact h.m29

theorem stage6 (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):
    Step flagStage 1 (fun _=>0) (B5 q A) (fun _=>0) (B6 q A):=
  dock_ready LookupReadBit.clear flagSlot (fun a b _=>Subsingleton.elim a b) (B5 q A)
    (fun _=>[]) (fun _=>[false]) clear_blank_step (by intro k;fin_cases k;exact s6in q A h)

theorem s7in (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):B6 q A (carrySlot 0)=[]:=by
  rw [B6_at q A _ (by decide),B5_at q A _ (by decide),B4_at q A _ (by decide),
    B3_at q A _ (by decide),B2_at q A _ (by decide),B1_at q A _ (by decide)]
  exact h.m32

theorem stage7 (q : ℕ) (A : Fin 96→List Bool) (h:MaskReady q A):
    Step carryStage 1 (fun _=>0) (B6 q A) (fun _=>0) (B7 q A):=
  dock_ready LookupReadBit.clear carrySlot (fun a b _=>Subsingleton.elim a b) (B6 q A)
    (fun _=>[]) (fun _=>[false]) clear_blank_step (by intro k;fin_cases k;exact s7in q A h)

/-! ### The group receipt -/

theorem mask_group_run (q : ℕ) (hq:0<q) (A : Fin 96→List Bool) (h:MaskReady q A):
    Step maskMachine (maskBudget q) (fun _=>0) A (fun _=>0) (B7 q A):=by
  have all:=((((((stage1 q A h).seq (stage2 q A h)).seq (stage3 q A h)).seq (stage4 q hq A)).seq
    (stage5 q hq A)).seq (stage6 q A h)).seq (stage7 q A h)
  exact all.enlarge (by unfold maskBudget;omega)

theorem mask_port01 (q : ℕ) (A : Fin 96→List Bool):B7 q A 1=List.replicate q false:=by
  rw [B7_at q A 1 (by decide),B6_at q A 1 (by decide),B5_at q A 1 (by decide),
    B4_at q A 1 (by decide),show (1 : Fin 96)=padSlots 0 from by decide,B3,
    install_slot padSlots (by decide)]
  exact pad_out0 q

theorem mask_port02 (q : ℕ) (A : Fin 96→List Bool):
    B7 q A 2=List.ofFn (fun i : Fin q=>decide (i.val=0)):=by
  rw [B7_at q A 2 (by decide),B6_at q A 2 (by decide),B5_at q A 2 (by decide),
    show (2 : Fin 96)=oneSlot 0 from by decide,B4,install_slot oneSlot
      (fun a b _=>Subsingleton.elim a b)]

theorem mask_port03 (q : ℕ) (A : Fin 96→List Bool):
    B7 q A 3=List.ofFn (fun i : Fin q=>decide (0 < i.val)):=by
  rw [B7_at q A 3 (by decide),B6_at q A 3 (by decide),
    show (3 : Fin 96)=remSlot 0 from by decide,B5,install_slot remSlot
      (fun a b _=>Subsingleton.elim a b)]

theorem mask_port29 (q : ℕ) (A : Fin 96→List Bool):B7 q A 29=[false]:=by
  rw [B7_at q A 29 (by decide),show (29 : Fin 96)=flagSlot 0 from by decide,B6,
    install_slot flagSlot (fun a b _=>Subsingleton.elim a b)]

theorem mask_port32 (q : ℕ) (A : Fin 96→List Bool):B7 q A 32=[false]:=by
  rw [show (32 : Fin 96)=carrySlot 0 from by decide,B7,
    install_slot carrySlot (fun a b _=>Subsingleton.elim a b)]

/-- Every tape the group does not own is left exactly as it was: the group
composes with the others. -/
theorem mask_untouched (q : ℕ) (A : Fin 96→List Bool) (i : Fin 96) (h36:i.val<36)
    (h1:i.val≠1) (h2:i.val≠2) (h3:i.val≠3) (h29:i.val≠29) (h32:i.val≠32):B7 q A i=A i:=by
  have hu1:∀ k,u1Slots k≠i:=by
    intro k he
    have hv:=congrArg Fin.val he
    fin_cases k <;> simp [u1Slots] at hv <;> omega
  have hu2:∀ k,u2Slots k≠i:=by
    intro k he
    have hv:=congrArg Fin.val he
    fin_cases k <;> simp [u2Slots] at hv <;> omega
  have hup:∀ k,padSlots k≠i:=by
    intro k he
    have hv:=congrArg Fin.val he
    fin_cases k <;> simp [padSlots] at hv <;> omega
  have huo:∀ k,oneSlot k≠i:=by
    intro k he
    have hv:=congrArg Fin.val he
    fin_cases k;simp [oneSlot] at hv;omega
  have hur:∀ k,remSlot k≠i:=by
    intro k he
    have hv:=congrArg Fin.val he
    fin_cases k;simp [remSlot] at hv;omega
  have huf:∀ k,flagSlot k≠i:=by
    intro k he
    have hv:=congrArg Fin.val he
    fin_cases k;simp [flagSlot] at hv;omega
  have huc:∀ k,carrySlot k≠i:=by
    intro k he
    have hv:=congrArg Fin.val he
    fin_cases k;simp [carrySlot] at hv;omega
  rw [B7_at q A i huc,B6_at q A i huf,B5_at q A i hur,B4_at q A i huo,B3_at q A i hup,
    B2_at q A i hu2,B1_at q A i hu1]

/-- The drivers and the other groups' scratch are untouched as well. -/
theorem mask_scratch (q : ℕ) (A : Fin 96→List Bool) (i : Fin 96) (h:44 < i.val):B7 q A i=A i:=by
  have step:∀ {t : ℕ} (sl : Fin t→Fin 96),(∀ k,(sl k).val≤44)→∀ k,sl k≠i:=by
    intro t sl hb k he
    have hv:=congrArg Fin.val he
    have:=hb k
    omega
  rw [B7_at q A i (step carrySlot (by decide)),B6_at q A i (step flagSlot (by decide)),
    B5_at q A i (step remSlot (by decide)),B4_at q A i (step oneSlot (by decide)),
    B3_at q A i (step padSlots (by decide)),B2_at q A i (step u2Slots (by decide)),
    B1_at q A i (step u1Slots (by decide))]

theorem mask_count (q : ℕ) (A : Fin 96→List Bool):B7 q A 36=CompareMachine.word q:=by
  rw [B7_at q A 36 (by decide),B6_at q A 36 (by decide),B5_at q A 36 (by decide),
    B4_at q A 36 (by decide),B3_at q A 36 (by decide),
    show (36 : Fin 96)=u2Slots 0 from by decide,B2,install_slot u2Slots (by decide)]
  exact walk_out0 q

end NearCubicWires.RepairOrdinary.CloseoutFinalSelector
