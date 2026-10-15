import Proof.CaseAnalysis.FinalWordEngines
import Proof.MachineModel.Layout

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10FirstPhaseEntry

open NearCubicWires.ExtDecompositionBatch RecoveryRootRound

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/- The selected v3 first entry: two copies and two fixed zero-count words.
   Original width218 and nine fresh cells come from AdmittedEntry.run.
   The paid run keeps its actual installed output and every off-map cell. -/

noncomputable def localMachine :=
  Composition.machine
    (RecoveryFocus.machine (![0,1,2,3] : Fin 4 → Fin 10) ClockUnarySum.machine)
    (Composition.machine
      (RecoveryFocus.machine (![0,1,4,5] : Fin 4 → Fin 10) ClockUnarySum.machine)
      (Composition.machine
        (RecoveryFocus.machine (![6,7] : Fin 2 → Fin 10) (HierarchyFixedWord.machine [false]))
        (RecoveryFocus.machine (![8,9] : Fin 2 → Fin 10) (HierarchyFixedWord.machine [false]))))

def input (b : Nat) : Fin 10 → List Bool :=
  ![List.replicate b true,[],[],[],[],[],[],[],[],[]]

theorem local_run (b : Nat) :
    ∃ A : Fin 10 → List Bool,
      Step localMachine (4*b+23) (fun _ => 0) (input b) (fun _ => 0) A ∧
      A 0=List.replicate b true ∧ A 1=[] ∧
      A 2=List.replicate b true ∧ A 4=List.replicate b true ∧
      A 6=[false] ∧ A 8=[false] := by
  obtain ⟨H1,A1,r1,z1,w10,e11,w12,f1⟩ := CloseoutFinalC10WordEngines.copy_dock b
    (![0,1,2,3] : Fin 4 → Fin 10) (by decide) (fun _ => 0) (input b)
    (fun _ => rfl) rfl rfl rfl rfl
  obtain ⟨H2,A2,r2,z2,w20,e21,w24,f2⟩ := CloseoutFinalC10WordEngines.copy_dock b
    (![0,1,4,5] : Fin 4 → Fin 10) (by decide) H1 A1 z1 w10 e11
    ((f1 4 (by decide)).trans rfl) ((f1 5 (by decide)).trans rfl)
  obtain ⟨H3,A3,r3,z3,c36,f3⟩ := CloseoutFinalC10WordEngines.fixedWord_dock [false]
    (![6,7] : Fin 2 → Fin 10) (by decide) H2 A2 z2
    ((f2 6 (by decide)).trans ((f1 6 (by decide)).trans rfl))
    ((f2 7 (by decide)).trans ((f1 7 (by decide)).trans rfl))
  obtain ⟨H4,A4,r4,z4,c48,f4⟩ := CloseoutFinalC10WordEngines.fixedWord_dock [false]
    (![8,9] : Fin 2 → Fin 10) (by decide) H3 A3 z3
    ((f3 8 (by decide)).trans ((f2 8 (by decide)).trans ((f1 8 (by decide)).trans rfl)))
    ((f3 9 (by decide)).trans ((f2 9 (by decide)).trans ((f1 9 (by decide)).trans rfl)))
  have joined := r1.seq (r2.seq (r3.seq r4))
  have time : (2*(b+0)+6)+1+((2*(b+0)+6)+1+
      ((2*[false].length+2)+1+(2*[false].length+2)))=4*b+23 := by
    simp only [List.length_cons,List.length_nil]
    omega
  rw [time] at joined
  refine ⟨A4,joined.congr (funext z4) rfl,?_,?_,?_,?_,?_,c48⟩
  · exact (f4 0 (by decide)).trans ((f3 0 (by decide)).trans w20)
  · exact (f4 1 (by decide)).trans ((f3 1 (by decide)).trans e21)
  · exact (f4 2 (by decide)).trans ((f3 2 (by decide)).trans ((f2 2 (by decide)).trans w12))
  · exact (f4 4 (by decide)).trans ((f3 4 (by decide)).trans w24)
  · exact (f4 6 (by decide)).trans c36

def firstSlots (L B : Nat) (hL : 301≤L) (hSpace : L+1095<B) : Fin 10 → Fin B :=
  ![⟨218,by omega⟩,⟨L+135,by omega⟩,⟨L+817,by omega⟩,⟨L+136,by omega⟩,
    ⟨L+1095,by omega⟩,⟨L+137,by omega⟩,⟨L+689,by omega⟩,⟨L+124,by omega⟩,
    ⟨L+967,by omega⟩,⟨L+125,by omega⟩]

theorem slots_injective (L B : Nat) (hL : 301≤L) (hSpace : L+1095<B) :
    Function.Injective (firstSlots L B hL hSpace) := by
  intro i j hij
  have h := congrArg Fin.val hij
  clear hij
  fin_cases i <;> fin_cases j <;> norm_num [firstSlots] at h
  all_goals first | rfl | omega

noncomputable def machine (L B : Nat) (hL : 301≤L) (hSpace : L+1095<B) :=
  RecoveryFocus.machine (firstSlots L B hL hSpace) localMachine

/-- The exact width and future-bank fields exported by AdmittedEntry suffice.
    Only the selected ten heads must be zero; the external counter is retained. -/
theorem run (L B : Nat) (hL : 301≤L) (hSpace : L+1095<B)
    (b : Nat) (H : Fin B → Nat) (finalBank : Fin B → List Bool)
    (hH : ∀ i,H (firstSlots L B hL hSpace i)=0)
    (width : finalBank ⟨218,by omega⟩=List.replicate b true)
    (future : ∀ v : Fin B,L+96≤v.val → finalBank v=[]) :
    ∃ A : Fin 10 → List Bool,
      Step (machine L B hL hSpace) (4*b+23) H finalBank H
        (install (firstSlots L B hL hSpace) finalBank A) ∧
      A 0=List.replicate b true ∧ A 1=[] ∧
      A 2=List.replicate b true ∧ A 4=List.replicate b true ∧
      A 6=[false] ∧ A 8=[false] ∧
      (∀ i,install (firstSlots L B hL hSpace) finalBank A
        (firstSlots L B hL hSpace i)=A i) ∧
      (∀ v,(∀ i,firstSlots L B hL hSpace i≠v) →
        install (firstSlots L B hL hSpace) finalBank A v=finalBank v) := by
  have hi := slots_injective L B hL hSpace
  have hinput : ∀ i,finalBank (firstSlots L B hL hSpace i)=input b i := by
    intro i
    fin_cases i
    · exact width
    all_goals apply future; norm_num [firstSlots]
  obtain ⟨A,step,w0,e1,w2,w4,c6,c8⟩ := local_run b
  refine ⟨A,(step.dock _ hi H finalBank hH hinput).congr
    (dockH_existing _ H _ hH) rfl,w0,e1,w2,w4,c6,c8,?_,?_⟩
  · exact install_slot _ hi finalBank A
  · exact install_other _ finalBank A

/-- Consume the actual installed post-initializer bank, retaining the counter
    and all off-first-entry tapes in the full continuation state. -/
theorem docked_run (L B total : Nat) (hL : 301≤L) (hSpace : L+1095<B)
    (bodySlots : Fin B → Fin total) (hBody : Function.Injective bodySlots)
    (b : Nat) (H : Fin total → Nat) (post : Fin total → List Bool)
    (finalBank : Fin B → List Bool) (hH : ∀ i,H (bodySlots i)=0)
    (width : finalBank ⟨218,by omega⟩=List.replicate b true)
    (future : ∀ v : Fin B,L+96≤v.val → finalBank v=[]) :
    ∃ A : Fin 10 → List Bool,
      let initial := install bodySlots post finalBank
      let final := install bodySlots initial (install (firstSlots L B hL hSpace) finalBank A)
      Step (RecoveryFocus.machine bodySlots (machine L B hL hSpace))
        (4*b+23) H initial H final ∧
      A 0=List.replicate b true ∧ A 1=[] ∧
      A 2=List.replicate b true ∧ A 4=List.replicate b true ∧
      A 6=[false] ∧ A 8=[false] ∧
      (∀ i,final (bodySlots (firstSlots L B hL hSpace i))=A i) ∧
      (∀ v,(∀ i,bodySlots (firstSlots L B hL hSpace i)≠v) → final v=initial v) := by
  obtain ⟨A,step,w0,e1,w2,w4,c6,c8,slots,frame⟩ :=
    run L B hL hSpace b (fun _ => 0) finalBank (fun _ => rfl) width future
  let initial := install bodySlots post finalBank
  have input_eq : ∀ i,initial (bodySlots i)=finalBank i := install_slot _ hBody _ _
  refine ⟨A,(step.dock bodySlots hBody H initial hH input_eq).congr
    (dockH_existing bodySlots H _ hH) rfl,w0,e1,w2,w4,c6,c8,?_,?_⟩
  · intro i
    exact (install_slot bodySlots hBody initial _ _).trans (slots i)
  · intro v hv
    by_cases h : ∃ j,bodySlots j=v
    · obtain ⟨j,rfl⟩ := h
      rw [install_slot bodySlots hBody]
      exact (frame j (fun i hi => hv i (congrArg bodySlots hi))).trans (input_eq j).symm
    · exact install_other bodySlots initial _ v (fun j hj => h ⟨j,hj⟩)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10FirstPhaseEntry
