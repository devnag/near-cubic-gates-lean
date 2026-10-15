import Proof.SourceAssembly.SourceThresholdIndex

/- Append one THR staircase bottom and its declared support from retained
q/weights/bitmap caches and the physically produced native j field. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace SourceAssemblyThresholdGate
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
noncomputable section

def H (out : Fin 2→List Bool) (i : Fin 7):=if i=4 then (out 0).length else if i=5 then (out 1).length else 0
def A (q j C : Nat) (bits tail : List Bool) (out : Fin 2→List Bool) (i : Fin 7):=
  if i=0 then frame (natWord q) else if i=1 then frame (weights bits) else if i=2 then frame bits else
  if i=3 then frame (natWord j)++tail else if i=4 then out 0 else if i=5 then out 1 else List.replicate C false
def qSlots : Fin 3→Fin 7:=![0,4,6]
def wSlots : Fin 3→Fin 7:=![1,4,6]
def jSlots : Fin 3→Fin 7:=![3,4,6]
def sSlots : Fin 3→Fin 7:=![2,5,6]
def signSlots : Fin 2→Fin 7:=![0,4]
def qCopy:=RecoveryFocus.machine qSlots (Fragment.reusable false)
def wCopy:=RecoveryFocus.machine wSlots (Fragment.reusable false)
def jCopy:=RecoveryFocus.machine jSlots (Fragment.reusable true)
def sCopy:=RecoveryFocus.machine sSlots (Fragment.reusable true)
def signStrokes : List (Glyph.Stroke 1):=[![some (fun _=>true)],![some (fun _=>false)]]
def sign:=RecoveryFocus.machine signSlots (Glyph.machine signStrokes)
def machine:=Composition.machine qCopy (Composition.machine wCopy (Composition.machine sign (Composition.machine jCopy sCopy)))
def append (out : Fin 2→List Bool) (i : Fin 2) (word : List Bool) : Fin 2→List Bool:=fun k=>if k=i then out k++word else out k
def budget (q j : Nat) (bits : List Bool):=4*(natWord q).length+4*(weights bits).length+4*(natWord j).length+4*bits.length+24

theorem q_run (q j C : Nat) (bits tail : List Bool) (out : Fin 2→List Bool)
    (hC : 2*(natWord q).length+1≤C) :
    Step qCopy (4*(natWord q).length+4) (H out) (A q j C bits tail out)
      (H (append out 0 (Fragment.word false (natWord q))))
      (A q j C bits tail (append out 0 (Fragment.word false (natWord q)))) := by
  have localStep:=Gate.fragment_run false (natWord q) [] (out 0) C hC
  simp only [List.append_nil] at localStep
  refine CloseoutRowsEstimator.SubstitutionDock.run _ qSlots (by decide) _ _ _ _ _ _ _ _ localStep
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i hi;fin_cases i <;>first
    | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | rfl
  · intro i hi;fin_cases i <;>first
    | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | rfl

theorem w_run (q j C : Nat) (bits tail : List Bool) (out : Fin 2→List Bool)
    (hC : 2*(weights bits).length+1≤C) :
    Step wCopy (4*(weights bits).length+4) (H out) (A q j C bits tail out)
      (H (append out 0 (Fragment.word false (weights bits))))
      (A q j C bits tail (append out 0 (Fragment.word false (weights bits)))) := by
  have localStep:=Gate.fragment_run false (weights bits) [] (out 0) C hC
  simp only [List.append_nil] at localStep
  refine CloseoutRowsEstimator.SubstitutionDock.run _ wSlots (by decide) _ _ _ _ _ _ _ _ localStep
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i hi;fin_cases i <;>first
    | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | rfl
  · intro i hi;fin_cases i <;>first
    | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | rfl

theorem j_run (q j C : Nat) (bits tail : List Bool) (out : Fin 2→List Bool)
    (hC : 2*(natWord j).length+1≤C) :
    Step jCopy (4*(natWord j).length+4) (H out) (A q j C bits tail out)
      (H (append out 0 (Fragment.word true (natWord j))))
      (A q j C bits tail (append out 0 (Fragment.word true (natWord j)))) := by
  have localStep:=Gate.fragment_run true (natWord j) tail (out 0) C hC
  refine CloseoutRowsEstimator.SubstitutionDock.run _ jSlots (by decide) _ _ _ _ _ _ _ _ localStep
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i hi;fin_cases i <;>first
    | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | rfl
  · intro i hi;fin_cases i <;>first
    | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | rfl

theorem s_run (q j C : Nat) (bits tail : List Bool) (out : Fin 2→List Bool)
    (hC : 2*(bits).length+1≤C) :
    Step sCopy (4*(bits).length+4) (H out) (A q j C bits tail out)
      (H (append out 1 (Fragment.word true (bits))))
      (A q j C bits tail (append out 1 (Fragment.word true (bits)))) := by
  have localStep:=Gate.fragment_run true (bits) [] (out 1) C hC
  simp only [List.append_nil] at localStep
  refine CloseoutRowsEstimator.SubstitutionDock.run _ sSlots (by decide) _ _ _ _ _ _ _ _ localStep
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i hi;fin_cases i <;>first
    | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | rfl
  · intro i hi;fin_cases i <;>first
    | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | rfl

theorem sign_run (q j C : Nat) (bits tail : List Bool) (out : Fin 2→List Bool) :
    Step sign 4 (H out) (A q j C bits tail out)
      (H (append out 0 [true,false])) (A q j C bits tail (append out 0 [true,false])) := by
  have localStep:=Glyph.word_run signStrokes (readTapeBit (frame (natWord q)) 0)
    (frame (natWord q)) 0 (![out 0]) rfl
  have bytes (b : Bool) (i : Fin 1) : Glyph.word signStrokes b i=[true,false] := by
    fin_cases i;rfl
  simp only [bytes] at localStep
  refine CloseoutRowsEstimator.SubstitutionDock.run _ signSlots (by decide) _ _ _ _ _ _ _ _ localStep
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i hi;fin_cases i <;>first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | rfl
  · intro i hi;fin_cases i <;>first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | rfl

def emitted (q j : Nat) (bits : List Bool) : Fin 2→List Bool:=
  ![frame (natWord q++weights bits++false::natWord j),frame bits]

theorem append_eq (q j : Nat) (bits : List Bool) (out : Fin 2→List Bool) :
    append (append (append (append (append out 0 (Fragment.word false (natWord q)))
      0 (Fragment.word false (weights bits))) 0 [true,false]) 0 (Fragment.word true (natWord j)))
      1 (Fragment.word true bits)=(fun i=>out i++emitted q j bits i) := by
  funext i;fin_cases i <;>simp [append,emitted,Fragment.word,Fragment.frame_eq,Fragment.body,List.flatMap_append,List.append_assoc]

theorem run (q j C : Nat) (bits tail : List Bool) (out : Fin 2→List Bool)
    (hq : 2*(natWord q).length+1≤C) (hw : 2*(weights bits).length+1≤C)
    (hj : 2*(natWord j).length+1≤C) (hb : 2*bits.length+1≤C) :
    Step machine (budget q j bits) (H out) (A q j C bits tail out)
      (H (fun i=>out i++emitted q j bits i)) (A q j C bits tail (fun i=>out i++emitted q j bits i)) := by
  have actual:=(q_run q j C bits tail out hq).seq
    ((w_run q j C bits tail _ hw).seq ((sign_run q j C bits tail _).seq
      ((j_run q j C bits tail _ hj).seq (s_run q j C bits tail _ hb))))
  rw [append_eq] at actual
  exact actual.enlarge (by unfold budget;omega)

end
end SourceAssemblyThresholdGate
