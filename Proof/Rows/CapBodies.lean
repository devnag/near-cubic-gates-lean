import Proof.Rows.CapInput

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace CapDoublingBodies
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary RecoveryExecution
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open RadixSemantics
abbrev word := CapDoublingPass.word

def heads (pos k : Nat) : Fin 7 → Nat := ![1,1,pos,k,0,0,0]
def bank (flip : Bool) (n m w : Nat) (bits : List Bool) : Fin 7 → List Bool :=
  ![if flip then word m else word n,if flip then word n else word m,
    frame bits,UnaryTemplate.tape w,[],[],[]]
def doubleSlots (flip : Bool) : Fin 3 → Fin 7 :=
  if flip then ![1,0,2] else ![0,1,2]
def advanceSlots (i : Fin 4) : Fin 7 := i.castAdd 3
def copySlots (flip : Bool) : Fin 4 → Fin 7 :=
  if flip then ![0,4,5,6] else ![1,4,5,6]

theorem double_injective (flip : Bool) : Function.Injective (doubleSlots flip) := by
  cases flip <;> decide
theorem advance_injective : Function.Injective advanceSlots := by decide
theorem copy_injective (flip : Bool) : Function.Injective (copySlots flip) := by
  cases flip <;> decide

theorem pick_double (flip : Bool) (i : Fin 7) :
    RecoveryFocus.pick (doubleSlots flip) i=
      (if flip then ![some 1,some 0,some 2,none,none,none,none]
        else ![some 0,some 1,some 2,none,none,none,none]) i := by
  cases flip with
  | false =>
    fin_cases i
    · exact RecoveryFocus.pick_slot _ (double_injective false) 0
    · exact RecoveryFocus.pick_slot _ (double_injective false) 1
    · exact RecoveryFocus.pick_slot _ (double_injective false) 2
    all_goals decide
  | true =>
    fin_cases i
    · exact RecoveryFocus.pick_slot _ (double_injective true) 1
    · exact RecoveryFocus.pick_slot _ (double_injective true) 0
    · exact RecoveryFocus.pick_slot _ (double_injective true) 2
    all_goals decide
theorem pick_advance (i : Fin 7) : RecoveryFocus.pick advanceSlots i=
    (![some 0,some 1,some 2,some 3,none,none,none] : Fin 7 → Option (Fin 4)) i := by
  fin_cases i
  · exact RecoveryFocus.pick_slot _ advance_injective 0
  · exact RecoveryFocus.pick_slot _ advance_injective 1
  · exact RecoveryFocus.pick_slot _ advance_injective 2
  · exact RecoveryFocus.pick_slot _ advance_injective 3
  all_goals decide

noncomputable def double (flip : Bool) : Machine 7 8 :=
  RecoveryFocus.machine (doubleSlots flip) CapDoublingPass.machine
noncomputable def advance : Machine 7 3 :=
  RecoveryFocus.machine advanceSlots CapSentinelInput.advance
noncomputable def body (flip : Bool) : Machine 7 11 := Composition.machine (double flip) advance
noncomputable def copy (flip : Bool) : Machine 7 4 :=
  RecoveryFocus.machine (copySlots flip) MatrixDimensionHeader.machine

theorem double_run (flip : Bool) (n m w pos k : Nat) (bits : List Bool) (bit : Bool)
    (hm : m ≤ n) (hb : readTapeBit (frame bits) pos=bit) :
    Step (double flip) (6*n+7) (heads pos k) (bank flip n m w bits)
      (heads pos k) (bank (!flip) (2*n+bit.toNat) n w bits) := by
  have h := (CapDoublingPass.run n m (frame bits) pos bit hm hb).dock
    (doubleSlots flip) (double_injective flip) (heads pos k) (bank flip n m w bits)
    (by intro j;cases flip <;> fin_cases j <;> simp [doubleSlots,heads])
    (by intro j;cases flip <;> fin_cases j <;> simp [doubleSlots,bank])
  apply h.congr
  · funext i;cases flip <;> fin_cases i <;> simp [dockH,pick_double,heads]
  · funext i;cases flip <;> fin_cases i <;> simp [install,pick_double,bank]

theorem advance_run (flip : Bool) (n m w pos k : Nat) (bits : List Bool) :
    Step advance 2 (heads pos k) (bank flip n m w bits)
      (heads (pos-2) (k-1)) (bank flip n m w bits) := by
  have h := (CapSentinelInput.advance_run pos k
    (fun i => bank flip n m w bits (advanceSlots i))).dock
    advanceSlots advance_injective (heads pos k) (bank flip n m w bits)
    (by intro j;fin_cases j <;> rfl) (by intro j;rfl)
  apply h.congr
  · funext i;fin_cases i <;> simp [dockH,pick_advance,heads]
  · funext i;fin_cases i <;> simp [install,pick_advance,bank,advanceSlots]

theorem body_run (flip : Bool) (n m w pos k : Nat) (bits : List Bool) (bit : Bool)
    (hm : m ≤ n) (hb : readTapeBit (frame bits) pos=bit) :
    Step (body flip) (6*n+10) (heads pos k) (bank flip n m w bits)
      (heads (pos-2) (k-1)) (bank (!flip) (2*n+bit.toNat) n w bits) := by
  exact ((double_run flip n m w pos k bits bit hm hb).seq
    (advance_run (!flip) (2*n+bit.toNat) n w pos k bits)).enlarge (by omega)

def copied (n : Nat) (H : Fin 7 → Nat) (O : Fin 7 → List Bool) : Prop :=
  O 4=List.replicate n true ∧ H 4=0 ∧
  O 5=List.replicate n true ∧ H 5=0 ∧
  O 6=UnaryTemplate.tape n ∧ H 6=1

theorem copy_run (flip : Bool) (n m w pos k : Nat) (bits : List Bool) :
    ∃ H O, Step (copy flip) (2*n+3) (heads pos k) (bank (!flip) n m w bits) H O ∧
      copied n H O := by
  obtain ⟨H,O,h,h1,h1h,h2,h2h,h3,h3h⟩ := CapSentinelInput.copy_run n
  have step := h.dock (copySlots flip) (copy_injective flip)
    (heads pos k) (bank (!flip) n m w bits)
    (by intro j;cases flip <;> fin_cases j <;> simp [copySlots,heads])
    (by intro j;cases flip <;> fin_cases j <;> simp [copySlots,bank])
  have hs1 : copySlots flip 1=4 := by cases flip <;> rfl
  have hs2 : copySlots flip 2=5 := by cases flip <;> rfl
  have hs3 : copySlots flip 3=6 := by cases flip <;> rfl
  refine ⟨_,_,step,?_,?_,?_,?_,?_,?_⟩
  · rw [←hs1]
    simpa only [install,RecoveryFocus.pick_slot _ (copy_injective flip)] using h1
  · rw [←hs1]
    simpa only [dockH_slot _ (copy_injective flip)] using h1h
  · rw [←hs2]
    simpa only [install,RecoveryFocus.pick_slot _ (copy_injective flip)] using h2
  · rw [←hs2]
    simpa only [dockH_slot _ (copy_injective flip)] using h2h
  · rw [←hs3]
    simpa only [install,RecoveryFocus.pick_slot _ (copy_injective flip)] using h3
  · rw [←hs3]
    simpa only [dockH_slot _ (copy_injective flip)] using h3h

def sizes : Fin 4 → Nat := ![11,11,4,4]
noncomputable def programs (j : Fin 4) : Machine 7 (sizes j) := by
  refine Fin.cases (body false) ?_ j
  intro k
  refine Fin.cases (body true) ?_ k
  intro l
  refine Fin.cases (copy false) ?_ l
  intro last
  have he : last=0 := Subsingleton.elim _ _
  subst last
  exact copy true
def next (j : Fin 4) (_ : Fin (sizes j)) (bits : Fin 7 → Bool) : Option (Fin 4) :=
  if j=0 then if bits 3 then some 1 else some 2
  else if j=1 then if bits 3 then some 0 else some 3 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def bodyIndex (flip : Bool) : Fin 4 := if flip then 1 else 0
def copyIndex (flip : Bool) : Fin 4 := if flip then 3 else 2
noncomputable def boundary (flip : Bool) (n m w pos k : Nat) (bits : List Bool) :=
  controlConfig (RecoveryCalls.code sizes (bodyIndex flip))
    (⟨(programs (bodyIndex flip)).start,heads pos k,bank flip n m w bits⟩ :
      Configuration 7 (sizes (bodyIndex flip)))

theorem read_last (lo hi : List Bool) (b : Bool) :
    readTapeBit (frame (lo++b::hi)) (2*lo.length+1)=b := by
  rw [Streaming.frame_append]
  have h := Streaming.read_append (Streaming.marks lo++[true]) (frame hi) b
  simpa [frame,List.append_assoc] using h

end CapDoublingBodies
