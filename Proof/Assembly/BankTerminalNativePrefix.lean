import Proof.Assembly.UnaryDriver
import Proof.Assembly.Dispatch

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.defProp false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RecoveryExecution RepairRepresentation RepairSource.VerifierDecoding
namespace TerminalPrefixDriver
namespace Bank
abbrev once := @PaidDriverBank.Bank.Once.machine

def denWord : List Bool := [true,true,true,false,true,true,false]
theorem denWord_eq : denWord=frame (natWord 1) := by decide

def denPrefix : Fin 8 → List Bool :=
 ![[],[true],[true,true],[true,true,true],[true,true,true,false],
   [true,true,true,false,true],[true,true,true,false,true,true],denWord]
def letter : Fin 7 → Bool := ![true,true,true,false,true,true,false]
@[simp] theorem prefix_zero : denPrefix 0=[] := rfl
@[simp] theorem prefix_last : denPrefix 7=denWord := rfl

theorem write_prefix (k : Fin 7) :
 writeTapeBit (denPrefix k.castSucc) k.val (letter k)=denPrefix k.succ := by
 fin_cases k <;> rfl

variable {t : Nat}
def heads (src : Fin t) (D : Fin t→Bool) : Fin t→Nat :=
 fun i=>if i=src then 1 else if D i then 1 else 0
def headed (src den : Fin t) (D : Fin t→Bool) (k : Nat) : Fin t→Nat :=
 fun i=>if i=den then k else heads src D i
def bank (den : Fin t) (D : Fin t→Bool) (A : Fin t→List Bool) (k : Fin 8) : Fin t→List Bool :=
 fun i=>if i=den then denPrefix k else if D i then [false] else A i

def setupW (D : Fin t→Bool) : Fin t→Option Bool := fun i=>if D i then some false else none
def setupM (src : Fin t) (D : Fin t→Bool) : Fin t→HeadMove :=
 fun i=>if i=src then .right else if D i then .right else .stay
def setup (src : Fin t) (D : Fin t→Bool) := once (setupW D) (setupM src D)
def writeW (den : Fin t) (b : Bool) : Fin t→Option Bool := fun i=>if i=den then some b else none
def move (den : Fin t) (m : HeadMove) : Fin t→HeadMove := fun i=>if i=den then m else .stay
def write (den : Fin t) (k : Fin 7) := once (writeW den (letter k)) (move den .right)
def rewind (den : Fin t) := once (fun _ : Fin t=>none) (move den .left)
def first (dst : Fin t) : Fin t→Option Bool := fun i=>if i=dst then some true else none
def copy (src dst : Fin t) := UnaryDriver.machine src (first dst) (fun _=>none) (fun _=>none)
def output (src den dst : Fin t) (D : Fin t→Bool) (A : Fin t→List Bool) (v : Nat) : Fin t→List Bool :=
 fun i=>if i=dst then CompareMachine.word v else bank den D A 7 i

variable (src den dst : Fin t) (D : Fin t→Bool) (A : Fin t→List Bool) (v : Nat)
variable (hsd : src≠den) (hsx : src≠dst) (hdx : den≠dst)
 (hds : D src=false) (hdd : D den=false) (hdv : D dst=true)
 (ha : A src=UnaryTemplate.tape v) (had : A den=[])
 (hblank : ∀ i, D i=true → A i=[])

include hsd hdd in
theorem heads_den : heads src D den=0 := by simp [heads,Ne.symm hsd,hdd]

include hsd hdd had hblank in
theorem setup_run : Step (setup src D) 1 (fun _=>0) A
 (headed src den D 0) (bank den D A 0) := by
 have h:=PaidDriverBank.Bank.Once.run (setupW D) (setupM src D) (fun _=>0) A
 have hh : (fun i=>(setupM src D i).apply 0)=headed src den D 0 := by
  funext i
  by_cases hid:i=den
  · subst i; simp [setupM,headed,HeadMove.apply,Ne.symm hsd,hdd]
  · simp [setupM,headed,heads,hid,HeadMove.apply]; split_ifs <;> rfl
 have ht : (fun i=>match setupW D i with | none=>A i | some b=>writeTapeBit (A i) 0 b)=bank den D A 0 := by
  funext i
  by_cases hid:i=den
  · subst i; simp [setupW,bank,hdd,had]
  · cases hdi:D i with
    | false => simp [setupW,bank,hid,hdi]
    | true => simp [setupW,bank,hid,hdi,hblank i hdi,writeTapeBit]
 rw [hh] at h
 exact (congrArg (fun B=>Step (setup src D) 1 (fun _=>0) A (headed src den D 0) B) ht).mp h

theorem write_run (k : Fin 7) : Step (write den k) 1
 (headed src den D k.val) (bank den D A k.castSucc)
 (headed src den D (k.val+1)) (bank den D A k.succ) := by
 have h:=PaidDriverBank.Bank.Once.run (writeW den (letter k)) (move den .right)
  (headed src den D k.val) (bank den D A k.castSucc)
 have hh : (fun i=>(move den .right i).apply (headed src den D k.val i))=
   headed src den D (k.val+1) := by
  funext i; by_cases hi:i=den <;> simp [move,headed,hi,HeadMove.apply]
 have ht : (fun i=>match writeW den (letter k) i with
   | none=>bank den D A k.castSucc i
   | some b=>writeTapeBit (bank den D A k.castSucc i) (headed src den D k.val i) b)=bank den D A k.succ := by
  funext i; by_cases hi:i=den
  · subst i; simp [writeW,bank,headed,write_prefix]
  · simp [writeW,bank,hi]
 rw [hh] at h
 exact (congrArg (fun B=>Step (write den k) 1 (headed src den D k.val)
  (bank den D A k.castSucc) (headed src den D (k.val+1)) B) ht).mp h

theorem rewind_run (k : Nat) : Step (rewind den) 1
 (headed src den D (k+1)) (bank den D A 7)
 (headed src den D k) (bank den D A 7) := by
 have h:=PaidDriverBank.Bank.Once.run (fun _ : Fin t=>none) (move den .left)
  (headed src den D (k+1)) (bank den D A 7)
 have hh : (fun i=>(move den .left i).apply (headed src den D (k+1) i))=headed src den D k := by
  funext i; by_cases hi:i=den <;> simp [move,headed,hi,HeadMove.apply]
 rw [hh] at h
 exact h

include hsd hsx hdx hds hdv ha in
theorem copy_ready : UnaryDriver.Ready src (first dst) (fun _=>none) (fun _=>none)
 (headed src den D 0) (bank den D A 7) v := by
 refine ⟨?_,?_,?_,rfl,rfl,?_⟩
 · simp [headed,heads,hsd]
 · simp [bank,hsd,hds,ha]
 · simp [first,hsx]
 · intro i hi
   have hid : i=dst := by
    by_contra hne
    simp [first,hne] at hi
   subst i
   simp [headed,bank,Ne.symm hdx,heads,hdv]

include hdx hdv in
theorem copy_output : UnaryDriver.output (first dst) (fun _=>none) (fun _=>none)
 (bank den D A 7) v=output src den dst D A v := by
 funext i
 by_cases hi:i=dst
 · subst i
   simp [UnaryDriver.output,output,first,bank,Ne.symm hdx,hdv,CompareMachine.word]
 · simp [UnaryDriver.output,output,first,hi]

include hsd hsx hdx hds hdv ha in
theorem copy_run : Step (copy src dst) (4*v+2)
 (headed src den D 0) (bank den D A 7)
 (headed src den D 0) (output src den dst D A v) := by
 have h:=UnaryDriver.run src (first dst) (fun _=>none) (fun _=>none)
  (headed src den D 0) (bank den D A 7) v
  (copy_ready src den dst D A v hsd hsx hdx hds hdv ha)
 rw [copy_output src den dst D A v hdx hdv] at h
 exact h

def machine (src den dst : Fin t) (D : Fin t→Bool) : Machine t 35 :=
 Composition.machine (setup src D) (Composition.machine (write den 0) (Composition.machine (write den 1) (Composition.machine (write den 2) (Composition.machine (write den 3) (Composition.machine (write den 4) (Composition.machine (write den 5) (Composition.machine (write den 6) (Composition.machine (rewind den) (Composition.machine (rewind den) (Composition.machine (rewind den) (Composition.machine (rewind den) (Composition.machine (rewind den) (Composition.machine (rewind den) (Composition.machine (rewind den) (copy src dst)))))))))))))))

include hsd hsx hdx hds hdd hdv ha had hblank in
attribute [local irreducible] Step Composition.machine setup write rewind copy
 heads headed bank output machine in
 theorem run : Step (machine src den dst D) (4*v+32) (fun _=>0) A
 (headed src den D 0) (output src den dst D A v) := by
 let p15 : Machine t 5 := copy src dst
 have h15 : Step p15 (4*v+2) (headed src den D 0) (bank den D A 7)
  (headed src den D 0) (output src den dst D A v) :=
  copy_run src den dst D A v hsd hsx hdx hds hdv ha
 let p14 : Machine t 7 := Composition.machine (rewind den) p15
 have h14 : Step p14 (4*v+4) (headed src den D 1) (bank den D A 7)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (rewind_run src den D A 0).seq h15
  have hc : 1+1+(4*v+2)=4*v+4 := by omega
  rw [hc] at h
  exact h
 let p13 : Machine t 9 := Composition.machine (rewind den) p14
 have h13 : Step p13 (4*v+6) (headed src den D 2) (bank den D A 7)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (rewind_run src den D A 1).seq h14
  have hc : 1+1+(4*v+4)=4*v+6 := by omega
  rw [hc] at h
  exact h
 let p12 : Machine t 11 := Composition.machine (rewind den) p13
 have h12 : Step p12 (4*v+8) (headed src den D 3) (bank den D A 7)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (rewind_run src den D A 2).seq h13
  have hc : 1+1+(4*v+6)=4*v+8 := by omega
  rw [hc] at h
  exact h
 let p11 : Machine t 13 := Composition.machine (rewind den) p12
 have h11 : Step p11 (4*v+10) (headed src den D 4) (bank den D A 7)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (rewind_run src den D A 3).seq h12
  have hc : 1+1+(4*v+8)=4*v+10 := by omega
  rw [hc] at h
  exact h
 let p10 : Machine t 15 := Composition.machine (rewind den) p11
 have h10 : Step p10 (4*v+12) (headed src den D 5) (bank den D A 7)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (rewind_run src den D A 4).seq h11
  have hc : 1+1+(4*v+10)=4*v+12 := by omega
  rw [hc] at h
  exact h
 let p9 : Machine t 17 := Composition.machine (rewind den) p10
 have h9 : Step p9 (4*v+14) (headed src den D 6) (bank den D A 7)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (rewind_run src den D A 5).seq h10
  have hc : 1+1+(4*v+12)=4*v+14 := by omega
  rw [hc] at h
  exact h
 let p8 : Machine t 19 := Composition.machine (rewind den) p9
 have h8 : Step p8 (4*v+16) (headed src den D 7) (bank den D A 7)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (rewind_run src den D A 6).seq h9
  have hc : 1+1+(4*v+14)=4*v+16 := by omega
  rw [hc] at h
  exact h
 let p7 : Machine t 21 := Composition.machine (write den 6) p8
 have h7 : Step p7 (4*v+18) (headed src den D 6) (bank den D A 6)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (write_run src den D A 6).seq h8
  have hc : 1+1+(4*v+16)=4*v+18 := by omega
  rw [hc] at h
  exact h
 let p6 : Machine t 23 := Composition.machine (write den 5) p7
 have h6 : Step p6 (4*v+20) (headed src den D 5) (bank den D A 5)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (write_run src den D A 5).seq h7
  have hc : 1+1+(4*v+18)=4*v+20 := by omega
  rw [hc] at h
  exact h
 let p5 : Machine t 25 := Composition.machine (write den 4) p6
 have h5 : Step p5 (4*v+22) (headed src den D 4) (bank den D A 4)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (write_run src den D A 4).seq h6
  have hc : 1+1+(4*v+20)=4*v+22 := by omega
  rw [hc] at h
  exact h
 let p4 : Machine t 27 := Composition.machine (write den 3) p5
 have h4 : Step p4 (4*v+24) (headed src den D 3) (bank den D A 3)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (write_run src den D A 3).seq h5
  have hc : 1+1+(4*v+22)=4*v+24 := by omega
  rw [hc] at h
  exact h
 let p3 : Machine t 29 := Composition.machine (write den 2) p4
 have h3 : Step p3 (4*v+26) (headed src den D 2) (bank den D A 2)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (write_run src den D A 2).seq h4
  have hc : 1+1+(4*v+24)=4*v+26 := by omega
  rw [hc] at h
  exact h
 let p2 : Machine t 31 := Composition.machine (write den 1) p3
 have h2 : Step p2 (4*v+28) (headed src den D 1) (bank den D A 1)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (write_run src den D A 1).seq h3
  have hc : 1+1+(4*v+26)=4*v+28 := by omega
  rw [hc] at h
  exact h
 let p1 : Machine t 33 := Composition.machine (write den 0) p2
 have h1 : Step p1 (4*v+30) (headed src den D 0) (bank den D A 0)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (write_run src den D A 0).seq h2
  have hc : 1+1+(4*v+28)=4*v+30 := by omega
  rw [hc] at h
  exact h
 let p0 : Machine t 35 := Composition.machine (setup src D) p1
 have h0 : Step p0 (4*v+32) (fun _=>0) (A)
  (headed src den D 0) (output src den dst D A v) := by
  have h := (setup_run src den D A hsd hdd had hblank).seq h1
  have hc : 1+1+(4*v+30)=4*v+32 := by omega
  rw [hc] at h
  exact h
 unfold machine
 exact h0

end Bank
end TerminalPrefixDriver
