import Proof.Assembly.Driver
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RecoveryExecution RepairSource.VerifierDecoding
namespace PaidDriverBank
namespace Bank
open FamilyInitGenerator (Scalars)

/-- The literal existing family layout, followed by the seven paid drivers. -/
def layout {α : Type} (t : Nat) (payload : Fin t→α) (cap : α)
 (row : Fin 2→α) (body : Fin 4→α) (count : α) (extra : Fin 11→α) (drivers : Fin 7→α) :
 Fin (t+26)→α :=
 Fin.addCases (m:=t+19) (n:=7) (motive:=fun _=>α)
  (Fin.addCases (m:=t+8) (n:=11) (motive:=fun _=>α)
   (Fin.addCases (m:=t+7) (n:=1) (motive:=fun _=>α)
    (Fin.addCases (m:=t+3) (n:=4) (motive:=fun _=>α)
     (Fin.addCases (m:=t+1) (n:=2) (motive:=fun _=>α)
      (Fin.addCases (m:=t) (n:=1) (motive:=fun _=>α) payload (fun _=>cap)) row) body)
    (fun _=>count)) extra) drivers

def pay (t : Nat) (i : Fin t) : Fin (t+26) :=
 (((((i.castAdd 1).castAdd 2).castAdd 4).castAdd 1).castAdd 11).castAdd 7
def cap (t : Nat) (i : Fin 1) : Fin (t+26) :=
 (((((i.natAdd t).castAdd 2).castAdd 4).castAdd 1).castAdd 11).castAdd 7
def row (t : Nat) (i : Fin 2) : Fin (t+26) :=
 ((((i.natAdd (t+1)).castAdd 4).castAdd 1).castAdd 11).castAdd 7
def body (t : Nat) (i : Fin 4) : Fin (t+26) :=
 (((i.natAdd (t+1+2)).castAdd 1).castAdd 11).castAdd 7
def count (t : Nat) (i : Fin 1) : Fin (t+26) :=
 ((i.natAdd (t+1+2+4)).castAdd 11).castAdd 7
def extra (t : Nat) (i : Fin 11) : Fin (t+26) :=
 (i.natAdd (t+1+2+4+1)).castAdd 7
def source (t : Nat) (i : Fin 7) : Fin (t+26) := i.natAdd (t+19)

theorem all (t : Nat) (P : Fin (t+26)→Prop)
 (hp : ∀i,P (pay t i)) (hc : ∀i,P (cap t i)) (hr : ∀i,P (row t i))
 (hb : ∀i,P (body t i)) (hn : ∀i,P (count t i)) (he : ∀i,P (extra t i))
 (hd : ∀i,P (source t i)) : ∀i,P i := by
 intro i
 refine Fin.addCases (m:=t+19) (n:=7) (fun i=>?_) hd i
 refine Fin.addCases (m:=t+1+2+4+1) (n:=11) (fun i=>?_) he i
 refine Fin.addCases (m:=t+1+2+4) (n:=1) (fun i=>?_) hn i
 refine Fin.addCases (m:=t+1+2) (n:=4) (fun i=>?_) hb i
 refine Fin.addCases (m:=t+1) (n:=2) (fun i=>?_) hr i
 exact Fin.addCases hp hc i

@[simp] theorem layout_pay {α : Type} (t : Nat) (A : Fin t→α) (C : α)
 (R : Fin 2→α) (B : Fin 4→α) (N : α) (E : Fin 11→α) (D : Fin 7→α) (i : Fin t) :
 layout t A C R B N E D (pay t i)=A i := by simp [layout,pay]
@[simp] theorem layout_cap {α : Type} (t : Nat) (A : Fin t→α) (C : α)
 (R : Fin 2→α) (B : Fin 4→α) (N : α) (E : Fin 11→α) (D : Fin 7→α) (i : Fin 1) :
 layout t A C R B N E D (cap t i)=C := by simp [layout,cap]
@[simp] theorem layout_row {α : Type} (t : Nat) (A : Fin t→α) (C : α)
 (R : Fin 2→α) (B : Fin 4→α) (N : α) (E : Fin 11→α) (D : Fin 7→α) (i : Fin 2) :
 layout t A C R B N E D (row t i)=R i := by simp [layout,row]
@[simp] theorem layout_body {α : Type} (t : Nat) (A : Fin t→α) (C : α)
 (R : Fin 2→α) (B : Fin 4→α) (N : α) (E : Fin 11→α) (D : Fin 7→α) (i : Fin 4) :
 layout t A C R B N E D (body t i)=B i := by simp [layout,body]
@[simp] theorem layout_count {α : Type} (t : Nat) (A : Fin t→α) (C : α)
 (R : Fin 2→α) (B : Fin 4→α) (N : α) (E : Fin 11→α) (D : Fin 7→α) (i : Fin 1) :
 layout t A C R B N E D (count t i)=N := by simp [layout,count]
@[simp] theorem layout_extra {α : Type} (t : Nat) (A : Fin t→α) (C : α)
 (R : Fin 2→α) (B : Fin 4→α) (N : α) (E : Fin 11→α) (D : Fin 7→α) (i : Fin 11) :
 layout t A C R B N E D (extra t i)=E i := by simp [layout,extra]
@[simp] theorem layout_source {α : Type} (t : Nat) (A : Fin t→α) (C : α)
 (R : Fin 2→α) (B : Fin 4→α) (N : α) (E : Fin 11→α) (D : Fin 7→α) (i : Fin 7) :
 layout t A C R B N E D (source t i)=D i := by simp [layout,source]

def values (m : Scalars) : Fin 7→Nat := ![m.S,m.R,m.B,m.b,m.v,m.N,m.N*m.b]
def inputH (t : Nat) : Fin (t+26)→Nat :=
 layout t (fun _=>0) 0 (fun _=>0) (fun _=>0) 0 (fun _=>0) (fun _=>1)
def heads (t : Nat) : Fin (t+26)→Nat :=
 layout t (fun _=>0) 0 (fun _=>0) (fun _=>0) 1 ![0,0,0,0,0,0,0,0,0,1,0] (fun _=>1)
def finalH (t : Nat) : Fin (t+26)→Nat :=
 layout t (fun _=>0) 0 (fun _=>0) (fun _=>0) 1 (fun _=>0) (fun _=>1)
def input (t : Nat) (m : Scalars) (D : List Bool) : Fin (t+26)→List Bool :=
 layout t (fun _=>[]) [] (fun _=>[]) ![D,[],[],[]] [] (fun _=>[])
  (fun i=>CompareMachine.word (values m i))
def bank (t : Nat) (m : Scalars) (D : List Bool) (k : Nat) : Fin (t+26)→List Bool :=
 layout t (fun _=>if 1≤k then List.replicate m.S false else [])
  (if 2≤k then List.replicate m.R false else [])
  ![[],if 3≤k then List.replicate m.B true else []]
  ![D,if 1≤k then List.replicate m.S false else [],
    if 1≤k then List.replicate m.S true else [],
    if 1≤k then List.replicate (m.S+1) false else []]
  (if 6≤k then CompareMachine.word m.N else [false])
  ![if 7≤k then List.replicate (m.N*m.b) true else [],[],
    if 4≤k then List.replicate m.b true else [],
    if 5≤k then List.replicate m.v true else [],[],
    if 5≤k then List.replicate (2*m.v+1) false else [],
    if 5≤k then frame (SignedSortKey.binary m.v 0) else [],[],[],
    if 6≤k then CompareMachine.word m.N else [false],[]]
  (fun i=>CompareMachine.word (values m i))

def first (t : Nat) : Fin 7→Fin (t+26)→Option Bool :=
 ![layout t (fun _=>some false) none (fun _=>none) ![none,some false,some true,some false] none (fun _=>none) (fun _=>none),
   layout t (fun _=>none) (some false) (fun _=>none) (fun _=>none) none (fun _=>none) (fun _=>none),
   layout t (fun _=>none) none ![none,some true] (fun _=>none) none (fun _=>none) (fun _=>none),
   layout t (fun _=>none) none (fun _=>none) (fun _=>none) none ![none,none,some true,none,none,none,none,none,none,none,none] (fun _=>none),
   layout t (fun _=>none) none (fun _=>none) (fun _=>none) none ![none,none,none,some true,none,some false,some true,none,none,none,none] (fun _=>none),
   layout t (fun _=>none) none (fun _=>none) (fun _=>none) (some true) ![none,none,none,none,none,none,none,none,none,some true,none] (fun _=>none),
   layout t (fun _=>none) none (fun _=>none) (fun _=>none) none ![some true,none,none,none,none,none,none,none,none,none,none] (fun _=>none)]
def second (t : Nat) (j : Fin 7) : Fin (t+26)→Option Bool :=
 if j=4 then
  layout t (fun _=>none) none (fun _=>none) (fun _=>none) none ![none,none,none,none,none,some false,some false,none,none,none,none] (fun _=>none)
 else fun _=>none
def tail (t : Nat) (j : Fin 7) : Fin (t+26)→Option Bool :=
 if j=0 then layout t (fun _=>none) none (fun _=>none) ![none,none,none,some false] none (fun _=>none) (fun _=>none)
 else if j=4 then second t j else fun _=>none

def pass (t : Nat) (j : Fin 7) : Machine (t+26) 5 :=
 Driver.machine (source t j) (first t j) (second t j) (tail t j)

@[simp] theorem replicate_tail (b : Bool) (n : Nat) :
 List.replicate n b++[b]=List.replicate (n+1) b := by
 rw [List.replicate_add]; rfl

theorem ready (t : Nat) (m : Scalars) (D : List Bool) (j : Fin 7) :
 Driver.Ready (source t j) (first t j) (second t j) (tail t j)
  (heads t) (bank t m D j.val) (values m j) := by
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · simp [heads]
 · simp [bank]
 · fin_cases j <;> simp [first]
 · fin_cases j <;> simp [second]
 · fin_cases j <;> simp [tail,second]
 · apply all t
   · intro i; fin_cases j <;> simp [first,second,tail,heads,bank]
   all_goals intro i; fin_cases i <;> fin_cases j <;> simp [first,second,tail,heads,bank]

theorem output_next (t : Nat) (m : Scalars) (D : List Bool) (j : Fin 7) :
 Driver.output (first t j) (second t j) (tail t j) (bank t m D j.val) (values m j)=
  bank t m D (j.val+1) := by
 apply funext
 apply all t
 · intro i; fin_cases j <;> simp [Driver.output,first,second,tail,bank,values]
 all_goals intro i; fin_cases i <;> fin_cases j <;>
  simp [Driver.output,first,second,tail,bank,values,CompareMachine.word]

theorem pass_run (t : Nat) (m : Scalars) (D : List Bool) (j : Fin 7) :
 Step (pass t j) (4*values m j+2) (heads t) (bank t m D j.val)
  (heads t) (bank t m D (j.val+1)) := by
 have h := Driver.run (source t j) (first t j) (second t j) (tail t j)
  (heads t) (bank t m D j.val) (values m j) (ready t m D j)
 rw [output_next] at h
 exact h

namespace Once
variable {t : Nat}
def machine (W : Fin t→Option Bool) (M : Fin t→HeadMove) : Machine t 2 where
 descriptionBits:=0
 start:=0
 halted:=fun q=>q.val==1
 rule:=fun q _=>if q.val=0 then some ⟨1,W,M⟩ else none

theorem run (W : Fin t→Option Bool) (M : Fin t→HeadMove)
 (H : Fin t→Nat) (A : Fin t→List Bool) :
 Step (machine W M) 1 H A (fun i=>(M i).apply (H i))
  (fun i=>match W i with | none=>A i | some b=>writeTapeBit (A i) (H i) b) := by
 have hs : step (machine W M) (⟨0,H,A⟩ : Configuration t 2)=
  some (applyAction (⟨0,H,A⟩ : Configuration t 2) ⟨1,W,M⟩) := rfl
 obtain ⟨r,hr,hf,hn⟩:=(Timed.single (by rfl) hs).run (by rfl)
 exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
end Once

def setupW (t : Nat) : Fin (t+26)→Option Bool :=
 layout t (fun _=>none) none (fun _=>none) (fun _=>none) (some false)
  ![none,none,none,none,none,none,none,none,none,some false,none] (fun _=>none)
def setupM (t : Nat) : Fin (t+26)→HeadMove :=
 layout t (fun _=>.stay) .stay (fun _=>.stay) (fun _=>.stay) .right
  ![.stay,.stay,.stay,.stay,.stay,.stay,.stay,.stay,.stay,.right,.stay] (fun _=>.stay)
def cleanupM (t : Nat) : Fin (t+26)→HeadMove :=
 layout t (fun _=>.stay) .stay (fun _=>.stay) (fun _=>.stay) .stay
  ![.stay,.stay,.stay,.stay,.stay,.stay,.stay,.stay,.stay,.left,.stay] (fun _=>.stay)
def setup (t : Nat) := Once.machine (setupW t) (setupM t)
def cleanup (t : Nat) := Once.machine (fun _ : Fin (t+26)=>none) (cleanupM t)

theorem setup_run (t : Nat) (m : Scalars) (D : List Bool) :
 Step (setup t) 1 (inputH t) (input t m D) (heads t) (bank t m D 0) := by
 have h:=Once.run (setupW t) (setupM t) (inputH t) (input t m D)
 have hh : (fun i=>(setupM t i).apply (inputH t i))=heads t := by
  apply funext; apply all t
  · intro i; simp [setupM,inputH,heads,HeadMove.apply]
  all_goals intro i; fin_cases i <;> simp [setupM,inputH,heads,HeadMove.apply]
 have ht : (fun i=>
   match setupW t i with
   | none=>input t m D i
   | some b=>writeTapeBit (input t m D i) (inputH t i) b)=bank t m D 0 := by
  apply funext; apply all t
  · intro i; simp [setupW,input,inputH,bank]
  all_goals intro i; fin_cases i <;> simp [setupW,input,inputH,bank,writeTapeBit]
 rw [hh,ht] at h
 exact h

theorem cleanup_run (t : Nat) (m : Scalars) (D : List Bool) :
 Step (cleanup t) 1 (heads t) (bank t m D 7) (finalH t) (bank t m D 7) := by
 have h:=Once.run (fun _ : Fin (t+26)=>none) (cleanupM t) (heads t) (bank t m D 7)
 have hh : (fun i=>(cleanupM t i).apply (heads t i))=finalH t := by
  apply funext; apply all t
  · intro i; simp [cleanupM,heads,finalH,HeadMove.apply]
  all_goals intro i; fin_cases i <;> simp [cleanupM,heads,finalH,HeadMove.apply]
 rw [hh] at h
 exact h

def machine (t : Nat) : Machine (t+26) 39 :=
 Composition.machine (setup t)
  (Composition.machine (pass t 0)
   (Composition.machine (pass t 1)
    (Composition.machine (pass t 2)
     (Composition.machine (pass t 3)
      (Composition.machine (pass t 4)
       (Composition.machine (pass t 5)
        (Composition.machine (pass t 6) (cleanup t))))))))

attribute [local irreducible] Step Composition.machine pass setup cleanup machine values bank heads inputH input finalH

set_option diagnostics true in
theorem run (t : Nat) (m : Scalars) (D : List Bool) :
 Step (machine t) (4*(m.S+m.R+m.B+m.b+m.v+m.N+m.N*m.b)+24)
  (inputH t) (input t m D) (finalH t) (bank t m D 7) := by
 let p6 : Machine (t+26) 7 := Composition.machine (pass t 6) (cleanup t)
 let p5 : Machine (t+26) 12 := Composition.machine (pass t 5) p6
 let p4 : Machine (t+26) 17 := Composition.machine (pass t 4) p5
 let p3 : Machine (t+26) 22 := Composition.machine (pass t 3) p4
 let p2 : Machine (t+26) 27 := Composition.machine (pass t 2) p3
 let p1 : Machine (t+26) 32 := Composition.machine (pass t 1) p2
 let p0 : Machine (t+26) 37 := Composition.machine (pass t 0) p1
 have h6 : Step p6 (4*values m 6+2+1+1) (heads t) (bank t m D 6) (finalH t) (bank t m D 7) :=
  (pass_run t m D 6).seq (cleanup_run t m D)
 have h5 : Step p5 (4*values m 5+2+1+(4*values m 6+2+1+1)) (heads t) (bank t m D 5) (finalH t) (bank t m D 7) :=
  (pass_run t m D 5).seq h6
 have h4 : Step p4 (4*values m 4+2+1+(4*values m 5+2+1+(4*values m 6+2+1+1))) (heads t) (bank t m D 4) (finalH t) (bank t m D 7) :=
  (pass_run t m D 4).seq h5
 have h3 : Step p3 (4*values m 3+2+1+(4*values m 4+2+1+(4*values m 5+2+1+(4*values m 6+2+1+1)))) (heads t) (bank t m D 3) (finalH t) (bank t m D 7) :=
  (pass_run t m D 3).seq h4
 have h2 : Step p2 (4*values m 2+2+1+(4*values m 3+2+1+(4*values m 4+2+1+(4*values m 5+2+1+(4*values m 6+2+1+1))))) (heads t) (bank t m D 2) (finalH t) (bank t m D 7) :=
  (pass_run t m D 2).seq h3
 have h1 : Step p1 (4*values m 1+2+1+(4*values m 2+2+1+(4*values m 3+2+1+(4*values m 4+2+1+(4*values m 5+2+1+(4*values m 6+2+1+1)))))) (heads t) (bank t m D 1) (finalH t) (bank t m D 7) :=
  (pass_run t m D 1).seq h2
 have h0 : Step p0 (4*values m 0+2+1+(4*values m 1+2+1+(4*values m 2+2+1+(4*values m 3+2+1+(4*values m 4+2+1+(4*values m 5+2+1+(4*values m 6+2+1+1))))))) (heads t) (bank t m D 0) (finalH t) (bank t m D 7) :=
  (pass_run t m D 0).seq h1
 have h := (setup_run t m D).seq h0
 have hm : Composition.machine (setup t) p0=machine t := by unfold machine; rfl
 rw [hm] at h
 have hc : 1+1+(4*values m 0+2+1+(4*values m 1+2+1+(4*values m 2+2+1+(4*values m 3+2+1+(4*values m 4+2+1+(4*values m 5+2+1+(4*values m 6+2+1+1)))))))=
   4*(m.S+m.R+m.B+m.b+m.v+m.N+m.N*m.b)+24 := by
  unfold values
  change 1+1+(4*m.S+2+1+(4*m.R+2+1+(4*m.B+2+1+(4*m.b+2+1+
   (4*m.v+2+1+(4*m.N+2+1+(4*(m.N*m.b)+2+1+1)))))))=
   4*(m.S+m.R+m.B+m.b+m.v+m.N+m.N*m.b)+24
  omega
 rw [hc] at h
 exact h

end Bank
end PaidDriverBank
