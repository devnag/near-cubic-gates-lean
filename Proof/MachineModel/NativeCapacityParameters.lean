import Proof.MachineModel.NativeAllocation
import Proof.CaseAnalysis.RowsCapacityDriver

/-! The six actual native dimensions produce the exact preparation scale
and exponent. The mode exponent w is separate from the native field width. -/
namespace NearCubicWires.ExtIncidence.NativeCapacityParameters
open LocalBitMultitape RepairOrdinary
open RepairOrdinary.RecoveryRootRound
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Store := Fin 32→List Bool
def put (a : Store) (i j : Fin 32) (x y : List Bool) : Store :=
  fun k=>if k=i then x else if k=j then y else a k
def input (n p F w N Q : ℕ) : Store:=fun i=>
  if i=0 then UnaryTemplate.tape n else if i=1 then List.replicate p true
  else if i=2 then List.replicate F true else if i=3 then List.replicate w true
  else if i=4 then UnaryTemplate.tape N else if i=5 then UnaryTemplate.tape Q else []

theorem focus_put {t s : ℕ} (p : Machine t s) (fuel : ℕ) (src dst : Fin t→List Bool)
    (h : ClockJoin.ReadyRun p fuel src dst) (slots : Fin t→Fin 32)
    (hs : Function.Injective slots) (a : Store) (i j : Fin t) (x y : List Bool)
    (hin : ∀ k,a (slots k)=src k)
    (hout : ∀ k,put a (slots i) (slots j) x y (slots k)=dst k) :
    ClockJoin.ReadyRun (RecoveryFocus.machine slots p) fuel a (put a (slots i) (slots j) x y) := by
  have hf:=h.focus slots hs a hin
  have he:=HierarchyWidth.install_eq slots hs a (put a (slots i) (slots j) x y) dst hout (by
    intro k hk;simp [put,Ne.symm (hk i),Ne.symm (hk j)])
  rw [he] at hf
  exact hf

def data1 (n p F w N Q : ℕ):=put (input n p F w N Q) 6 7
  (List.replicate n true) (List.replicate (n+2) false)
def slots1 : Fin 3→Fin 32:=![0,6,7]
noncomputable def phase1:=RecoveryFocus.machine slots1 (UWalkUnary.machine false false)
noncomputable def joined1:=phase1
theorem ready1 (n p F w N Q : ℕ) : ClockJoin.ReadyRun phase1 (2*n+6) (input n p F w N Q) (data1 n p F w N Q):=by
  apply focus_put _ _ _ _ (DecompositionCountDrivers.template_ready false false n) slots1 (by decide) _ 1 2
  · intro i;fin_cases i <;> simp [input,slots1]
  · intro i;fin_cases i <;> simp [input,put,slots1,UWalkUnary.output,UWalkUnary.lead]
theorem joined1_ready (n p F w N Q : ℕ) : ClockJoin.ReadyRun joined1
    ((2*n+6)) (input n p F w N Q) (data1 n p F w N Q):=
  ready1 n p F w N Q

def data2 (n p F w N Q : ℕ):=put (data1 n p F w N Q) 8 9
  (List.replicate N true) (List.replicate (N+2) false)
def slots2 : Fin 3→Fin 32:=![4,8,9]
noncomputable def phase2:=RecoveryFocus.machine slots2 (UWalkUnary.machine false false)
noncomputable def joined2:=Composition.machine joined1 phase2
theorem ready2 (n p F w N Q : ℕ) : ClockJoin.ReadyRun phase2 (2*N+6) (data1 n p F w N Q) (data2 n p F w N Q):=by
  apply focus_put _ _ _ _ (DecompositionCountDrivers.template_ready false false N) slots2 (by decide) _ 1 2
  · intro i;fin_cases i <;> simp [data1,input,put,slots2]
  · intro i;fin_cases i <;> simp [data1,input,put,slots2,UWalkUnary.output,UWalkUnary.lead]
theorem joined2_ready (n p F w N Q : ℕ) : ClockJoin.ReadyRun joined2
    ((2*n+6)+1+(2*N+6)) (input n p F w N Q) (data2 n p F w N Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined1_ready n p F w N Q) (ready2 n p F w N Q)

def data3 (n p F w N Q : ℕ):=put (data2 n p F w N Q) 10 11
  (List.replicate (Q+1) true) (List.replicate (Q+2) false)
def slots3 : Fin 3→Fin 32:=![5,10,11]
noncomputable def phase3:=RecoveryFocus.machine slots3 (UWalkUnary.machine false true)
noncomputable def joined3:=Composition.machine joined2 phase3
theorem ready3 (n p F w N Q : ℕ) : ClockJoin.ReadyRun phase3 (2*Q+6) (data2 n p F w N Q) (data3 n p F w N Q):=by
  apply focus_put _ _ _ _ (DecompositionCountDrivers.template_ready false true Q) slots3 (by decide) _ 1 2
  · intro i;fin_cases i <;> simp [data2,data1,input,put,slots3]
  · intro i;fin_cases i <;> simp [data2,data1,input,put,slots3,UWalkUnary.output,UWalkUnary.lead]
theorem joined3_ready (n p F w N Q : ℕ) : ClockJoin.ReadyRun joined3
    ((2*n+6)+1+(2*N+6)+1+(2*Q+6)) (input n p F w N Q) (data3 n p F w N Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined2_ready n p F w N Q) (ready3 n p F w N Q)

def data4 (n p F w N Q : ℕ):=put (data3 n p F w N Q) 12 13
  (List.replicate ((n)+(p)) true) (List.replicate ((n)+(p)+2) false)
def slots4 : Fin 4→Fin 32:=![6,1,12,13]
noncomputable def phase4:=RecoveryFocus.machine slots4 (ClockUnarySum.machine)
noncomputable def joined4:=Composition.machine joined3 phase4
theorem ready4 (n p F w N Q : ℕ) : ClockJoin.ReadyRun phase4 (2*((n)+(p))+6) (data3 n p F w N Q) (data4 n p F w N Q):=by
  apply focus_put _ _ _ _ (ClockUnarySum.sum_ready (n) (p)) slots4 (by decide) _ 2 3
  · intro i;fin_cases i <;> simp [data3,data2,data1,input,put,slots4]
  · intro i;fin_cases i <;> simp [data3,data2,data1,input,put,slots4]
theorem joined4_ready (n p F w N Q : ℕ) : ClockJoin.ReadyRun joined4
    ((2*n+6)+1+(2*N+6)+1+(2*Q+6)+1+(2*((n)+(p))+6)) (input n p F w N Q) (data4 n p F w N Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined3_ready n p F w N Q) (ready4 n p F w N Q)

def data5 (n p F w N Q : ℕ):=put (data4 n p F w N Q) 14 15
  (List.replicate ((n+p)+(F)) true) (List.replicate ((n+p)+(F)+2) false)
def slots5 : Fin 4→Fin 32:=![12,2,14,15]
noncomputable def phase5:=RecoveryFocus.machine slots5 (ClockUnarySum.machine)
noncomputable def joined5:=Composition.machine joined4 phase5
theorem ready5 (n p F w N Q : ℕ) : ClockJoin.ReadyRun phase5 (2*((n+p)+(F))+6) (data4 n p F w N Q) (data5 n p F w N Q):=by
  apply focus_put _ _ _ _ (ClockUnarySum.sum_ready (n+p) (F)) slots5 (by decide) _ 2 3
  · intro i;fin_cases i <;> simp [data4,data3,data2,data1,input,put,slots5]
  · intro i;fin_cases i <;> simp [data4,data3,data2,data1,input,put,slots5]
theorem joined5_ready (n p F w N Q : ℕ) : ClockJoin.ReadyRun joined5
    ((2*n+6)+1+(2*N+6)+1+(2*Q+6)+1+(2*((n)+(p))+6)+1+(2*((n+p)+(F))+6)) (input n p F w N Q) (data5 n p F w N Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined4_ready n p F w N Q) (ready5 n p F w N Q)

def data6 (n p F w N Q : ℕ):=put (data5 n p F w N Q) 16 17
  (List.replicate ((n+p+F)+(w)) true) (List.replicate ((n+p+F)+(w)+2) false)
def slots6 : Fin 4→Fin 32:=![14,3,16,17]
noncomputable def phase6:=RecoveryFocus.machine slots6 (ClockUnarySum.machine)
noncomputable def joined6:=Composition.machine joined5 phase6
theorem ready6 (n p F w N Q : ℕ) : ClockJoin.ReadyRun phase6 (2*((n+p+F)+(w))+6) (data5 n p F w N Q) (data6 n p F w N Q):=by
  apply focus_put _ _ _ _ (ClockUnarySum.sum_ready (n+p+F) (w)) slots6 (by decide) _ 2 3
  · intro i;fin_cases i <;> simp [data5,data4,data3,data2,data1,input,put,slots6]
  · intro i;fin_cases i <;> simp [data5,data4,data3,data2,data1,input,put,slots6]
theorem joined6_ready (n p F w N Q : ℕ) : ClockJoin.ReadyRun joined6
    ((2*n+6)+1+(2*N+6)+1+(2*Q+6)+1+(2*((n)+(p))+6)+1+(2*((n+p)+(F))+6)+1+(2*((n+p+F)+(w))+6)) (input n p F w N Q) (data6 n p F w N Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined5_ready n p F w N Q) (ready6 n p F w N Q)

def data7 (n p F w N Q : ℕ):=put (data6 n p F w N Q) 18 19
  (List.replicate ((n+p+F+w)+(N)) true) (List.replicate ((n+p+F+w)+(N)+2) false)
def slots7 : Fin 4→Fin 32:=![16,8,18,19]
noncomputable def phase7:=RecoveryFocus.machine slots7 (ClockUnarySum.machine)
noncomputable def joined7:=Composition.machine joined6 phase7
theorem ready7 (n p F w N Q : ℕ) : ClockJoin.ReadyRun phase7 (2*((n+p+F+w)+(N))+6) (data6 n p F w N Q) (data7 n p F w N Q):=by
  apply focus_put _ _ _ _ (ClockUnarySum.sum_ready (n+p+F+w) (N)) slots7 (by decide) _ 2 3
  · intro i;fin_cases i <;> simp [data6,data5,data4,data3,data2,data1,input,put,slots7]
  · intro i;fin_cases i <;> simp [data6,data5,data4,data3,data2,put,slots7]
theorem joined7_ready (n p F w N Q : ℕ) : ClockJoin.ReadyRun joined7
    ((2*n+6)+1+(2*N+6)+1+(2*Q+6)+1+(2*((n)+(p))+6)+1+(2*((n+p)+(F))+6)+1+(2*((n+p+F)+(w))+6)+1+(2*((n+p+F+w)+(N))+6)) (input n p F w N Q) (data7 n p F w N Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined6_ready n p F w N Q) (ready7 n p F w N Q)

def data8 (n p F w N Q : ℕ):=put (data7 n p F w N Q) 20 21
  (List.replicate ((n+p+F+w+N)+(Q+1)) true) (List.replicate ((n+p+F+w+N)+(Q+1)+2) false)
def slots8 : Fin 4→Fin 32:=![18,10,20,21]
noncomputable def phase8:=RecoveryFocus.machine slots8 (ClockUnarySum.machine)
noncomputable def joined8:=Composition.machine joined7 phase8
theorem ready8 (n p F w N Q : ℕ) : ClockJoin.ReadyRun phase8 (2*((n+p+F+w+N)+(Q+1))+6) (data7 n p F w N Q) (data8 n p F w N Q):=by
  apply focus_put _ _ _ _ (ClockUnarySum.sum_ready (n+p+F+w+N) (Q+1)) slots8 (by decide) _ 2 3
  · intro i;fin_cases i <;> simp [data7,data6,data5,data4,data3,data2,data1,input,put,slots8]
  · intro i;fin_cases i <;> simp [data7,data6,data5,data4,data3,put,slots8]
theorem joined8_ready (n p F w N Q : ℕ) : ClockJoin.ReadyRun joined8
    ((2*n+6)+1+(2*N+6)+1+(2*Q+6)+1+(2*((n)+(p))+6)+1+(2*((n+p)+(F))+6)+1+(2*((n+p+F)+(w))+6)+1+(2*((n+p+F+w)+(N))+6)+1+(2*((n+p+F+w+N)+(Q+1))+6)) (input n p F w N Q) (data8 n p F w N Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined7_ready n p F w N Q) (ready8 n p F w N Q)

def data9 (n p F w N Q : ℕ):=put (data8 n p F w N Q) 22 23
  (UnaryTemplate.tape (n+p+F+w+N+(Q+1))) (List.replicate ((n+p+F+w+N+(Q+1))+3) false)
def slots9 : Fin 3→Fin 32:=![20,22,23]
noncomputable def phase9:=RecoveryFocus.machine slots9 (DimensionTemplate.machine false)
noncomputable def joined9:=Composition.machine joined8 phase9
theorem ready9 (n p F w N Q : ℕ) : ClockJoin.ReadyRun phase9 (2*(n+p+F+w+N+(Q+1))+8) (data8 n p F w N Q) (data9 n p F w N Q):=by
  apply focus_put _ _ _ _ (DimensionTemplate.ready false (n+p+F+w+N+(Q+1))) slots9 (by decide) _ 1 2
  · intro i;fin_cases i <;> simp [data8,data7,data6,data5,data4,data3,data2,data1,input,put,slots9,DimensionTemplate.input]
  · intro i;fin_cases i <;> simp [data8,put,slots9,DimensionTemplate.output]
theorem joined9_ready (n p F w N Q : ℕ) : ClockJoin.ReadyRun joined9
    ((2*n+6)+1+(2*N+6)+1+(2*Q+6)+1+(2*((n)+(p))+6)+1+(2*((n+p)+(F))+6)+1+(2*((n+p+F)+(w))+6)+1+(2*((n+p+F+w)+(N))+6)+1+(2*((n+p+F+w+N)+(Q+1))+6)+1+(2*(n+p+F+w+N+(Q+1))+8)) (input n p F w N Q) (data9 n p F w N Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined8_ready n p F w N Q) (ready9 n p F w N Q)

def data10 (n p F w N Q : ℕ):=put (data9 n p F w N Q) 24 25
  (UnaryTemplate.tape (Q+1)) (List.replicate (Q+1+3) false)
def slots10 : Fin 3→Fin 32:=![10,24,25]
noncomputable def phase10:=RecoveryFocus.machine slots10 (DimensionTemplate.machine false)
noncomputable def joined10:=Composition.machine joined9 phase10
theorem ready10 (n p F w N Q : ℕ) : ClockJoin.ReadyRun phase10 (2*(Q+1)+8) (data9 n p F w N Q) (data10 n p F w N Q):=by
  apply focus_put _ _ _ _ (DimensionTemplate.ready false (Q+1)) slots10 (by decide) _ 1 2
  · intro i;fin_cases i <;> simp [data9,data8,data7,data6,data5,data4,data3,data2,data1,input,put,slots10,DimensionTemplate.input]
  · intro i;fin_cases i <;> simp [data9,data8,data7,data6,data5,data4,data3,put,slots10,DimensionTemplate.output]
theorem joined10_ready (n p F w N Q : ℕ) : ClockJoin.ReadyRun joined10
    ((2*n+6)+1+(2*N+6)+1+(2*Q+6)+1+(2*((n)+(p))+6)+1+(2*((n+p)+(F))+6)+1+(2*((n+p+F)+(w))+6)+1+(2*((n+p+F+w)+(N))+6)+1+(2*((n+p+F+w+N)+(Q+1))+6)+1+(2*(n+p+F+w+N+(Q+1))+8)+1+(2*(Q+1)+8)) (input n p F w N Q) (data10 n p F w N Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined9_ready n p F w N Q) (ready10 n p F w N Q)

def data11 (n p F w N Q : ℕ):=put (data10 n p F w N Q) 26 27
  (List.replicate (w*(Q+1)) true) (List.replicate (WilliamsUnaryProduct.scratch w (Q+1)) false)
def slots11 : Fin 4→Fin 32:=![3,24,26,27]
noncomputable def phase11:=RecoveryFocus.machine slots11 (ClockUnaryProduct.machine)
noncomputable def joined11:=Composition.machine joined10 phase11
theorem ready11 (n p F w N Q : ℕ) : ClockJoin.ReadyRun phase11 (WilliamsUnaryProduct.budget w (Q+1)) (data10 n p F w N Q) (data11 n p F w N Q):=by
  apply focus_put _ _ _ _ (RowCommonResources.product_ready w (Q+1)) slots11 (by decide) _ 2 3
  · intro i;fin_cases i <;> simp [data10,data9,data8,data7,data6,data5,data4,data3,data2,data1,input,put,slots11,WilliamsUnaryProduct.input]
  · intro i;fin_cases i <;> simp [data10,data9,data8,data7,data6,data5,data4,data3,data2,data1,input,put,slots11,WilliamsUnaryProduct.output]
theorem joined11_ready (n p F w N Q : ℕ) : ClockJoin.ReadyRun joined11
    ((2*n+6)+1+(2*N+6)+1+(2*Q+6)+1+(2*((n)+(p))+6)+1+(2*((n+p)+(F))+6)+1+(2*((n+p+F)+(w))+6)+1+(2*((n+p+F+w)+(N))+6)+1+(2*((n+p+F+w+N)+(Q+1))+6)+1+(2*(n+p+F+w+N+(Q+1))+8)+1+(2*(Q+1)+8)+1+(WilliamsUnaryProduct.budget w (Q+1))) (input n p F w N Q) (data11 n p F w N Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined10_ready n p F w N Q) (ready11 n p F w N Q)

def data12 (n p F w N Q : ℕ):=put (data11 n p F w N Q) 28 29
  (UnaryTemplate.tape (w*(Q+1))) (List.replicate ((w*(Q+1))+3) false)
def slots12 : Fin 3→Fin 32:=![26,28,29]
noncomputable def phase12:=RecoveryFocus.machine slots12 (DimensionTemplate.machine false)
noncomputable def joined12:=Composition.machine joined11 phase12
theorem ready12 (n p F w N Q : ℕ) : ClockJoin.ReadyRun phase12 (2*(w*(Q+1))+8) (data11 n p F w N Q) (data12 n p F w N Q):=by
  apply focus_put _ _ _ _ (DimensionTemplate.ready false (w*(Q+1))) slots12 (by decide) _ 1 2
  · intro i;fin_cases i <;> simp [data11,data10,data9,data8,data7,data6,data5,data4,data3,data2,data1,input,put,slots12,DimensionTemplate.input]
  · intro i;fin_cases i <;> simp [data11,put,slots12,DimensionTemplate.output]
theorem joined12_ready (n p F w N Q : ℕ) : ClockJoin.ReadyRun joined12
    ((2*n+6)+1+(2*N+6)+1+(2*Q+6)+1+(2*((n)+(p))+6)+1+(2*((n+p)+(F))+6)+1+(2*((n+p+F)+(w))+6)+1+(2*((n+p+F+w)+(N))+6)+1+(2*((n+p+F+w+N)+(Q+1))+6)+1+(2*(n+p+F+w+N+(Q+1))+8)+1+(2*(Q+1)+8)+1+(WilliamsUnaryProduct.budget w (Q+1))+1+(2*(w*(Q+1))+8)) (input n p F w N Q) (data12 n p F w N Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined11_ready n p F w N Q) (ready12 n p F w N Q)

def output (n p F w N Q : ℕ):=put (data12 n p F w N Q) 30 31
  (CompareMachine.word (w*(Q+1))) (List.replicate ((w*(Q+1))+2) false)
def slots13 : Fin 3→Fin 32:=![28,30,31]
noncomputable def phase13:=RecoveryFocus.machine slots13 (UWalkUnary.machine true false)
noncomputable def joined13:=Composition.machine joined12 phase13
theorem ready13 (n p F w N Q : ℕ) : ClockJoin.ReadyRun phase13 (2*(w*(Q+1))+6) (data12 n p F w N Q) (output n p F w N Q):=by
  apply focus_put _ _ _ _ (DecompositionCountDrivers.template_ready true false (w*(Q+1))) slots13 (by decide) _ 1 2
  · intro i;fin_cases i <;> simp [data12,data11,data10,data9,data8,data7,data6,data5,data4,data3,data2,data1,input,put,slots13]
  · intro i;fin_cases i <;> simp [data12,put,slots13,UWalkUnary.output,UWalkUnary.lead,CompareMachine.word]
theorem joined13_ready (n p F w N Q : ℕ) : ClockJoin.ReadyRun joined13
    ((2*n+6)+1+(2*N+6)+1+(2*Q+6)+1+(2*((n)+(p))+6)+1+(2*((n+p)+(F))+6)+1+(2*((n+p+F)+(w))+6)+1+(2*((n+p+F+w)+(N))+6)+1+(2*((n+p+F+w+N)+(Q+1))+6)+1+(2*(n+p+F+w+N+(Q+1))+8)+1+(2*(Q+1)+8)+1+(WilliamsUnaryProduct.budget w (Q+1))+1+(2*(w*(Q+1))+8)+1+(2*(w*(Q+1))+6)) (input n p F w N Q) (output n p F w N Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined12_ready n p F w N Q) (ready13 n p F w N Q)

noncomputable def machine:=joined13
def budget (n p F w N Q : ℕ):=(2*n+6)+1+(2*N+6)+1+(2*Q+6)+1+(2*((n)+(p))+6)+1+(2*((n+p)+(F))+6)+1+(2*((n+p+F)+(w))+6)+1+(2*((n+p+F+w)+(N))+6)+1+(2*((n+p+F+w+N)+(Q+1))+6)+1+(2*(n+p+F+w+N+(Q+1))+8)+1+(2*(Q+1)+8)+1+(WilliamsUnaryProduct.budget w (Q+1))+1+(2*(w*(Q+1))+8)+1+(2*(w*(Q+1))+6)
theorem ready (n p F w N Q : ℕ) : ClockJoin.ReadyRun machine (budget n p F w N Q) (input n p F w N Q) (output n p F w N Q):=
  joined13_ready n p F w N Q
theorem scale_output (n p F w N Q : ℕ) : output n p F w N Q 22=
    UnaryTemplate.tape (CloseoutRowsPreparationBounds.scale n p F w N Q):=by
  simp [output,data12,data11,data10,data9,put,CloseoutRowsPreparationBounds.scale,Nat.add_assoc]
theorem exponent_output (n p F w N Q : ℕ) : output n p F w N Q 30=CompareMachine.word (w*(Q+1)):=rfl
theorem input_retained (n p F w N Q : ℕ) (i : Fin 6) : output n p F w N Q (i.castAdd 26)=input n p F w N Q (i.castAdd 26):=by
  fin_cases i <;> rfl

end NearCubicWires.ExtIncidence.NativeCapacityParameters

