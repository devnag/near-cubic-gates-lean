import Proof.Assembly.ClosureBinaryCacheParameters
import Proof.Supplier.RowCommonResources
import Proof.PCP.ProjectionDimensionTemplate
import Proof.Supplier.RowTupleFields

/-! Fixed finite arithmetic composition producing the cold binary-cache palette
from six original runtime words. Generated wiring is checked for aliasing and
unproduced reads; every step and exact final store are checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryCacheColdMetadata
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding

noncomputable def zeroOutput (w : Nat) := Classical.choose (RowTupleColdFields.zero_ready w)
theorem zero_spec (w : Nat) :
    ClockJoin.ReadyRun ClockNormalize.machine (4*w+4) (ClockScalarFields.zeroInput w) (zeroOutput w) ∧
    zeroOutput w 0=List.replicate w true ∧
    zeroOutput w 2=RepairOrdinary.frame (SignedSortKey.binary w 0) :=
  Classical.choose_spec (RowTupleColdFields.zero_ready w)

def v1 (L _q _N _K _W : Nat) := (L)+(1)

def v2 (L q N K W : Nat) := (v1 L q N K W)+(1)

def v3 (_L q _N _K _W : Nat) := (q)+1

def v4 (L q N K W : Nat) := (v2 L q N K W)+(v1 L q N K W)

def v5 (L q N K W : Nat) := (v4 L q N K W)+(v3 L q N K W)

def v6 (L q N K W : Nat) := (v5 L q N K W)*(v5 L q N K W)

def v7 (L q N K W : Nat) := (v6 L q N K W)*(1024)

def v8 (L q N K W : Nat) := (v1 L q N K W)*(8)

def v9 (L q N K W : Nat) := (v8 L q N K W)+(12)

def v10 (L q N K W : Nat) := (v7 L q N K W)*(16)

def v11 (L q N K W : Nat) := (v10 L q N K W)+(4)

def v12 (L q N K W : Nat) := (v11 L q N K W)*(N)

def v13 (L q N K W : Nat) := (v7 L q N K W)*(5)

def v14 (L q N K W : Nat) := (v12 L q N K W)+(v13 L q N K W)

def v15 (_L q _N _K _W : Nat) := (q)*(9)

def v16 (L q N K W : Nat) := (v14 L q N K W)+(v15 L q N K W)

def v17 (_L _q _N K _W : Nat) := (K)*(7)

def v18 (L q N K W : Nat) := (v16 L q N K W)+(v17 L q N K W)

def v19 (_L _q _N _K W : Nat) := (W)*(2)

def v20 (L q N K W : Nat) := (v18 L q N K W)+(v19 L q N K W)

def v21 (L q N K W : Nat) := (v20 L q N K W)+(133)

def v22 (L q N K W : Nat) := (v21 L q N K W)+(1)

theorem width_eq (L q N K W : Nat) : v1 L q N K W=BinaryCacheColdParameters.w L := by
  simp only [v1,BinaryCacheColdParameters.w]

theorem bound_eq (L q N K W : Nat) : v2 L q N K W=BinaryCacheColdParameters.B L := by
  simp only [v1,v2,BinaryCacheColdParameters.B]

theorem scale_eq (L q N K W : Nat) : v5 L q N K W=BinaryCacheColdParameters.X L q := by
  simp only [v1,v2,v3,v4,v5,BinaryCacheColdParameters.X,BinaryCacheColdParameters.B,BinaryCacheColdParameters.w]
  ring

theorem reset_eq (L q N K W : Nat) : v7 L q N K W=BinaryCacheColdParameters.R L q := by
  simp only [v1,v2,v3,v4,v5,v6,v7,BinaryCacheColdParameters.R,BinaryCacheColdParameters.X,BinaryCacheColdParameters.B,BinaryCacheColdParameters.w]
  ring

theorem counter_eq (L q N K W : Nat) : v9 L q N K W=BinaryCacheColdParameters.C L := by
  simp only [v1,v8,v9,BinaryCacheColdParameters.C,BinaryCacheColdParameters.w]
  ring

theorem reserve_eq (L q N K W : Nat) : v21 L q N K W=BinaryCacheColdParameters.S L q N K W := by
  simp only [v1,v2,v3,v4,v5,v6,v7,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,BinaryCacheColdParameters.S,BinaryCacheColdParameters.X,BinaryCacheColdParameters.B,BinaryCacheColdParameters.w]
  ring

theorem capacity_eq (L q N K W : Nat) : v22 L q N K W=BinaryCacheColdParameters.U L q N K W := by
  simp only [v1,v2,v3,v4,v5,v6,v7,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,BinaryCacheColdParameters.U,BinaryCacheColdParameters.S,BinaryCacheColdParameters.X,BinaryCacheColdParameters.B,BinaryCacheColdParameters.w]
  ring

abbrev Store := Fin 88→List Bool

def input (L q N K W : Nat) (membership : List Bool) : Store := fun i=>
  if i=0 then List.replicate L true else if i=1 then UnaryTemplate.tape q else if i=2 then UnaryTemplate.tape N else if i=3 then UnaryTemplate.tape K else if i=4 then List.replicate W true else if i=5 then membership else []

theorem input_fresh (L q N K W : Nat) (membership : List Bool) (i : Fin 88) (hi : 6 ≤ i.val) : input L q N K W membership i=[] := by
  simp only [input]
  split_ifs <;> first | rfl | (exfalso; omega)

def slots1 : Fin 2→Fin 88 := ![6,7]

theorem slots1_inj : Function.Injective slots1 := by decide

noncomputable def phase1 := RecoveryFocus.machine slots1 (HierarchyFixedWord.machine (List.replicate (1) true))

noncomputable def data1 (L q N K W : Nat) (membership : List Bool) : Store := install slots1 (input L q N K W membership) (![List.replicate (1) true,List.replicate (List.replicate (1) true).length false])

theorem data1_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 2) : data1 L q N K W membership (slots1 j)=(![List.replicate (1) true,List.replicate (List.replicate (1) true).length false]) j :=
  install_slot slots1 slots1_inj (input L q N K W membership) _ j

theorem data1_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots1 j≠k) : data1 L q N K W membership k=input L q N K W membership k :=
  install_other slots1 (input L q N K W membership) _ k hk

theorem data1_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 8 ≤ k.val) : data1 L q N K W membership k=[] := by
  rw [data1_other L q N K W membership k (by
    have hs : ∀ j,(slots1 j).val<8 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact input_fresh L q N K W membership k (by omega)

theorem ready1 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase1 (2*(List.replicate (1) true).length+2) (input L q N K W membership) (data1 L q N K W membership) := by
  apply (RowCommonResources.literal_ready (List.replicate (1) true)).focus slots1 slots1_inj (input L q N K W membership)
  intro j
  fin_cases j

  · change input L q N K W membership 6=[]
    exact input_fresh L q N K W membership 6 (by decide)

  · change input L q N K W membership 7=[]
    exact input_fresh L q N K W membership 7 (by decide)

noncomputable def joined1 := phase1

def budget1 (_L _q _N _K _W : Nat) := 2*(List.replicate (1) true).length+2

theorem joined1_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined1 (budget1 L q N K W) (input L q N K W membership) (data1 L q N K W membership) := ready1 L q N K W membership

def slots2 : Fin 4→Fin 88 := ![0,6,8,9]

theorem slots2_inj : Function.Injective slots2 := by decide

noncomputable def phase2 := RecoveryFocus.machine slots2 ClockUnarySum.machine

noncomputable def data2 (L q N K W : Nat) (membership : List Bool) : Store := install slots2 (data1 L q N K W membership) (![List.replicate (L) true,List.replicate (1) true,List.replicate (v1 L q N K W) true,List.replicate ((L)+(1)+2) false])

theorem data2_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data2 L q N K W membership (slots2 j)=(![List.replicate (L) true,List.replicate (1) true,List.replicate (v1 L q N K W) true,List.replicate ((L)+(1)+2) false]) j :=
  install_slot slots2 slots2_inj (data1 L q N K W membership) _ j

theorem data2_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots2 j≠k) : data2 L q N K W membership k=data1 L q N K W membership k :=
  install_other slots2 (data1 L q N K W membership) _ k hk

theorem data2_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 10 ≤ k.val) : data2 L q N K W membership k=[] := by
  rw [data2_other L q N K W membership k (by
    have hs : ∀ j,(slots2 j).val<10 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data1_fresh L q N K W membership k (by omega)

theorem ready2 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase2 (2*((L)+(1))+6) (data1 L q N K W membership) (data2 L q N K W membership) := by
  apply (ClockUnarySum.sum_ready (L) (1)).focus slots2 slots2_inj (data1 L q N K W membership)
  intro j
  fin_cases j

  · change data1 L q N K W membership 0=List.replicate (L) true
    rw [data1_other L q N K W membership 0 (by decide)]
    all_goals rfl

  · change data1 L q N K W membership 6=List.replicate (1) true
    rw [show data1 L q N K W membership 6=(![List.replicate (1) true,List.replicate (List.replicate (1) true).length false]) 0 from data1_slot L q N K W membership 0]
    all_goals rfl

  · change data1 L q N K W membership 8=[]
    exact data1_fresh L q N K W membership 8 (by decide)

  · change data1 L q N K W membership 9=[]
    exact data1_fresh L q N K W membership 9 (by decide)

noncomputable def joined2 := Composition.machine joined1 phase2

def budget2 (L q N K W : Nat) := budget1 L q N K W+1+(2*((L)+(1))+6)

theorem joined2_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined2 (budget2 L q N K W) (input L q N K W membership) (data2 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined1_ready L q N K W membership) (ready2 L q N K W membership)

def slots3 : Fin 4→Fin 88 := ![8,6,10,11]

theorem slots3_inj : Function.Injective slots3 := by decide

noncomputable def phase3 := RecoveryFocus.machine slots3 ClockUnarySum.machine

noncomputable def data3 (L q N K W : Nat) (membership : List Bool) : Store := install slots3 (data2 L q N K W membership) (![List.replicate (v1 L q N K W) true,List.replicate (1) true,List.replicate (v2 L q N K W) true,List.replicate ((v1 L q N K W)+(1)+2) false])

theorem data3_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data3 L q N K W membership (slots3 j)=(![List.replicate (v1 L q N K W) true,List.replicate (1) true,List.replicate (v2 L q N K W) true,List.replicate ((v1 L q N K W)+(1)+2) false]) j :=
  install_slot slots3 slots3_inj (data2 L q N K W membership) _ j

theorem data3_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots3 j≠k) : data3 L q N K W membership k=data2 L q N K W membership k :=
  install_other slots3 (data2 L q N K W membership) _ k hk

theorem data3_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 12 ≤ k.val) : data3 L q N K W membership k=[] := by
  rw [data3_other L q N K W membership k (by
    have hs : ∀ j,(slots3 j).val<12 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data2_fresh L q N K W membership k (by omega)

theorem ready3 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase3 (2*((v1 L q N K W)+(1))+6) (data2 L q N K W membership) (data3 L q N K W membership) := by
  apply (ClockUnarySum.sum_ready (v1 L q N K W) (1)).focus slots3 slots3_inj (data2 L q N K W membership)
  intro j
  fin_cases j

  · change data2 L q N K W membership 8=List.replicate (v1 L q N K W) true
    rw [show data2 L q N K W membership 8=(![List.replicate (L) true,List.replicate (1) true,List.replicate (v1 L q N K W) true,List.replicate ((L)+(1)+2) false]) 2 from data2_slot L q N K W membership 2]
    all_goals rfl

  · change data2 L q N K W membership 6=List.replicate (1) true
    rw [show data2 L q N K W membership 6=(![List.replicate (L) true,List.replicate (1) true,List.replicate (v1 L q N K W) true,List.replicate ((L)+(1)+2) false]) 1 from data2_slot L q N K W membership 1]
    all_goals rfl

  · change data2 L q N K W membership 10=[]
    exact data2_fresh L q N K W membership 10 (by decide)

  · change data2 L q N K W membership 11=[]
    exact data2_fresh L q N K W membership 11 (by decide)

noncomputable def joined3 := Composition.machine joined2 phase3

def budget3 (L q N K W : Nat) := budget2 L q N K W+1+(2*((v1 L q N K W)+(1))+6)

theorem joined3_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined3 (budget3 L q N K W) (input L q N K W membership) (data3 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined2_ready L q N K W membership) (ready3 L q N K W membership)

def slots4 : Fin 3→Fin 88 := ![1,12,13]

theorem slots4_inj : Function.Injective slots4 := by decide

noncomputable def phase4 := RecoveryFocus.machine slots4 (UWalkUnary.machine false false)

noncomputable def data4 (L q N K W : Nat) (membership : List Bool) : Store := install slots4 (data3 L q N K W membership) (![UnaryTemplate.tape (q),List.replicate (q) true,List.replicate ((q)+2) false])

theorem data4_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 3) : data4 L q N K W membership (slots4 j)=(![UnaryTemplate.tape (q),List.replicate (q) true,List.replicate ((q)+2) false]) j :=
  install_slot slots4 slots4_inj (data3 L q N K W membership) _ j

theorem data4_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots4 j≠k) : data4 L q N K W membership k=data3 L q N K W membership k :=
  install_other slots4 (data3 L q N K W membership) _ k hk

theorem data4_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 14 ≤ k.val) : data4 L q N K W membership k=[] := by
  rw [data4_other L q N K W membership k (by
    have hs : ∀ j,(slots4 j).val<14 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data3_fresh L q N K W membership k (by omega)

theorem ready4 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase4 (2*(q)+6) (data3 L q N K W membership) (data4 L q N K W membership) := by
  apply (DecompositionCountDrivers.template_ready false false (q)).focus slots4 slots4_inj (data3 L q N K W membership)
  intro j
  fin_cases j

  · change data3 L q N K W membership 1=UnaryTemplate.tape (q)
    rw [data3_other L q N K W membership 1 (by decide)]
    rw [data2_other L q N K W membership 1 (by decide)]
    rw [data1_other L q N K W membership 1 (by decide)]
    all_goals rfl

  · change data3 L q N K W membership 12=[]
    exact data3_fresh L q N K W membership 12 (by decide)

  · change data3 L q N K W membership 13=[]
    exact data3_fresh L q N K W membership 13 (by decide)

noncomputable def joined4 := Composition.machine joined3 phase4

def budget4 (L q N K W : Nat) := budget3 L q N K W+1+(2*(q)+6)

theorem joined4_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined4 (budget4 L q N K W) (input L q N K W membership) (data4 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined3_ready L q N K W membership) (ready4 L q N K W membership)

def slots5 : Fin 3→Fin 88 := ![3,14,15]

theorem slots5_inj : Function.Injective slots5 := by decide

noncomputable def phase5 := RecoveryFocus.machine slots5 (UWalkUnary.machine false false)

noncomputable def data5 (L q N K W : Nat) (membership : List Bool) : Store := install slots5 (data4 L q N K W membership) (![UnaryTemplate.tape (K),List.replicate (K) true,List.replicate ((K)+2) false])

theorem data5_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 3) : data5 L q N K W membership (slots5 j)=(![UnaryTemplate.tape (K),List.replicate (K) true,List.replicate ((K)+2) false]) j :=
  install_slot slots5 slots5_inj (data4 L q N K W membership) _ j

theorem data5_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots5 j≠k) : data5 L q N K W membership k=data4 L q N K W membership k :=
  install_other slots5 (data4 L q N K W membership) _ k hk

theorem data5_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 16 ≤ k.val) : data5 L q N K W membership k=[] := by
  rw [data5_other L q N K W membership k (by
    have hs : ∀ j,(slots5 j).val<16 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data4_fresh L q N K W membership k (by omega)

theorem ready5 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase5 (2*(K)+6) (data4 L q N K W membership) (data5 L q N K W membership) := by
  apply (DecompositionCountDrivers.template_ready false false (K)).focus slots5 slots5_inj (data4 L q N K W membership)
  intro j
  fin_cases j

  · change data4 L q N K W membership 3=UnaryTemplate.tape (K)
    rw [data4_other L q N K W membership 3 (by decide)]
    rw [data3_other L q N K W membership 3 (by decide)]
    rw [data2_other L q N K W membership 3 (by decide)]
    rw [data1_other L q N K W membership 3 (by decide)]
    all_goals rfl

  · change data4 L q N K W membership 14=[]
    exact data4_fresh L q N K W membership 14 (by decide)

  · change data4 L q N K W membership 15=[]
    exact data4_fresh L q N K W membership 15 (by decide)

noncomputable def joined5 := Composition.machine joined4 phase5

def budget5 (L q N K W : Nat) := budget4 L q N K W+1+(2*(K)+6)

theorem joined5_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined5 (budget5 L q N K W) (input L q N K W membership) (data5 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined4_ready L q N K W membership) (ready5 L q N K W membership)

def slots6 : Fin 3→Fin 88 := ![1,16,17]

theorem slots6_inj : Function.Injective slots6 := by decide

noncomputable def phase6 := RecoveryFocus.machine slots6 (UWalkUnary.machine true false)

noncomputable def data6 (L q N K W : Nat) (membership : List Bool) : Store := install slots6 (data5 L q N K W membership) (![UnaryTemplate.tape (q),CompareMachine.word (q),List.replicate ((q)+2) false])

theorem data6_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 3) : data6 L q N K W membership (slots6 j)=(![UnaryTemplate.tape (q),CompareMachine.word (q),List.replicate ((q)+2) false]) j :=
  install_slot slots6 slots6_inj (data5 L q N K W membership) _ j

theorem data6_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots6 j≠k) : data6 L q N K W membership k=data5 L q N K W membership k :=
  install_other slots6 (data5 L q N K W membership) _ k hk

theorem data6_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 18 ≤ k.val) : data6 L q N K W membership k=[] := by
  rw [data6_other L q N K W membership k (by
    have hs : ∀ j,(slots6 j).val<18 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data5_fresh L q N K W membership k (by omega)

theorem ready6 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase6 (2*(q)+6) (data5 L q N K W membership) (data6 L q N K W membership) := by
  apply (DecompositionCountDrivers.template_ready true false (q)).focus slots6 slots6_inj (data5 L q N K W membership)
  intro j
  fin_cases j

  · change data5 L q N K W membership 1=UnaryTemplate.tape (q)
    rw [data5_other L q N K W membership 1 (by decide)]
    rw [show data4 L q N K W membership 1=(![UnaryTemplate.tape (q),List.replicate (q) true,List.replicate ((q)+2) false]) 0 from data4_slot L q N K W membership 0]
    all_goals rfl

  · change data5 L q N K W membership 16=[]
    exact data5_fresh L q N K W membership 16 (by decide)

  · change data5 L q N K W membership 17=[]
    exact data5_fresh L q N K W membership 17 (by decide)

noncomputable def joined6 := Composition.machine joined5 phase6

def budget6 (L q N K W : Nat) := budget5 L q N K W+1+(2*(q)+6)

theorem joined6_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined6 (budget6 L q N K W) (input L q N K W membership) (data6 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined5_ready L q N K W membership) (ready6 L q N K W membership)

def slots7 : Fin 3→Fin 88 := ![2,18,19]

theorem slots7_inj : Function.Injective slots7 := by decide

noncomputable def phase7 := RecoveryFocus.machine slots7 (UWalkUnary.machine true false)

noncomputable def data7 (L q N K W : Nat) (membership : List Bool) : Store := install slots7 (data6 L q N K W membership) (![UnaryTemplate.tape (N),CompareMachine.word (N),List.replicate ((N)+2) false])

theorem data7_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 3) : data7 L q N K W membership (slots7 j)=(![UnaryTemplate.tape (N),CompareMachine.word (N),List.replicate ((N)+2) false]) j :=
  install_slot slots7 slots7_inj (data6 L q N K W membership) _ j

theorem data7_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots7 j≠k) : data7 L q N K W membership k=data6 L q N K W membership k :=
  install_other slots7 (data6 L q N K W membership) _ k hk

theorem data7_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 20 ≤ k.val) : data7 L q N K W membership k=[] := by
  rw [data7_other L q N K W membership k (by
    have hs : ∀ j,(slots7 j).val<20 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data6_fresh L q N K W membership k (by omega)

theorem ready7 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase7 (2*(N)+6) (data6 L q N K W membership) (data7 L q N K W membership) := by
  apply (DecompositionCountDrivers.template_ready true false (N)).focus slots7 slots7_inj (data6 L q N K W membership)
  intro j
  fin_cases j

  · change data6 L q N K W membership 2=UnaryTemplate.tape (N)
    rw [data6_other L q N K W membership 2 (by decide)]
    rw [data5_other L q N K W membership 2 (by decide)]
    rw [data4_other L q N K W membership 2 (by decide)]
    rw [data3_other L q N K W membership 2 (by decide)]
    rw [data2_other L q N K W membership 2 (by decide)]
    rw [data1_other L q N K W membership 2 (by decide)]
    all_goals rfl

  · change data6 L q N K W membership 18=[]
    exact data6_fresh L q N K W membership 18 (by decide)

  · change data6 L q N K W membership 19=[]
    exact data6_fresh L q N K W membership 19 (by decide)

noncomputable def joined7 := Composition.machine joined6 phase7

def budget7 (L q N K W : Nat) := budget6 L q N K W+1+(2*(N)+6)

theorem joined7_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined7 (budget7 L q N K W) (input L q N K W membership) (data7 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined6_ready L q N K W membership) (ready7 L q N K W membership)

def slots8 : Fin 3→Fin 88 := ![3,20,21]

theorem slots8_inj : Function.Injective slots8 := by decide

noncomputable def phase8 := RecoveryFocus.machine slots8 (UWalkUnary.machine true false)

noncomputable def data8 (L q N K W : Nat) (membership : List Bool) : Store := install slots8 (data7 L q N K W membership) (![UnaryTemplate.tape (K),CompareMachine.word (K),List.replicate ((K)+2) false])

theorem data8_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 3) : data8 L q N K W membership (slots8 j)=(![UnaryTemplate.tape (K),CompareMachine.word (K),List.replicate ((K)+2) false]) j :=
  install_slot slots8 slots8_inj (data7 L q N K W membership) _ j

theorem data8_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots8 j≠k) : data8 L q N K W membership k=data7 L q N K W membership k :=
  install_other slots8 (data7 L q N K W membership) _ k hk

theorem data8_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 22 ≤ k.val) : data8 L q N K W membership k=[] := by
  rw [data8_other L q N K W membership k (by
    have hs : ∀ j,(slots8 j).val<22 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data7_fresh L q N K W membership k (by omega)

theorem ready8 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase8 (2*(K)+6) (data7 L q N K W membership) (data8 L q N K W membership) := by
  apply (DecompositionCountDrivers.template_ready true false (K)).focus slots8 slots8_inj (data7 L q N K W membership)
  intro j
  fin_cases j

  · change data7 L q N K W membership 3=UnaryTemplate.tape (K)
    rw [data7_other L q N K W membership 3 (by decide)]
    rw [data6_other L q N K W membership 3 (by decide)]
    rw [show data5 L q N K W membership 3=(![UnaryTemplate.tape (K),List.replicate (K) true,List.replicate ((K)+2) false]) 0 from data5_slot L q N K W membership 0]
    all_goals rfl

  · change data7 L q N K W membership 20=[]
    exact data7_fresh L q N K W membership 20 (by decide)

  · change data7 L q N K W membership 21=[]
    exact data7_fresh L q N K W membership 21 (by decide)

noncomputable def joined8 := Composition.machine joined7 phase8

def budget8 (L q N K W : Nat) := budget7 L q N K W+1+(2*(K)+6)

theorem joined8_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined8 (budget8 L q N K W) (input L q N K W membership) (data8 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined7_ready L q N K W membership) (ready8 L q N K W membership)

def slots9 : Fin 3→Fin 88 := ![1,22,23]

theorem slots9_inj : Function.Injective slots9 := by decide

noncomputable def phase9 := RecoveryFocus.machine slots9 (UWalkUnary.machine false true)

noncomputable def data9 (L q N K W : Nat) (membership : List Bool) : Store := install slots9 (data8 L q N K W membership) (![UnaryTemplate.tape (q),List.replicate (v3 L q N K W) true,List.replicate ((q)+2) false])

theorem data9_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 3) : data9 L q N K W membership (slots9 j)=(![UnaryTemplate.tape (q),List.replicate (v3 L q N K W) true,List.replicate ((q)+2) false]) j :=
  install_slot slots9 slots9_inj (data8 L q N K W membership) _ j

theorem data9_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots9 j≠k) : data9 L q N K W membership k=data8 L q N K W membership k :=
  install_other slots9 (data8 L q N K W membership) _ k hk

theorem data9_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 24 ≤ k.val) : data9 L q N K W membership k=[] := by
  rw [data9_other L q N K W membership k (by
    have hs : ∀ j,(slots9 j).val<24 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data8_fresh L q N K W membership k (by omega)

theorem ready9 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase9 (2*(q)+6) (data8 L q N K W membership) (data9 L q N K W membership) := by
  apply (DecompositionCountDrivers.template_ready false true (q)).focus slots9 slots9_inj (data8 L q N K W membership)
  intro j
  fin_cases j

  · change data8 L q N K W membership 1=UnaryTemplate.tape (q)
    rw [data8_other L q N K W membership 1 (by decide)]
    rw [data7_other L q N K W membership 1 (by decide)]
    rw [show data6 L q N K W membership 1=(![UnaryTemplate.tape (q),CompareMachine.word (q),List.replicate ((q)+2) false]) 0 from data6_slot L q N K W membership 0]
    all_goals rfl

  · change data8 L q N K W membership 22=[]
    exact data8_fresh L q N K W membership 22 (by decide)

  · change data8 L q N K W membership 23=[]
    exact data8_fresh L q N K W membership 23 (by decide)

noncomputable def joined9 := Composition.machine joined8 phase9

def budget9 (L q N K W : Nat) := budget8 L q N K W+1+(2*(q)+6)

theorem joined9_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined9 (budget9 L q N K W) (input L q N K W membership) (data9 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined8_ready L q N K W membership) (ready9 L q N K W membership)

def slots10 : Fin 4→Fin 88 := ![10,8,24,25]

theorem slots10_inj : Function.Injective slots10 := by decide

noncomputable def phase10 := RecoveryFocus.machine slots10 ClockUnarySum.machine

noncomputable def data10 (L q N K W : Nat) (membership : List Bool) : Store := install slots10 (data9 L q N K W membership) (![List.replicate (v2 L q N K W) true,List.replicate (v1 L q N K W) true,List.replicate (v4 L q N K W) true,List.replicate ((v2 L q N K W)+(v1 L q N K W)+2) false])

theorem data10_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data10 L q N K W membership (slots10 j)=(![List.replicate (v2 L q N K W) true,List.replicate (v1 L q N K W) true,List.replicate (v4 L q N K W) true,List.replicate ((v2 L q N K W)+(v1 L q N K W)+2) false]) j :=
  install_slot slots10 slots10_inj (data9 L q N K W membership) _ j

theorem data10_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots10 j≠k) : data10 L q N K W membership k=data9 L q N K W membership k :=
  install_other slots10 (data9 L q N K W membership) _ k hk

theorem data10_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 26 ≤ k.val) : data10 L q N K W membership k=[] := by
  rw [data10_other L q N K W membership k (by
    have hs : ∀ j,(slots10 j).val<26 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data9_fresh L q N K W membership k (by omega)

theorem ready10 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase10 (2*((v2 L q N K W)+(v1 L q N K W))+6) (data9 L q N K W membership) (data10 L q N K W membership) := by
  apply (ClockUnarySum.sum_ready (v2 L q N K W) (v1 L q N K W)).focus slots10 slots10_inj (data9 L q N K W membership)
  intro j
  fin_cases j

  · change data9 L q N K W membership 10=List.replicate (v2 L q N K W) true
    rw [data9_other L q N K W membership 10 (by decide)]
    rw [data8_other L q N K W membership 10 (by decide)]
    rw [data7_other L q N K W membership 10 (by decide)]
    rw [data6_other L q N K W membership 10 (by decide)]
    rw [data5_other L q N K W membership 10 (by decide)]
    rw [data4_other L q N K W membership 10 (by decide)]
    rw [show data3 L q N K W membership 10=(![List.replicate (v1 L q N K W) true,List.replicate (1) true,List.replicate (v2 L q N K W) true,List.replicate ((v1 L q N K W)+(1)+2) false]) 2 from data3_slot L q N K W membership 2]
    all_goals rfl

  · change data9 L q N K W membership 8=List.replicate (v1 L q N K W) true
    rw [data9_other L q N K W membership 8 (by decide)]
    rw [data8_other L q N K W membership 8 (by decide)]
    rw [data7_other L q N K W membership 8 (by decide)]
    rw [data6_other L q N K W membership 8 (by decide)]
    rw [data5_other L q N K W membership 8 (by decide)]
    rw [data4_other L q N K W membership 8 (by decide)]
    rw [show data3 L q N K W membership 8=(![List.replicate (v1 L q N K W) true,List.replicate (1) true,List.replicate (v2 L q N K W) true,List.replicate ((v1 L q N K W)+(1)+2) false]) 0 from data3_slot L q N K W membership 0]
    all_goals rfl

  · change data9 L q N K W membership 24=[]
    exact data9_fresh L q N K W membership 24 (by decide)

  · change data9 L q N K W membership 25=[]
    exact data9_fresh L q N K W membership 25 (by decide)

noncomputable def joined10 := Composition.machine joined9 phase10

def budget10 (L q N K W : Nat) := budget9 L q N K W+1+(2*((v2 L q N K W)+(v1 L q N K W))+6)

theorem joined10_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined10 (budget10 L q N K W) (input L q N K W membership) (data10 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined9_ready L q N K W membership) (ready10 L q N K W membership)

def slots11 : Fin 4→Fin 88 := ![24,22,26,27]

theorem slots11_inj : Function.Injective slots11 := by decide

noncomputable def phase11 := RecoveryFocus.machine slots11 ClockUnarySum.machine

noncomputable def data11 (L q N K W : Nat) (membership : List Bool) : Store := install slots11 (data10 L q N K W membership) (![List.replicate (v4 L q N K W) true,List.replicate (v3 L q N K W) true,List.replicate (v5 L q N K W) true,List.replicate ((v4 L q N K W)+(v3 L q N K W)+2) false])

theorem data11_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data11 L q N K W membership (slots11 j)=(![List.replicate (v4 L q N K W) true,List.replicate (v3 L q N K W) true,List.replicate (v5 L q N K W) true,List.replicate ((v4 L q N K W)+(v3 L q N K W)+2) false]) j :=
  install_slot slots11 slots11_inj (data10 L q N K W membership) _ j

theorem data11_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots11 j≠k) : data11 L q N K W membership k=data10 L q N K W membership k :=
  install_other slots11 (data10 L q N K W membership) _ k hk

theorem data11_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 28 ≤ k.val) : data11 L q N K W membership k=[] := by
  rw [data11_other L q N K W membership k (by
    have hs : ∀ j,(slots11 j).val<28 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data10_fresh L q N K W membership k (by omega)

theorem ready11 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase11 (2*((v4 L q N K W)+(v3 L q N K W))+6) (data10 L q N K W membership) (data11 L q N K W membership) := by
  apply (ClockUnarySum.sum_ready (v4 L q N K W) (v3 L q N K W)).focus slots11 slots11_inj (data10 L q N K W membership)
  intro j
  fin_cases j

  · change data10 L q N K W membership 24=List.replicate (v4 L q N K W) true
    rw [show data10 L q N K W membership 24=(![List.replicate (v2 L q N K W) true,List.replicate (v1 L q N K W) true,List.replicate (v4 L q N K W) true,List.replicate ((v2 L q N K W)+(v1 L q N K W)+2) false]) 2 from data10_slot L q N K W membership 2]
    all_goals rfl

  · change data10 L q N K W membership 22=List.replicate (v3 L q N K W) true
    rw [data10_other L q N K W membership 22 (by decide)]
    rw [show data9 L q N K W membership 22=(![UnaryTemplate.tape (q),List.replicate (v3 L q N K W) true,List.replicate ((q)+2) false]) 1 from data9_slot L q N K W membership 1]
    all_goals rfl

  · change data10 L q N K W membership 26=[]
    exact data10_fresh L q N K W membership 26 (by decide)

  · change data10 L q N K W membership 27=[]
    exact data10_fresh L q N K W membership 27 (by decide)

noncomputable def joined11 := Composition.machine joined10 phase11

def budget11 (L q N K W : Nat) := budget10 L q N K W+1+(2*((v4 L q N K W)+(v3 L q N K W))+6)

theorem joined11_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined11 (budget11 L q N K W) (input L q N K W membership) (data11 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined10_ready L q N K W membership) (ready11 L q N K W membership)

def slots12 : Fin 3→Fin 88 := ![26,28,29]

theorem slots12_inj : Function.Injective slots12 := by decide

noncomputable def phase12 := RecoveryFocus.machine slots12 (RepairSource.ProjectionNormalization.DimensionTemplate.machine false)

noncomputable def data12 (L q N K W : Nat) (membership : List Bool) : Store := install slots12 (data11 L q N K W membership) (![List.replicate (v5 L q N K W) true,UnaryTemplate.tape (v5 L q N K W),List.replicate ((v5 L q N K W)+3) false])

theorem data12_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 3) : data12 L q N K W membership (slots12 j)=(![List.replicate (v5 L q N K W) true,UnaryTemplate.tape (v5 L q N K W),List.replicate ((v5 L q N K W)+3) false]) j :=
  install_slot slots12 slots12_inj (data11 L q N K W membership) _ j

theorem data12_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots12 j≠k) : data12 L q N K W membership k=data11 L q N K W membership k :=
  install_other slots12 (data11 L q N K W membership) _ k hk

theorem data12_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 30 ≤ k.val) : data12 L q N K W membership k=[] := by
  rw [data12_other L q N K W membership k (by
    have hs : ∀ j,(slots12 j).val<30 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data11_fresh L q N K W membership k (by omega)

theorem ready12 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase12 (2*(v5 L q N K W)+8) (data11 L q N K W membership) (data12 L q N K W membership) := by
  apply (RepairSource.ProjectionNormalization.DimensionTemplate.ready false (v5 L q N K W)).focus slots12 slots12_inj (data11 L q N K W membership)
  intro j
  fin_cases j

  · change data11 L q N K W membership 26=List.replicate (v5 L q N K W) true
    rw [show data11 L q N K W membership 26=(![List.replicate (v4 L q N K W) true,List.replicate (v3 L q N K W) true,List.replicate (v5 L q N K W) true,List.replicate ((v4 L q N K W)+(v3 L q N K W)+2) false]) 2 from data11_slot L q N K W membership 2]
    all_goals rfl

  · change data11 L q N K W membership 28=[]
    exact data11_fresh L q N K W membership 28 (by decide)

  · change data11 L q N K W membership 29=[]
    exact data11_fresh L q N K W membership 29 (by decide)

noncomputable def joined12 := Composition.machine joined11 phase12

def budget12 (L q N K W : Nat) := budget11 L q N K W+1+(2*(v5 L q N K W)+8)

theorem joined12_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined12 (budget12 L q N K W) (input L q N K W membership) (data12 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined11_ready L q N K W membership) (ready12 L q N K W membership)

def slots13 : Fin 4→Fin 88 := ![26,28,30,31]

theorem slots13_inj : Function.Injective slots13 := by decide

noncomputable def phase13 := RecoveryFocus.machine slots13 ClockUnaryProduct.machine

noncomputable def data13 (L q N K W : Nat) (membership : List Bool) : Store := install slots13 (data12 L q N K W membership) (![List.replicate (v5 L q N K W) true,UnaryTemplate.tape (v5 L q N K W),List.replicate (v6 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v5 L q N K W) (v5 L q N K W)) false])

theorem data13_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data13 L q N K W membership (slots13 j)=(![List.replicate (v5 L q N K W) true,UnaryTemplate.tape (v5 L q N K W),List.replicate (v6 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v5 L q N K W) (v5 L q N K W)) false]) j :=
  install_slot slots13 slots13_inj (data12 L q N K W membership) _ j

theorem data13_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots13 j≠k) : data13 L q N K W membership k=data12 L q N K W membership k :=
  install_other slots13 (data12 L q N K W membership) _ k hk

theorem data13_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 32 ≤ k.val) : data13 L q N K W membership k=[] := by
  rw [data13_other L q N K W membership k (by
    have hs : ∀ j,(slots13 j).val<32 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data12_fresh L q N K W membership k (by omega)

theorem ready13 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase13 (WilliamsUnaryProduct.budget (v5 L q N K W) (v5 L q N K W)) (data12 L q N K W membership) (data13 L q N K W membership) := by
  apply (RowCommonResources.product_ready (v5 L q N K W) (v5 L q N K W)).focus slots13 slots13_inj (data12 L q N K W membership)
  intro j
  fin_cases j

  · change data12 L q N K W membership 26=List.replicate (v5 L q N K W) true
    rw [show data12 L q N K W membership 26=(![List.replicate (v5 L q N K W) true,UnaryTemplate.tape (v5 L q N K W),List.replicate ((v5 L q N K W)+3) false]) 0 from data12_slot L q N K W membership 0]
    all_goals rfl

  · change data12 L q N K W membership 28=UnaryTemplate.tape (v5 L q N K W)
    rw [show data12 L q N K W membership 28=(![List.replicate (v5 L q N K W) true,UnaryTemplate.tape (v5 L q N K W),List.replicate ((v5 L q N K W)+3) false]) 1 from data12_slot L q N K W membership 1]
    all_goals rfl

  · change data12 L q N K W membership 30=[]
    exact data12_fresh L q N K W membership 30 (by decide)

  · change data12 L q N K W membership 31=[]
    exact data12_fresh L q N K W membership 31 (by decide)

noncomputable def joined13 := Composition.machine joined12 phase13

def budget13 (L q N K W : Nat) := budget12 L q N K W+1+(WilliamsUnaryProduct.budget (v5 L q N K W) (v5 L q N K W))

theorem joined13_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined13 (budget13 L q N K W) (input L q N K W membership) (data13 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined12_ready L q N K W membership) (ready13 L q N K W membership)

def slots14 : Fin 2→Fin 88 := ![32,33]

theorem slots14_inj : Function.Injective slots14 := by decide

noncomputable def phase14 := RecoveryFocus.machine slots14 (HierarchyFixedWord.machine (UnaryTemplate.tape (1024)))

noncomputable def data14 (L q N K W : Nat) (membership : List Bool) : Store := install slots14 (data13 L q N K W membership) (![UnaryTemplate.tape (1024),List.replicate (UnaryTemplate.tape (1024)).length false])

theorem data14_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 2) : data14 L q N K W membership (slots14 j)=(![UnaryTemplate.tape (1024),List.replicate (UnaryTemplate.tape (1024)).length false]) j :=
  install_slot slots14 slots14_inj (data13 L q N K W membership) _ j

theorem data14_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots14 j≠k) : data14 L q N K W membership k=data13 L q N K W membership k :=
  install_other slots14 (data13 L q N K W membership) _ k hk

theorem data14_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 34 ≤ k.val) : data14 L q N K W membership k=[] := by
  rw [data14_other L q N K W membership k (by
    have hs : ∀ j,(slots14 j).val<34 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data13_fresh L q N K W membership k (by omega)

theorem ready14 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase14 (2*(UnaryTemplate.tape (1024)).length+2) (data13 L q N K W membership) (data14 L q N K W membership) := by
  apply (RowCommonResources.literal_ready (UnaryTemplate.tape (1024))).focus slots14 slots14_inj (data13 L q N K W membership)
  intro j
  fin_cases j

  · change data13 L q N K W membership 32=[]
    exact data13_fresh L q N K W membership 32 (by decide)

  · change data13 L q N K W membership 33=[]
    exact data13_fresh L q N K W membership 33 (by decide)

noncomputable def joined14 := Composition.machine joined13 phase14

def budget14 (L q N K W : Nat) := budget13 L q N K W+1+(2*(UnaryTemplate.tape (1024)).length+2)

theorem joined14_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined14 (budget14 L q N K W) (input L q N K W membership) (data14 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined13_ready L q N K W membership) (ready14 L q N K W membership)

def slots15 : Fin 4→Fin 88 := ![30,32,34,35]

theorem slots15_inj : Function.Injective slots15 := by decide

noncomputable def phase15 := RecoveryFocus.machine slots15 ClockUnaryProduct.machine

noncomputable def data15 (L q N K W : Nat) (membership : List Bool) : Store := install slots15 (data14 L q N K W membership) (![List.replicate (v6 L q N K W) true,UnaryTemplate.tape (1024),List.replicate (v7 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v6 L q N K W) (1024)) false])

theorem data15_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data15 L q N K W membership (slots15 j)=(![List.replicate (v6 L q N K W) true,UnaryTemplate.tape (1024),List.replicate (v7 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v6 L q N K W) (1024)) false]) j :=
  install_slot slots15 slots15_inj (data14 L q N K W membership) _ j

theorem data15_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots15 j≠k) : data15 L q N K W membership k=data14 L q N K W membership k :=
  install_other slots15 (data14 L q N K W membership) _ k hk

theorem data15_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 36 ≤ k.val) : data15 L q N K W membership k=[] := by
  rw [data15_other L q N K W membership k (by
    have hs : ∀ j,(slots15 j).val<36 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data14_fresh L q N K W membership k (by omega)

theorem ready15 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase15 (WilliamsUnaryProduct.budget (v6 L q N K W) (1024)) (data14 L q N K W membership) (data15 L q N K W membership) := by
  apply (RowCommonResources.product_ready (v6 L q N K W) (1024)).focus slots15 slots15_inj (data14 L q N K W membership)
  intro j
  fin_cases j

  · change data14 L q N K W membership 30=List.replicate (v6 L q N K W) true
    rw [data14_other L q N K W membership 30 (by decide)]
    rw [show data13 L q N K W membership 30=(![List.replicate (v5 L q N K W) true,UnaryTemplate.tape (v5 L q N K W),List.replicate (v6 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v5 L q N K W) (v5 L q N K W)) false]) 2 from data13_slot L q N K W membership 2]
    all_goals rfl

  · change data14 L q N K W membership 32=UnaryTemplate.tape (1024)
    rw [show data14 L q N K W membership 32=(![UnaryTemplate.tape (1024),List.replicate (UnaryTemplate.tape (1024)).length false]) 0 from data14_slot L q N K W membership 0]
    all_goals rfl

  · change data14 L q N K W membership 34=[]
    exact data14_fresh L q N K W membership 34 (by decide)

  · change data14 L q N K W membership 35=[]
    exact data14_fresh L q N K W membership 35 (by decide)

noncomputable def joined15 := Composition.machine joined14 phase15

def budget15 (L q N K W : Nat) := budget14 L q N K W+1+(WilliamsUnaryProduct.budget (v6 L q N K W) (1024))

theorem joined15_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined15 (budget15 L q N K W) (input L q N K W membership) (data15 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined14_ready L q N K W membership) (ready15 L q N K W membership)

def slots16 : Fin 2→Fin 88 := ![36,37]

theorem slots16_inj : Function.Injective slots16 := by decide

noncomputable def phase16 := RecoveryFocus.machine slots16 (HierarchyFixedWord.machine (UnaryTemplate.tape (8)))

noncomputable def data16 (L q N K W : Nat) (membership : List Bool) : Store := install slots16 (data15 L q N K W membership) (![UnaryTemplate.tape (8),List.replicate (UnaryTemplate.tape (8)).length false])

theorem data16_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 2) : data16 L q N K W membership (slots16 j)=(![UnaryTemplate.tape (8),List.replicate (UnaryTemplate.tape (8)).length false]) j :=
  install_slot slots16 slots16_inj (data15 L q N K W membership) _ j

theorem data16_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots16 j≠k) : data16 L q N K W membership k=data15 L q N K W membership k :=
  install_other slots16 (data15 L q N K W membership) _ k hk

theorem data16_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 38 ≤ k.val) : data16 L q N K W membership k=[] := by
  rw [data16_other L q N K W membership k (by
    have hs : ∀ j,(slots16 j).val<38 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data15_fresh L q N K W membership k (by omega)

theorem ready16 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase16 (2*(UnaryTemplate.tape (8)).length+2) (data15 L q N K W membership) (data16 L q N K W membership) := by
  apply (RowCommonResources.literal_ready (UnaryTemplate.tape (8))).focus slots16 slots16_inj (data15 L q N K W membership)
  intro j
  fin_cases j

  · change data15 L q N K W membership 36=[]
    exact data15_fresh L q N K W membership 36 (by decide)

  · change data15 L q N K W membership 37=[]
    exact data15_fresh L q N K W membership 37 (by decide)

noncomputable def joined16 := Composition.machine joined15 phase16

def budget16 (L q N K W : Nat) := budget15 L q N K W+1+(2*(UnaryTemplate.tape (8)).length+2)

theorem joined16_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined16 (budget16 L q N K W) (input L q N K W membership) (data16 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined15_ready L q N K W membership) (ready16 L q N K W membership)

def slots17 : Fin 4→Fin 88 := ![8,36,38,39]

theorem slots17_inj : Function.Injective slots17 := by decide

noncomputable def phase17 := RecoveryFocus.machine slots17 ClockUnaryProduct.machine

noncomputable def data17 (L q N K W : Nat) (membership : List Bool) : Store := install slots17 (data16 L q N K W membership) (![List.replicate (v1 L q N K W) true,UnaryTemplate.tape (8),List.replicate (v8 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v1 L q N K W) (8)) false])

theorem data17_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data17 L q N K W membership (slots17 j)=(![List.replicate (v1 L q N K W) true,UnaryTemplate.tape (8),List.replicate (v8 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v1 L q N K W) (8)) false]) j :=
  install_slot slots17 slots17_inj (data16 L q N K W membership) _ j

theorem data17_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots17 j≠k) : data17 L q N K W membership k=data16 L q N K W membership k :=
  install_other slots17 (data16 L q N K W membership) _ k hk

theorem data17_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 40 ≤ k.val) : data17 L q N K W membership k=[] := by
  rw [data17_other L q N K W membership k (by
    have hs : ∀ j,(slots17 j).val<40 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data16_fresh L q N K W membership k (by omega)

theorem ready17 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase17 (WilliamsUnaryProduct.budget (v1 L q N K W) (8)) (data16 L q N K W membership) (data17 L q N K W membership) := by
  apply (RowCommonResources.product_ready (v1 L q N K W) (8)).focus slots17 slots17_inj (data16 L q N K W membership)
  intro j
  fin_cases j

  · change data16 L q N K W membership 8=List.replicate (v1 L q N K W) true
    rw [data16_other L q N K W membership 8 (by decide)]
    rw [data15_other L q N K W membership 8 (by decide)]
    rw [data14_other L q N K W membership 8 (by decide)]
    rw [data13_other L q N K W membership 8 (by decide)]
    rw [data12_other L q N K W membership 8 (by decide)]
    rw [data11_other L q N K W membership 8 (by decide)]
    rw [show data10 L q N K W membership 8=(![List.replicate (v2 L q N K W) true,List.replicate (v1 L q N K W) true,List.replicate (v4 L q N K W) true,List.replicate ((v2 L q N K W)+(v1 L q N K W)+2) false]) 1 from data10_slot L q N K W membership 1]
    all_goals rfl

  · change data16 L q N K W membership 36=UnaryTemplate.tape (8)
    rw [show data16 L q N K W membership 36=(![UnaryTemplate.tape (8),List.replicate (UnaryTemplate.tape (8)).length false]) 0 from data16_slot L q N K W membership 0]
    all_goals rfl

  · change data16 L q N K W membership 38=[]
    exact data16_fresh L q N K W membership 38 (by decide)

  · change data16 L q N K W membership 39=[]
    exact data16_fresh L q N K W membership 39 (by decide)

noncomputable def joined17 := Composition.machine joined16 phase17

def budget17 (L q N K W : Nat) := budget16 L q N K W+1+(WilliamsUnaryProduct.budget (v1 L q N K W) (8))

theorem joined17_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined17 (budget17 L q N K W) (input L q N K W membership) (data17 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined16_ready L q N K W membership) (ready17 L q N K W membership)

def slots18 : Fin 2→Fin 88 := ![40,41]

theorem slots18_inj : Function.Injective slots18 := by decide

noncomputable def phase18 := RecoveryFocus.machine slots18 (HierarchyFixedWord.machine (List.replicate (12) true))

noncomputable def data18 (L q N K W : Nat) (membership : List Bool) : Store := install slots18 (data17 L q N K W membership) (![List.replicate (12) true,List.replicate (List.replicate (12) true).length false])

theorem data18_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 2) : data18 L q N K W membership (slots18 j)=(![List.replicate (12) true,List.replicate (List.replicate (12) true).length false]) j :=
  install_slot slots18 slots18_inj (data17 L q N K W membership) _ j

theorem data18_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots18 j≠k) : data18 L q N K W membership k=data17 L q N K W membership k :=
  install_other slots18 (data17 L q N K W membership) _ k hk

theorem data18_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 42 ≤ k.val) : data18 L q N K W membership k=[] := by
  rw [data18_other L q N K W membership k (by
    have hs : ∀ j,(slots18 j).val<42 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data17_fresh L q N K W membership k (by omega)

theorem ready18 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase18 (2*(List.replicate (12) true).length+2) (data17 L q N K W membership) (data18 L q N K W membership) := by
  apply (RowCommonResources.literal_ready (List.replicate (12) true)).focus slots18 slots18_inj (data17 L q N K W membership)
  intro j
  fin_cases j

  · change data17 L q N K W membership 40=[]
    exact data17_fresh L q N K W membership 40 (by decide)

  · change data17 L q N K W membership 41=[]
    exact data17_fresh L q N K W membership 41 (by decide)

noncomputable def joined18 := Composition.machine joined17 phase18

def budget18 (L q N K W : Nat) := budget17 L q N K W+1+(2*(List.replicate (12) true).length+2)

theorem joined18_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined18 (budget18 L q N K W) (input L q N K W membership) (data18 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined17_ready L q N K W membership) (ready18 L q N K W membership)

def slots19 : Fin 4→Fin 88 := ![38,40,42,43]

theorem slots19_inj : Function.Injective slots19 := by decide

noncomputable def phase19 := RecoveryFocus.machine slots19 ClockUnarySum.machine

noncomputable def data19 (L q N K W : Nat) (membership : List Bool) : Store := install slots19 (data18 L q N K W membership) (![List.replicate (v8 L q N K W) true,List.replicate (12) true,List.replicate (v9 L q N K W) true,List.replicate ((v8 L q N K W)+(12)+2) false])

theorem data19_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data19 L q N K W membership (slots19 j)=(![List.replicate (v8 L q N K W) true,List.replicate (12) true,List.replicate (v9 L q N K W) true,List.replicate ((v8 L q N K W)+(12)+2) false]) j :=
  install_slot slots19 slots19_inj (data18 L q N K W membership) _ j

theorem data19_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots19 j≠k) : data19 L q N K W membership k=data18 L q N K W membership k :=
  install_other slots19 (data18 L q N K W membership) _ k hk

theorem data19_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 44 ≤ k.val) : data19 L q N K W membership k=[] := by
  rw [data19_other L q N K W membership k (by
    have hs : ∀ j,(slots19 j).val<44 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data18_fresh L q N K W membership k (by omega)

theorem ready19 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase19 (2*((v8 L q N K W)+(12))+6) (data18 L q N K W membership) (data19 L q N K W membership) := by
  apply (ClockUnarySum.sum_ready (v8 L q N K W) (12)).focus slots19 slots19_inj (data18 L q N K W membership)
  intro j
  fin_cases j

  · change data18 L q N K W membership 38=List.replicate (v8 L q N K W) true
    rw [data18_other L q N K W membership 38 (by decide)]
    rw [show data17 L q N K W membership 38=(![List.replicate (v1 L q N K W) true,UnaryTemplate.tape (8),List.replicate (v8 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v1 L q N K W) (8)) false]) 2 from data17_slot L q N K W membership 2]
    all_goals rfl

  · change data18 L q N K W membership 40=List.replicate (12) true
    rw [show data18 L q N K W membership 40=(![List.replicate (12) true,List.replicate (List.replicate (12) true).length false]) 0 from data18_slot L q N K W membership 0]
    all_goals rfl

  · change data18 L q N K W membership 42=[]
    exact data18_fresh L q N K W membership 42 (by decide)

  · change data18 L q N K W membership 43=[]
    exact data18_fresh L q N K W membership 43 (by decide)

noncomputable def joined19 := Composition.machine joined18 phase19

def budget19 (L q N K W : Nat) := budget18 L q N K W+1+(2*((v8 L q N K W)+(12))+6)

theorem joined19_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined19 (budget19 L q N K W) (input L q N K W membership) (data19 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined18_ready L q N K W membership) (ready19 L q N K W membership)

def slots20 : Fin 2→Fin 88 := ![44,45]

theorem slots20_inj : Function.Injective slots20 := by decide

noncomputable def phase20 := RecoveryFocus.machine slots20 (HierarchyFixedWord.machine (UnaryTemplate.tape (16)))

noncomputable def data20 (L q N K W : Nat) (membership : List Bool) : Store := install slots20 (data19 L q N K W membership) (![UnaryTemplate.tape (16),List.replicate (UnaryTemplate.tape (16)).length false])

theorem data20_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 2) : data20 L q N K W membership (slots20 j)=(![UnaryTemplate.tape (16),List.replicate (UnaryTemplate.tape (16)).length false]) j :=
  install_slot slots20 slots20_inj (data19 L q N K W membership) _ j

theorem data20_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots20 j≠k) : data20 L q N K W membership k=data19 L q N K W membership k :=
  install_other slots20 (data19 L q N K W membership) _ k hk

theorem data20_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 46 ≤ k.val) : data20 L q N K W membership k=[] := by
  rw [data20_other L q N K W membership k (by
    have hs : ∀ j,(slots20 j).val<46 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data19_fresh L q N K W membership k (by omega)

theorem ready20 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase20 (2*(UnaryTemplate.tape (16)).length+2) (data19 L q N K W membership) (data20 L q N K W membership) := by
  apply (RowCommonResources.literal_ready (UnaryTemplate.tape (16))).focus slots20 slots20_inj (data19 L q N K W membership)
  intro j
  fin_cases j

  · change data19 L q N K W membership 44=[]
    exact data19_fresh L q N K W membership 44 (by decide)

  · change data19 L q N K W membership 45=[]
    exact data19_fresh L q N K W membership 45 (by decide)

noncomputable def joined20 := Composition.machine joined19 phase20

def budget20 (L q N K W : Nat) := budget19 L q N K W+1+(2*(UnaryTemplate.tape (16)).length+2)

theorem joined20_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined20 (budget20 L q N K W) (input L q N K W membership) (data20 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined19_ready L q N K W membership) (ready20 L q N K W membership)

def slots21 : Fin 4→Fin 88 := ![34,44,46,47]

theorem slots21_inj : Function.Injective slots21 := by decide

noncomputable def phase21 := RecoveryFocus.machine slots21 ClockUnaryProduct.machine

noncomputable def data21 (L q N K W : Nat) (membership : List Bool) : Store := install slots21 (data20 L q N K W membership) (![List.replicate (v7 L q N K W) true,UnaryTemplate.tape (16),List.replicate (v10 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v7 L q N K W) (16)) false])

theorem data21_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data21 L q N K W membership (slots21 j)=(![List.replicate (v7 L q N K W) true,UnaryTemplate.tape (16),List.replicate (v10 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v7 L q N K W) (16)) false]) j :=
  install_slot slots21 slots21_inj (data20 L q N K W membership) _ j

theorem data21_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots21 j≠k) : data21 L q N K W membership k=data20 L q N K W membership k :=
  install_other slots21 (data20 L q N K W membership) _ k hk

theorem data21_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 48 ≤ k.val) : data21 L q N K W membership k=[] := by
  rw [data21_other L q N K W membership k (by
    have hs : ∀ j,(slots21 j).val<48 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data20_fresh L q N K W membership k (by omega)

theorem ready21 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase21 (WilliamsUnaryProduct.budget (v7 L q N K W) (16)) (data20 L q N K W membership) (data21 L q N K W membership) := by
  apply (RowCommonResources.product_ready (v7 L q N K W) (16)).focus slots21 slots21_inj (data20 L q N K W membership)
  intro j
  fin_cases j

  · change data20 L q N K W membership 34=List.replicate (v7 L q N K W) true
    rw [data20_other L q N K W membership 34 (by decide)]
    rw [data19_other L q N K W membership 34 (by decide)]
    rw [data18_other L q N K W membership 34 (by decide)]
    rw [data17_other L q N K W membership 34 (by decide)]
    rw [data16_other L q N K W membership 34 (by decide)]
    rw [show data15 L q N K W membership 34=(![List.replicate (v6 L q N K W) true,UnaryTemplate.tape (1024),List.replicate (v7 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v6 L q N K W) (1024)) false]) 2 from data15_slot L q N K W membership 2]
    all_goals rfl

  · change data20 L q N K W membership 44=UnaryTemplate.tape (16)
    rw [show data20 L q N K W membership 44=(![UnaryTemplate.tape (16),List.replicate (UnaryTemplate.tape (16)).length false]) 0 from data20_slot L q N K W membership 0]
    all_goals rfl

  · change data20 L q N K W membership 46=[]
    exact data20_fresh L q N K W membership 46 (by decide)

  · change data20 L q N K W membership 47=[]
    exact data20_fresh L q N K W membership 47 (by decide)

noncomputable def joined21 := Composition.machine joined20 phase21

def budget21 (L q N K W : Nat) := budget20 L q N K W+1+(WilliamsUnaryProduct.budget (v7 L q N K W) (16))

theorem joined21_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined21 (budget21 L q N K W) (input L q N K W membership) (data21 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined20_ready L q N K W membership) (ready21 L q N K W membership)

def slots22 : Fin 2→Fin 88 := ![48,49]

theorem slots22_inj : Function.Injective slots22 := by decide

noncomputable def phase22 := RecoveryFocus.machine slots22 (HierarchyFixedWord.machine (List.replicate (4) true))

noncomputable def data22 (L q N K W : Nat) (membership : List Bool) : Store := install slots22 (data21 L q N K W membership) (![List.replicate (4) true,List.replicate (List.replicate (4) true).length false])

theorem data22_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 2) : data22 L q N K W membership (slots22 j)=(![List.replicate (4) true,List.replicate (List.replicate (4) true).length false]) j :=
  install_slot slots22 slots22_inj (data21 L q N K W membership) _ j

theorem data22_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots22 j≠k) : data22 L q N K W membership k=data21 L q N K W membership k :=
  install_other slots22 (data21 L q N K W membership) _ k hk

theorem data22_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 50 ≤ k.val) : data22 L q N K W membership k=[] := by
  rw [data22_other L q N K W membership k (by
    have hs : ∀ j,(slots22 j).val<50 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data21_fresh L q N K W membership k (by omega)

theorem ready22 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase22 (2*(List.replicate (4) true).length+2) (data21 L q N K W membership) (data22 L q N K W membership) := by
  apply (RowCommonResources.literal_ready (List.replicate (4) true)).focus slots22 slots22_inj (data21 L q N K W membership)
  intro j
  fin_cases j

  · change data21 L q N K W membership 48=[]
    exact data21_fresh L q N K W membership 48 (by decide)

  · change data21 L q N K W membership 49=[]
    exact data21_fresh L q N K W membership 49 (by decide)

noncomputable def joined22 := Composition.machine joined21 phase22

def budget22 (L q N K W : Nat) := budget21 L q N K W+1+(2*(List.replicate (4) true).length+2)

theorem joined22_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined22 (budget22 L q N K W) (input L q N K W membership) (data22 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined21_ready L q N K W membership) (ready22 L q N K W membership)

def slots23 : Fin 4→Fin 88 := ![46,48,50,51]

theorem slots23_inj : Function.Injective slots23 := by decide

noncomputable def phase23 := RecoveryFocus.machine slots23 ClockUnarySum.machine

noncomputable def data23 (L q N K W : Nat) (membership : List Bool) : Store := install slots23 (data22 L q N K W membership) (![List.replicate (v10 L q N K W) true,List.replicate (4) true,List.replicate (v11 L q N K W) true,List.replicate ((v10 L q N K W)+(4)+2) false])

theorem data23_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data23 L q N K W membership (slots23 j)=(![List.replicate (v10 L q N K W) true,List.replicate (4) true,List.replicate (v11 L q N K W) true,List.replicate ((v10 L q N K W)+(4)+2) false]) j :=
  install_slot slots23 slots23_inj (data22 L q N K W membership) _ j

theorem data23_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots23 j≠k) : data23 L q N K W membership k=data22 L q N K W membership k :=
  install_other slots23 (data22 L q N K W membership) _ k hk

theorem data23_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 52 ≤ k.val) : data23 L q N K W membership k=[] := by
  rw [data23_other L q N K W membership k (by
    have hs : ∀ j,(slots23 j).val<52 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data22_fresh L q N K W membership k (by omega)

theorem ready23 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase23 (2*((v10 L q N K W)+(4))+6) (data22 L q N K W membership) (data23 L q N K W membership) := by
  apply (ClockUnarySum.sum_ready (v10 L q N K W) (4)).focus slots23 slots23_inj (data22 L q N K W membership)
  intro j
  fin_cases j

  · change data22 L q N K W membership 46=List.replicate (v10 L q N K W) true
    rw [data22_other L q N K W membership 46 (by decide)]
    rw [show data21 L q N K W membership 46=(![List.replicate (v7 L q N K W) true,UnaryTemplate.tape (16),List.replicate (v10 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v7 L q N K W) (16)) false]) 2 from data21_slot L q N K W membership 2]
    all_goals rfl

  · change data22 L q N K W membership 48=List.replicate (4) true
    rw [show data22 L q N K W membership 48=(![List.replicate (4) true,List.replicate (List.replicate (4) true).length false]) 0 from data22_slot L q N K W membership 0]
    all_goals rfl

  · change data22 L q N K W membership 50=[]
    exact data22_fresh L q N K W membership 50 (by decide)

  · change data22 L q N K W membership 51=[]
    exact data22_fresh L q N K W membership 51 (by decide)

noncomputable def joined23 := Composition.machine joined22 phase23

def budget23 (L q N K W : Nat) := budget22 L q N K W+1+(2*((v10 L q N K W)+(4))+6)

theorem joined23_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined23 (budget23 L q N K W) (input L q N K W membership) (data23 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined22_ready L q N K W membership) (ready23 L q N K W membership)

def slots24 : Fin 4→Fin 88 := ![50,2,52,53]

theorem slots24_inj : Function.Injective slots24 := by decide

noncomputable def phase24 := RecoveryFocus.machine slots24 ClockUnaryProduct.machine

noncomputable def data24 (L q N K W : Nat) (membership : List Bool) : Store := install slots24 (data23 L q N K W membership) (![List.replicate (v11 L q N K W) true,UnaryTemplate.tape (N),List.replicate (v12 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v11 L q N K W) (N)) false])

theorem data24_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data24 L q N K W membership (slots24 j)=(![List.replicate (v11 L q N K W) true,UnaryTemplate.tape (N),List.replicate (v12 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v11 L q N K W) (N)) false]) j :=
  install_slot slots24 slots24_inj (data23 L q N K W membership) _ j

theorem data24_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots24 j≠k) : data24 L q N K W membership k=data23 L q N K W membership k :=
  install_other slots24 (data23 L q N K W membership) _ k hk

theorem data24_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 54 ≤ k.val) : data24 L q N K W membership k=[] := by
  rw [data24_other L q N K W membership k (by
    have hs : ∀ j,(slots24 j).val<54 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data23_fresh L q N K W membership k (by omega)

theorem ready24 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase24 (WilliamsUnaryProduct.budget (v11 L q N K W) (N)) (data23 L q N K W membership) (data24 L q N K W membership) := by
  apply (RowCommonResources.product_ready (v11 L q N K W) (N)).focus slots24 slots24_inj (data23 L q N K W membership)
  intro j
  fin_cases j

  · change data23 L q N K W membership 50=List.replicate (v11 L q N K W) true
    rw [show data23 L q N K W membership 50=(![List.replicate (v10 L q N K W) true,List.replicate (4) true,List.replicate (v11 L q N K W) true,List.replicate ((v10 L q N K W)+(4)+2) false]) 2 from data23_slot L q N K W membership 2]
    all_goals rfl

  · change data23 L q N K W membership 2=UnaryTemplate.tape (N)
    rw [data23_other L q N K W membership 2 (by decide)]
    rw [data22_other L q N K W membership 2 (by decide)]
    rw [data21_other L q N K W membership 2 (by decide)]
    rw [data20_other L q N K W membership 2 (by decide)]
    rw [data19_other L q N K W membership 2 (by decide)]
    rw [data18_other L q N K W membership 2 (by decide)]
    rw [data17_other L q N K W membership 2 (by decide)]
    rw [data16_other L q N K W membership 2 (by decide)]
    rw [data15_other L q N K W membership 2 (by decide)]
    rw [data14_other L q N K W membership 2 (by decide)]
    rw [data13_other L q N K W membership 2 (by decide)]
    rw [data12_other L q N K W membership 2 (by decide)]
    rw [data11_other L q N K W membership 2 (by decide)]
    rw [data10_other L q N K W membership 2 (by decide)]
    rw [data9_other L q N K W membership 2 (by decide)]
    rw [data8_other L q N K W membership 2 (by decide)]
    rw [show data7 L q N K W membership 2=(![UnaryTemplate.tape (N),CompareMachine.word (N),List.replicate ((N)+2) false]) 0 from data7_slot L q N K W membership 0]
    all_goals rfl

  · change data23 L q N K W membership 52=[]
    exact data23_fresh L q N K W membership 52 (by decide)

  · change data23 L q N K W membership 53=[]
    exact data23_fresh L q N K W membership 53 (by decide)

noncomputable def joined24 := Composition.machine joined23 phase24

def budget24 (L q N K W : Nat) := budget23 L q N K W+1+(WilliamsUnaryProduct.budget (v11 L q N K W) (N))

theorem joined24_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined24 (budget24 L q N K W) (input L q N K W membership) (data24 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined23_ready L q N K W membership) (ready24 L q N K W membership)

def slots25 : Fin 2→Fin 88 := ![54,55]

theorem slots25_inj : Function.Injective slots25 := by decide

noncomputable def phase25 := RecoveryFocus.machine slots25 (HierarchyFixedWord.machine (UnaryTemplate.tape (5)))

noncomputable def data25 (L q N K W : Nat) (membership : List Bool) : Store := install slots25 (data24 L q N K W membership) (![UnaryTemplate.tape (5),List.replicate (UnaryTemplate.tape (5)).length false])

theorem data25_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 2) : data25 L q N K W membership (slots25 j)=(![UnaryTemplate.tape (5),List.replicate (UnaryTemplate.tape (5)).length false]) j :=
  install_slot slots25 slots25_inj (data24 L q N K W membership) _ j

theorem data25_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots25 j≠k) : data25 L q N K W membership k=data24 L q N K W membership k :=
  install_other slots25 (data24 L q N K W membership) _ k hk

theorem data25_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 56 ≤ k.val) : data25 L q N K W membership k=[] := by
  rw [data25_other L q N K W membership k (by
    have hs : ∀ j,(slots25 j).val<56 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data24_fresh L q N K W membership k (by omega)

theorem ready25 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase25 (2*(UnaryTemplate.tape (5)).length+2) (data24 L q N K W membership) (data25 L q N K W membership) := by
  apply (RowCommonResources.literal_ready (UnaryTemplate.tape (5))).focus slots25 slots25_inj (data24 L q N K W membership)
  intro j
  fin_cases j

  · change data24 L q N K W membership 54=[]
    exact data24_fresh L q N K W membership 54 (by decide)

  · change data24 L q N K W membership 55=[]
    exact data24_fresh L q N K W membership 55 (by decide)

noncomputable def joined25 := Composition.machine joined24 phase25

def budget25 (L q N K W : Nat) := budget24 L q N K W+1+(2*(UnaryTemplate.tape (5)).length+2)

theorem joined25_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined25 (budget25 L q N K W) (input L q N K W membership) (data25 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined24_ready L q N K W membership) (ready25 L q N K W membership)

def slots26 : Fin 4→Fin 88 := ![34,54,56,57]

theorem slots26_inj : Function.Injective slots26 := by decide

noncomputable def phase26 := RecoveryFocus.machine slots26 ClockUnaryProduct.machine

noncomputable def data26 (L q N K W : Nat) (membership : List Bool) : Store := install slots26 (data25 L q N K W membership) (![List.replicate (v7 L q N K W) true,UnaryTemplate.tape (5),List.replicate (v13 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v7 L q N K W) (5)) false])

theorem data26_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data26 L q N K W membership (slots26 j)=(![List.replicate (v7 L q N K W) true,UnaryTemplate.tape (5),List.replicate (v13 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v7 L q N K W) (5)) false]) j :=
  install_slot slots26 slots26_inj (data25 L q N K W membership) _ j

theorem data26_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots26 j≠k) : data26 L q N K W membership k=data25 L q N K W membership k :=
  install_other slots26 (data25 L q N K W membership) _ k hk

theorem data26_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 58 ≤ k.val) : data26 L q N K W membership k=[] := by
  rw [data26_other L q N K W membership k (by
    have hs : ∀ j,(slots26 j).val<58 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data25_fresh L q N K W membership k (by omega)

theorem ready26 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase26 (WilliamsUnaryProduct.budget (v7 L q N K W) (5)) (data25 L q N K W membership) (data26 L q N K W membership) := by
  apply (RowCommonResources.product_ready (v7 L q N K W) (5)).focus slots26 slots26_inj (data25 L q N K W membership)
  intro j
  fin_cases j

  · change data25 L q N K W membership 34=List.replicate (v7 L q N K W) true
    rw [data25_other L q N K W membership 34 (by decide)]
    rw [data24_other L q N K W membership 34 (by decide)]
    rw [data23_other L q N K W membership 34 (by decide)]
    rw [data22_other L q N K W membership 34 (by decide)]
    rw [show data21 L q N K W membership 34=(![List.replicate (v7 L q N K W) true,UnaryTemplate.tape (16),List.replicate (v10 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v7 L q N K W) (16)) false]) 0 from data21_slot L q N K W membership 0]
    all_goals rfl

  · change data25 L q N K W membership 54=UnaryTemplate.tape (5)
    rw [show data25 L q N K W membership 54=(![UnaryTemplate.tape (5),List.replicate (UnaryTemplate.tape (5)).length false]) 0 from data25_slot L q N K W membership 0]
    all_goals rfl

  · change data25 L q N K W membership 56=[]
    exact data25_fresh L q N K W membership 56 (by decide)

  · change data25 L q N K W membership 57=[]
    exact data25_fresh L q N K W membership 57 (by decide)

noncomputable def joined26 := Composition.machine joined25 phase26

def budget26 (L q N K W : Nat) := budget25 L q N K W+1+(WilliamsUnaryProduct.budget (v7 L q N K W) (5))

theorem joined26_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined26 (budget26 L q N K W) (input L q N K W membership) (data26 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined25_ready L q N K W membership) (ready26 L q N K W membership)

def slots27 : Fin 4→Fin 88 := ![52,56,58,59]

theorem slots27_inj : Function.Injective slots27 := by decide

noncomputable def phase27 := RecoveryFocus.machine slots27 ClockUnarySum.machine

noncomputable def data27 (L q N K W : Nat) (membership : List Bool) : Store := install slots27 (data26 L q N K W membership) (![List.replicate (v12 L q N K W) true,List.replicate (v13 L q N K W) true,List.replicate (v14 L q N K W) true,List.replicate ((v12 L q N K W)+(v13 L q N K W)+2) false])

theorem data27_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data27 L q N K W membership (slots27 j)=(![List.replicate (v12 L q N K W) true,List.replicate (v13 L q N K W) true,List.replicate (v14 L q N K W) true,List.replicate ((v12 L q N K W)+(v13 L q N K W)+2) false]) j :=
  install_slot slots27 slots27_inj (data26 L q N K W membership) _ j

theorem data27_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots27 j≠k) : data27 L q N K W membership k=data26 L q N K W membership k :=
  install_other slots27 (data26 L q N K W membership) _ k hk

theorem data27_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 60 ≤ k.val) : data27 L q N K W membership k=[] := by
  rw [data27_other L q N K W membership k (by
    have hs : ∀ j,(slots27 j).val<60 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data26_fresh L q N K W membership k (by omega)

theorem ready27 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase27 (2*((v12 L q N K W)+(v13 L q N K W))+6) (data26 L q N K W membership) (data27 L q N K W membership) := by
  apply (ClockUnarySum.sum_ready (v12 L q N K W) (v13 L q N K W)).focus slots27 slots27_inj (data26 L q N K W membership)
  intro j
  fin_cases j

  · change data26 L q N K W membership 52=List.replicate (v12 L q N K W) true
    rw [data26_other L q N K W membership 52 (by decide)]
    rw [data25_other L q N K W membership 52 (by decide)]
    rw [show data24 L q N K W membership 52=(![List.replicate (v11 L q N K W) true,UnaryTemplate.tape (N),List.replicate (v12 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v11 L q N K W) (N)) false]) 2 from data24_slot L q N K W membership 2]
    all_goals rfl

  · change data26 L q N K W membership 56=List.replicate (v13 L q N K W) true
    rw [show data26 L q N K W membership 56=(![List.replicate (v7 L q N K W) true,UnaryTemplate.tape (5),List.replicate (v13 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v7 L q N K W) (5)) false]) 2 from data26_slot L q N K W membership 2]
    all_goals rfl

  · change data26 L q N K W membership 58=[]
    exact data26_fresh L q N K W membership 58 (by decide)

  · change data26 L q N K W membership 59=[]
    exact data26_fresh L q N K W membership 59 (by decide)

noncomputable def joined27 := Composition.machine joined26 phase27

def budget27 (L q N K W : Nat) := budget26 L q N K W+1+(2*((v12 L q N K W)+(v13 L q N K W))+6)

theorem joined27_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined27 (budget27 L q N K W) (input L q N K W membership) (data27 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined26_ready L q N K W membership) (ready27 L q N K W membership)

def slots28 : Fin 2→Fin 88 := ![60,61]

theorem slots28_inj : Function.Injective slots28 := by decide

noncomputable def phase28 := RecoveryFocus.machine slots28 (HierarchyFixedWord.machine (UnaryTemplate.tape (9)))

noncomputable def data28 (L q N K W : Nat) (membership : List Bool) : Store := install slots28 (data27 L q N K W membership) (![UnaryTemplate.tape (9),List.replicate (UnaryTemplate.tape (9)).length false])

theorem data28_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 2) : data28 L q N K W membership (slots28 j)=(![UnaryTemplate.tape (9),List.replicate (UnaryTemplate.tape (9)).length false]) j :=
  install_slot slots28 slots28_inj (data27 L q N K W membership) _ j

theorem data28_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots28 j≠k) : data28 L q N K W membership k=data27 L q N K W membership k :=
  install_other slots28 (data27 L q N K W membership) _ k hk

theorem data28_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 62 ≤ k.val) : data28 L q N K W membership k=[] := by
  rw [data28_other L q N K W membership k (by
    have hs : ∀ j,(slots28 j).val<62 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data27_fresh L q N K W membership k (by omega)

theorem ready28 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase28 (2*(UnaryTemplate.tape (9)).length+2) (data27 L q N K W membership) (data28 L q N K W membership) := by
  apply (RowCommonResources.literal_ready (UnaryTemplate.tape (9))).focus slots28 slots28_inj (data27 L q N K W membership)
  intro j
  fin_cases j

  · change data27 L q N K W membership 60=[]
    exact data27_fresh L q N K W membership 60 (by decide)

  · change data27 L q N K W membership 61=[]
    exact data27_fresh L q N K W membership 61 (by decide)

noncomputable def joined28 := Composition.machine joined27 phase28

def budget28 (L q N K W : Nat) := budget27 L q N K W+1+(2*(UnaryTemplate.tape (9)).length+2)

theorem joined28_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined28 (budget28 L q N K W) (input L q N K W membership) (data28 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined27_ready L q N K W membership) (ready28 L q N K W membership)

def slots29 : Fin 4→Fin 88 := ![12,60,62,63]

theorem slots29_inj : Function.Injective slots29 := by decide

noncomputable def phase29 := RecoveryFocus.machine slots29 ClockUnaryProduct.machine

noncomputable def data29 (L q N K W : Nat) (membership : List Bool) : Store := install slots29 (data28 L q N K W membership) (![List.replicate (q) true,UnaryTemplate.tape (9),List.replicate (v15 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (q) (9)) false])

theorem data29_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data29 L q N K W membership (slots29 j)=(![List.replicate (q) true,UnaryTemplate.tape (9),List.replicate (v15 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (q) (9)) false]) j :=
  install_slot slots29 slots29_inj (data28 L q N K W membership) _ j

theorem data29_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots29 j≠k) : data29 L q N K W membership k=data28 L q N K W membership k :=
  install_other slots29 (data28 L q N K W membership) _ k hk

theorem data29_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 64 ≤ k.val) : data29 L q N K W membership k=[] := by
  rw [data29_other L q N K W membership k (by
    have hs : ∀ j,(slots29 j).val<64 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data28_fresh L q N K W membership k (by omega)

theorem ready29 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase29 (WilliamsUnaryProduct.budget (q) (9)) (data28 L q N K W membership) (data29 L q N K W membership) := by
  apply (RowCommonResources.product_ready (q) (9)).focus slots29 slots29_inj (data28 L q N K W membership)
  intro j
  fin_cases j

  · change data28 L q N K W membership 12=List.replicate (q) true
    rw [data28_other L q N K W membership 12 (by decide)]
    rw [data27_other L q N K W membership 12 (by decide)]
    rw [data26_other L q N K W membership 12 (by decide)]
    rw [data25_other L q N K W membership 12 (by decide)]
    rw [data24_other L q N K W membership 12 (by decide)]
    rw [data23_other L q N K W membership 12 (by decide)]
    rw [data22_other L q N K W membership 12 (by decide)]
    rw [data21_other L q N K W membership 12 (by decide)]
    rw [data20_other L q N K W membership 12 (by decide)]
    rw [data19_other L q N K W membership 12 (by decide)]
    rw [data18_other L q N K W membership 12 (by decide)]
    rw [data17_other L q N K W membership 12 (by decide)]
    rw [data16_other L q N K W membership 12 (by decide)]
    rw [data15_other L q N K W membership 12 (by decide)]
    rw [data14_other L q N K W membership 12 (by decide)]
    rw [data13_other L q N K W membership 12 (by decide)]
    rw [data12_other L q N K W membership 12 (by decide)]
    rw [data11_other L q N K W membership 12 (by decide)]
    rw [data10_other L q N K W membership 12 (by decide)]
    rw [data9_other L q N K W membership 12 (by decide)]
    rw [data8_other L q N K W membership 12 (by decide)]
    rw [data7_other L q N K W membership 12 (by decide)]
    rw [data6_other L q N K W membership 12 (by decide)]
    rw [data5_other L q N K W membership 12 (by decide)]
    rw [show data4 L q N K W membership 12=(![UnaryTemplate.tape (q),List.replicate (q) true,List.replicate ((q)+2) false]) 1 from data4_slot L q N K W membership 1]
    all_goals rfl

  · change data28 L q N K W membership 60=UnaryTemplate.tape (9)
    rw [show data28 L q N K W membership 60=(![UnaryTemplate.tape (9),List.replicate (UnaryTemplate.tape (9)).length false]) 0 from data28_slot L q N K W membership 0]
    all_goals rfl

  · change data28 L q N K W membership 62=[]
    exact data28_fresh L q N K W membership 62 (by decide)

  · change data28 L q N K W membership 63=[]
    exact data28_fresh L q N K W membership 63 (by decide)

noncomputable def joined29 := Composition.machine joined28 phase29

def budget29 (L q N K W : Nat) := budget28 L q N K W+1+(WilliamsUnaryProduct.budget (q) (9))

theorem joined29_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined29 (budget29 L q N K W) (input L q N K W membership) (data29 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined28_ready L q N K W membership) (ready29 L q N K W membership)

def slots30 : Fin 4→Fin 88 := ![58,62,64,65]

theorem slots30_inj : Function.Injective slots30 := by decide

noncomputable def phase30 := RecoveryFocus.machine slots30 ClockUnarySum.machine

noncomputable def data30 (L q N K W : Nat) (membership : List Bool) : Store := install slots30 (data29 L q N K W membership) (![List.replicate (v14 L q N K W) true,List.replicate (v15 L q N K W) true,List.replicate (v16 L q N K W) true,List.replicate ((v14 L q N K W)+(v15 L q N K W)+2) false])

theorem data30_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data30 L q N K W membership (slots30 j)=(![List.replicate (v14 L q N K W) true,List.replicate (v15 L q N K W) true,List.replicate (v16 L q N K W) true,List.replicate ((v14 L q N K W)+(v15 L q N K W)+2) false]) j :=
  install_slot slots30 slots30_inj (data29 L q N K W membership) _ j

theorem data30_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots30 j≠k) : data30 L q N K W membership k=data29 L q N K W membership k :=
  install_other slots30 (data29 L q N K W membership) _ k hk

theorem data30_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 66 ≤ k.val) : data30 L q N K W membership k=[] := by
  rw [data30_other L q N K W membership k (by
    have hs : ∀ j,(slots30 j).val<66 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data29_fresh L q N K W membership k (by omega)

theorem ready30 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase30 (2*((v14 L q N K W)+(v15 L q N K W))+6) (data29 L q N K W membership) (data30 L q N K W membership) := by
  apply (ClockUnarySum.sum_ready (v14 L q N K W) (v15 L q N K W)).focus slots30 slots30_inj (data29 L q N K W membership)
  intro j
  fin_cases j

  · change data29 L q N K W membership 58=List.replicate (v14 L q N K W) true
    rw [data29_other L q N K W membership 58 (by decide)]
    rw [data28_other L q N K W membership 58 (by decide)]
    rw [show data27 L q N K W membership 58=(![List.replicate (v12 L q N K W) true,List.replicate (v13 L q N K W) true,List.replicate (v14 L q N K W) true,List.replicate ((v12 L q N K W)+(v13 L q N K W)+2) false]) 2 from data27_slot L q N K W membership 2]
    all_goals rfl

  · change data29 L q N K W membership 62=List.replicate (v15 L q N K W) true
    rw [show data29 L q N K W membership 62=(![List.replicate (q) true,UnaryTemplate.tape (9),List.replicate (v15 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (q) (9)) false]) 2 from data29_slot L q N K W membership 2]
    all_goals rfl

  · change data29 L q N K W membership 64=[]
    exact data29_fresh L q N K W membership 64 (by decide)

  · change data29 L q N K W membership 65=[]
    exact data29_fresh L q N K W membership 65 (by decide)

noncomputable def joined30 := Composition.machine joined29 phase30

def budget30 (L q N K W : Nat) := budget29 L q N K W+1+(2*((v14 L q N K W)+(v15 L q N K W))+6)

theorem joined30_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined30 (budget30 L q N K W) (input L q N K W membership) (data30 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined29_ready L q N K W membership) (ready30 L q N K W membership)

def slots31 : Fin 2→Fin 88 := ![66,67]

theorem slots31_inj : Function.Injective slots31 := by decide

noncomputable def phase31 := RecoveryFocus.machine slots31 (HierarchyFixedWord.machine (UnaryTemplate.tape (7)))

noncomputable def data31 (L q N K W : Nat) (membership : List Bool) : Store := install slots31 (data30 L q N K W membership) (![UnaryTemplate.tape (7),List.replicate (UnaryTemplate.tape (7)).length false])

theorem data31_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 2) : data31 L q N K W membership (slots31 j)=(![UnaryTemplate.tape (7),List.replicate (UnaryTemplate.tape (7)).length false]) j :=
  install_slot slots31 slots31_inj (data30 L q N K W membership) _ j

theorem data31_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots31 j≠k) : data31 L q N K W membership k=data30 L q N K W membership k :=
  install_other slots31 (data30 L q N K W membership) _ k hk

theorem data31_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 68 ≤ k.val) : data31 L q N K W membership k=[] := by
  rw [data31_other L q N K W membership k (by
    have hs : ∀ j,(slots31 j).val<68 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data30_fresh L q N K W membership k (by omega)

theorem ready31 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase31 (2*(UnaryTemplate.tape (7)).length+2) (data30 L q N K W membership) (data31 L q N K W membership) := by
  apply (RowCommonResources.literal_ready (UnaryTemplate.tape (7))).focus slots31 slots31_inj (data30 L q N K W membership)
  intro j
  fin_cases j

  · change data30 L q N K W membership 66=[]
    exact data30_fresh L q N K W membership 66 (by decide)

  · change data30 L q N K W membership 67=[]
    exact data30_fresh L q N K W membership 67 (by decide)

noncomputable def joined31 := Composition.machine joined30 phase31

def budget31 (L q N K W : Nat) := budget30 L q N K W+1+(2*(UnaryTemplate.tape (7)).length+2)

theorem joined31_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined31 (budget31 L q N K W) (input L q N K W membership) (data31 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined30_ready L q N K W membership) (ready31 L q N K W membership)

def slots32 : Fin 4→Fin 88 := ![14,66,68,69]

theorem slots32_inj : Function.Injective slots32 := by decide

noncomputable def phase32 := RecoveryFocus.machine slots32 ClockUnaryProduct.machine

noncomputable def data32 (L q N K W : Nat) (membership : List Bool) : Store := install slots32 (data31 L q N K W membership) (![List.replicate (K) true,UnaryTemplate.tape (7),List.replicate (v17 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (K) (7)) false])

theorem data32_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data32 L q N K W membership (slots32 j)=(![List.replicate (K) true,UnaryTemplate.tape (7),List.replicate (v17 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (K) (7)) false]) j :=
  install_slot slots32 slots32_inj (data31 L q N K W membership) _ j

theorem data32_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots32 j≠k) : data32 L q N K W membership k=data31 L q N K W membership k :=
  install_other slots32 (data31 L q N K W membership) _ k hk

theorem data32_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 70 ≤ k.val) : data32 L q N K W membership k=[] := by
  rw [data32_other L q N K W membership k (by
    have hs : ∀ j,(slots32 j).val<70 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data31_fresh L q N K W membership k (by omega)

theorem ready32 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase32 (WilliamsUnaryProduct.budget (K) (7)) (data31 L q N K W membership) (data32 L q N K W membership) := by
  apply (RowCommonResources.product_ready (K) (7)).focus slots32 slots32_inj (data31 L q N K W membership)
  intro j
  fin_cases j

  · change data31 L q N K W membership 14=List.replicate (K) true
    rw [data31_other L q N K W membership 14 (by decide)]
    rw [data30_other L q N K W membership 14 (by decide)]
    rw [data29_other L q N K W membership 14 (by decide)]
    rw [data28_other L q N K W membership 14 (by decide)]
    rw [data27_other L q N K W membership 14 (by decide)]
    rw [data26_other L q N K W membership 14 (by decide)]
    rw [data25_other L q N K W membership 14 (by decide)]
    rw [data24_other L q N K W membership 14 (by decide)]
    rw [data23_other L q N K W membership 14 (by decide)]
    rw [data22_other L q N K W membership 14 (by decide)]
    rw [data21_other L q N K W membership 14 (by decide)]
    rw [data20_other L q N K W membership 14 (by decide)]
    rw [data19_other L q N K W membership 14 (by decide)]
    rw [data18_other L q N K W membership 14 (by decide)]
    rw [data17_other L q N K W membership 14 (by decide)]
    rw [data16_other L q N K W membership 14 (by decide)]
    rw [data15_other L q N K W membership 14 (by decide)]
    rw [data14_other L q N K W membership 14 (by decide)]
    rw [data13_other L q N K W membership 14 (by decide)]
    rw [data12_other L q N K W membership 14 (by decide)]
    rw [data11_other L q N K W membership 14 (by decide)]
    rw [data10_other L q N K W membership 14 (by decide)]
    rw [data9_other L q N K W membership 14 (by decide)]
    rw [data8_other L q N K W membership 14 (by decide)]
    rw [data7_other L q N K W membership 14 (by decide)]
    rw [data6_other L q N K W membership 14 (by decide)]
    rw [show data5 L q N K W membership 14=(![UnaryTemplate.tape (K),List.replicate (K) true,List.replicate ((K)+2) false]) 1 from data5_slot L q N K W membership 1]
    all_goals rfl

  · change data31 L q N K W membership 66=UnaryTemplate.tape (7)
    rw [show data31 L q N K W membership 66=(![UnaryTemplate.tape (7),List.replicate (UnaryTemplate.tape (7)).length false]) 0 from data31_slot L q N K W membership 0]
    all_goals rfl

  · change data31 L q N K W membership 68=[]
    exact data31_fresh L q N K W membership 68 (by decide)

  · change data31 L q N K W membership 69=[]
    exact data31_fresh L q N K W membership 69 (by decide)

noncomputable def joined32 := Composition.machine joined31 phase32

def budget32 (L q N K W : Nat) := budget31 L q N K W+1+(WilliamsUnaryProduct.budget (K) (7))

theorem joined32_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined32 (budget32 L q N K W) (input L q N K W membership) (data32 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined31_ready L q N K W membership) (ready32 L q N K W membership)

def slots33 : Fin 4→Fin 88 := ![64,68,70,71]

theorem slots33_inj : Function.Injective slots33 := by decide

noncomputable def phase33 := RecoveryFocus.machine slots33 ClockUnarySum.machine

noncomputable def data33 (L q N K W : Nat) (membership : List Bool) : Store := install slots33 (data32 L q N K W membership) (![List.replicate (v16 L q N K W) true,List.replicate (v17 L q N K W) true,List.replicate (v18 L q N K W) true,List.replicate ((v16 L q N K W)+(v17 L q N K W)+2) false])

theorem data33_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data33 L q N K W membership (slots33 j)=(![List.replicate (v16 L q N K W) true,List.replicate (v17 L q N K W) true,List.replicate (v18 L q N K W) true,List.replicate ((v16 L q N K W)+(v17 L q N K W)+2) false]) j :=
  install_slot slots33 slots33_inj (data32 L q N K W membership) _ j

theorem data33_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots33 j≠k) : data33 L q N K W membership k=data32 L q N K W membership k :=
  install_other slots33 (data32 L q N K W membership) _ k hk

theorem data33_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 72 ≤ k.val) : data33 L q N K W membership k=[] := by
  rw [data33_other L q N K W membership k (by
    have hs : ∀ j,(slots33 j).val<72 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data32_fresh L q N K W membership k (by omega)

theorem ready33 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase33 (2*((v16 L q N K W)+(v17 L q N K W))+6) (data32 L q N K W membership) (data33 L q N K W membership) := by
  apply (ClockUnarySum.sum_ready (v16 L q N K W) (v17 L q N K W)).focus slots33 slots33_inj (data32 L q N K W membership)
  intro j
  fin_cases j

  · change data32 L q N K W membership 64=List.replicate (v16 L q N K W) true
    rw [data32_other L q N K W membership 64 (by decide)]
    rw [data31_other L q N K W membership 64 (by decide)]
    rw [show data30 L q N K W membership 64=(![List.replicate (v14 L q N K W) true,List.replicate (v15 L q N K W) true,List.replicate (v16 L q N K W) true,List.replicate ((v14 L q N K W)+(v15 L q N K W)+2) false]) 2 from data30_slot L q N K W membership 2]
    all_goals rfl

  · change data32 L q N K W membership 68=List.replicate (v17 L q N K W) true
    rw [show data32 L q N K W membership 68=(![List.replicate (K) true,UnaryTemplate.tape (7),List.replicate (v17 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (K) (7)) false]) 2 from data32_slot L q N K W membership 2]
    all_goals rfl

  · change data32 L q N K W membership 70=[]
    exact data32_fresh L q N K W membership 70 (by decide)

  · change data32 L q N K W membership 71=[]
    exact data32_fresh L q N K W membership 71 (by decide)

noncomputable def joined33 := Composition.machine joined32 phase33

def budget33 (L q N K W : Nat) := budget32 L q N K W+1+(2*((v16 L q N K W)+(v17 L q N K W))+6)

theorem joined33_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined33 (budget33 L q N K W) (input L q N K W membership) (data33 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined32_ready L q N K W membership) (ready33 L q N K W membership)

def slots34 : Fin 2→Fin 88 := ![72,73]

theorem slots34_inj : Function.Injective slots34 := by decide

noncomputable def phase34 := RecoveryFocus.machine slots34 (HierarchyFixedWord.machine (UnaryTemplate.tape (2)))

noncomputable def data34 (L q N K W : Nat) (membership : List Bool) : Store := install slots34 (data33 L q N K W membership) (![UnaryTemplate.tape (2),List.replicate (UnaryTemplate.tape (2)).length false])

theorem data34_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 2) : data34 L q N K W membership (slots34 j)=(![UnaryTemplate.tape (2),List.replicate (UnaryTemplate.tape (2)).length false]) j :=
  install_slot slots34 slots34_inj (data33 L q N K W membership) _ j

theorem data34_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots34 j≠k) : data34 L q N K W membership k=data33 L q N K W membership k :=
  install_other slots34 (data33 L q N K W membership) _ k hk

theorem data34_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 74 ≤ k.val) : data34 L q N K W membership k=[] := by
  rw [data34_other L q N K W membership k (by
    have hs : ∀ j,(slots34 j).val<74 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data33_fresh L q N K W membership k (by omega)

theorem ready34 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase34 (2*(UnaryTemplate.tape (2)).length+2) (data33 L q N K W membership) (data34 L q N K W membership) := by
  apply (RowCommonResources.literal_ready (UnaryTemplate.tape (2))).focus slots34 slots34_inj (data33 L q N K W membership)
  intro j
  fin_cases j

  · change data33 L q N K W membership 72=[]
    exact data33_fresh L q N K W membership 72 (by decide)

  · change data33 L q N K W membership 73=[]
    exact data33_fresh L q N K W membership 73 (by decide)

noncomputable def joined34 := Composition.machine joined33 phase34

def budget34 (L q N K W : Nat) := budget33 L q N K W+1+(2*(UnaryTemplate.tape (2)).length+2)

theorem joined34_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined34 (budget34 L q N K W) (input L q N K W membership) (data34 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined33_ready L q N K W membership) (ready34 L q N K W membership)

def slots35 : Fin 4→Fin 88 := ![4,72,74,75]

theorem slots35_inj : Function.Injective slots35 := by decide

noncomputable def phase35 := RecoveryFocus.machine slots35 ClockUnaryProduct.machine

noncomputable def data35 (L q N K W : Nat) (membership : List Bool) : Store := install slots35 (data34 L q N K W membership) (![List.replicate (W) true,UnaryTemplate.tape (2),List.replicate (v19 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (W) (2)) false])

theorem data35_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data35 L q N K W membership (slots35 j)=(![List.replicate (W) true,UnaryTemplate.tape (2),List.replicate (v19 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (W) (2)) false]) j :=
  install_slot slots35 slots35_inj (data34 L q N K W membership) _ j

theorem data35_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots35 j≠k) : data35 L q N K W membership k=data34 L q N K W membership k :=
  install_other slots35 (data34 L q N K W membership) _ k hk

theorem data35_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 76 ≤ k.val) : data35 L q N K W membership k=[] := by
  rw [data35_other L q N K W membership k (by
    have hs : ∀ j,(slots35 j).val<76 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data34_fresh L q N K W membership k (by omega)

theorem ready35 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase35 (WilliamsUnaryProduct.budget (W) (2)) (data34 L q N K W membership) (data35 L q N K W membership) := by
  apply (RowCommonResources.product_ready (W) (2)).focus slots35 slots35_inj (data34 L q N K W membership)
  intro j
  fin_cases j

  · change data34 L q N K W membership 4=List.replicate (W) true
    rw [data34_other L q N K W membership 4 (by decide)]
    rw [data33_other L q N K W membership 4 (by decide)]
    rw [data32_other L q N K W membership 4 (by decide)]
    rw [data31_other L q N K W membership 4 (by decide)]
    rw [data30_other L q N K W membership 4 (by decide)]
    rw [data29_other L q N K W membership 4 (by decide)]
    rw [data28_other L q N K W membership 4 (by decide)]
    rw [data27_other L q N K W membership 4 (by decide)]
    rw [data26_other L q N K W membership 4 (by decide)]
    rw [data25_other L q N K W membership 4 (by decide)]
    rw [data24_other L q N K W membership 4 (by decide)]
    rw [data23_other L q N K W membership 4 (by decide)]
    rw [data22_other L q N K W membership 4 (by decide)]
    rw [data21_other L q N K W membership 4 (by decide)]
    rw [data20_other L q N K W membership 4 (by decide)]
    rw [data19_other L q N K W membership 4 (by decide)]
    rw [data18_other L q N K W membership 4 (by decide)]
    rw [data17_other L q N K W membership 4 (by decide)]
    rw [data16_other L q N K W membership 4 (by decide)]
    rw [data15_other L q N K W membership 4 (by decide)]
    rw [data14_other L q N K W membership 4 (by decide)]
    rw [data13_other L q N K W membership 4 (by decide)]
    rw [data12_other L q N K W membership 4 (by decide)]
    rw [data11_other L q N K W membership 4 (by decide)]
    rw [data10_other L q N K W membership 4 (by decide)]
    rw [data9_other L q N K W membership 4 (by decide)]
    rw [data8_other L q N K W membership 4 (by decide)]
    rw [data7_other L q N K W membership 4 (by decide)]
    rw [data6_other L q N K W membership 4 (by decide)]
    rw [data5_other L q N K W membership 4 (by decide)]
    rw [data4_other L q N K W membership 4 (by decide)]
    rw [data3_other L q N K W membership 4 (by decide)]
    rw [data2_other L q N K W membership 4 (by decide)]
    rw [data1_other L q N K W membership 4 (by decide)]
    all_goals rfl

  · change data34 L q N K W membership 72=UnaryTemplate.tape (2)
    rw [show data34 L q N K W membership 72=(![UnaryTemplate.tape (2),List.replicate (UnaryTemplate.tape (2)).length false]) 0 from data34_slot L q N K W membership 0]
    all_goals rfl

  · change data34 L q N K W membership 74=[]
    exact data34_fresh L q N K W membership 74 (by decide)

  · change data34 L q N K W membership 75=[]
    exact data34_fresh L q N K W membership 75 (by decide)

noncomputable def joined35 := Composition.machine joined34 phase35

def budget35 (L q N K W : Nat) := budget34 L q N K W+1+(WilliamsUnaryProduct.budget (W) (2))

theorem joined35_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined35 (budget35 L q N K W) (input L q N K W membership) (data35 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined34_ready L q N K W membership) (ready35 L q N K W membership)

def slots36 : Fin 4→Fin 88 := ![70,74,76,77]

theorem slots36_inj : Function.Injective slots36 := by decide

noncomputable def phase36 := RecoveryFocus.machine slots36 ClockUnarySum.machine

noncomputable def data36 (L q N K W : Nat) (membership : List Bool) : Store := install slots36 (data35 L q N K W membership) (![List.replicate (v18 L q N K W) true,List.replicate (v19 L q N K W) true,List.replicate (v20 L q N K W) true,List.replicate ((v18 L q N K W)+(v19 L q N K W)+2) false])

theorem data36_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data36 L q N K W membership (slots36 j)=(![List.replicate (v18 L q N K W) true,List.replicate (v19 L q N K W) true,List.replicate (v20 L q N K W) true,List.replicate ((v18 L q N K W)+(v19 L q N K W)+2) false]) j :=
  install_slot slots36 slots36_inj (data35 L q N K W membership) _ j

theorem data36_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots36 j≠k) : data36 L q N K W membership k=data35 L q N K W membership k :=
  install_other slots36 (data35 L q N K W membership) _ k hk

theorem data36_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 78 ≤ k.val) : data36 L q N K W membership k=[] := by
  rw [data36_other L q N K W membership k (by
    have hs : ∀ j,(slots36 j).val<78 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data35_fresh L q N K W membership k (by omega)

theorem ready36 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase36 (2*((v18 L q N K W)+(v19 L q N K W))+6) (data35 L q N K W membership) (data36 L q N K W membership) := by
  apply (ClockUnarySum.sum_ready (v18 L q N K W) (v19 L q N K W)).focus slots36 slots36_inj (data35 L q N K W membership)
  intro j
  fin_cases j

  · change data35 L q N K W membership 70=List.replicate (v18 L q N K W) true
    rw [data35_other L q N K W membership 70 (by decide)]
    rw [data34_other L q N K W membership 70 (by decide)]
    rw [show data33 L q N K W membership 70=(![List.replicate (v16 L q N K W) true,List.replicate (v17 L q N K W) true,List.replicate (v18 L q N K W) true,List.replicate ((v16 L q N K W)+(v17 L q N K W)+2) false]) 2 from data33_slot L q N K W membership 2]
    all_goals rfl

  · change data35 L q N K W membership 74=List.replicate (v19 L q N K W) true
    rw [show data35 L q N K W membership 74=(![List.replicate (W) true,UnaryTemplate.tape (2),List.replicate (v19 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (W) (2)) false]) 2 from data35_slot L q N K W membership 2]
    all_goals rfl

  · change data35 L q N K W membership 76=[]
    exact data35_fresh L q N K W membership 76 (by decide)

  · change data35 L q N K W membership 77=[]
    exact data35_fresh L q N K W membership 77 (by decide)

noncomputable def joined36 := Composition.machine joined35 phase36

def budget36 (L q N K W : Nat) := budget35 L q N K W+1+(2*((v18 L q N K W)+(v19 L q N K W))+6)

theorem joined36_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined36 (budget36 L q N K W) (input L q N K W membership) (data36 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined35_ready L q N K W membership) (ready36 L q N K W membership)

def slots37 : Fin 2→Fin 88 := ![78,79]

theorem slots37_inj : Function.Injective slots37 := by decide

noncomputable def phase37 := RecoveryFocus.machine slots37 (HierarchyFixedWord.machine (List.replicate (133) true))

noncomputable def data37 (L q N K W : Nat) (membership : List Bool) : Store := install slots37 (data36 L q N K W membership) (![List.replicate (133) true,List.replicate (List.replicate (133) true).length false])

theorem data37_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 2) : data37 L q N K W membership (slots37 j)=(![List.replicate (133) true,List.replicate (List.replicate (133) true).length false]) j :=
  install_slot slots37 slots37_inj (data36 L q N K W membership) _ j

theorem data37_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots37 j≠k) : data37 L q N K W membership k=data36 L q N K W membership k :=
  install_other slots37 (data36 L q N K W membership) _ k hk

theorem data37_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 80 ≤ k.val) : data37 L q N K W membership k=[] := by
  rw [data37_other L q N K W membership k (by
    have hs : ∀ j,(slots37 j).val<80 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data36_fresh L q N K W membership k (by omega)

theorem ready37 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase37 (2*(List.replicate (133) true).length+2) (data36 L q N K W membership) (data37 L q N K W membership) := by
  apply (RowCommonResources.literal_ready (List.replicate (133) true)).focus slots37 slots37_inj (data36 L q N K W membership)
  intro j
  fin_cases j

  · change data36 L q N K W membership 78=[]
    exact data36_fresh L q N K W membership 78 (by decide)

  · change data36 L q N K W membership 79=[]
    exact data36_fresh L q N K W membership 79 (by decide)

noncomputable def joined37 := Composition.machine joined36 phase37

def budget37 (L q N K W : Nat) := budget36 L q N K W+1+(2*(List.replicate (133) true).length+2)

theorem joined37_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined37 (budget37 L q N K W) (input L q N K W membership) (data37 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined36_ready L q N K W membership) (ready37 L q N K W membership)

def slots38 : Fin 4→Fin 88 := ![76,78,80,81]

theorem slots38_inj : Function.Injective slots38 := by decide

noncomputable def phase38 := RecoveryFocus.machine slots38 ClockUnarySum.machine

noncomputable def data38 (L q N K W : Nat) (membership : List Bool) : Store := install slots38 (data37 L q N K W membership) (![List.replicate (v20 L q N K W) true,List.replicate (133) true,List.replicate (v21 L q N K W) true,List.replicate ((v20 L q N K W)+(133)+2) false])

theorem data38_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data38 L q N K W membership (slots38 j)=(![List.replicate (v20 L q N K W) true,List.replicate (133) true,List.replicate (v21 L q N K W) true,List.replicate ((v20 L q N K W)+(133)+2) false]) j :=
  install_slot slots38 slots38_inj (data37 L q N K W membership) _ j

theorem data38_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots38 j≠k) : data38 L q N K W membership k=data37 L q N K W membership k :=
  install_other slots38 (data37 L q N K W membership) _ k hk

theorem data38_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 82 ≤ k.val) : data38 L q N K W membership k=[] := by
  rw [data38_other L q N K W membership k (by
    have hs : ∀ j,(slots38 j).val<82 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data37_fresh L q N K W membership k (by omega)

theorem ready38 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase38 (2*((v20 L q N K W)+(133))+6) (data37 L q N K W membership) (data38 L q N K W membership) := by
  apply (ClockUnarySum.sum_ready (v20 L q N K W) (133)).focus slots38 slots38_inj (data37 L q N K W membership)
  intro j
  fin_cases j

  · change data37 L q N K W membership 76=List.replicate (v20 L q N K W) true
    rw [data37_other L q N K W membership 76 (by decide)]
    rw [show data36 L q N K W membership 76=(![List.replicate (v18 L q N K W) true,List.replicate (v19 L q N K W) true,List.replicate (v20 L q N K W) true,List.replicate ((v18 L q N K W)+(v19 L q N K W)+2) false]) 2 from data36_slot L q N K W membership 2]
    all_goals rfl

  · change data37 L q N K W membership 78=List.replicate (133) true
    rw [show data37 L q N K W membership 78=(![List.replicate (133) true,List.replicate (List.replicate (133) true).length false]) 0 from data37_slot L q N K W membership 0]
    all_goals rfl

  · change data37 L q N K W membership 80=[]
    exact data37_fresh L q N K W membership 80 (by decide)

  · change data37 L q N K W membership 81=[]
    exact data37_fresh L q N K W membership 81 (by decide)

noncomputable def joined38 := Composition.machine joined37 phase38

def budget38 (L q N K W : Nat) := budget37 L q N K W+1+(2*((v20 L q N K W)+(133))+6)

theorem joined38_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined38 (budget38 L q N K W) (input L q N K W membership) (data38 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined37_ready L q N K W membership) (ready38 L q N K W membership)

def slots39 : Fin 4→Fin 88 := ![80,6,82,83]

theorem slots39_inj : Function.Injective slots39 := by decide

noncomputable def phase39 := RecoveryFocus.machine slots39 ClockUnarySum.machine

noncomputable def data39 (L q N K W : Nat) (membership : List Bool) : Store := install slots39 (data38 L q N K W membership) (![List.replicate (v21 L q N K W) true,List.replicate (1) true,List.replicate (v22 L q N K W) true,List.replicate ((v21 L q N K W)+(1)+2) false])

theorem data39_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 4) : data39 L q N K W membership (slots39 j)=(![List.replicate (v21 L q N K W) true,List.replicate (1) true,List.replicate (v22 L q N K W) true,List.replicate ((v21 L q N K W)+(1)+2) false]) j :=
  install_slot slots39 slots39_inj (data38 L q N K W membership) _ j

theorem data39_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots39 j≠k) : data39 L q N K W membership k=data38 L q N K W membership k :=
  install_other slots39 (data38 L q N K W membership) _ k hk

theorem data39_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 84 ≤ k.val) : data39 L q N K W membership k=[] := by
  rw [data39_other L q N K W membership k (by
    have hs : ∀ j,(slots39 j).val<84 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data38_fresh L q N K W membership k (by omega)

theorem ready39 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase39 (2*((v21 L q N K W)+(1))+6) (data38 L q N K W membership) (data39 L q N K W membership) := by
  apply (ClockUnarySum.sum_ready (v21 L q N K W) (1)).focus slots39 slots39_inj (data38 L q N K W membership)
  intro j
  fin_cases j

  · change data38 L q N K W membership 80=List.replicate (v21 L q N K W) true
    rw [show data38 L q N K W membership 80=(![List.replicate (v20 L q N K W) true,List.replicate (133) true,List.replicate (v21 L q N K W) true,List.replicate ((v20 L q N K W)+(133)+2) false]) 2 from data38_slot L q N K W membership 2]
    all_goals rfl

  · change data38 L q N K W membership 6=List.replicate (1) true
    rw [data38_other L q N K W membership 6 (by decide)]
    rw [data37_other L q N K W membership 6 (by decide)]
    rw [data36_other L q N K W membership 6 (by decide)]
    rw [data35_other L q N K W membership 6 (by decide)]
    rw [data34_other L q N K W membership 6 (by decide)]
    rw [data33_other L q N K W membership 6 (by decide)]
    rw [data32_other L q N K W membership 6 (by decide)]
    rw [data31_other L q N K W membership 6 (by decide)]
    rw [data30_other L q N K W membership 6 (by decide)]
    rw [data29_other L q N K W membership 6 (by decide)]
    rw [data28_other L q N K W membership 6 (by decide)]
    rw [data27_other L q N K W membership 6 (by decide)]
    rw [data26_other L q N K W membership 6 (by decide)]
    rw [data25_other L q N K W membership 6 (by decide)]
    rw [data24_other L q N K W membership 6 (by decide)]
    rw [data23_other L q N K W membership 6 (by decide)]
    rw [data22_other L q N K W membership 6 (by decide)]
    rw [data21_other L q N K W membership 6 (by decide)]
    rw [data20_other L q N K W membership 6 (by decide)]
    rw [data19_other L q N K W membership 6 (by decide)]
    rw [data18_other L q N K W membership 6 (by decide)]
    rw [data17_other L q N K W membership 6 (by decide)]
    rw [data16_other L q N K W membership 6 (by decide)]
    rw [data15_other L q N K W membership 6 (by decide)]
    rw [data14_other L q N K W membership 6 (by decide)]
    rw [data13_other L q N K W membership 6 (by decide)]
    rw [data12_other L q N K W membership 6 (by decide)]
    rw [data11_other L q N K W membership 6 (by decide)]
    rw [data10_other L q N K W membership 6 (by decide)]
    rw [data9_other L q N K W membership 6 (by decide)]
    rw [data8_other L q N K W membership 6 (by decide)]
    rw [data7_other L q N K W membership 6 (by decide)]
    rw [data6_other L q N K W membership 6 (by decide)]
    rw [data5_other L q N K W membership 6 (by decide)]
    rw [data4_other L q N K W membership 6 (by decide)]
    rw [show data3 L q N K W membership 6=(![List.replicate (v1 L q N K W) true,List.replicate (1) true,List.replicate (v2 L q N K W) true,List.replicate ((v1 L q N K W)+(1)+2) false]) 1 from data3_slot L q N K W membership 1]
    all_goals rfl

  · change data38 L q N K W membership 82=[]
    exact data38_fresh L q N K W membership 82 (by decide)

  · change data38 L q N K W membership 83=[]
    exact data38_fresh L q N K W membership 83 (by decide)

noncomputable def joined39 := Composition.machine joined38 phase39

def budget39 (L q N K W : Nat) := budget38 L q N K W+1+(2*((v21 L q N K W)+(1))+6)

theorem joined39_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined39 (budget39 L q N K W) (input L q N K W membership) (data39 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined38_ready L q N K W membership) (ready39 L q N K W membership)

def slots40 : Fin 5→Fin 88 := ![8,84,85,86,87]

theorem slots40_inj : Function.Injective slots40 := by decide

noncomputable def phase40 := RecoveryFocus.machine slots40 ClockNormalize.machine

noncomputable def data40 (L q N K W : Nat) (membership : List Bool) : Store := install slots40 (data39 L q N K W membership) (zeroOutput (v1 L q N K W))

theorem data40_slot (L q N K W : Nat) (membership : List Bool) (j : Fin 5) : data40 L q N K W membership (slots40 j)=(zeroOutput (v1 L q N K W)) j :=
  install_slot slots40 slots40_inj (data39 L q N K W membership) _ j

theorem data40_other (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : ∀ j,slots40 j≠k) : data40 L q N K W membership k=data39 L q N K W membership k :=
  install_other slots40 (data39 L q N K W membership) _ k hk

theorem data40_fresh (L q N K W : Nat) (membership : List Bool) (k : Fin 88) (hk : 88 ≤ k.val) : data40 L q N K W membership k=[] := by
  rw [data40_other L q N K W membership k (by
    have hs : ∀ j,(slots40 j).val<88 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data39_fresh L q N K W membership k (by omega)

theorem ready40 (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun phase40 (4*(v1 L q N K W)+4) (data39 L q N K W membership) (data40 L q N K W membership) := by
  apply ((zero_spec (v1 L q N K W)).1).focus slots40 slots40_inj (data39 L q N K W membership)
  intro j
  fin_cases j

  · change data39 L q N K W membership 8=List.replicate (v1 L q N K W) true
    rw [data39_other L q N K W membership 8 (by decide)]
    rw [data38_other L q N K W membership 8 (by decide)]
    rw [data37_other L q N K W membership 8 (by decide)]
    rw [data36_other L q N K W membership 8 (by decide)]
    rw [data35_other L q N K W membership 8 (by decide)]
    rw [data34_other L q N K W membership 8 (by decide)]
    rw [data33_other L q N K W membership 8 (by decide)]
    rw [data32_other L q N K W membership 8 (by decide)]
    rw [data31_other L q N K W membership 8 (by decide)]
    rw [data30_other L q N K W membership 8 (by decide)]
    rw [data29_other L q N K W membership 8 (by decide)]
    rw [data28_other L q N K W membership 8 (by decide)]
    rw [data27_other L q N K W membership 8 (by decide)]
    rw [data26_other L q N K W membership 8 (by decide)]
    rw [data25_other L q N K W membership 8 (by decide)]
    rw [data24_other L q N K W membership 8 (by decide)]
    rw [data23_other L q N K W membership 8 (by decide)]
    rw [data22_other L q N K W membership 8 (by decide)]
    rw [data21_other L q N K W membership 8 (by decide)]
    rw [data20_other L q N K W membership 8 (by decide)]
    rw [data19_other L q N K W membership 8 (by decide)]
    rw [data18_other L q N K W membership 8 (by decide)]
    rw [show data17 L q N K W membership 8=(![List.replicate (v1 L q N K W) true,UnaryTemplate.tape (8),List.replicate (v8 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v1 L q N K W) (8)) false]) 0 from data17_slot L q N K W membership 0]
    all_goals rfl

  · change data39 L q N K W membership 84=[]
    exact data39_fresh L q N K W membership 84 (by decide)

  · change data39 L q N K W membership 85=[]
    exact data39_fresh L q N K W membership 85 (by decide)

  · change data39 L q N K W membership 86=[]
    exact data39_fresh L q N K W membership 86 (by decide)

  · change data39 L q N K W membership 87=[]
    exact data39_fresh L q N K W membership 87 (by decide)

noncomputable def joined40 := Composition.machine joined39 phase40

def budget40 (L q N K W : Nat) := budget39 L q N K W+1+(4*(v1 L q N K W)+4)

theorem joined40_ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun joined40 (budget40 L q N K W) (input L q N K W membership) (data40 L q N K W membership) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined39_ready L q N K W membership) (ready40 L q N K W membership)

noncomputable def machine := joined40
noncomputable def output := data40
def budget := budget40

def fields : Fin 9→Fin 88 := ![8,85,42,16,5,34,10,18,80]

theorem fields_injective : Function.Injective fields := by decide

def capacityPort : Fin 88 := 82
def compareKPort : Fin 88 := 20

theorem ready (L q N K W : Nat) (membership : List Bool) : ClockJoin.ReadyRun machine (budget L q N K W) (input L q N K W membership) (output L q N K W membership) := joined40_ready L q N K W membership

theorem output_fields (L q N K W : Nat) (membership : List Bool) : ∀ j,output L q N K W membership (fields j)=BinaryCacheColdParameters.words L q N K W membership j := by
  intro j
  fin_cases j

  · have h : data40 L q N K W membership 8=List.replicate (v1 L q N K W) true := by
      rw [show data40 L q N K W membership 8=(zeroOutput (v1 L q N K W)) 0 from data40_slot L q N K W membership 0]
      exact (zero_spec (v1 L q N K W)).2.1

    change data40 L q N K W membership 8=List.replicate (BinaryCacheColdParameters.w L) true
    simpa only [width_eq] using h

  · have h : data40 L q N K W membership 85=RepairOrdinary.frame (SignedSortKey.binary (v1 L q N K W) 0) := by
      rw [show data40 L q N K W membership 85=(zeroOutput (v1 L q N K W)) 2 from data40_slot L q N K W membership 2]
      exact (zero_spec (v1 L q N K W)).2.2

    change data40 L q N K W membership 85=RepairOrdinary.frame (SignedSortKey.binary (BinaryCacheColdParameters.w L) 0)
    simpa only [width_eq] using h

  · have h : data40 L q N K W membership 42=List.replicate (v9 L q N K W) true := by
      rw [data40_other L q N K W membership 42 (by decide)]
      rw [data39_other L q N K W membership 42 (by decide)]
      rw [data38_other L q N K W membership 42 (by decide)]
      rw [data37_other L q N K W membership 42 (by decide)]
      rw [data36_other L q N K W membership 42 (by decide)]
      rw [data35_other L q N K W membership 42 (by decide)]
      rw [data34_other L q N K W membership 42 (by decide)]
      rw [data33_other L q N K W membership 42 (by decide)]
      rw [data32_other L q N K W membership 42 (by decide)]
      rw [data31_other L q N K W membership 42 (by decide)]
      rw [data30_other L q N K W membership 42 (by decide)]
      rw [data29_other L q N K W membership 42 (by decide)]
      rw [data28_other L q N K W membership 42 (by decide)]
      rw [data27_other L q N K W membership 42 (by decide)]
      rw [data26_other L q N K W membership 42 (by decide)]
      rw [data25_other L q N K W membership 42 (by decide)]
      rw [data24_other L q N K W membership 42 (by decide)]
      rw [data23_other L q N K W membership 42 (by decide)]
      rw [data22_other L q N K W membership 42 (by decide)]
      rw [data21_other L q N K W membership 42 (by decide)]
      rw [data20_other L q N K W membership 42 (by decide)]
      rw [show data19 L q N K W membership 42=(![List.replicate (v8 L q N K W) true,List.replicate (12) true,List.replicate (v9 L q N K W) true,List.replicate ((v8 L q N K W)+(12)+2) false]) 2 from data19_slot L q N K W membership 2]
      all_goals rfl

    change data40 L q N K W membership 42=List.replicate (BinaryCacheColdParameters.C L) true
    simpa only [counter_eq] using h

  · have h : data40 L q N K W membership 16=CompareMachine.word (q) := by
      rw [data40_other L q N K W membership 16 (by decide)]
      rw [data39_other L q N K W membership 16 (by decide)]
      rw [data38_other L q N K W membership 16 (by decide)]
      rw [data37_other L q N K W membership 16 (by decide)]
      rw [data36_other L q N K W membership 16 (by decide)]
      rw [data35_other L q N K W membership 16 (by decide)]
      rw [data34_other L q N K W membership 16 (by decide)]
      rw [data33_other L q N K W membership 16 (by decide)]
      rw [data32_other L q N K W membership 16 (by decide)]
      rw [data31_other L q N K W membership 16 (by decide)]
      rw [data30_other L q N K W membership 16 (by decide)]
      rw [data29_other L q N K W membership 16 (by decide)]
      rw [data28_other L q N K W membership 16 (by decide)]
      rw [data27_other L q N K W membership 16 (by decide)]
      rw [data26_other L q N K W membership 16 (by decide)]
      rw [data25_other L q N K W membership 16 (by decide)]
      rw [data24_other L q N K W membership 16 (by decide)]
      rw [data23_other L q N K W membership 16 (by decide)]
      rw [data22_other L q N K W membership 16 (by decide)]
      rw [data21_other L q N K W membership 16 (by decide)]
      rw [data20_other L q N K W membership 16 (by decide)]
      rw [data19_other L q N K W membership 16 (by decide)]
      rw [data18_other L q N K W membership 16 (by decide)]
      rw [data17_other L q N K W membership 16 (by decide)]
      rw [data16_other L q N K W membership 16 (by decide)]
      rw [data15_other L q N K W membership 16 (by decide)]
      rw [data14_other L q N K W membership 16 (by decide)]
      rw [data13_other L q N K W membership 16 (by decide)]
      rw [data12_other L q N K W membership 16 (by decide)]
      rw [data11_other L q N K W membership 16 (by decide)]
      rw [data10_other L q N K W membership 16 (by decide)]
      rw [data9_other L q N K W membership 16 (by decide)]
      rw [data8_other L q N K W membership 16 (by decide)]
      rw [data7_other L q N K W membership 16 (by decide)]
      rw [show data6 L q N K W membership 16=(![UnaryTemplate.tape (q),CompareMachine.word (q),List.replicate ((q)+2) false]) 1 from data6_slot L q N K W membership 1]
      all_goals rfl

    change data40 L q N K W membership 16=CompareMachine.word (q)
    exact h

  · have h : data40 L q N K W membership 5=membership := by
      rw [data40_other L q N K W membership 5 (by decide)]
      rw [data39_other L q N K W membership 5 (by decide)]
      rw [data38_other L q N K W membership 5 (by decide)]
      rw [data37_other L q N K W membership 5 (by decide)]
      rw [data36_other L q N K W membership 5 (by decide)]
      rw [data35_other L q N K W membership 5 (by decide)]
      rw [data34_other L q N K W membership 5 (by decide)]
      rw [data33_other L q N K W membership 5 (by decide)]
      rw [data32_other L q N K W membership 5 (by decide)]
      rw [data31_other L q N K W membership 5 (by decide)]
      rw [data30_other L q N K W membership 5 (by decide)]
      rw [data29_other L q N K W membership 5 (by decide)]
      rw [data28_other L q N K W membership 5 (by decide)]
      rw [data27_other L q N K W membership 5 (by decide)]
      rw [data26_other L q N K W membership 5 (by decide)]
      rw [data25_other L q N K W membership 5 (by decide)]
      rw [data24_other L q N K W membership 5 (by decide)]
      rw [data23_other L q N K W membership 5 (by decide)]
      rw [data22_other L q N K W membership 5 (by decide)]
      rw [data21_other L q N K W membership 5 (by decide)]
      rw [data20_other L q N K W membership 5 (by decide)]
      rw [data19_other L q N K W membership 5 (by decide)]
      rw [data18_other L q N K W membership 5 (by decide)]
      rw [data17_other L q N K W membership 5 (by decide)]
      rw [data16_other L q N K W membership 5 (by decide)]
      rw [data15_other L q N K W membership 5 (by decide)]
      rw [data14_other L q N K W membership 5 (by decide)]
      rw [data13_other L q N K W membership 5 (by decide)]
      rw [data12_other L q N K W membership 5 (by decide)]
      rw [data11_other L q N K W membership 5 (by decide)]
      rw [data10_other L q N K W membership 5 (by decide)]
      rw [data9_other L q N K W membership 5 (by decide)]
      rw [data8_other L q N K W membership 5 (by decide)]
      rw [data7_other L q N K W membership 5 (by decide)]
      rw [data6_other L q N K W membership 5 (by decide)]
      rw [data5_other L q N K W membership 5 (by decide)]
      rw [data4_other L q N K W membership 5 (by decide)]
      rw [data3_other L q N K W membership 5 (by decide)]
      rw [data2_other L q N K W membership 5 (by decide)]
      rw [data1_other L q N K W membership 5 (by decide)]
      all_goals rfl

    change data40 L q N K W membership 5=membership
    exact h

  · have h : data40 L q N K W membership 34=List.replicate (v7 L q N K W) true := by
      rw [data40_other L q N K W membership 34 (by decide)]
      rw [data39_other L q N K W membership 34 (by decide)]
      rw [data38_other L q N K W membership 34 (by decide)]
      rw [data37_other L q N K W membership 34 (by decide)]
      rw [data36_other L q N K W membership 34 (by decide)]
      rw [data35_other L q N K W membership 34 (by decide)]
      rw [data34_other L q N K W membership 34 (by decide)]
      rw [data33_other L q N K W membership 34 (by decide)]
      rw [data32_other L q N K W membership 34 (by decide)]
      rw [data31_other L q N K W membership 34 (by decide)]
      rw [data30_other L q N K W membership 34 (by decide)]
      rw [data29_other L q N K W membership 34 (by decide)]
      rw [data28_other L q N K W membership 34 (by decide)]
      rw [data27_other L q N K W membership 34 (by decide)]
      rw [show data26 L q N K W membership 34=(![List.replicate (v7 L q N K W) true,UnaryTemplate.tape (5),List.replicate (v13 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v7 L q N K W) (5)) false]) 0 from data26_slot L q N K W membership 0]
      all_goals rfl

    change data40 L q N K W membership 34=List.replicate (BinaryCacheColdParameters.R L q) true
    simpa only [reset_eq] using h

  · have h : data40 L q N K W membership 10=List.replicate (v2 L q N K W) true := by
      rw [data40_other L q N K W membership 10 (by decide)]
      rw [data39_other L q N K W membership 10 (by decide)]
      rw [data38_other L q N K W membership 10 (by decide)]
      rw [data37_other L q N K W membership 10 (by decide)]
      rw [data36_other L q N K W membership 10 (by decide)]
      rw [data35_other L q N K W membership 10 (by decide)]
      rw [data34_other L q N K W membership 10 (by decide)]
      rw [data33_other L q N K W membership 10 (by decide)]
      rw [data32_other L q N K W membership 10 (by decide)]
      rw [data31_other L q N K W membership 10 (by decide)]
      rw [data30_other L q N K W membership 10 (by decide)]
      rw [data29_other L q N K W membership 10 (by decide)]
      rw [data28_other L q N K W membership 10 (by decide)]
      rw [data27_other L q N K W membership 10 (by decide)]
      rw [data26_other L q N K W membership 10 (by decide)]
      rw [data25_other L q N K W membership 10 (by decide)]
      rw [data24_other L q N K W membership 10 (by decide)]
      rw [data23_other L q N K W membership 10 (by decide)]
      rw [data22_other L q N K W membership 10 (by decide)]
      rw [data21_other L q N K W membership 10 (by decide)]
      rw [data20_other L q N K W membership 10 (by decide)]
      rw [data19_other L q N K W membership 10 (by decide)]
      rw [data18_other L q N K W membership 10 (by decide)]
      rw [data17_other L q N K W membership 10 (by decide)]
      rw [data16_other L q N K W membership 10 (by decide)]
      rw [data15_other L q N K W membership 10 (by decide)]
      rw [data14_other L q N K W membership 10 (by decide)]
      rw [data13_other L q N K W membership 10 (by decide)]
      rw [data12_other L q N K W membership 10 (by decide)]
      rw [data11_other L q N K W membership 10 (by decide)]
      rw [show data10 L q N K W membership 10=(![List.replicate (v2 L q N K W) true,List.replicate (v1 L q N K W) true,List.replicate (v4 L q N K W) true,List.replicate ((v2 L q N K W)+(v1 L q N K W)+2) false]) 0 from data10_slot L q N K W membership 0]
      all_goals rfl

    change data40 L q N K W membership 10=List.replicate (BinaryCacheColdParameters.B L) true
    simpa only [bound_eq] using h

  · have h : data40 L q N K W membership 18=CompareMachine.word (N) := by
      rw [data40_other L q N K W membership 18 (by decide)]
      rw [data39_other L q N K W membership 18 (by decide)]
      rw [data38_other L q N K W membership 18 (by decide)]
      rw [data37_other L q N K W membership 18 (by decide)]
      rw [data36_other L q N K W membership 18 (by decide)]
      rw [data35_other L q N K W membership 18 (by decide)]
      rw [data34_other L q N K W membership 18 (by decide)]
      rw [data33_other L q N K W membership 18 (by decide)]
      rw [data32_other L q N K W membership 18 (by decide)]
      rw [data31_other L q N K W membership 18 (by decide)]
      rw [data30_other L q N K W membership 18 (by decide)]
      rw [data29_other L q N K W membership 18 (by decide)]
      rw [data28_other L q N K W membership 18 (by decide)]
      rw [data27_other L q N K W membership 18 (by decide)]
      rw [data26_other L q N K W membership 18 (by decide)]
      rw [data25_other L q N K W membership 18 (by decide)]
      rw [data24_other L q N K W membership 18 (by decide)]
      rw [data23_other L q N K W membership 18 (by decide)]
      rw [data22_other L q N K W membership 18 (by decide)]
      rw [data21_other L q N K W membership 18 (by decide)]
      rw [data20_other L q N K W membership 18 (by decide)]
      rw [data19_other L q N K W membership 18 (by decide)]
      rw [data18_other L q N K W membership 18 (by decide)]
      rw [data17_other L q N K W membership 18 (by decide)]
      rw [data16_other L q N K W membership 18 (by decide)]
      rw [data15_other L q N K W membership 18 (by decide)]
      rw [data14_other L q N K W membership 18 (by decide)]
      rw [data13_other L q N K W membership 18 (by decide)]
      rw [data12_other L q N K W membership 18 (by decide)]
      rw [data11_other L q N K W membership 18 (by decide)]
      rw [data10_other L q N K W membership 18 (by decide)]
      rw [data9_other L q N K W membership 18 (by decide)]
      rw [data8_other L q N K W membership 18 (by decide)]
      rw [show data7 L q N K W membership 18=(![UnaryTemplate.tape (N),CompareMachine.word (N),List.replicate ((N)+2) false]) 1 from data7_slot L q N K W membership 1]
      all_goals rfl

    change data40 L q N K W membership 18=CompareMachine.word (N)
    exact h

  · have h : data40 L q N K W membership 80=List.replicate (v21 L q N K W) true := by
      rw [data40_other L q N K W membership 80 (by decide)]
      rw [show data39 L q N K W membership 80=(![List.replicate (v21 L q N K W) true,List.replicate (1) true,List.replicate (v22 L q N K W) true,List.replicate ((v21 L q N K W)+(1)+2) false]) 0 from data39_slot L q N K W membership 0]
      all_goals rfl

    change data40 L q N K W membership 80=List.replicate (BinaryCacheColdParameters.S L q N K W) true
    simpa only [reserve_eq] using h

theorem output_capacity (L q N K W : Nat) (membership : List Bool) : output L q N K W membership capacityPort=List.replicate (BinaryCacheColdParameters.U L q N K W) true := by
  have h : data40 L q N K W membership 82=List.replicate (v22 L q N K W) true := by
    rw [data40_other L q N K W membership 82 (by decide)]
    rw [show data39 L q N K W membership 82=(![List.replicate (v21 L q N K W) true,List.replicate (1) true,List.replicate (v22 L q N K W) true,List.replicate ((v21 L q N K W)+(1)+2) false]) 2 from data39_slot L q N K W membership 2]
    all_goals rfl
  change data40 L q N K W membership 82=List.replicate (BinaryCacheColdParameters.U L q N K W) true
  simpa only [capacity_eq] using h

theorem output_compareK (L q N K W : Nat) (membership : List Bool) : output L q N K W membership compareKPort=CompareMachine.word (K) := by
  have h : data40 L q N K W membership 20=CompareMachine.word (K) := by
    rw [data40_other L q N K W membership 20 (by decide)]
    rw [data39_other L q N K W membership 20 (by decide)]
    rw [data38_other L q N K W membership 20 (by decide)]
    rw [data37_other L q N K W membership 20 (by decide)]
    rw [data36_other L q N K W membership 20 (by decide)]
    rw [data35_other L q N K W membership 20 (by decide)]
    rw [data34_other L q N K W membership 20 (by decide)]
    rw [data33_other L q N K W membership 20 (by decide)]
    rw [data32_other L q N K W membership 20 (by decide)]
    rw [data31_other L q N K W membership 20 (by decide)]
    rw [data30_other L q N K W membership 20 (by decide)]
    rw [data29_other L q N K W membership 20 (by decide)]
    rw [data28_other L q N K W membership 20 (by decide)]
    rw [data27_other L q N K W membership 20 (by decide)]
    rw [data26_other L q N K W membership 20 (by decide)]
    rw [data25_other L q N K W membership 20 (by decide)]
    rw [data24_other L q N K W membership 20 (by decide)]
    rw [data23_other L q N K W membership 20 (by decide)]
    rw [data22_other L q N K W membership 20 (by decide)]
    rw [data21_other L q N K W membership 20 (by decide)]
    rw [data20_other L q N K W membership 20 (by decide)]
    rw [data19_other L q N K W membership 20 (by decide)]
    rw [data18_other L q N K W membership 20 (by decide)]
    rw [data17_other L q N K W membership 20 (by decide)]
    rw [data16_other L q N K W membership 20 (by decide)]
    rw [data15_other L q N K W membership 20 (by decide)]
    rw [data14_other L q N K W membership 20 (by decide)]
    rw [data13_other L q N K W membership 20 (by decide)]
    rw [data12_other L q N K W membership 20 (by decide)]
    rw [data11_other L q N K W membership 20 (by decide)]
    rw [data10_other L q N K W membership 20 (by decide)]
    rw [data9_other L q N K W membership 20 (by decide)]
    rw [show data8 L q N K W membership 20=(![UnaryTemplate.tape (K),CompareMachine.word (K),List.replicate ((K)+2) false]) 1 from data8_slot L q N K W membership 1]
    all_goals rfl
  change data40 L q N K W membership 20=CompareMachine.word (K)
  exact h

theorem retained (L q N K W : Nat) (membership : List Bool) (j : Fin 6) : output L q N K W membership (j.castLE (by decide))=input L q N K W membership (j.castLE (by decide)) := by
  fin_cases j

  · change data40 L q N K W membership 0=input L q N K W membership 0
    rw [data40_other L q N K W membership 0 (by decide)]
    rw [data39_other L q N K W membership 0 (by decide)]
    rw [data38_other L q N K W membership 0 (by decide)]
    rw [data37_other L q N K W membership 0 (by decide)]
    rw [data36_other L q N K W membership 0 (by decide)]
    rw [data35_other L q N K W membership 0 (by decide)]
    rw [data34_other L q N K W membership 0 (by decide)]
    rw [data33_other L q N K W membership 0 (by decide)]
    rw [data32_other L q N K W membership 0 (by decide)]
    rw [data31_other L q N K W membership 0 (by decide)]
    rw [data30_other L q N K W membership 0 (by decide)]
    rw [data29_other L q N K W membership 0 (by decide)]
    rw [data28_other L q N K W membership 0 (by decide)]
    rw [data27_other L q N K W membership 0 (by decide)]
    rw [data26_other L q N K W membership 0 (by decide)]
    rw [data25_other L q N K W membership 0 (by decide)]
    rw [data24_other L q N K W membership 0 (by decide)]
    rw [data23_other L q N K W membership 0 (by decide)]
    rw [data22_other L q N K W membership 0 (by decide)]
    rw [data21_other L q N K W membership 0 (by decide)]
    rw [data20_other L q N K W membership 0 (by decide)]
    rw [data19_other L q N K W membership 0 (by decide)]
    rw [data18_other L q N K W membership 0 (by decide)]
    rw [data17_other L q N K W membership 0 (by decide)]
    rw [data16_other L q N K W membership 0 (by decide)]
    rw [data15_other L q N K W membership 0 (by decide)]
    rw [data14_other L q N K W membership 0 (by decide)]
    rw [data13_other L q N K W membership 0 (by decide)]
    rw [data12_other L q N K W membership 0 (by decide)]
    rw [data11_other L q N K W membership 0 (by decide)]
    rw [data10_other L q N K W membership 0 (by decide)]
    rw [data9_other L q N K W membership 0 (by decide)]
    rw [data8_other L q N K W membership 0 (by decide)]
    rw [data7_other L q N K W membership 0 (by decide)]
    rw [data6_other L q N K W membership 0 (by decide)]
    rw [data5_other L q N K W membership 0 (by decide)]
    rw [data4_other L q N K W membership 0 (by decide)]
    rw [data3_other L q N K W membership 0 (by decide)]
    rw [show data2 L q N K W membership 0=(![List.replicate (L) true,List.replicate (1) true,List.replicate (v1 L q N K W) true,List.replicate ((L)+(1)+2) false]) 0 from data2_slot L q N K W membership 0]
    all_goals rfl

  · change data40 L q N K W membership 1=input L q N K W membership 1
    rw [data40_other L q N K W membership 1 (by decide)]
    rw [data39_other L q N K W membership 1 (by decide)]
    rw [data38_other L q N K W membership 1 (by decide)]
    rw [data37_other L q N K W membership 1 (by decide)]
    rw [data36_other L q N K W membership 1 (by decide)]
    rw [data35_other L q N K W membership 1 (by decide)]
    rw [data34_other L q N K W membership 1 (by decide)]
    rw [data33_other L q N K W membership 1 (by decide)]
    rw [data32_other L q N K W membership 1 (by decide)]
    rw [data31_other L q N K W membership 1 (by decide)]
    rw [data30_other L q N K W membership 1 (by decide)]
    rw [data29_other L q N K W membership 1 (by decide)]
    rw [data28_other L q N K W membership 1 (by decide)]
    rw [data27_other L q N K W membership 1 (by decide)]
    rw [data26_other L q N K W membership 1 (by decide)]
    rw [data25_other L q N K W membership 1 (by decide)]
    rw [data24_other L q N K W membership 1 (by decide)]
    rw [data23_other L q N K W membership 1 (by decide)]
    rw [data22_other L q N K W membership 1 (by decide)]
    rw [data21_other L q N K W membership 1 (by decide)]
    rw [data20_other L q N K W membership 1 (by decide)]
    rw [data19_other L q N K W membership 1 (by decide)]
    rw [data18_other L q N K W membership 1 (by decide)]
    rw [data17_other L q N K W membership 1 (by decide)]
    rw [data16_other L q N K W membership 1 (by decide)]
    rw [data15_other L q N K W membership 1 (by decide)]
    rw [data14_other L q N K W membership 1 (by decide)]
    rw [data13_other L q N K W membership 1 (by decide)]
    rw [data12_other L q N K W membership 1 (by decide)]
    rw [data11_other L q N K W membership 1 (by decide)]
    rw [data10_other L q N K W membership 1 (by decide)]
    rw [show data9 L q N K W membership 1=(![UnaryTemplate.tape (q),List.replicate (v3 L q N K W) true,List.replicate ((q)+2) false]) 0 from data9_slot L q N K W membership 0]
    all_goals rfl

  · change data40 L q N K W membership 2=input L q N K W membership 2
    rw [data40_other L q N K W membership 2 (by decide)]
    rw [data39_other L q N K W membership 2 (by decide)]
    rw [data38_other L q N K W membership 2 (by decide)]
    rw [data37_other L q N K W membership 2 (by decide)]
    rw [data36_other L q N K W membership 2 (by decide)]
    rw [data35_other L q N K W membership 2 (by decide)]
    rw [data34_other L q N K W membership 2 (by decide)]
    rw [data33_other L q N K W membership 2 (by decide)]
    rw [data32_other L q N K W membership 2 (by decide)]
    rw [data31_other L q N K W membership 2 (by decide)]
    rw [data30_other L q N K W membership 2 (by decide)]
    rw [data29_other L q N K W membership 2 (by decide)]
    rw [data28_other L q N K W membership 2 (by decide)]
    rw [data27_other L q N K W membership 2 (by decide)]
    rw [data26_other L q N K W membership 2 (by decide)]
    rw [data25_other L q N K W membership 2 (by decide)]
    rw [show data24 L q N K W membership 2=(![List.replicate (v11 L q N K W) true,UnaryTemplate.tape (N),List.replicate (v12 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (v11 L q N K W) (N)) false]) 1 from data24_slot L q N K W membership 1]
    all_goals rfl

  · change data40 L q N K W membership 3=input L q N K W membership 3
    rw [data40_other L q N K W membership 3 (by decide)]
    rw [data39_other L q N K W membership 3 (by decide)]
    rw [data38_other L q N K W membership 3 (by decide)]
    rw [data37_other L q N K W membership 3 (by decide)]
    rw [data36_other L q N K W membership 3 (by decide)]
    rw [data35_other L q N K W membership 3 (by decide)]
    rw [data34_other L q N K W membership 3 (by decide)]
    rw [data33_other L q N K W membership 3 (by decide)]
    rw [data32_other L q N K W membership 3 (by decide)]
    rw [data31_other L q N K W membership 3 (by decide)]
    rw [data30_other L q N K W membership 3 (by decide)]
    rw [data29_other L q N K W membership 3 (by decide)]
    rw [data28_other L q N K W membership 3 (by decide)]
    rw [data27_other L q N K W membership 3 (by decide)]
    rw [data26_other L q N K W membership 3 (by decide)]
    rw [data25_other L q N K W membership 3 (by decide)]
    rw [data24_other L q N K W membership 3 (by decide)]
    rw [data23_other L q N K W membership 3 (by decide)]
    rw [data22_other L q N K W membership 3 (by decide)]
    rw [data21_other L q N K W membership 3 (by decide)]
    rw [data20_other L q N K W membership 3 (by decide)]
    rw [data19_other L q N K W membership 3 (by decide)]
    rw [data18_other L q N K W membership 3 (by decide)]
    rw [data17_other L q N K W membership 3 (by decide)]
    rw [data16_other L q N K W membership 3 (by decide)]
    rw [data15_other L q N K W membership 3 (by decide)]
    rw [data14_other L q N K W membership 3 (by decide)]
    rw [data13_other L q N K W membership 3 (by decide)]
    rw [data12_other L q N K W membership 3 (by decide)]
    rw [data11_other L q N K W membership 3 (by decide)]
    rw [data10_other L q N K W membership 3 (by decide)]
    rw [data9_other L q N K W membership 3 (by decide)]
    rw [show data8 L q N K W membership 3=(![UnaryTemplate.tape (K),CompareMachine.word (K),List.replicate ((K)+2) false]) 0 from data8_slot L q N K W membership 0]
    all_goals rfl

  · change data40 L q N K W membership 4=input L q N K W membership 4
    rw [data40_other L q N K W membership 4 (by decide)]
    rw [data39_other L q N K W membership 4 (by decide)]
    rw [data38_other L q N K W membership 4 (by decide)]
    rw [data37_other L q N K W membership 4 (by decide)]
    rw [data36_other L q N K W membership 4 (by decide)]
    rw [show data35 L q N K W membership 4=(![List.replicate (W) true,UnaryTemplate.tape (2),List.replicate (v19 L q N K W) true,List.replicate (WilliamsUnaryProduct.scratch (W) (2)) false]) 0 from data35_slot L q N K W membership 0]
    all_goals rfl

  · change data40 L q N K W membership 5=input L q N K W membership 5
    rw [data40_other L q N K W membership 5 (by decide)]
    rw [data39_other L q N K W membership 5 (by decide)]
    rw [data38_other L q N K W membership 5 (by decide)]
    rw [data37_other L q N K W membership 5 (by decide)]
    rw [data36_other L q N K W membership 5 (by decide)]
    rw [data35_other L q N K W membership 5 (by decide)]
    rw [data34_other L q N K W membership 5 (by decide)]
    rw [data33_other L q N K W membership 5 (by decide)]
    rw [data32_other L q N K W membership 5 (by decide)]
    rw [data31_other L q N K W membership 5 (by decide)]
    rw [data30_other L q N K W membership 5 (by decide)]
    rw [data29_other L q N K W membership 5 (by decide)]
    rw [data28_other L q N K W membership 5 (by decide)]
    rw [data27_other L q N K W membership 5 (by decide)]
    rw [data26_other L q N K W membership 5 (by decide)]
    rw [data25_other L q N K W membership 5 (by decide)]
    rw [data24_other L q N K W membership 5 (by decide)]
    rw [data23_other L q N K W membership 5 (by decide)]
    rw [data22_other L q N K W membership 5 (by decide)]
    rw [data21_other L q N K W membership 5 (by decide)]
    rw [data20_other L q N K W membership 5 (by decide)]
    rw [data19_other L q N K W membership 5 (by decide)]
    rw [data18_other L q N K W membership 5 (by decide)]
    rw [data17_other L q N K W membership 5 (by decide)]
    rw [data16_other L q N K W membership 5 (by decide)]
    rw [data15_other L q N K W membership 5 (by decide)]
    rw [data14_other L q N K W membership 5 (by decide)]
    rw [data13_other L q N K W membership 5 (by decide)]
    rw [data12_other L q N K W membership 5 (by decide)]
    rw [data11_other L q N K W membership 5 (by decide)]
    rw [data10_other L q N K W membership 5 (by decide)]
    rw [data9_other L q N K W membership 5 (by decide)]
    rw [data8_other L q N K W membership 5 (by decide)]
    rw [data7_other L q N K W membership 5 (by decide)]
    rw [data6_other L q N K W membership 5 (by decide)]
    rw [data5_other L q N K W membership 5 (by decide)]
    rw [data4_other L q N K W membership 5 (by decide)]
    rw [data3_other L q N K W membership 5 (by decide)]
    rw [data2_other L q N K W membership 5 (by decide)]
    rw [data1_other L q N K W membership 5 (by decide)]

end NearCubicWires.P1Closure.BinaryCacheColdMetadata
