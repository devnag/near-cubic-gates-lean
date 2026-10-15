import Proof.MachineModel.ClockFields
import Proof.MachineModel.ClockJoin
import Proof.MachineModel.ClockLogWidth

/-! Complete short-data clock-field preparation from the actual counted
binary N. Each phase consumes its predecessor's literal tapes; all heads
are reset before the next physical call. -/
namespace NearCubicWires.RepairOrdinary.ClockNumericPrep
open LocalBitMultitape ClockJoin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ellReset : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==1
  rule := fun s _ => if s.val=0 then some ⟨1,fun _ => none,
    fun i => if i.val=1 then .left else .stay⟩ else none

def ellMachine : Machine 2 8 := Composition.machine RepairSource.VerifierDecoding.LengthMachine.machine ellReset

theorem ell_ready (N : ℕ) :
    ReadyRun ellMachine (4*PCPResourceLedger.ell N+5)
      ![frame (ClockBinary.word N),[]]
      ![frame (ClockBinary.word N),false::List.replicate (PCPResourceLedger.ell N) true] := by
  obtain ⟨base,hb,hf,hs,_⟩ := RepairSource.VerifierDecoding.LengthMachine.length_run (ClockBinary.word N)
  rw [ClockDyadicLedger.bit_width] at hb hf hs
  let tapes : Fin 2 → List Bool := ![frame (ClockBinary.word N),false::List.replicate (PCPResourceLedger.ell N) true]
  let c : Configuration 2 2 := ⟨0,![0,1],tapes⟩
  let final : Configuration 2 2 := ⟨1,fun _ => 0,tapes⟩
  have hstep : step ellReset c=some final := by
    simp [step,ellReset,c]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  let last : ExecutionReceipt 2 2 := ⟨final,1,max c.tapeCells final.tapeCells⟩
  have hl : runFrom ellReset 1 c=some last :=
    runFrom_step ellReset c final ⟨final,0,final.tapeCells⟩ (by rfl) hstep
      (runFrom_zero_of_halted ellReset final (by rfl))
  have hi : Composition.restart base.final ellReset.start=c := by rw [hf]; rfl
  have hl' : runFrom ellReset 1 (Composition.restart base.final ellReset.start)=some last := by rw [hi]; exact hl
  have hr := Composition.run_join RepairSource.VerifierDecoding.LengthMachine.machine ellReset
    (4*PCPResourceLedger.ell N+3) 1 _ base last hb hl'
  refine ⟨Composition.joinedReceipt base last,?_,rfl,fun _ => rfl,?_⟩
  · have htime : (4*PCPResourceLedger.ell N+3)+1+1=4*PCPResourceLedger.ell N+5 := by omega
    rw [htime] at hr
    exact hr
  · dsimp only [Composition.joinedReceipt,last]
    omega

def degreeCost (N : ℕ) := 4*PCPResourceLedger.ell N+10
def ellCost (N : ℕ) := 4*PCPResourceLedger.ell N+5
def productCost (N : ℕ) := 2*(PowerSlice.degree N*(2*PCPResourceLedger.ell N+3)+2)+2
def fieldCost (N : ℕ) := 4*ClockDyadicLedger.exponent N+22

def input (N : ℕ) : Fin 11 → List Bool := ![frame (ClockBinary.word N),[],[],[],[],[],[],[],[],[],[]]
def afterDegree (N g : ℕ) : Fin 11 → List Bool :=
  ![frame (ClockBinary.word N),List.replicate (PowerSlice.degree N) true,List.replicate g false,
    [],[],[],[],[],[],[],[]]
def afterEll (N g : ℕ) : Fin 11 → List Bool :=
  ![frame (ClockBinary.word N),List.replicate (PowerSlice.degree N) true,List.replicate g false,
    false::List.replicate (PCPResourceLedger.ell N) true,[],[],[],[],[],[],[]]
def afterProduct (N g : ℕ) : Fin 11 → List Bool :=
  ![frame (ClockBinary.word N),List.replicate (PowerSlice.degree N) true,List.replicate g false,
    false::List.replicate (PCPResourceLedger.ell N) true,List.replicate (ClockDyadicLedger.exponent N) true,
    List.replicate (PowerSlice.degree N*(2*PCPResourceLedger.ell N+3)+2) false,[],[],[],[],[]]
def output (N g : ℕ) : Fin 11 → List Bool :=
  ![frame (ClockBinary.word N),List.replicate (PowerSlice.degree N) true,List.replicate g false,
    false::List.replicate (PCPResourceLedger.ell N) true,List.replicate (ClockDyadicLedger.exponent N) true,
    List.replicate (PowerSlice.degree N*(2*PCPResourceLedger.ell N+3)+2) false,
    frame (List.replicate (ClockDyadicLedger.exponent N) false++[true]),
    List.replicate (ClockDyadicLedger.width N) true,
    List.replicate (2*ClockDyadicLedger.width N) true,
    List.replicate (2*ClockDyadicLedger.width N+2) true,
    List.replicate (2*ClockDyadicLedger.exponent N+10) false]

def ellLayout : Fin 11 ≃ Fin 11 where
  toFun := ![0,3,2,1,4,5,6,7,8,9,10]
  invFun := ![0,3,2,1,4,5,6,7,8,9,10]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def productLayout : Fin 11 ≃ Fin 11 where
  toFun := ![1,3,4,5,0,2,6,7,8,9,10]
  invFun := ![4,0,5,1,2,3,6,7,8,9,10]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def fieldLayout : Fin 11 ≃ Fin 11 where
  toFun := ![4,6,7,8,9,10,0,1,2,3,5]
  invFun := ![6,7,8,9,0,10,1,2,3,4,5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def degreePhase : Machine 11 7 := ClockJoin.lifted (e:=8) (Equiv.refl (Fin 11)) ClockDegree.machine
def ellPhase : Machine 11 8 := ClockJoin.lifted (e:=9) ellLayout ellMachine
def productPhase : Machine 11 7 := ClockJoin.lifted (e:=7) productLayout ClockUnaryProduct.machine
def fieldPhase : Machine 11 14 := ClockJoin.lifted (e:=5) fieldLayout ClockFields.machine

theorem degree_phase (N : ℕ) (hn : 0<N) :
    ∃ g, g≤2*PCPResourceLedger.ell N+4 ∧ ReadyRun degreePhase (degreeCost N) (input N) (afterDegree N g) := by
  obtain ⟨g,hg,r,hr,h0,h1,h2,hh,hs⟩ := ClockDegree.degree_run N hn
  rw [ClockDyadicLedger.bit_width] at hg hr hs
  have h : ReadyRun ClockDegree.machine (degreeCost N) ![frame (ClockBinary.word N),[],[]]
      ![frame (ClockBinary.word N),List.replicate (PowerSlice.degree N) true,List.replicate g false] := by
    refine ⟨r,hr,?_,hh,hs⟩
    funext i; fin_cases i <;> simp [h0,h1,h2]
  have hl := ClockJoin.lift (e:=8) (Equiv.refl (Fin 11)) ClockDegree.machine (degreeCost N) _ _ (fun _ => []) h
  have hi : data (e:=8) (Equiv.refl (Fin 11)) ![frame (ClockBinary.word N),[],[]] (fun _ => [])=input N := by
    funext i; fin_cases i <;> rfl
  have ho : data (e:=8) (Equiv.refl (Fin 11))
      ![frame (ClockBinary.word N),List.replicate (PowerSlice.degree N) true,List.replicate g false]
      (fun _ => [])=afterDegree N g := by funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact ⟨g,hg,hl⟩

theorem ell_phase (N g : ℕ) : ReadyRun ellPhase (ellCost N) (afterDegree N g) (afterEll N g) := by
  let extra : Fin 9 → List Bool := ![List.replicate g false,List.replicate (PowerSlice.degree N) true,[],[],[],[],[],[],[]]
  have hl := ClockJoin.lift ellLayout ellMachine (ellCost N) _ _ extra (ell_ready N)
  have hi : data ellLayout ![frame (ClockBinary.word N),[]] extra=afterDegree N g := by
    funext i; fin_cases i <;> rfl
  have ho : data ellLayout ![frame (ClockBinary.word N),false::List.replicate (PCPResourceLedger.ell N) true] extra=afterEll N g := by
    funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact hl

theorem product_phase (N g : ℕ) : ReadyRun productPhase (productCost N) (afterEll N g) (afterProduct N g) := by
  let D := PowerSlice.degree N
  let ell := PCPResourceLedger.ell N
  obtain ⟨r,hr,h0,h1,h2,h3,hh,hs⟩ := ClockUnaryProduct.product_run D ell
  have hi0 : (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![List.replicate D true,false::List.replicate ell true,[]] (fun _ : Fin 1 => []))=
      ![List.replicate D true,false::List.replicate ell true,[],[]] := by funext i; fin_cases i <;> rfl
  rw [hi0] at hr
  have h : ReadyRun ClockUnaryProduct.machine (productCost N)
      ![List.replicate D true,false::List.replicate ell true,[],[]]
      ![List.replicate D true,false::List.replicate ell true,List.replicate (D*ell) true,
        List.replicate (D*(2*ell+3)+2) false] := by
    refine ⟨r,hr,?_,hh,hs.le⟩
    funext i; fin_cases i <;> simp [h0,h1,h2,h3]
  let extra : Fin 7 → List Bool := ![frame (ClockBinary.word N),List.replicate g false,[],[],[],[],[]]
  have hl := ClockJoin.lift productLayout ClockUnaryProduct.machine (productCost N) _ _ extra h
  have hi : data productLayout ![List.replicate D true,false::List.replicate ell true,[],[]] extra=afterEll N g := by
    funext i; fin_cases i <;> rfl
  have ho : data productLayout
      ![List.replicate D true,false::List.replicate ell true,List.replicate (D*ell) true,
        List.replicate (D*(2*ell+3)+2) false] extra=afterProduct N g := by
    funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact hl

theorem field_phase (N g : ℕ) : ReadyRun fieldPhase (fieldCost N) (afterProduct N g) (output N g) := by
  let exponent := ClockDyadicLedger.exponent N
  obtain ⟨r,hr,h0,h1,h2,h3,h4,h5,hh,hs⟩ := ClockFields.fields_run exponent
  have hi0 : (Fin.addCases (motive := fun _ : Fin (5+1) => List Bool)
      ![List.replicate exponent true,[],[],[],[]] (fun _ : Fin 1 => []))=
      ![List.replicate exponent true,[],[],[],[],[]] := by funext i; fin_cases i <;> rfl
  rw [hi0] at hr
  have h : ReadyRun ClockFields.machine (fieldCost N)
      ![List.replicate exponent true,[],[],[],[],[]]
      ![List.replicate exponent true,frame (List.replicate exponent false++[true]),
        List.replicate (exponent+3) true,List.replicate (2*(exponent+3)) true,
        List.replicate (2*(exponent+3)+2) true,List.replicate (2*exponent+10) false] := by
    refine ⟨r,hr,?_,hh,hs.le⟩
    funext i; fin_cases i <;> simp [h0,h1,h2,h3,h4,h5]
  let extra : Fin 5 → List Bool := ![frame (ClockBinary.word N),List.replicate (PowerSlice.degree N) true,
    List.replicate g false,false::List.replicate (PCPResourceLedger.ell N) true,
    List.replicate (PowerSlice.degree N*(2*PCPResourceLedger.ell N+3)+2) false]
  have hl := ClockJoin.lift fieldLayout ClockFields.machine (fieldCost N) _ _ extra h
  have hi : data fieldLayout ![List.replicate exponent true,[],[],[],[],[]] extra=afterProduct N g := by
    funext i; fin_cases i <;> rfl
  have ho : data fieldLayout
      ![List.replicate exponent true,frame (List.replicate exponent false++[true]),
        List.replicate (exponent+3) true,List.replicate (2*(exponent+3)) true,
        List.replicate (2*(exponent+3)+2) true,List.replicate (2*exponent+10) false]
      extra=output N g := by funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact hl

def first : Machine 11 15 := Composition.machine degreePhase ellPhase
def second : Machine 11 22 := Composition.machine first productPhase
def machine : Machine 11 36 := Composition.machine second fieldPhase

def budget (N : ℕ) := ((degreeCost N+1+ellCost N)+1+productCost N)+1+fieldCost N

theorem prepare_run (N : ℕ) (hn : 0<N) :
    ∃ g, g≤2*PCPResourceLedger.ell N+4 ∧ ReadyRun machine (budget N) (input N) (output N g) := by
  obtain ⟨g,hg,hdegree⟩ := degree_phase N hn
  have hell := ell_phase N g
  have hproduct := product_phase N g
  have hfields := field_phase N g
  have hfirst := ClockJoin.join degreePhase ellPhase _ _ _ _ _ hdegree hell
  have hsecond := ClockJoin.join first productPhase _ _ _ _ _ hfirst hproduct
  have hwhole := ClockJoin.join second fieldPhase _ _ _ _ _ hsecond hfields
  exact ⟨g,hg,hwhole⟩

theorem budget_bound (N : ℕ) : budget N≤60*PCPResourceLedger.q N^2 := by
  have hN : N≤2^PCPResourceLedger.ell N :=
    (Nat.le_succ N).trans (Nat.le_pow_clog (by decide) (N+1))
  have hD : PowerSlice.degree N≤PCPResourceLedger.ell N+2 := by
    have := Nat.factorization_le_of_le_pow hN
    dsimp only [PowerSlice.degree]
    omega
  have hmul := Nat.mul_le_mul_right (PCPResourceLedger.ell N) hD
  dsimp only [budget,degreeCost,ellCost,productCost,fieldCost,ClockDyadicLedger.exponent,PCPResourceLedger.q]
  nlinarith

end NearCubicWires.RepairOrdinary.ClockNumericPrep
