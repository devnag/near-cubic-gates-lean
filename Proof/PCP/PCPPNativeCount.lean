import Proof.PCP.PCPPNativeCapacityReady

/-! Native header counts from the actual Q, oracle size and compact-clause
count. Retained intermediate counters are the original Q-loop endpoint and
the M-loop's three-node contribution; neither loop output is substituted. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCount
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stride (s : ℕ) := 2*s+1
def queryEnd (Q s : ℕ) := Q*stride s
def outputIndex (Q s M : ℕ) := queryEnd Q s+M*3
def nativeSize (Q s M : ℕ) := outputIndex Q s M+1
def strideSlots : Fin 4 → Fin 18 := ![3,1,4,5]
def templateSlots : Fin 3 → Fin 18 := ![4,6,7]
def querySlots : Fin 4 → Fin 18 := ![0,6,8,9]
def fixedSlots : Fin 2 → Fin 18 := ![10,11]
def clauseSlots : Fin 4 → Fin 18 := ![2,10,12,13]
def sumSlots : Fin 4 → Fin 18 := ![8,12,14,15]
def sizeSlots : Fin 4 → Fin 18 := ![14,3,16,17]
def data (Q s M phase : ℕ) : Fin 18 → List Bool :=
  ![List.replicate Q true,List.replicate s true,List.replicate M true,[],
    if 1≤phase then List.replicate (stride s) true else [],
    if 1≤phase then List.replicate (2*s+2) false else [],
    if 2≤phase then UnaryTemplate.tape (stride s) else [],
    if 2≤phase then List.replicate (stride s+3) false else [],
    if 3≤phase then List.replicate (queryEnd Q s) true else [],
    if 3≤phase then List.replicate (WilliamsUnaryProduct.scratch Q (stride s)) false else [],
    if 4≤phase then UnaryTemplate.tape 3 else [],
    if 4≤phase then List.replicate 5 false else [],
    if 5≤phase then List.replicate (M*3) true else [],
    if 5≤phase then List.replicate (WilliamsUnaryProduct.scratch M 3) false else [],
    if 6≤phase then List.replicate (outputIndex Q s M) true else [],
    if 6≤phase then List.replicate (outputIndex Q s M+2) false else [],
    if 7≤phase then List.replicate (nativeSize Q s M) true else [],
    if 7≤phase then List.replicate (outputIndex Q s M+2) false else []]
noncomputable def first := RecoveryFocus.machine strideSlots PCPPNativeAddress.machine
noncomputable def second := RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
noncomputable def third := RecoveryFocus.machine querySlots ClockUnaryProduct.machine
noncomputable def fourth := RecoveryFocus.machine fixedSlots (HierarchyFixedWord.machine (UnaryTemplate.tape 3))
noncomputable def fifth := RecoveryFocus.machine clauseSlots ClockUnaryProduct.machine
noncomputable def sixth := RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def seventh := RecoveryFocus.machine sizeSlots PCPPNativeAddress.machine
noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine first second) third) fourth) fifth) sixth) seventh
def budget (Q s M : ℕ) :=
  (4*s+6)+1+(2*stride s+8)+1+WilliamsUnaryProduct.budget Q (stride s)+1+12+1+
    WilliamsUnaryProduct.budget M 3+1+(2*outputIndex Q s M+6)+1+(2*outputIndex Q s M+6)

private theorem bounded {t s b : ℕ} {p : Machine t s} {a z : Fin t → List Bool}
    (h : RecoveryRootRound.ReadyRun p b a z) : ClockJoin.ReadyRun p b a z := by
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  exact ⟨r,hr,ht,hh,hs.le⟩

private theorem stage {t s b : ℕ} (p : Machine t s) (slots : Fin t → Fin 18)
    (hi : Function.Injective slots) (Q n M k : ℕ) (a z : Fin t → List Bool)
    (h : ClockJoin.ReadyRun p b a z)
    (hin : ∀ j,data Q n M k (slots j)=a j)
    (hout : ∀ j,data Q n M (k+1) (slots j)=z j)
    (hkeep : ∀ i,(∀ j,slots j≠i) → data Q n M (k+1) i=data Q n M k i) :
    ClockJoin.ReadyRun (RecoveryFocus.machine slots p) b (data Q n M k) (data Q n M (k+1)) := by
  have hf := h.focus slots hi (data Q n M k) hin
  rw [HierarchyWidth.install_eq slots hi _ _ _ hout hkeep] at hf
  exact hf

theorem first_run (Q s M : ℕ) :
    ClockJoin.ReadyRun first (2*0+4*s+6) (data Q s M 0) (data Q s M 1) := by
  exact stage PCPPNativeAddress.machine strideSlots (by decide) Q s M 0 _ _
    (PCPPNativeAddress.address_ready 0 s)
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [data,strideSlots,stride,PCPPSubstitution.address])
    (by intro i hi; have h4 := hi 2; have h5 := hi 3; fin_cases i <;> simp_all [data,strideSlots])

theorem second_run (Q s M : ℕ) :
    ClockJoin.ReadyRun second (2*stride s+8) (data Q s M 1) (data Q s M 2) := by
  exact stage (DimensionTemplate.machine false) templateSlots (by decide) Q s M 1 _ _
    (DimensionTemplate.ready false (stride s))
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; have h6 := hi 1; have h7 := hi 2; fin_cases i <;> simp_all [data,templateSlots])

theorem third_run (Q s M : ℕ) :
    ClockJoin.ReadyRun third (WilliamsUnaryProduct.budget Q (stride s)) (data Q s M 2) (data Q s M 3) := by
  exact stage ClockUnaryProduct.machine querySlots (by decide) Q s M 2 _ _
    (bounded (WilliamsUnaryProduct.product_ready Q (stride s)))
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; have h8 := hi 2; have h9 := hi 3; fin_cases i <;> simp_all [data,querySlots])

theorem fourth_run (Q s M : ℕ) :
    ClockJoin.ReadyRun fourth (2*(UnaryTemplate.tape 3).length+2) (data Q s M 3) (data Q s M 4) := by
  exact stage (HierarchyFixedWord.machine (UnaryTemplate.tape 3)) fixedSlots (by decide) Q s M 3 _ _
    (bounded (HierarchyFixedWord.word_ready (UnaryTemplate.tape 3)))
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; have h10 := hi 0; have h11 := hi 1; fin_cases i <;> simp_all [data,fixedSlots])

theorem fifth_run (Q s M : ℕ) :
    ClockJoin.ReadyRun fifth (WilliamsUnaryProduct.budget M 3) (data Q s M 4) (data Q s M 5) := by
  exact stage ClockUnaryProduct.machine clauseSlots (by decide) Q s M 4 _ _
    (bounded (WilliamsUnaryProduct.product_ready M 3))
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; have h12 := hi 2; have h13 := hi 3; fin_cases i <;> simp_all [data,clauseSlots])

theorem sixth_run (Q s M : ℕ) :
    ClockJoin.ReadyRun sixth (2*outputIndex Q s M+6) (data Q s M 5) (data Q s M 6) := by
  exact stage ClockUnarySum.machine sumSlots (by decide) Q s M 5 _ _
    (ClockUnarySum.sum_ready (queryEnd Q s) (M*3))
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; have h14 := hi 2; have h15 := hi 3; fin_cases i <;> simp_all [data,sumSlots])

theorem seventh_run (Q s M : ℕ) :
    ClockJoin.ReadyRun seventh (2*outputIndex Q s M+4*0+6) (data Q s M 6) (data Q s M 7) := by
  exact stage PCPPNativeAddress.machine sizeSlots (by decide) Q s M 6 _ _
    (PCPPNativeAddress.address_ready (outputIndex Q s M) 0)
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [data,sizeSlots,PCPPSubstitution.address,nativeSize])
    (by intro i hi; have h16 := hi 2; have h17 := hi 3; fin_cases i <;> simp_all [data,sizeSlots])

theorem count_run (Q s M : ℕ) :
    ClockJoin.ReadyRun machine (budget Q s M) (data Q s M 0) (data Q s M 7) := by
  have joined := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _
      (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _
        (ClockJoin.join _ _ _ _ _ _ _ (first_run Q s M) (second_run Q s M)) (third_run Q s M)) (fourth_run Q s M)) (fifth_run Q s M)) (sixth_run Q s M)) (seventh_run Q s M)
  have he : (2*0+4*s+6)+1+(2*stride s+8)+1+WilliamsUnaryProduct.budget Q (stride s)+1+
      (2*(UnaryTemplate.tape 3).length+2)+1+WilliamsUnaryProduct.budget M 3+1+
      (2*outputIndex Q s M+6)+1+(2*outputIndex Q s M+4*0+6)=budget Q s M := by
    norm_num [budget,UnaryTemplate.tape]
  rw [he] at joined
  exact joined

theorem fields (Q s M : ℕ) :
    data Q s M 7 0=List.replicate Q true ∧ data Q s M 7 1=List.replicate s true ∧
    data Q s M 7 2=List.replicate M true ∧ data Q s M 7 4=List.replicate (stride s) true ∧
    data Q s M 7 6=UnaryTemplate.tape (stride s) ∧
    data Q s M 7 8=List.replicate (queryEnd Q s) true ∧
    data Q s M 7 14=List.replicate (outputIndex Q s M) true ∧
    data Q s M 7 16=List.replicate (nativeSize Q s M) true := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end NearCubicWires.RepairOrdinary.PCPPNativeCount
