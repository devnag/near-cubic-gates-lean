import Proof.MachineModel.OrdinaryMatrixBucketSizeBranches

/-! Whole cold bucket-size controller. The physical budget test selects
the appropriate executed branch; the final increment produces B. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketSize
open LocalBitMultitape RecoveryRootRound RecoveryExecution CompetitorRationalProducts
open MatrixBucketSizeBranches (value)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 3 → ℕ := ![31,12,8]
noncomputable def programs : (j : Fin 3) → Machine 28 (sizes j)
  | ⟨0,_⟩ => MatrixBucketSizePrepare.machine
  | ⟨1,_⟩ => MatrixBucketSizeBranches.positive
  | ⟨2,_⟩ => MatrixBucketSizeBranches.small
  | ⟨n+3,h⟩ => False.elim (by omega)
def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 28 → Bool) : Option (Fin 3) :=
  if j=0 then if bits 15 then some 1 else some 2 else none
noncomputable def decision := RecoveryCalls.machine sizes programs 0 next
def incrementSlots : Fin 1 → Fin 28 := fun _ => 20
noncomputable def increment := RecoveryFocus.machine incrementSlots MatrixBucketDimensions.Increment.machine
noncomputable def machine := Composition.machine decision increment
def decisionBudget (U q : ℕ) := MatrixBucketSizePrepare.budget U q+24*U+17
def budget (U q : ℕ) := decisionBudget U q+1+(2*value U q+5)

structure Fields (U q : ℕ) (out : Fin 28 → List Bool) : Prop where
  u : out 0=UnaryTemplate.tape U
  numerator : out 7=List.replicate (2*U) true
  twice : out 8=UnaryTemplate.tape (2*U)
  budget : out 11=List.replicate q true
  divisor : out 12=UnaryTemplate.tape (q-1)
  budgetTemplate : out 13=UnaryTemplate.tape q
  rawSize1 : out 18=List.replicate (value U q) true
  rawSize2 : out 19=List.replicate (value U q) true
  size : out 20=UnaryTemplate.tape (value U q)
  fresh : ∀ i : Fin 28,22 ≤ i.val → out i=[]

theorem decision_run (U q : ℕ) (hq : 0<q) :
    ∃ out,ClockJoin.ReadyRun decision (decisionBudget U q) (MatrixBucketSizePrepare.input U q) out ∧
      Fields U q out := by
  obtain ⟨prepared,prep,p0,p6,p7,p8,p11,p12,p13,p15,pfresh⟩ := MatrixBucketSizePrepare.prepare_run U q hq
  obtain ⟨first,hfirst,ft,fh,_⟩ := prep
  have flag : first.final.scanned 15=decide (1<q) := by
    simp only [Configuration.scanned,fh,ft,p15]
    rfl
  have close (j : Fin 3) (fuel : ℕ) (out : Fin 28 → List Bool)
      (hj : j≠0) (branch : next 0 first.final.control first.final.scanned=some j)
      (body : ClockJoin.ReadyRun (programs j) fuel prepared out) (bound : fuel≤24*U+15) :
      ClockJoin.ReadyRun decision (decisionBudget U q) (MatrixBucketSizePrepare.input U q) out := by
    obtain ⟨t0,h0,path0⟩ := call_receipt sizes programs 0 next 0 j (MatrixBucketSizePrepare.budget U q)
      (initialConfiguration (programs 0) (MatrixBucketSizePrepare.input U q)) first hfirst branch
    have hh : first.final.heads=(fun _ => 0) := funext fh
    rw [hh,ft] at path0
    obtain ⟨last,hl,lt,lh,_⟩ := body
    obtain ⟨t1,h1,path1⟩ := stop_receipt sizes programs 0 next j fuel
      (initialConfiguration (programs j) prepared) last hl (by simp [next,hj])
    have path := path0.trans path1
    obtain ⟨actual,ha,hf,hs⟩ := path.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have ht : t0+t1≤decisionBudget U q := by unfold decisionBudget; omega
    have he := run_moreFuel decision _ (decisionBudget U q-(t0+t1)) (MatrixBucketSizePrepare.input U q) actual ha
    rw [Nat.add_sub_of_le ht] at he
    exact ⟨actual,he,by rw [hf]; exact lt,by intro i; rw [hf]; exact lh i,hs.trans_le ht⟩
  by_cases hlarge : 1<q
  · obtain ⟨out,body,old,o18,o19,o20,fresh⟩ := MatrixBucketSizeBranches.positive_run U q hlarge prepared p6 p12 pfresh
    have bound : MatrixBucketSizeBranches.positiveBudget U q≤24*U+15 := by
      have hdiv := Nat.div_le_self (2*U) (q-1)
      unfold MatrixBucketSizeBranches.positiveBudget
      omega
    have ready := close 1 _ out (by decide) (by simp [next]; exact flag.trans (by simp [hlarge])) body bound
    exact ⟨out,ready,⟨(old 0).trans p0,(old 7).trans p7,(old 8).trans p8,(old 11).trans p11,
      (old 12).trans p12,(old 13).trans p13,o18,o19,o20,fresh⟩⟩
  · obtain ⟨out,body,old,o18,o19,o20,fresh⟩ := MatrixBucketSizeBranches.small_run U q (by omega) prepared p8 pfresh
    have ready := close 2 _ out (by decide) (by simp [next]; exact flag.trans (by simp [hlarge])) body (by omega)
    exact ⟨out,ready,⟨(old 0).trans p0,(old 7).trans p7,(old 8).trans p8,(old 11).trans p11,
      (old 12).trans p12,(old 13).trans p13,o18,o19,o20,fresh⟩⟩

theorem size_run (U q : ℕ) (hq : 0<q) : ∃ out,ClockJoin.ReadyRun machine (budget U q)
    (MatrixBucketSizePrepare.input U q) out ∧
    out 0=UnaryTemplate.tape U ∧ out 7=List.replicate (2*U) true ∧ out 8=UnaryTemplate.tape (2*U) ∧
    out 11=List.replicate q true ∧ out 12=UnaryTemplate.tape (q-1) ∧ out 13=UnaryTemplate.tape q ∧
    out 18=List.replicate (value U q) true ∧ out 19=List.replicate (value U q) true ∧
    out 20=UnaryTemplate.tape (value U q+1) ∧ (∀ i : Fin 28,22 ≤ i.val → out i=[]) := by
  obtain ⟨prepared,hd,fields⟩ := decision_run U q hq
  obtain ⟨base,hb,bt,bh,bs⟩ := MatrixBucketDimensions.Increment.increment_run (value U q)
  have ready : ClockJoin.ReadyRun MatrixBucketDimensions.Increment.machine (2*value U q+5)
      (fun _ => UnaryTemplate.tape (value U q)) (fun _ => UnaryTemplate.tape (value U q+1)) :=
    ⟨base,hb,bt,bh,bs.le⟩
  let out := install incrementSlots prepared (fun _ => UnaryTemplate.tape (value U q+1))
  have hi := bounded_focus incrementSlots (by decide) _ _ _ ready prepared (by intro i; exact fields.size)
  have whole := ClockJoin.join decision increment _ _ _ _ _ hd hi
  have old (i : Fin 28) (hi : i≠20) : out i=prepared i := by
    apply install_other
    intro j; exact Ne.symm hi
  refine ⟨out,whole,(old 0 (by decide)).trans fields.u,(old 7 (by decide)).trans fields.numerator,
    (old 8 (by decide)).trans fields.twice,(old 11 (by decide)).trans fields.budget,
    (old 12 (by decide)).trans fields.divisor,(old 13 (by decide)).trans fields.budgetTemplate,
    (old 18 (by decide)).trans fields.rawSize1,(old 19 (by decide)).trans fields.rawSize2,
    install_slot incrementSlots (by decide) _ _ 0,?_⟩
  intro i hi
  exact (old i (by intro h; subst i; omega)).trans (fields.fresh i hi)

end NearCubicWires.RepairOrdinary.MatrixBucketSize
