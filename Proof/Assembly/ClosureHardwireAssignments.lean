import Proof.Assembly.ClosureHardwireAssignmentsRaw
import Proof.Assembly.ClosureAssignmentRestore
import Proof.Assembly.ClosureBinarySerialization
import Proof.Assembly.ClosureOriginalCacheBounds

/-! The complete reusable assignment callback and the actual outer binary
loop. The supplied original child cache is scanned physically on every
assignment; all callback state is restored and the emitted order is exact.
Cold preparation of the displayed baseline and outer driver is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.HardwireAssignments
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RepairRepresentation RepairSource CloseoutFinal SupplierPipeline SupplierEstimator
open VerifierDecoding CanonicalRecoveryLanguage SignedSortKey
open scoped BigOperators

variable {q : Nat} (live : Finset (Fin q)) (gs : List (ExactThresholdGate q)) (B w cap : Nat)

def reserve := HardwireAssignmentsRaw.budget live gs B w+HardwireBudget.R B q w+
  gs.length+q+live.card+cap+100
noncomputable def baseline := HardwireAssignmentsRaw.baseline live gs B w cap
noncomputable def input (j : Nat) (out : List Bool) := AssignmentRestore.input
  (baseline live gs B w cap (RepairOrdinary.frame (binary live.card j))) out (reserve live gs B w cap)
noncomputable def callback := AssignmentRestore.machine HardwireAssignmentsRaw.machine
def callbackBudget := 2*HardwireAssignmentsRaw.budget live gs B w+4*reserve live gs B w cap+12

theorem baseline_tail (framed out : List Bool) (i : Fin 14) :
    baseline live gs B w cap framed out (i.natAdd 98)=
      (![exactListWord gs,[],UnaryTemplate.tape q,List.replicate B true,List.replicate (B+1) false,
        CompareMachine.word gs.length,framed,List.replicate cap false,List.replicate live.card false,
        List.replicate live.card false,CompareMachine.word q,List.replicate (4*q+3) false,[],[]] : Fin 14→List Bool) i := by
  refine Fin.addCases (m:=6) (n:=8) (fun i=>?_) (fun i=>?_) i
  · refine Fin.addCases (m:=5) (n:=1) (fun i=>?_) (fun i=>?_) i
    · change baseline live gs B w cap framed out (((i.natAdd 98).castAdd 1).castAdd 8)=_
      simp only [baseline,HardwireAssignmentsRaw.baseline,RepeatMachine.cfg,controlConfig,
        TapeEmbedding.config,HardwireCacheLoop.entry,HardwireCacheLoop.state,HardwireCacheBody.state,
        Fin.addCases_left,Fin.addCases_right]
      fin_cases i <;> rfl
    · fin_cases i
      change baseline live gs B w cap framed out (((0 : Fin 1).natAdd 103).castAdd 8)=_
      simp only [baseline,HardwireAssignmentsRaw.baseline,RepeatMachine.cfg,controlConfig,
        TapeEmbedding.config,Fin.addCases_left,Fin.addCases_right]
      rfl
  · have he : (i.natAdd 6).natAdd 98=i.natAdd 104 := Fin.ext (by simp only [Fin.val_natAdd];omega)
    rw [he]
    change baseline live gs B w cap framed out (i.natAdd 104)=_
    simp only [baseline,HardwireAssignmentsRaw.baseline,Fin.addCases_right]
    fin_cases i <;> rfl

theorem padded_other (out next : List Bool) (i : Fin 48) (hi : i≠34) :
    HardwireCacheBody.padded live (fun _=>false) [] w (HardwireBudget.C w) (HardwireBudget.D q w)
      (HardwireBudget.E B q) [] out (HardwireBudget.R B q w) i=
    HardwireCacheBody.padded live (fun _=>false) [] w (HardwireBudget.C w) (HardwireBudget.D q w)
      (HardwireBudget.E B q) [] next (HardwireBudget.R B q w) i := by
  have surj : ∀ i : Fin 48,i≠34 → ∃ j,HardwireReusable.work j=i := by decide
  obtain ⟨j,hj⟩ := surj i hi
  rw [←hj,HardwireCacheBody.padded_work,HardwireCacheBody.padded_work]

theorem baseline_out_change (framed out next : List Bool) (i : Fin 112) (h34 : i≠34) :
    baseline live gs B w cap framed out i=baseline live gs B w cap framed next i := by
  revert h34
  refine Fin.addCases (m:=98) (n:=14) (fun i=>?_) (fun i=>?_) i
  · intro h34
    change HardwireAssignmentsRaw.baseline live gs B w cap framed out (HardwireAssignmentsRaw.old i)=
      HardwireAssignmentsRaw.baseline live gs B w cap framed next (HardwireAssignmentsRaw.old i)
    rw [HardwireAssignmentsRaw.baseline_old,HardwireAssignmentsRaw.baseline_old]
    revert h34
    refine Fin.addCases (m:=48) (n:=50) (fun i=>?_) (fun i=>?_) i
    · intro h34
      simp only [HardwireCacheBody.localState,HardwireReusable.state,Fin.addCases_left]
      exact padded_other live B w out next i (by intro h;subst i;exact h34 rfl)
    · intro _
      simp only [HardwireCacheBody.localState,HardwireReusable.state,Fin.addCases_right]
  · intro _
    rw [baseline_tail,baseline_tail]

theorem baseline_frame_change (framed other out : List Bool) (i : Fin 112) (h104 : i≠104) :
    baseline live gs B w cap framed out i=baseline live gs B w cap other out i := by
  revert h104
  refine Fin.addCases (m:=104) (n:=8) (fun i=>?_) (fun i=>?_) i
  · intro _
    simp only [baseline,HardwireAssignmentsRaw.baseline,Fin.addCases_left]
  · intro h104
    simp only [baseline,HardwireAssignmentsRaw.baseline,Fin.addCases_right]
    revert h104
    refine Fin.cases ?_ (fun i=>?_) i
    · intro h104;exact False.elim (h104 rfl)
    · intro _;rfl

theorem baseline_other (framed other out next : List Bool) (i : Fin 112) (h34 : i≠34) (h104 : i≠104) :
    baseline live gs B w cap framed out i=baseline live gs B w cap other next i :=
  (baseline_out_change live gs B w cap framed out next i h34).trans
    (baseline_frame_change live gs B w cap framed other next i h104)

theorem baseline_out (framed out : List Bool) : baseline live gs B w cap framed out 34=out :=
  ZeroPadding.pad_zero _

theorem baseline_output_only (framed out : List Bool) (i : Fin 112) (hi : i≠34) :
    baseline live gs B w cap framed out i=baseline live gs B w cap framed [] i :=
  baseline_out_change live gs B w cap framed out [] i hi

theorem reserve_bounds : HardwireAssignmentsRaw.budget live gs B w+1≤reserve live gs B w cap ∧
    HardwireBudget.R B q w+1≤reserve live gs B w cap ∧ gs.length+1≤reserve live gs B w cap ∧
    B+1≤reserve live gs B w cap ∧ live.card≤reserve live gs B w cap ∧ 4*q+3≤reserve live gs B w cap := by
  have square := Nat.le_self_pow (by decide : 2≠0) (B+q+w+1)
  unfold reserve HardwireAssignmentsRaw.budget HardwireBudget.R
  omega

theorem baseline_fit (framed out : List Bool) (i : Fin 112)
    (h34 : i≠34) (h98 : i≠98) (h104 : i≠104) (h105 : i≠105) :
    (baseline live gs B w cap framed out i).length≤reserve live gs B w cap := by
  obtain ⟨_,hR,hN,hB,hK,hq⟩ := reserve_bounds live gs B w cap
  revert h34 h98 h104 h105
  refine Fin.addCases (m:=98) (n:=14) (fun i=>?_) (fun i=>?_) i
  · intro h34 _ _ _
    change (HardwireAssignmentsRaw.baseline live gs B w cap framed out (HardwireAssignmentsRaw.old i)).length≤_
    rw [HardwireAssignmentsRaw.baseline_old]
    revert h34
    refine Fin.addCases (m:=48) (n:=50) (fun i=>?_) (fun i=>?_) i
    · intro h34
      simp only [HardwireCacheBody.localState,HardwireReusable.state,Fin.addCases_left]
      have surj : ∀ i : Fin 48,i≠34 → ∃ j,HardwireReusable.work j=i := by decide
      obtain ⟨j,hj⟩ := surj i (by intro h;subst i;exact h34 rfl)
      rw [←hj,HardwireCacheBody.padded_work,ZeroPadding.pad_length]
      exact max_le (by omega) ((HardwireAssignmentsRaw.masters_fit live B w (fun _=>false) j).trans (by omega))
    · intro _
      simp only [HardwireCacheBody.localState,HardwireReusable.state,Fin.addCases_right]
      refine Fin.addCases (m:=47) (n:=3) (fun j=>?_) (fun j=>?_) i
      · simp only [Fin.addCases_left]
        exact (HardwireAssignmentsRaw.masters_fit live B w (fun _=>false) j).trans (by omega)
      · simp only [Fin.addCases_right]
        fin_cases j <;> simp <;> omega
  · intro _ h98 h104 h105
    rw [baseline_tail]
    fin_cases i <;> first
      | exact False.elim (h98 rfl)
      | exact False.elim (h104 rfl)
      | exact False.elim (h105 rfl)
      | (simp [CompareMachine.word] <;> omega)

theorem masters_fit (framed : List Bool) :
    ∀ j,(AssignmentRestore.masters (baseline live gs B w cap framed) j).length≤reserve live gs B w cap := by
  have hn : ∀ j,AssignmentRestore.work j≠34 ∧ AssignmentRestore.work j≠98 ∧
      AssignmentRestore.work j≠104 ∧ AssignmentRestore.work j≠105 := by decide
  intro j
  exact baseline_fit live gs B w cap framed [] _ (hn j).1 (hn j).2.1 (hn j).2.2.1 (hn j).2.2.2

theorem callback_run (hbytes : ∀ g∈gs,(exactWord g).length+2≤B) (hw : 0<w)
    (hm : ∀ g∈gs,g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w) (j : Nat) (out : List Bool) :
    Step callback (callbackBudget live gs B w cap) (AssignmentRestore.heads out) (input live gs B w cap j out)
      (AssignmentRestore.heads (out++HardwireAssignmentsRaw.emitted live gs j))
      (input live gs B w cap j (out++HardwireAssignmentsRaw.emitted live gs j)) := by
  have raw := HardwireAssignmentsRaw.run live gs B w cap hbytes hw hm j out
  have hh : HardwireAssignmentsRaw.heads out false=AssignmentRestore.localHeads out := by
    funext i;simp [HardwireAssignmentsRaw.heads,AssignmentRestore.localHeads]
  have actual := AssignmentRestore.run HardwireAssignmentsRaw.machine
    (baseline live gs B w cap (RepairOrdinary.frame (binary live.card j))) out
    (out++HardwireAssignmentsRaw.emitted live gs j) (HardwireAssignmentsRaw.budget live gs B w)
    (reserve live gs B w cap) _ _
    (baseline_output_only live gs B w cap _) (baseline_out live gs B w cap _)
    (raw.congr_in hh rfl) (HardwireAssignmentsRaw.final_output_head live gs B w j out)
    (HardwireAssignmentsRaw.final_output live gs B w cap j out)
    (HardwireAssignmentsRaw.final_kept live gs B w cap j out)
    (masters_fit live gs B w cap _) (reserve_bounds live gs B w cap).1
  exact actual

def slots : Fin 2 → Fin 223 := ![104,105]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def machine := BinaryEnumerator.machine callback slots
def budget := BinaryEnumerator.budget live.card (callbackBudget live gs B w cap)
noncomputable def emitted := (LiveEnumeration.binary live.card).flatMap
  (fun y=>gs.flatMap (fun g=>exactWord (C10SupplierRowInput.hardwire live g y)))

theorem input_other (j k : Nat) (out : List Bool) (i : Fin 223) (h104 : i≠104) :
    input live gs B w cap j out i=input live gs B w cap k out i := by
  revert h104
  refine Fin.addCases (m:=112) (n:=111) (fun i=>?_) (fun i=>?_) i
  · intro h104
    simp only [input,AssignmentRestore.input,AssignmentRestore.state,Fin.addCases_left,AssignmentRestore.padded]
    apply congrArg
    by_cases h34 : i=34
    · subst i;rw [baseline_out,baseline_out]
    · exact baseline_other live gs B w cap _ _ out out i h34 (by intro h;subst i;exact h104 rfl)
  · intro _
    simp only [input,AssignmentRestore.input,AssignmentRestore.state,Fin.addCases_right]
    refine Fin.addCases (m:=108) (n:=3) (fun i=>?_) (fun i=>?_) i
    · simp only [Fin.addCases_left,AssignmentRestore.masters]
      have hn : ∀ i,AssignmentRestore.work i≠34 ∧ AssignmentRestore.work i≠104 := by decide
      exact baseline_other live gs B w cap _ _ [] [] _ (hn i).1 (hn i).2
    · simp only [Fin.addCases_right]

theorem bank_eq (j : Nat) (out : List Bool) :
    BinaryEnumerator.bank slots (input live gs B w cap 0) live.card cap j out=input live gs B w cap j out := by
  apply HierarchyAllocation.install_eq slots slots_injective
  · intro i
    fin_cases i <;> exact ZeroPadding.pad_zero _
  · intro i hi
    exact input_other live gs B w cap j 0 out i (Ne.symm (hi 0))

theorem heads_eq (out : List Bool) :
    BinaryEnumerator.heads slots AssignmentRestore.heads out=AssignmentRestore.heads out := by
  exact dockH_existing _ _ _ (by intro i;fin_cases i <;> rfl)

theorem run (hbytes : ∀ g∈gs,(exactWord g).length+2≤B) (hw : 0<w)
    (hm : ∀ g∈gs,g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w)
    (hc : 2*live.card≤cap) (out : List Bool) :
    Step machine (budget live gs B w cap)
      (Fin.addCases (AssignmentRestore.heads out) (fun _ : Fin 1=>1))
      (Fin.addCases (input live gs B w cap 0 out) (fun _ : Fin 1=>CompareMachine.word (2^live.card-1)))
      (Fin.addCases (AssignmentRestore.heads (out++emitted live gs)) (fun _ : Fin 1=>1))
      (Fin.addCases (input live gs B w cap (2^live.card-1) (out++emitted live gs))
        (fun _ : Fin 1=>CompareMachine.word (2^live.card-1))) := by
  have actual := BinaryEnumerator.enumerate_step callback slots slots_injective
    AssignmentRestore.heads (input live gs B w cap 0) live.card cap (callbackBudget live gs B w cap)
    (fun y=>gs.flatMap (fun g=>exactWord (C10SupplierRowInput.hardwire live g y))) out hc (by
      intro j _ pre
      simpa only [heads_eq,bank_eq,HardwireAssignmentsRaw.emitted] using callback_run live gs B w cap hbytes hw hm j pre)
  simpa only [heads_eq,bank_eq,machine,budget,emitted] using actual

theorem native_run (out : List Bool) :
    let B := OriginalCacheBounds.capacity gs
    let w := OriginalCacheBounds.width gs
    let cap := 2*live.card
    Step machine (budget live gs B w cap)
      (Fin.addCases (AssignmentRestore.heads out) (fun _ : Fin 1=>1))
      (Fin.addCases (input live gs B w cap 0 out) (fun _ : Fin 1=>CompareMachine.word (2^live.card-1)))
      (Fin.addCases (AssignmentRestore.heads (out++emitted live gs)) (fun _ : Fin 1=>1))
      (Fin.addCases (input live gs B w cap (2^live.card-1) (out++emitted live gs))
        (fun _ : Fin 1=>CompareMachine.word (2^live.card-1))) :=
  run live gs (OriginalCacheBounds.capacity gs) (OriginalCacheBounds.width gs) (2*live.card)
    (OriginalCacheBounds.bytes gs) (by unfold OriginalCacheBounds.width;omega)
    (OriginalCacheBounds.magnitude gs) le_rfl out

variable (a : DecompositionAlgorithm) (occ : List (SupportedNormalizedGate q)) (s : Nat)
  (harity : (s+1)/2+s/2=liveᶜ.card)

theorem c10_run (hbytes : ∀ g∈C10SupplierRowInput.childList a live occ,(exactWord g).length+2≤B) (hw : 0<w)
    (hm : ∀ g∈C10SupplierRowInput.childList a live occ,g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w)
    (hc : 2*live.card≤cap) (out : List Bool) :
    let gs := C10SupplierRowInput.childList a live occ
    let pre := out++natWord (2^live.card*gs.length+1)++exactWord (C10SupplierRowInput.falseGate ((s+1)/2+s/2))
    Step machine (budget live gs B w cap)
      (Fin.addCases (AssignmentRestore.heads pre) (fun _ : Fin 1=>1))
      (Fin.addCases (input live gs B w cap 0 pre) (fun _ : Fin 1=>CompareMachine.word (2^live.card-1)))
      (Fin.addCases (AssignmentRestore.heads (out++exactListWord (BinaryPool.pool a live occ s harity)))
        (fun _ : Fin 1=>1))
      (Fin.addCases (input live gs B w cap (2^live.card-1) (out++exactListWord (BinaryPool.pool a live occ s harity)))
        (fun _ : Fin 1=>CompareMachine.word (2^live.card-1))) := by
  dsimp only
  have actual := run live (C10SupplierRowInput.childList a live occ) B w cap hbytes hw hm hc
    (out++natWord (2^live.card*(C10SupplierRowInput.childList a live occ).length+1)++
      exactWord (C10SupplierRowInput.falseGate ((s+1)/2+s/2)))
  simpa only [BinarySerialization.exactListWord_eq_native,emitted,List.append_assoc] using actual

end NearCubicWires.P1Closure.HardwireAssignments
