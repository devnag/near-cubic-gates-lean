import Proof.Assembly.ClosureBinaryCachePalette

/-! One paid fanout builds every repeated private assignment bank field.
The downstream program is the accepted enumeration machine, transported by
literal false padding. Nine scalar/source words and one capacity word are
the explicit boundary to the preceding cold arithmetic composition. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryCacheColdFanout
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound ExtIncidence
open RepairRepresentation RepairSource CloseoutFinal SupplierPipeline SupplierEstimator
open VerifierDecoding SignedSortKey BinaryCacheColdPalette
open scoped BigOperators

variable {q : Nat} (live : Finset (Fin q)) (gs : List (ExactThresholdGate q)) (B w : Nat)
noncomputable def bank (j : Nat) (out : List Bool) : Fin 224→List Bool :=
  fun i=>Fin.addCases (HardwireAssignments.input live gs B w (2*live.card) j out)
    (fun _ : Fin 1=>CompareMachine.word (2^live.card-1)) i
noncomputable def request (j : Nat) (out : List Bool) (i : Fin 224) : List Bool :=
  if i=34 then out else if i=98 then exactListWord gs
  else if i=104 then RepairOrdinary.frame (binary live.card j)
  else if i=223 then CompareMachine.word (2^live.card-1)
  else ZeroPadding.pad (U live gs B w) (NativeFanout.word select (words live gs B w) i)
def heads (out : List Bool) (i : Fin 224) : Nat := if i=34 then out.length else if i=223 then 1 else 0

theorem private_pad (j : Nat) (out : List Bool) (i : Fin 224)
    (h34 : i≠34) (h98 : i≠98) (h104 : i≠104) (h223 : i≠223) :
    ZeroPadding.pad (U live gs B w) (bank live gs B w j out i)=
      ZeroPadding.pad (U live gs B w) (NativeFanout.word select (words live gs B w) i) := by
  revert h34 h98 h104 h223
  refine Fin.addCases (m:=223) (n:=1) (fun i=>?_) (fun i=>?_) i
  · simp only [bank,Fin.addCases_left,HardwireAssignments.input,AssignmentRestore.input,AssignmentRestore.state]
    refine Fin.addCases (m:=112) (n:=111) (fun i=>?_) (fun i=>?_) i
    · intro h34 h98 h104 _
      simp only [Fin.addCases_left,AssignmentRestore.padded]
      have hc : AssignmentRestore.caps (S live gs B w) i≤U live gs B w := by
        unfold AssignmentRestore.caps U
        split_ifs <;>omega
      change AssignmentRestore.caps (HardwireAssignments.reserve live gs B w (2*live.card)) i≤_ at hc
      rw [MatrixBucketRootPower.pad_pad _ _ _ hc]
      simpa only [NativeFanout.word,select,Fin.addCases_left] using
        baseline_pad live gs B w (RepairOrdinary.frame (binary live.card j)) out i
          (by intro h;subst i;exact h34 rfl) (by intro h;subst i;exact h98 rfl)
          (by intro h;subst i;exact h104 rfl)
    · intro _ _ _ _
      simp only [Fin.addCases_right]
      refine Fin.addCases (m:=108) (n:=3) (fun i=>?_) (fun i=>?_) i
      · simp only [Fin.addCases_left,AssignmentRestore.masters]
        have hn : ∀ i,AssignmentRestore.work i≠34 ∧ AssignmentRestore.work i≠98 ∧ AssignmentRestore.work i≠104 := by decide
        simpa only [NativeFanout.word,select,Fin.addCases_left,Fin.addCases_right] using
          baseline_pad live gs B w (RepairOrdinary.frame (binary live.card j)) []
            (AssignmentRestore.work i) (hn i).1 (hn i).2.1 (hn i).2.2
      · fin_cases i
        · exact pad_zeros _ _ (by unfold U S;omega)
        · rfl
        · exact pad_zeros _ _ (by unfold U S;omega)
  · intro _ _ _ h223
    fin_cases i
    exact False.elim (h223 rfl)

theorem padded_eq (j : Nat) (out : List Bool) :
    (fun i=>ZeroPadding.pad (caps (U live gs B w) i) (bank live gs B w j out i))=
      request live gs B w j out := by
  funext i
  by_cases h34 : i=34
  · subst i
    change ZeroPadding.pad 0 (ZeroPadding.pad 0
      (HardwireAssignments.baseline live gs B w (2*live.card) (RepairOrdinary.frame (binary live.card j)) out 34))=out
    rw [HardwireAssignments.baseline_out]
    simp only [ZeroPadding.pad_zero]
  by_cases h98 : i=98
  · subst i
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (exactListWord gs))=exactListWord gs
    simp only [ZeroPadding.pad_zero]
  by_cases h104 : i=104
  · subst i
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (RepairOrdinary.frame (binary live.card j)))=_
    simp only [ZeroPadding.pad_zero]
    rfl
  by_cases h223 : i=223
  · subst i;exact ZeroPadding.pad_zero _
  simpa only [caps,request,h34,h98,h104,h223,or_self,↓reduceIte] using
    private_pad live gs B w j out i h34 h98 h104 h223

theorem run (hbytes : ∀ g∈gs,(exactWord g).length+2≤B) (hw : 0<w)
    (hm : ∀ g∈gs,g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w) (out : List Bool) :
    Step HardwireAssignments.machine (HardwireAssignments.budget live gs B w (2*live.card))
      (heads out) (request live gs B w 0 out)
      (heads (out++HardwireAssignments.emitted live gs))
      (request live gs B w (2^live.card-1) (out++HardwireAssignments.emitted live gs)) := by
  have actual := (HardwireAssignments.run live gs B w (2*live.card) hbytes hw hm le_rfl out).pad
    (caps (U live gs B w))
  have hh (out : List Bool) :
      (fun i=>Fin.addCases (AssignmentRestore.heads out) (fun _ : Fin 1=>1) i)=heads out := by
    funext i;fin_cases i <;>rfl
  exact (actual.congr_in (hh out) (padded_eq live gs B w 0 out)).congr (hh _)
    (padded_eq live gs B w (2^live.card-1) _)

theorem words_fit : ∀ j,(words live gs B w j).length≤U live gs B w := by
  obtain ⟨hC,_,_,hq,hR,hB,_,_,hN,_⟩ := scalar_bounds live gs B w
  have hw : 2*w+1≤U live gs B w := by
    unfold HardwireBudget.C at hC
    omega
  intro j
  fin_cases j <;>simp [words,RepairOrdinary.frame_length,binary_length,
    CompareMachine.word,CloseoutRowsGateSupport.gateMembers] <;>first | omega | (unfold U;omega)

end NearCubicWires.P1Closure.BinaryCacheColdFanout
