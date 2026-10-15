import Proof.PCP.PCPPNativeNodeReuseLayout
import Proof.Amplification.RecoveryRowLookupTapes

/-! Execute one complete native-node substitution, reset its scratch and
row-cache cursors, then physically erase the scratch with the actual F
driver. The resulting entire tape/head layout is ready for the next node. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeReusable
open LocalBitMultitape SourceInterfaces PCPPNativeNodeMachine RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem data_work (source queries : List Bool) (base position C F : ℕ) (out : List Bool)
    (i : Fin 122) (hi : 6 ≤ i.val) (hi120 : i.val < 120) :
    data source queries base position C F out i=List.replicate F false := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  have h2 : i≠2 := by intro h; subst i; simp at hi
  have h3 : i≠3 := by intro h; subst i; simp at hi
  have h4 : i≠4 := by intro h; subst i; simp at hi
  have h5 : i≠5 := by intro h; subst i; simp at hi
  have h120 : i≠120 := by intro h; subst i; simp at hi120
  have h121 : i≠121 := by intro h; subst i; simp at hi120
  simp only [data,h0,h1,h2,h3,h4,h5,h120,h121,ite_false]

theorem heads_work (pos : ℕ) (out : List Bool) (i : Fin 122) (hi : 6 ≤ i.val) : heads pos out i=0 := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h5 : i≠5 := by intro h; subst i; simp at hi
  simp only [heads,h0,h5,ite_false]

def budget {n r : ℕ} (base index C F : ℕ) (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n) :=
  2*nodeBudget base index C projection node+2*F+7

theorem node_run {n r : ℕ} (pre tail : List Bool) (base index C F : ℕ)
    (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n) (out : List Bool)
    (hC : nodeCapacity base index C projection node)
    (hF : nodeBudget base index C projection node+1 ≤ F) (hCF : C+1 ≤ F) :
    ∃ result,runFrom machine (budget base index C F projection node)
      (entry (originalSource pre tail node) (rowCache projection) pre.length base (base+2*index) C F out)=some result ∧
      result.steps ≤ budget base index C F projection node ∧
      result.final.heads=heads (pre.length+(PCPPRequestNodeSchema.native node).length) (out++emittedNode base index projection node) ∧
      result.final.tapes=data (originalSource pre tail node) (rowCache projection) base (base+2*index) C F
        (out++emittedNode base index projection node) := by
  obtain ⟨reset,hr,rs,meaning,rh1,work⟩ := PCPPNativeNodeReset.reset_run pre tail base index C F projection node out hC hF hCF
  obtain ⟨a,ha,_,asteps,aheads,atapes,akeep⟩ := RecoveryFocus.dock resetSlots
    (by intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 122 => k.val) h)
    PCPPNativeNodeReset.machine _ (heads pre.length out)
    (data (originalSource pre tail node) (rowCache projection) base (base+2*index) C F out)
    (PCPPNativeNodeReset.entry pre tail base index C F projection node out)
    (fun i => (reset_input pre tail base index C F projection node out hCF i).1)
    (fun i => (reset_input pre tail base index C F projection node out hCF i).2) reset hr
  let backing : Fin 114 → List Bool := fun j => a.final.tapes (eraseSlots (j.castAdd 2))
  have scratch (j : Fin 114) : a.final.heads (eraseSlots (j.castAdd 2))=0 ∧ (backing j).length ≤ F := by
    let k : Fin 120 := ⟨j.val+6,by omega⟩
    have hs : eraseSlots (j.castAdd 2)=resetSlots k := Fin.ext rfl
    have hk : 6 ≤ k.val := by change 6 ≤ j.val+6; omega
    exact ⟨by rw [hs,aheads]; exact (work k hk).1,
      by unfold backing; rw [hs,atapes]; exact (work k hk).2⟩
  have keep120 := akeep 120 (by intro j; apply Fin.ne_of_val_ne; change j.val≠120; omega)
  have keep121 := akeep 121 (by intro j; apply Fin.ne_of_val_ne; change j.val≠121; omega)
  have erased := RecoveryScratchErase.erase_ready F (F+1) backing (fun j => (scratch j).2)
  obtain ⟨b,hb,bh,bt,bs⟩ := erased.focus_at eraseSlots erase_injective a.final.heads a.final.tapes
    (by intro i
        refine Fin.addCases (m := 115) (n := 1) (fun j => ?_) (fun j => ?_) i
        · refine Fin.addCases (m := 114) (n := 1) (fun k => ?_) (fun k => ?_) j
          · simp only [Fin.addCases_left]; rfl
          · fin_cases k; exact keep120.2
        · fin_cases j; exact keep121.2)
    (by intro i
        refine Fin.addCases (m := 115) (n := 1) (fun j => ?_) (fun j => ?_) i
        · refine Fin.addCases (m := 114) (n := 1) (fun k => ?_) (fun k => ?_) j
          · exact (scratch k).1
          · fin_cases k; exact keep120.1
        · fin_cases j; exact keep121.1)
  let result := Composition.joinedReceipt a b
  have joined := Composition.run_join first last _ _ _ a b ha hb
  have timeEq : 2*nodeBudget base index C projection node+2+1+(2*F+4)=budget base index C F projection node := by
    unfold budget; omega
  rw [timeEq] at joined
  rcases meaning with ⟨r0,rh0,r1,r5,rh5,retained⟩
  have main (j : Fin 6) :
      a.final.heads (j.castAdd 116)=heads (pre.length+(PCPPRequestNodeSchema.native node).length)
        (out++emittedNode base index projection node) (j.castAdd 116) ∧
      a.final.tapes (j.castAdd 116)=data (originalSource pre tail node) (rowCache projection) base (base+2*index) C F
        (out++emittedNode base index projection node) (j.castAdd 116) := by
    fin_cases j
    · exact ⟨(aheads 0).trans rh0,(atapes 0).trans r0⟩
    · exact ⟨(aheads 1).trans rh1,(atapes 1).trans r1⟩
    · exact ⟨(aheads 2).trans (retained 0).1,(atapes 2).trans (retained 0).2⟩
    · exact ⟨(aheads 3).trans (retained 1).1,(atapes 3).trans (retained 1).2⟩
    · exact ⟨(aheads 4).trans (retained 2).1,(atapes 4).trans (retained 2).2⟩
    · exact ⟨(aheads 5).trans rh5,(atapes 5).trans r5⟩
  have cleared (j : Fin 114) : b.final.tapes (eraseSlots (j.castAdd 2))=List.replicate F false := by
    rw [bt,install_slot eraseSlots erase_injective]
    change (Fin.addCases (m := 115) (n := 1) (motive := fun _ : Fin 116 => List Bool)
      (Fin.addCases (m := 114) (n := 1) (motive := fun _ : Fin 115 => List Bool)
        (fun _ => List.replicate F false) (fun _ => List.replicate F true))
      (fun _ => List.replicate (max (F+1) (F+1)) false) ((j.castAdd 1).castAdd 1))=_
    simp only [Fin.addCases_left]
  have capT : b.final.tapes 120=List.replicate F true := by
    change b.final.tapes (eraseSlots 114)=_
    rw [bt,install_slot eraseSlots erase_injective]
    rfl
  have logT : b.final.tapes 121=List.replicate (F+1) false := by
    change b.final.tapes (eraseSlots 115)=_
    rw [bt,install_slot eraseSlots erase_injective]
    simp only [max_self]
    rfl
  refine ⟨result,joined,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ _
    rw [asteps,bs]
    unfold budget; omega
  · change b.final.heads=_
    rw [bh]
    funext i
    by_cases h6 : i.val < 6
    · let j : Fin 6 := ⟨i.val,h6⟩
      have hi : i=j.castAdd 116 := Fin.ext rfl
      rw [hi]; exact (main j).1
    · by_cases h120 : i.val < 120
      · let j : Fin 120 := ⟨i.val,h120⟩
        have hi : i=resetSlots j := Fin.ext rfl
        rw [hi,aheads,(work j (by change 6 ≤ i.val; omega)).1]
        exact (heads_work _ _ _ (by change 6 ≤ i.val; omega)).symm
      · have hi : i=120 ∨ i=121 := by
          have hv : i.val=120 ∨ i.val=121 := by omega
          exact hv.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
        rcases hi with hi | hi <;> subst i
        · exact keep120.1
        · exact keep121.1
  · change b.final.tapes=_
    funext i
    by_cases h6 : i.val < 6
    · rw [bt,install_other eraseSlots _ _ i (by
        intro j h
        have hv := congrArg Fin.val h
        have hj := erase_away j
        omega)]
      let j : Fin 6 := ⟨i.val,h6⟩
      have hi : i=j.castAdd 116 := Fin.ext rfl
      rw [hi]; exact (main j).2
    · by_cases h120 : i.val < 120
      · let j : Fin 114 := ⟨i.val-6,by omega⟩
        have hi : i=eraseSlots (j.castAdd 2) := Fin.ext (by change i.val=i.val-6+6; omega)
        rw [data_work _ _ _ _ _ _ _ i (by omega) h120,hi]
        exact cleared j
      · have hi : i=120 ∨ i=121 := by
          have hv : i.val=120 ∨ i.val=121 := by omega
          exact hv.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
        rcases hi with hi | hi <;> subst i
        · exact capT
        · exact logT

end NearCubicWires.RepairOrdinary.PCPPNativeNodeReusable
