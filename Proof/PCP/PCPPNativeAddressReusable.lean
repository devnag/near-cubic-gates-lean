import Proof.PCP.PCPPNativeAddressReset
import Proof.Amplification.RecoveryScratchErase

/-! The shared-address append operation with physically reusable workspace.
The bounded scratch is swept after its heads are reset; the two counters
and live descriptor cursor are retained across the whole operation. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeAddressReusable
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def resetSlots (i : Fin 22) : Fin 24 := i.castAdd 2
def eraseSlots (i : Fin 21) : Fin 24 := if i.val < 18 then ⟨i.val+2,by omega⟩ else ⟨i.val+3,by omega⟩
theorem erase_injective : Function.Injective eraseSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [eraseSlots] at hv
  split_ifs at hv <;> dsimp only at hv <;> omega
theorem erase_away (i : Fin 21) : 2 ≤ (eraseSlots i).val ∧ (eraseSlots i).val≠20 := by
  unfold eraseSlots
  split_ifs <;> dsimp only <;> omega
noncomputable def first := RecoveryFocus.machine resetSlots PCPPNativeAddressReset.machine
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 19)
noncomputable def machine := Composition.machine first last
def data (base index C : ℕ) (out : List Bool) (i : Fin 24) : List Bool :=
  if i=0 then List.replicate base true else if i=1 then List.replicate index true
  else if i=20 then out else if i=22 then List.replicate C true
  else if i=23 then List.replicate (C+1) false else List.replicate C false
def heads (out : List Bool) (i : Fin 24) : ℕ := if i=20 then out.length else 0
noncomputable def entry (base index C : ℕ) (out : List Bool) :=
  (⟨machine.start,heads out,data base index C out⟩ : Configuration 24 _)
def budget (base index C : ℕ) := 2*PCPPNativeAddressAppend.budget base index+2*C+7

theorem reset_input (base index C : ℕ) (out : List Bool) (i : Fin 22) :
    heads out (resetSlots i)=(PCPPNativeAddressReset.entry base index C out).heads i ∧
      data base index C out (resetSlots i)=(PCPPNativeAddressReset.entry base index C out).tapes i := by
  fin_cases i <;> simp [heads,data,resetSlots,PCPPNativeAddressReset.entry,PCPPNativeAddressReset.caps,
    PCPPNativeAddressAppend.entry,PCPPNativeAddressAppend.heads,PCPPNativeAddressAppend.data,
    ZeroPadding.config,Rewind.recording,Rewind.config,ZeroPadding.pad,Fin.addCases]

theorem append_run (base index C : ℕ) (out : List Bool)
    (hC : PCPPNativeAddressAppend.budget base index+1 ≤ C) :
    ∃ r,runFrom machine (budget base index C) (entry base index C out)=some r ∧
      r.steps ≤ budget base index C ∧
      r.final.heads=heads (out++natWord (PCPPSubstitution.address base index)) ∧
      r.final.tapes=data base index C (out++natWord (PCPPSubstitution.address base index)) := by
  obtain ⟨reset,hr,rs,rt,rh,r0,rh0,r1,rh1,work⟩ := PCPPNativeAddressReset.reset_run base index C out hC
  obtain ⟨a,ha,_,asteps,aheads,atapes,akeep⟩ := RecoveryFocus.dock
    resetSlots (by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 24 => x.val) h)
    PCPPNativeAddressReset.machine _ (heads out) (data base index C out)
    (PCPPNativeAddressReset.entry base index C out)
    (fun i => (reset_input base index C out i).1)
    (fun i => (reset_input base index C out i).2) reset hr
  let backing : Fin 19 → List Bool := fun j => a.final.tapes (eraseSlots (j.castAdd 2))
  have scratch (j : Fin 19) :
      a.final.heads (eraseSlots (j.castAdd 2))=0 ∧ (backing j).length ≤ C := by
    let k : Fin 22 := if j.val < 18 then ⟨j.val+2,by omega⟩ else 21
    have hk : 2 ≤ k.val ∧ k.val < 20 ∨ k.val=21 := by
      unfold k
      split_ifs
      · left; change 2 ≤ j.val+2 ∧ j.val+2 < 20; omega
      · exact Or.inr rfl
    have hs : eraseSlots (j.castAdd 2)=resetSlots k := by
      apply Fin.ext
      by_cases hj : j.val < 18
      · simp only [eraseSlots,Fin.val_castAdd,resetSlots,k,hj,ite_true]
      · have hv : j.val=18 := by omega
        simp [eraseSlots,resetSlots,k,hv]
    exact ⟨by rw [hs,aheads]; exact (work k hk).1,
      by unfold backing; rw [hs,atapes]; exact (work k hk).2⟩
  obtain ⟨erased,he,et,eh,es⟩ := RecoveryScratchErase.erase_ready C (C+1) backing (fun j => (scratch j).2)
  have outside22 := akeep 22 (by intro j; apply Fin.ne_of_val_ne; change j.val≠22; omega)
  have outside23 := akeep 23 (by intro j; apply Fin.ne_of_val_ne; change j.val≠23; omega)
  obtain ⟨b,hb,_,bsteps,bheads,btapes,bkeep⟩ := RecoveryFocus.dock
    eraseSlots erase_injective (RecoveryScratchErase.resetMachine 19) _ a.final.heads a.final.tapes
    (initialConfiguration (RecoveryScratchErase.resetMachine 19)
      (Fin.addCases (motive := fun _ : Fin 21 => List Bool)
        (Fin.addCases (motive := fun _ : Fin 20 => List Bool) backing (fun _ : Fin 1 => List.replicate C true))
        (fun _ : Fin 1 => List.replicate (C+1) false)))
    (by intro i
        refine Fin.addCases (m := 20) (n := 1) (fun j => ?_) (fun j => ?_) i
        · refine Fin.addCases (m := 19) (n := 1) (fun k => ?_) (fun k => ?_) j
          · exact (scratch k).1
          · fin_cases k; exact outside22.1
        · fin_cases j; exact outside23.1)
    (by intro i
        refine Fin.addCases (m := 20) (n := 1) (fun j => ?_) (fun j => ?_) i
        · refine Fin.addCases (m := 19) (n := 1) (fun k => ?_) (fun k => ?_) j
          · simp only [initialConfiguration,Fin.addCases_left]; rfl
          · fin_cases k; exact outside22.2
        · fin_cases j; exact outside23.2) erased he
  let result := Composition.joinedReceipt a b
  have joined := Composition.run_join first last _ _ _ a b ha hb
  have timeEq : 2*PCPPNativeAddressAppend.budget base index+2+1+(2*C+4)=budget base index C := by
    unfold budget; omega
  rw [timeEq] at joined
  have keep0 := bkeep 0 (by intro j; have := (erase_away j).1; apply Fin.ne_of_val_ne; omega)
  have keep1 := bkeep 1 (by intro j; have := (erase_away j).1; apply Fin.ne_of_val_ne; omega)
  have keep20 := bkeep 20 (by intro j; have := (erase_away j).2; apply Fin.ne_of_val_ne; exact this)
  have sh (j : Fin 21) : b.final.heads (eraseSlots j)=0 := (bheads j).trans (eh j)
  have st (j : Fin 19) : b.final.tapes (eraseSlots (j.castAdd 2))=List.replicate C false :=
    (btapes (j.castAdd 2)).trans (by
      change erased.final.tapes ((j.castAdd 1).castAdd 1)=_
      rw [et]; simp only [Fin.addCases_left])
  have capT : b.final.tapes 22=List.replicate C true :=
    (btapes 19).trans (by rw [et]; rfl)
  have logT : b.final.tapes 23=List.replicate (C+1) false :=
    (btapes 20).trans (by rw [et]; simp only [max_self]; rfl)
  refine ⟨result,joined,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ _
    rw [asteps,bsteps]
    unfold budget
    omega
  · funext i
    change b.final.heads i=heads _ i
    fin_cases i
    · exact keep0.1.trans ((aheads 0).trans rh0)
    · exact keep1.1.trans ((aheads 1).trans rh1)
    all_goals first | exact sh 0 | exact sh 1 | exact sh 2 | exact sh 3 | exact sh 4 | exact sh 5 | exact sh 6 | exact sh 7 | exact sh 8 | exact sh 9 | exact sh 10 | exact sh 11 | exact sh 12 | exact sh 13 | exact sh 14 | exact sh 15 | exact sh 16 | exact sh 17 | exact sh 18 | exact sh 19 | exact sh 20 | exact keep20.1.trans ((aheads 20).trans rh)
  · funext i
    change b.final.tapes i=data _ _ _ _ i
    fin_cases i
    · exact keep0.2.trans ((atapes 0).trans r0)
    · exact keep1.2.trans ((atapes 1).trans r1)
    all_goals first | exact st 0 | exact st 1 | exact st 2 | exact st 3 | exact st 4 | exact st 5 | exact st 6 | exact st 7 | exact st 8 | exact st 9 | exact st 10 | exact st 11 | exact st 12 | exact st 13 | exact st 14 | exact st 15 | exact st 16 | exact st 17 | exact st 18 | exact capT | exact logT | exact keep20.2.trans ((atapes 20).trans rt)

end NearCubicWires.RepairOrdinary.PCPPNativeAddressReusable
