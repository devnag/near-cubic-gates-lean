import Proof.Hierarchy.CompetitorProducedScalarMidpoint

/-! The signed score-table consumer computes the residue of the actual
signed difference. It executes borrow subtraction at the supplied common
width and physically crops to the paid Q-bit output width, including the
negative-score case; no truncated Nat subtraction is substituted. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSignedResidue
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def residue (w q a b : ℕ) := (a+2^w-b)%2^q

theorem binary_mod (w n : ℕ) : binary w (n%2^w)=binary w n := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih =>
    have hm : (n%2^(w+1))%2=n%2 := by rw [pow_succ,Nat.mod_mul_left_mod]
    have hd : (n%2^(w+1))/2=(n/2)%2^w := by rw [pow_succ,Nat.mod_mul_left_div_self]
    simp only [binary,hm,hd,ih]

theorem difference_binary (w a b : ℕ) (ha : a<2^w) (hb : b<2^w) :
    Subtract.difference (binary w a) (binary w b) false=binary w (residue w w a b) := by
  let bits := Subtract.difference (binary w a) (binary w b) false
  have hlen : bits.length=w := by simp [bits]
  have hvalue := Subtract.difference_value (binary w a) (binary w b) false (by simp)
  simp only [binary_value w a ha,binary_value w b hb,binary_length,Bool.toNat_false,Nat.add_zero] at hvalue
  have hbound : value bits<2^w := by simpa only [hlen] using value_lt bits
  have hv : value bits=residue w w a b := by
    unfold residue
    cases he : Subtract.underflow (binary w a) (binary w b) false with
    | false =>
      simp only [he,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at hvalue
      have hx : a+2^w-b=value bits+2^w := by change value bits+b=a at hvalue; omega
      rw [hx,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt hbound]
    | true =>
      simp only [he,Bool.toNat_true,Nat.mul_one] at hvalue
      have hx : a+2^w-b=value bits := by change value bits+b=a+2^w at hvalue; omega
      rw [hx,Nat.mod_eq_of_lt hbound]
  have he := BoundedCounter.binary_of_value bits
  rw [hlen,hv] at he
  exact he.symm

theorem raw_run (left right : List Bool) (hw : left.length=right.length) :
    ∃ r,run Subtract.machine (2*left.length+1) ![frame left,frame right,[]]=some r ∧
      r.final.tapes=![frame left,frame right,frame (Subtract.difference left right false)] ∧
      r.steps=2*left.length+1 := by
  have hp := Subtract.subtract_prefix [] [] left right [] [] [] [] false hw
  obtain ⟨r,hr,hf,hs,_⟩ := hp.run (by rfl) (by simp [Subtract.difference_length left right false hw]; omega)
  have hi : Subtract.config (Subtract.scanState false) (frame left) (frame right) 0 0 [] []=
      initialConfiguration Subtract.machine ![frame left,frame right,[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · simp [Subtract.config,initialConfiguration,StablePartition.Workspace.overlay]
  refine ⟨r,?_,?_,by simpa using hs⟩
  · rw [run,← hi]
    simpa using hr
  · rw [hf]
    simp [Subtract.config,StablePartition.Workspace.overlay]

noncomputable def subtractProgram := Rewind.machine Subtract.machine

theorem subtract_ready (w a b : ℕ) (ha : a<2^w) (hb : b<2^w) :
    ∃ out,ClockJoin.ReadyRun subtractProgram (4*w+4)
      ![frame (binary w a),frame (binary w b),[],[]] out ∧
      out 0=frame (binary w a) ∧ out 1=frame (binary w b) ∧ out 2=frame (binary w (residue w w a b)) := by
  obtain ⟨base,hr,ht,hs⟩ := raw_run (binary w a) (binary w b) (by simp)
  obtain ⟨r,hrun,hrt,hrh,hrs,_⟩ := Rewind.reset_run Subtract.machine _ _ base hr
  have htime : 2*base.steps+2=4*w+4 := by simp only [binary_length] at hs; omega
  rw [htime] at hrun
  have hin : (Fin.addCases (m := 3) (n := 1) (motive := fun _ => List Bool)
      ![frame (binary w a),frame (binary w b),[]] (fun _ => []))=
      ![frame (binary w a),frame (binary w b),[],[]] := by funext i; fin_cases i <;> rfl
  rw [hin] at hrun
  refine ⟨r.final.tapes,⟨r,hrun,rfl,hrh,by omega⟩,(hrt 0).trans (congrFun ht 0),(hrt 1).trans (congrFun ht 1),?_⟩
  have hv := (hrt 2).trans (congrFun ht 2)
  change r.final.tapes 2=frame (Subtract.difference (binary w a) (binary w b) false) at hv
  rw [difference_binary w a b ha hb] at hv
  exact hv

def subtractSlots (i : Fin 4) : Fin 8 := i.castAdd 4
def cropSlots : Fin 5 → Fin 8 := ![4,2,5,6,7]
noncomputable def firstProgram := RecoveryFocus.machine subtractSlots subtractProgram
noncomputable def lastProgram := RecoveryFocus.machine cropSlots ClockNormalize.machine
noncomputable def machine := Composition.machine firstProgram lastProgram
def input (w q a b : ℕ) : Fin 8 → List Bool :=
  ![frame (binary w a),frame (binary w b),[],[],List.replicate q true,[],[],[]]

theorem crop_residue (w q a b : ℕ) (hq : q≤w) :
    ClockNormalize.resize q (binary w (residue w w a b))=binary q (residue w q a b) := by
  rw [CompetitorRationalSum.resize_prefix q w _ hq]
  rw [← binary_mod q (residue w w a b)]
  unfold residue
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hq)]

theorem residue_run (w q a b : ℕ) (ha : a<2^w) (hb : b<2^w) (hq : q≤w) :
    ∃ out,ClockJoin.ReadyRun machine (4*w+4*q+9) (input w q a b) out ∧
      out 0=frame (binary w a) ∧ out 1=frame (binary w b) ∧
      out 4=List.replicate q true ∧ out 5=frame (binary q (residue w q a b)) := by
  obtain ⟨sub,hsub,h0,h1,h2⟩ := subtract_ready w a b ha hb
  have hi : Function.Injective subtractSlots := by intro i j h; exact Fin.ext (congrArg (fun a : Fin 8 => a.val) h)
  have hin : ∀ i,input w q a b (subtractSlots i)=![frame (binary w a),frame (binary w b),[],[]] i := by intro i; fin_cases i <;> rfl
  have hfirst := CompetitorRationalProducts.bounded_focus subtractSlots hi _ _ _ hsub (input w q a b) hin
  let middle := install subtractSlots (input w q a b) sub
  obtain ⟨crop,hcrop,hc0,_,hc2,_,_,hch,hcs⟩ := ClockNormalize.normalize_run q (binary w (residue w w a b))
  have cropReady : ClockJoin.ReadyRun ClockNormalize.machine (4*q+4)
      (ClockNormalize.input q (binary w (residue w w a b))) crop.final.tapes := ⟨crop,hcrop,rfl,hch,hcs.le⟩
  have hcInput : ∀ i,middle (cropSlots i)=ClockNormalize.input q (binary w (residue w w a b)) i := by
    intro i
    fin_cases i
    · exact install_other subtractSlots _ _ 4 (by decide)
    · exact (install_slot subtractSlots hi (input w q a b) sub 2).trans h2
    · exact install_other subtractSlots _ _ 5 (by decide)
    · exact install_other subtractSlots _ _ 6 (by decide)
    · exact install_other subtractSlots _ _ 7 (by decide)
  have hlast := CompetitorRationalProducts.bounded_focus cropSlots (by decide) _ _ _ cropReady middle hcInput
  have hall := ClockJoin.join firstProgram lastProgram _ _ _ _ _ hfirst hlast
  have htime : (4*w+4)+1+(4*q+4)=4*w+4*q+9 := by omega
  rw [htime] at hall
  refine ⟨install cropSlots middle crop.final.tapes,hall,?_,?_,?_,?_⟩
  · exact (install_other cropSlots _ _ 0 (by decide)).trans ((install_slot subtractSlots hi _ sub 0).trans h0)
  · exact (install_other cropSlots _ _ 1 (by decide)).trans ((install_slot subtractSlots hi _ sub 1).trans h1)
  · exact (install_slot cropSlots (by decide) middle crop.final.tapes 0).trans hc0
  · have ho := (install_slot cropSlots (by decide) middle crop.final.tapes 2).trans hc2
    change install cropSlots middle crop.final.tapes 5=frame (ClockNormalize.resize q (binary w (residue w w a b))) at ho
    rw [crop_residue w q a b hq] at ho
    exact ho

end NearCubicWires.RepairOrdinary.CompetitorSignedResidue
