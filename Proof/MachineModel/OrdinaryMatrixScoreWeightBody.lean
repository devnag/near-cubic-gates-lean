import Proof.MachineModel.OrdinaryMatrixScoreWeightLayout

/-! One complete selected weight entry. Its finite controller reads the
executed flags and updates exactly the selected signed accumulator. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreWeight
open LocalBitMultitape RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes (_ : Fin 3) := 13
noncomputable def programs (j : Fin 3) : Machine 15 (sizes j) :=
  if j.val=0 then wideProgram else addProgram (j.val==2)
def next (j : Fin 3) (_ : Fin (sizes j)) (scanned : Fin 15 → Bool) : Option (Fin 3) :=
  if j.val=0 then if scanned 2 then some 1 else if scanned 3 then some 2 else none else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

noncomputable def updated (negative : Bool) (ambient : Fin 15 → List Bool) (c w x a : ℕ) :=
  install (slots negative) ambient
    ![scalar c w x,scalar c w (x+a),scalar c w (x+a),zeros c,zeros c]

theorem add_run (negative : Bool) (source assignment : List Bool) (pos apos c w p n x : ℕ)
    (pflag nflag native flag : List Bool) (hc : 4*w+3≤c)
    (hfit : x+(if negative then n else p)<2^w) :
    ∃ actual : ExecutionReceipt 15 13,
      runFrom (addProgram negative) (12*w+13)
        (RecoveryCalls.restarted (addProgram negative) (heads pos apos)
          (tapes source assignment c w p n pflag nflag native (frame (binary w x)) flag))=some actual ∧
      actual.final.heads=heads pos apos ∧
      actual.final.tapes=updated negative
        (tapes source assignment c w p n pflag nflag native (frame (binary w x)) flag)
        c w x (if negative then n else p) ∧ actual.steps=12*w+13 :=
  HierarchyBinary.focused_run (slots negative) (slots_injective negative) MatrixScoreAccumulate.machine _ _
    (padded_accumulate c w x (if negative then n else p) hc hfit) _ _
    (selected_heads negative pos apos) (selected_input negative source assignment c w p n x pflag nflag native flag)

noncomputable def entry (source assignment : List Bool) (pos apos c w p n : ℕ) :=
  controlConfig (RecoveryCalls.code sizes 0)
    (⟨0,heads pos apos,tapes source assignment c w p n [] [] [] [] []⟩ : Configuration 15 13)
noncomputable def after (source assignment : List Bool) (bits : List Bool) (c w p n : ℕ) (sign bit : Bool) :=
  let ambient := tapes source assignment c w p n [bit && !sign] [bit && sign]
    (frame bits) (frame (binary w (RadixSemantics.value bits))) [true]
  if bit then updated sign ambient c w (RadixSemantics.value bits) (if sign then n else p) else ambient

theorem body_run (pre suffix apre asuffix bits : List Bool) (c w p n : ℕ) (sign bit : Bool)
    (hw : bits.length≤w) (hc : 4*w+3≤c)
    (hfit : bit=true → RadixSemantics.value bits+(if sign then n else p)<2^w) :
    ∃ actual,
      runFrom machine (4*bits.length+16*w+26)
        (entry (pre++frame (sign::bits)++suffix) (apre++[true,bit]++asuffix)
          pre.length apre.length c w p n)=some actual ∧
      actual.final.heads=heads (pre.length+2*bits.length+3) (apre.length+2) ∧
      actual.final.tapes=after (pre++frame (sign::bits)++suffix) (apre++[true,bit]++asuffix)
        bits c w p n sign bit ∧ actual.steps≤4*bits.length+16*w+26 := by
  let source := pre++frame (sign::bits)++suffix
  let assignment := apre++[true,bit]++asuffix
  let endpoint := tapes source assignment c w p n [bit && !sign] [bit && sign]
    (frame bits) (frame (binary w (RadixSemantics.value bits))) [true]
  obtain ⟨wide,hr,hh,ht,hs⟩ := wide_run pre suffix apre asuffix bits c w p n sign bit hw (by omega)
  have hread2 : wide.final.scanned 2=(bit && !sign) := by
    simp only [Configuration.scanned,hh,ht]
    change readTapeBit (ZeroPadding.pad c [bit && !sign]) 0=(bit && !sign)
    rw [ZeroPadding.read_pad]
    rfl
  have hread3 : wide.final.scanned 3=(bit && sign) := by
    simp only [Configuration.scanned,hh,ht]
    change readTapeBit (ZeroPadding.pad c [bit && sign]) 0=(bit && sign)
    rw [ZeroPadding.read_pad]
    rfl
  have hr' : runFrom (programs 0) (4*bits.length+4*w+11)
      (⟨0,heads pre.length apre.length,tapes source assignment c w p n [] [] [] [] []⟩ : Configuration 15 13)=some wide := hr
  cases bit with
  | false =>
    obtain ⟨steps,hbound,timed⟩ := stop_receipt sizes programs 0 next 0 _ _ wide hr'
      (by
        change (if wide.final.scanned 2 then some 1 else if wide.final.scanned 3 then some 2 else none)=none
        rw [hread2,hread3]
        rfl)
    obtain ⟨actual,ha,hf,has⟩ := timed.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hb : steps≤4*bits.length+16*w+26 := by omega
    have hm := runFrom_moreFuel machine steps (4*bits.length+16*w+26-steps) _ actual ha
    rw [Nat.add_sub_of_le hb] at hm
    refine ⟨actual,hm,?_,?_,has.le.trans hb⟩
    · rw [hf]; exact hh
    · rw [hf]; simpa [after,RecoveryCalls.stopped] using ht
  | true =>
    let j : Fin 3 := if sign then 2 else 1
    have hj : programs j=addProgram sign := by cases sign <;> rfl
    obtain ⟨added,har,hah,hat,has⟩ := add_run sign source assignment
      (pre.length+2*bits.length+3) (apre.length+2) c w p n (RadixSemantics.value bits)
      [true && !sign] [true && sign] (frame bits) [true] hc (hfit rfl)
    have har' : runFrom (programs j) (12*w+13)
        (RecoveryCalls.restarted (programs j) wide.final.heads wide.final.tapes)=some added := by
      rw [hj,hh,ht]
      exact har
    obtain ⟨firstSteps,hfirst,firstTimed⟩ := call_receipt sizes programs 0 next 0 j _ _ wide hr'
      (by
        change (if wide.final.scanned 2 then some 1 else if wide.final.scanned 3 then some 2 else none)=some j
        rw [hread2,hread3]
        cases sign <;> rfl)
    obtain ⟨lastSteps,hlast,lastTimed⟩ := stop_receipt sizes programs 0 next j _ _ added har'
      (by cases sign <;> rfl)
    have timed := firstTimed.trans lastTimed
    obtain ⟨actual,ha,hf,has'⟩ := timed.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hb : firstSteps+lastSteps≤4*bits.length+16*w+26 := by omega
    have hm := runFrom_moreFuel machine (firstSteps+lastSteps)
      (4*bits.length+16*w+26-(firstSteps+lastSteps)) _ actual ha
    rw [Nat.add_sub_of_le hb] at hm
    refine ⟨actual,hm,?_,?_,has'.le.trans hb⟩
    · rw [hf]; exact hah
    · rw [hf]; simpa [after,RecoveryCalls.stopped,source,assignment] using hat

end NearCubicWires.RepairOrdinary.MatrixScoreWeight
