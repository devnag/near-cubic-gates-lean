import Proof.Amplification.RecoveryCompactNative

/-! Every compact broadcast source comes from the actual cold-marker run:
the same valuation, both produced suffixes/counts, and the retained original
width/cap/erase drivers. No workspace or source-length premise is added. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCompact
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sourceSlots : Fin 11→Fin 338 := ![10,2,1,24,271,275,14,21,270,274,16]
def sourceTapes (bits word innerBits outerBits : List Bool) (n m : Nat) : Fin 11→List Bool :=
  ![frame (RecoveryColdHeader.zeroWord bits),CompareMachine.word (width bits),
    frame word,CompareMachine.word word.length,frame innerBits,frame outerBits,
    CompareMachine.word (width bits+1),CompareMachine.word (limit bits),
    CompareMachine.word n,CompareMachine.word m,List.replicate (erase bits) true]
def sourceHeads : Fin 11→Nat := ![0,0,0,0,0,0,0,0,1,1,0]

theorem source_ready (bits word : List Bool) (H : Fin 338→Nat) (A : Fin 338→List Bool)
    (hr : RecoveryColdMarker.Ready bits word H A) :
    ∃ n innerBits m outerBits,n≤limit bits ∧ m≤limit bits ∧
      (fun j=>A (sourceSlots j))=sourceTapes bits word innerBits outerBits n m ∧
      (fun j=>H (sourceSlots j))=sourceHeads ∧
      A 336=List.replicate (RecoveryColdMarker.reset6 bits) false ∧ A 337=[] ∧
      H 336=0 ∧ H 337=0 := by
  obtain ⟨h,a,hfront,hH,hA⟩ := hr
  have lowT (i : Fin 279) : A (i.castAdd 59)=a i := by
    rw [hA,RecoveryColdMarker.retained]
  have lowH (i : Fin 279) : H (i.castAdd 59)=h i := by
    rw [hH]
    simp only [RecoveryColdMarker.heads,Fin.addCases_left]
  obtain ⟨k,g,b,_,hp,hsat,_⟩ := hfront
  obtain ⟨pos,c,hc,_,hh,ht⟩ := hsat
  obtain ⟨n,innerBits,m,outerBits,logged,hn,hm,_,_,_,hpH,hpA⟩ := hp
  have t10 := congrFun ht (10 : Fin 172)
  rw [RecoveryColdSAT.low_retained bits word c 10 (by decide)] at t10
  have a10 : A 10=frame (RecoveryColdHeader.zeroWord bits) :=
    (lowT 10).trans (t10.trans hc.zero)
  have h10 : H 10=0 := (lowH 10).trans (congrFun hh 10)
  have t2 := congrFun ht (2 : Fin 172)
  rw [RecoveryColdSAT.low_retained bits word c 2 (by decide)] at t2
  have a2 : A 2=CompareMachine.word (width bits) :=
    (lowT 2).trans (t2.trans hc.width)
  have h2 : H 2=0 := (lowH 2).trans (congrFun hh 2)
  have t1 := congrFun ht (1 : Fin 172)
  rw [RecoveryColdSAT.low_retained bits word c 1 (by decide)] at t1
  have a1 : A 1=frame word :=
    (lowT 1).trans (t1.trans hc.source)
  have h1 : H 1=0 := (lowH 1).trans (congrFun hh 1)
  have t24 := congrFun ht (24 : Fin 172)
  rw [RecoveryColdSAT.low_retained bits word c 24 (by decide)] at t24
  have a24 : A 24=CompareMachine.word word.length :=
    (lowT 24).trans (t24.trans hc.length)
  have h24 : H 24=0 := (lowH 24).trans (congrFun hh 24)
  have t14 := congrFun ht (14 : Fin 172)
  rw [RecoveryColdSAT.low_retained bits word c 14 (by decide)] at t14
  have a14 : A 14=CompareMachine.word (width bits+1) :=
    (lowT 14).trans (t14.trans hc.increment)
  have h14 : H 14=0 := (lowH 14).trans (congrFun hh 14)
  have t21 := congrFun ht (21 : Fin 172)
  rw [RecoveryColdSAT.low_retained bits word c 21 (by decide)] at t21
  have a21 : A 21=CompareMachine.word (limit bits) :=
    (lowT 21).trans (t21.trans hc.cap)
  have h21 : H 21=0 := (lowH 21).trans (congrFun hh 21)
  have t16 := congrFun ht (16 : Fin 172)
  rw [RecoveryColdSAT.low_retained bits word c 16 (by decide)] at t16
  have a16 : A 16=List.replicate (erase bits) true :=
    (lowT 16).trans (t16.trans hc.erase)
  have h16 : H 16=0 := (lowH 16).trans (congrFun hh 16)
  have a271 : A 271=frame innerBits := by
    apply (lowT 271).trans
    change a (RecoveryColdTablesAmbient.slots 3)=_
    rw [hpA]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot RecoveryColdTablesAmbient.slots
      RecoveryColdTablesAmbient.slots_injective]
    rfl
  have h271 : H 271=0 := by
    apply (lowH 271).trans
    change h (RecoveryColdTablesAmbient.slots 3)=_
    rw [hpH]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot RecoveryColdTablesAmbient.slots
      RecoveryColdTablesAmbient.slots_injective]
    rfl
  have a275 : A 275=frame outerBits := by
    apply (lowT 275).trans
    change a (RecoveryColdTablesAmbient.slots 8)=_
    rw [hpA]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot RecoveryColdTablesAmbient.slots
      RecoveryColdTablesAmbient.slots_injective]
    rfl
  have h275 : H 275=0 := by
    apply (lowH 275).trans
    change h (RecoveryColdTablesAmbient.slots 8)=_
    rw [hpH]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot RecoveryColdTablesAmbient.slots
      RecoveryColdTablesAmbient.slots_injective]
    rfl
  have a270 : A 270=CompareMachine.word n := by
    apply (lowT 270).trans
    change a (RecoveryColdTablesAmbient.slots 1)=_
    rw [hpA]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot RecoveryColdTablesAmbient.slots
      RecoveryColdTablesAmbient.slots_injective]
    rfl
  have h270 : H 270=1 := by
    apply (lowH 270).trans
    change h (RecoveryColdTablesAmbient.slots 1)=_
    rw [hpH]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot RecoveryColdTablesAmbient.slots
      RecoveryColdTablesAmbient.slots_injective]
    rfl
  have a274 : A 274=CompareMachine.word m := by
    apply (lowT 274).trans
    change a (RecoveryColdTablesAmbient.slots 7)=_
    rw [hpA]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot RecoveryColdTablesAmbient.slots
      RecoveryColdTablesAmbient.slots_injective]
    rfl
  have h274 : H 274=1 := by
    apply (lowH 274).trans
    change h (RecoveryColdTablesAmbient.slots 7)=_
    rw [hpH]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot RecoveryColdTablesAmbient.slots
      RecoveryColdTablesAmbient.slots_injective]
    rfl
  refine ⟨n,innerBits,m,outerBits,hn,hm,?_,?_,?_,?_,?_,?_⟩
  · funext j
    fin_cases j
    · exact a10
    · exact a2
    · exact a1
    · exact a24
    · exact a271
    · exact a275
    · exact a14
    · exact a21
    · exact a270
    · exact a274
    · exact a16
  · funext j
    fin_cases j
    · exact h10
    · exact h2
    · exact h1
    · exact h24
    · exact h271
    · exact h275
    · exact h14
    · exact h21
    · exact h270
    · exact h274
    · exact h16
  · rw [hA]
    simp only [RecoveryColdMarker.stage6,RecoveryColdMarker.put,Function.update_self]
  · rw [hA]
    simp [RecoveryColdMarker.stage6,RecoveryColdMarker.stage5,RecoveryColdMarker.stage4,
      RecoveryColdMarker.stage3,RecoveryColdMarker.stage2,RecoveryColdMarker.stage1,
      RecoveryColdMarker.put,RecoveryColdMarker.lift,Fin.addCases]
  · rw [hH]; rfl
  · rw [hH]; rfl

end NearCubicWires.RepairOrdinary.RecoveryColdCompact

