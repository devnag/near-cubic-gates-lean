import Proof.Amplification.RecoveryCompactSources

/-! One paid transition positions the two produced count sources for the
reused copying machines. Every new compact-bank tape is physically blank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCompact
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bankInput (a : Fin 338→List Bool) : Fin 493→List Bool :=
  Fin.addCases (m:=338) (n:=155) (motive:=fun _=>List Bool) a (fun _=>[])
def liftedHeads (h : Fin 338→Nat) : Fin 493→Nat :=
  Fin.addCases (m:=338) (n:=155) (motive:=fun _=>Nat) h (fun _=>0)
def bankHeads (h : Fin 338→Nat) (i : Fin 493) : Nat :=
  if i=270 ∨ i=274 then 0 else liftedHeads h i
def bankSlot (j : Fin 11) : Fin 493 := (sourceSlots j).castAdd 155

structure Sources (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) : Prop where
  source : ∀ j,a (bankSlot j)=sourceTapes bits word innerBits outerBits n m j
  source_head : ∀ j,h (bankSlot j)=0
  fresh : ∀ (i : Fin 493),338 ≤ i.val → a i=[]
  fresh_head : ∀ (i : Fin 493),338 ≤ i.val → h i=0
  reset : a 336=List.replicate (RecoveryColdMarker.reset6 bits) false
  spare : a 337=[]
  reset_head : h 336=0
  spare_head : h 337=0

def countBoot : Machine 493 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>none,
    fun i=>if i=270 ∨ i=274 then .left else .stay⟩ else none

theorem count_boot (h : Fin 338→Nat) (a : Fin 338→List Bool)
    (hn : h 270=1) (hm : h 274=1) :
    ∃ r,runFrom countBoot 1 ⟨countBoot.start,liftedHeads h,bankInput a⟩=some r ∧
      r.final.heads=bankHeads h ∧ r.final.tapes=bankInput a ∧ r.steps=1 := by
  let final : Configuration 493 2 := ⟨1,bankHeads h,bankInput a⟩
  have hs : step countBoot ⟨countBoot.start,liftedHeads h,bankInput a⟩=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=270 ∨ i=274
      · rcases hi with rfl|rfl
        · simp [applyAction,bankHeads,liftedHeads,HeadMove.apply,Fin.addCases,hn,final]
        · simp [applyAction,bankHeads,liftedHeads,HeadMove.apply,Fin.addCases,hm,final]
      · simp [applyAction,bankHeads,HeadMove.apply,hi,final]
    · rfl
  obtain ⟨r,hr,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf],ht⟩

theorem bank_sources (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 338→Nat) (a : Fin 338→List Bool)
    (ht : (fun j=>a (sourceSlots j))=sourceTapes bits word innerBits outerBits n m)
    (hh : (fun j=>h (sourceSlots j))=sourceHeads)
    (hr : a 336=List.replicate (RecoveryColdMarker.reset6 bits) false)
    (he : a 337=[]) (hrh : h 336=0) (heh : h 337=0) :
    Sources bits word innerBits outerBits n m (bankHeads h) (bankInput a) := by
  constructor
  · intro j
    simpa only [bankSlot,bankInput,Fin.addCases_left] using congrFun ht j
  · intro j
    fin_cases j <;> simp [bankHeads,bankSlot,sourceSlots,liftedHeads,Fin.addCases]
    all_goals first
      | exact congrFun hh 0
      | exact congrFun hh 1
      | exact congrFun hh 2
      | exact congrFun hh 3
      | exact congrFun hh 4
      | exact congrFun hh 5
      | exact congrFun hh 6
      | exact congrFun hh 7
      | exact congrFun hh 10
  · intro i hi
    simp [bankInput,Fin.addCases,show ¬i.val<338 by omega]
  · intro i hi
    have hne : i≠270 ∧ i≠274 := by
      simp only [ne_eq,Fin.ext_iff]
      change i.val≠270 ∧ i.val≠274
      omega
    simp [bankHeads,hne.1,hne.2,liftedHeads,Fin.addCases,show ¬i.val<338 by omega]
  · exact hr
  · exact he
  · exact hrh
  · exact heh

end NearCubicWires.RepairOrdinary.RecoveryColdCompact
