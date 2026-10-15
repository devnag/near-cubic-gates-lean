import Proof.Amplification.RecoveryPrefixLoop

/-! Physical initial field allocation for canonical prefix recovery. One
bulk sweep allocates the reusable native workspace, then the accepted literal
printer installs the high sentinel and count one. The capacity driver is an
actual retained input; its input-derived producer belongs to the cold entry. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixInitialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryPrefixBody RecoveryPrefix RecoveryQuery
open RecoveryQueryKernel.Prepare
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scratchSlot (i : Fin 357) : Fin 360 :=
  ⟨if i.val<2 then i.val+1 else i.val+3,by split_ifs <;> have h:=i.isLt <;> omega⟩
def eraseSlots (i : Fin 359) : Fin 360 :=
  ⟨if i.val<2 then i.val+1 else if i.val<357 then i.val+3 else if i.val=357 then 3 else 4,
    by split_ifs <;> have h:=i.isLt <;> omega⟩

theorem erase_injective : Function.Injective eraseSlots := by
  intro a b h
  apply Fin.ext
  have hv := congrArg (fun i : Fin 360=>i.val) h
  dsimp only [eraseSlots] at hv
  split_ifs at hv <;> have ha:=a.isLt <;> have hb:=b.isLt <;> omega

-- A numerical version avoids expanding the nested finite sum in callers.
theorem scratch_val (i : Fin 357) : (scratchSlot i).val=if i.val<2 then i.val+1 else i.val+3 := rfl

def cold (cap payload : Nat) (padding : List Bool) : Fin 360→List Bool :=
  fun i=>if i.val=0 then frame payload.bits++padding else
    if i.val=3 then List.replicate cap true else []
def erased (cap payload : Nat) (padding : List Bool) : Fin 360→List Bool :=
  fun i=>if i.val=0 then frame payload.bits++padding else
    if i.val=3 then List.replicate cap true else
    if i.val=4 then List.replicate (cap+1) false else List.replicate cap false
noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 357)

theorem erase_ready (cap payload : Nat) (padding : List Bool) :
    ClockJoin.ReadyRun eraseMachine (2*cap+4) (cold cap payload padding) (erased cap payload padding) := by
  classical
  have h := (RecoveryScratchErase.erase_ready cap 0 (fun _ : Fin 357=>[]) (by simp)).focus
    eraseSlots erase_injective (cold cap payload padding) (by
      intro i
      refine Fin.addCases (fun x=>?_) (fun x=>?_) i
      · refine Fin.addCases (fun j=>?_) (fun j=>?_) x
        · simp only [eraseSlots,Fin.val_castAdd,cold]
          have hj:=j.isLt
          split_ifs <;> simp_all
        · fin_cases j; rfl
      · fin_cases x; rfl)
  have he : install eraseSlots (cold cap payload padding)
      (fun i=>Fin.addCases (m:=358) (n:=1)
        (fun j=>Fin.addCases (m:=357) (n:=1) (fun _=>List.replicate cap false)
          (fun _=>List.replicate cap true) j)
        (fun _=>List.replicate (max 0 (cap+1)) false) i)=erased cap payload padding := by
    funext i
    by_cases h0 : i.val=0
    · rw [install_other _ _ _ _ (by
        intro j hj
        have hv := congrArg (fun k : Fin 360=>k.val) hj
        dsimp only [eraseSlots] at hv
        split_ifs at hv <;> omega)]
      simp [cold,erased,h0]
    by_cases h3 : i.val=3
    · have hi : i=eraseSlots ((0 : Fin 1).natAdd 357 |>.castAdd 1) := Fin.ext h3
      rw [hi,install_slot _ erase_injective]
      simp only [Fin.addCases_left,Fin.addCases_right]
      simp [eraseSlots,erased]
    by_cases h4 : i.val=4
    · have hi : i=eraseSlots ((0 : Fin 1).natAdd 358) := Fin.ext h4
      rw [hi,install_slot _ erase_injective]
      simp only [Fin.addCases_right]
      simp [eraseSlots,erased]
    let j : Fin 357 := ⟨if i.val<3 then i.val-1 else i.val-3,by split_ifs <;> have hi:=i.isLt <;> omega⟩
    have hi : i=eraseSlots ((j.castAdd 1).castAdd 1) := by
      apply Fin.ext
      change i.val=(if j.val<2 then j.val+1 else if j.val<357 then j.val+3 else if j.val=357 then 3 else 4)
      dsimp only [j]
      split_ifs <;> omega
    rw [hi,install_slot _ erase_injective]
    simp only [Fin.addCases_left]
    rw [←hi]
    simp [erased,h0,h3,h4]
  rw [he] at h
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  exact ⟨r,hr,ht,hh,hs.le⟩

def querySlots : Fin 357→Fin 360 := fun i=>⟨i.val,by have h:=i.isLt; omega⟩
theorem query_injective : Function.Injective querySlots := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 360=>i.val) h)
noncomputable def literal (slot : Fin 357) (word : List Bool) :=
  RecoveryFocus.machine querySlots (literalMachine slot word)

theorem literal_ready (slot : Fin 357) (word : List Bool) (cap : Nat)
    (ambient : Fin 360→List Bool) (hs : slot≠356) (hc : word.length≤cap)
    (hw : ambient (querySlots slot)=List.replicate cap false)
    (hl : ambient 356=List.replicate cap false) :
    ClockJoin.ReadyRun (literal slot word) (2*word.length+2) ambient
      (Function.update ambient (querySlots slot) (ZeroPadding.pad cap word)) := by
  classical
  have h := (RecoveryQueryKernel.Prepare.literal_run slot word cap (ambient ∘ querySlots)
    hs hc hw hl).focus querySlots query_injective ambient (by intro i; rfl)
  have he : install querySlots ambient (Function.update (ambient ∘ querySlots) slot (ZeroPadding.pad cap word))=
      Function.update ambient (querySlots slot) (ZeroPadding.pad cap word) := by
    funext i
    by_cases hi : i=querySlots slot
    · subst i; rw [install_slot _ query_injective]; simp
    by_cases hex : ∃ j,querySlots j=i
    · obtain ⟨j,rfl⟩ := hex
      have hj : j≠slot := by intro he; subst j; exact hi rfl
      rw [install_slot _ query_injective]
      simp [hj,hi]
    · rw [install_other _ _ _ _ (by intro j he; exact hex ⟨j,he⟩)]
      simp [hi]
  rw [he] at h
  exact h

noncomputable def machine := Composition.machine
  (Composition.machine eraseMachine (literal 1 (frame [false,true]))) (literal 2 (frame [true]))
noncomputable def output (cap payload : Nat) (padding : List Bool) :=
  Function.update (Function.update (erased cap payload padding) 1 (ZeroPadding.pad cap (frame [false,true])))
    2 (ZeroPadding.pad cap (frame [true]))

theorem initialize_ready (cap payload : Nat) (padding : List Bool) (hc : 5≤cap) :
    ClockJoin.ReadyRun machine (2*cap+26) (cold cap payload padding) (output cap payload padding) := by
  let middle := Function.update (erased cap payload padding) 1 (ZeroPadding.pad cap (frame [false,true]))
  have hp := literal_ready 1 (frame [false,true]) cap (erased cap payload padding) (by decide) hc rfl rfl
  have hn := literal_ready 2 (frame [true]) cap middle (by decide) (by change 3≤cap; omega)
    (by simp [middle,querySlots,erased]) (by simp [middle,erased])
  have h := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (erase_ready cap payload padding) hp) hn
  exact h

theorem output_inv (cap payload : Nat) (padding : List Bool) (hc : 5≤cap) :
    Inv cap payload (cap+1) [] false padding (output cap payload padding) := by
  constructor
  · simp [output,erased]
  · simp [output]
  · simp [output,queryCount]
  · simp [output,erased]
  · simp [output,erased]
  · intro i hi
    have h1 : RecoveryPrefixUpdate.querySlots i≠1 := by intro he; have hv:=congrArg Fin.val he; change i.val=1 at hv; omega
    have h2 : RecoveryPrefixUpdate.querySlots i≠2 := by intro he; have hv:=congrArg Fin.val he; change i.val=2 at hv; omega
    simp only [Function.comp_apply,output,Function.update_of_ne h1,Function.update_of_ne h2]
    simp [erased,RecoveryPrefixUpdate.querySlots,show i.val≠0 by omega,show i.val≠3 by omega,show i.val≠4 by omega]
  · change List.replicate cap false=ZeroPadding.pad cap [false]
    simp only [ZeroPadding.pad,List.length_singleton]
    rw [show [false]=List.replicate 1 false by rfl,←List.replicate_add]
    congr 1
    omega
  · simp [output,erased]
  · simp [output,erased]

end NearCubicWires.RepairSource.RecoveryPrefixInitialize
