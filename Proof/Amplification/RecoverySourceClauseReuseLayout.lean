import Proof.Amplification.RecoverySourceClausePadded
import Proof.Hierarchy.CompetitorFieldEmit
import Proof.Amplification.RecoveryScratchErase

/-! Physical reusable layout for the original PCP source clause. The source
and address streams are retained; the formula keeps its append cursor. -/
namespace NearCubicWires.RepairSource.RecoverySourceClauseReuse
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (i : Fin 276) : Fin 280 := i.castAdd 4
theorem native_injective : Function.Injective nativeSlots := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 280=>i.val) h)
def scratch (i : Fin 274) : Fin 276 :=
  ⟨if i.val<159 then i.val else if i.val<271 then i.val+1 else i.val+2, by
    have hi:=i.isLt; split_ifs <;> omega⟩
theorem scratch_injective : Function.Injective scratch := by
  intro a b h
  have hv:=congrArg Fin.val h
  apply Fin.ext
  dsimp [scratch] at hv
  split_ifs at hv <;> omega
theorem scratch_work (i : Fin 274) : RecoverySourceClauseLoad.work (scratch i) := by
  constructor <;> intro h
  all_goals have hv:=congrArg Fin.val h
  all_goals dsimp [scratch] at hv; split_ifs at hv <;> omega

def eraseSlots : Fin 276→Fin 280 :=
  Fin.addCases (m:=275) (n:=1) (motive:=fun _=>Fin 280)
    (Fin.addCases (m:=274) (n:=1) (motive:=fun _=>Fin 280)
      (fun j=>nativeSlots (scratch j)) (fun _=>278)) (fun _=>279)
theorem erase_injective : Function.Injective eraseSlots := by
  intro a b
  refine Fin.addCases (m:=275) (n:=1) (fun a=>?_) (fun a=>?_) a
  all_goals refine Fin.addCases (m:=275) (n:=1) (fun b=>?_) (fun b=>?_) b
  · refine Fin.addCases (m:=274) (n:=1) (fun a=>?_) (fun a=>?_) a
    all_goals refine Fin.addCases (m:=274) (n:=1) (fun b=>?_) (fun b=>?_) b
    · intro h
      simp only [eraseSlots,Fin.addCases_left] at h
      exact congrArg (fun i : Fin 274=>(i.castAdd 1).castAdd 1)
        (scratch_injective (native_injective h))
    · intro h
      simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right] at h
      have hv:=congrArg (fun i : Fin 280=>i.val) h
      change (scratch a).val=278 at hv
      have hi:=(scratch a).isLt; omega
    · intro h
      simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right] at h
      have hv:=congrArg (fun i : Fin 280=>i.val) h
      change 278=(scratch b).val at hv
      have hi:=(scratch b).isLt; omega
    · intro _h
      have he : a=b := Subsingleton.elim _ _
      subst b; rfl
  · refine Fin.addCases (m:=274) (n:=1) (fun a=>?_) (fun a=>?_) a
    · intro h
      simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right] at h
      have hv:=congrArg (fun i : Fin 280=>i.val) h
      change (scratch a).val=279 at hv
      have hi:=(scratch a).isLt; omega
    · intro h
      simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right] at h
      have hv:=congrArg (fun i : Fin 280=>i.val) h
      change 278=279 at hv; omega
  · refine Fin.addCases (m:=274) (n:=1) (fun b=>?_) (fun b=>?_) b
    · intro h
      simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right] at h
      have hv:=congrArg (fun i : Fin 280=>i.val) h
      change 279=(scratch b).val at hv
      have hi:=(scratch b).isLt; omega
    · intro h
      simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right] at h
      have hv:=congrArg (fun i : Fin 280=>i.val) h
      change 279=278 at hv; omega
  · intro _h
    have he : a=b := Subsingleton.elim _ _
    subst b; rfl

def heads (sourcePosition outputPosition : Nat) (i : Fin 280) :=
  if i.val=272 then sourcePosition else if i.val=276 then outputPosition else 0
def data (source address out : List Bool) (cap : Nat) (i : Fin 280) :=
  if i.val=159 then address else if i.val=272 then source else if i.val=276 then out
  else if i.val=278 then List.replicate cap true
  else if i.val=279 then List.replicate (cap+1) false else List.replicate cap false
noncomputable def first := RecoveryFocus.machine nativeSlots RecoverySourceClauseLoad.machine
noncomputable def appendMachine := CompetitorFieldEmit.program (262 : Fin 280) 276 277
noncomputable def prefixMachine := Composition.machine first appendMachine
noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 274)
noncomputable def machine := Composition.machine prefixMachine eraseMachine

theorem outside_native (i : Fin 280) (hi : 276 ≤ i.val) : ∀ j,nativeSlots j≠i := by
  intro j h
  have hv:=congrArg (fun k : Fin 280=>k.val) h; have hj:=j.isLt
  change j.val=i.val at hv
  omega

theorem native_input (pre : List Bool) (codes : Fin 3→List Bool) (suffix address out : List Bool)
    (cap : Nat) (j : Fin 276) :
    heads pre.length out.length (nativeSlots j)=RecoverySourceClauseLoad.heads pre j ∧
    data (RecoverySourceClauseRead.source pre codes suffix) address out cap (nativeSlots j)=
      (ZeroPadding.config (RecoverySourceClauseLoad.caps cap)
        ⟨RecoverySourceClauseLoad.machine.start,RecoverySourceClauseLoad.heads pre,
          RecoverySourceClauseLoad.input pre codes suffix address⟩).tapes j := by
  have hn276 : j.val≠276 := by have hj:=j.isLt; omega
  have hn278 : j.val≠278 := by have hj:=j.isLt; omega
  have hn279 : j.val≠279 := by have hj:=j.isLt; omega
  constructor
  · simp only [heads,nativeSlots,Fin.val_castAdd,RecoverySourceClauseLoad.heads,hn276,ite_false]
  · by_cases h159 : j.val=159
    · have he : j=159 := Fin.ext h159
      subst j
      exact (ZeroPadding.pad_zero _).symm
    by_cases h272 : j.val=272
    · have he : j=272 := Fin.ext h272
      subst j
      exact (ZeroPadding.pad_zero _).symm
    have hw : RecoverySourceClauseLoad.work j :=
      ⟨fun he=>h159 (congrArg Fin.val he),fun he=>h272 (congrArg Fin.val he)⟩
    simp only [data,nativeSlots,Fin.val_castAdd,h159,h272,hn276,hn278,hn279,ite_false,
      ZeroPadding.config,RecoverySourceClauseLoad.caps,hw,ite_true,
      RecoverySourceClauseLoad.input,ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]

end NearCubicWires.RepairSource.RecoverySourceClauseReuse
