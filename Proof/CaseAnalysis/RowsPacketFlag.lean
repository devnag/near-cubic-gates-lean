import Proof.CaseAnalysis.RowsPacketIndependent

/-! The packet flag is consumed by one actual transition. It distinguishes
zero monomials from one empty monomial even when the gate pool is empty. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPacketFlag
open LocalBitMultitape RecoveryExecution CloseoutRowsBankPacket
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine {t : ℕ} (source : Fin t) : Machine t 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q != 0
  rule := fun q bits=>if q=0 then
    some ⟨if bits source then 1 else 2,fun _=>none,
      fun i=>if i=source then .right else .stay⟩ else none

theorem flag_step {t : ℕ} (source : Fin t) (hh : Fin t→ℕ)
    (tt : Fin t→List Bool) (b : Bool) (hb : readTapeBit (tt source) (hh source)=b) :
    step (machine source) ⟨0,hh,tt⟩=
      some ⟨if b then 1 else 2,Function.update hh source (hh source+1),tt⟩ := by
  simp only [step,machine,Configuration.scanned,hb,↓reduceIte,Option.map_some]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i=source
    · subst i
      simp [applyAction,HeadMove.apply]
    · simp [applyAction,HeadMove.apply,hi]
  · rfl

theorem advanced (out : List Bool) (pos : ℕ) :
    Function.update (heads out pos) (113 : Fin 114) (pos+1)=heads out (pos+1) := by
  funext i
  refine Fin.addCases (m:=113) (n:=1) (fun j=>?_) (fun j=>?_) i
  · have hj : j.castAdd 1≠(113 : Fin 114) := by
      intro he
      have hv:=congrArg (fun a : Fin 114=>a.val) he
      change j.val=113 at hv
      have hlt:=j.isLt
      omega
    simp only [Function.update_of_ne hj,heads,extend,Fin.addCases_left]
  · fin_cases j
    change Function.update (heads out pos) (113 : Fin 114) (pos+1) 113=pos+1
    exact Function.update_self _ _ _

theorem packet_step (C : ℕ) (out pre tail : List Bool) (b : Bool) :
    step (machine (113 : Fin 114))
      ⟨0,heads out pre.length,tapes C out (pre++b::tail)⟩=
      some ⟨if b then 1 else 2,heads out (pre.length+1),tapes C out (pre++b::tail)⟩ := by
  have hs:=flag_step (113 : Fin 114) (heads out pre.length)
    (tapes C out (pre++b::tail)) b (by change readTapeBit (pre++b::tail) pre.length=b; simp [Streaming.read_append])
  change step (machine (113 : Fin 114))
    ⟨0,heads out pre.length,tapes C out (pre++b::tail)⟩=
    some ⟨if b then 1 else 2,Function.update (heads out pre.length) 113 (pre.length+1),
      tapes C out (pre++b::tail)⟩ at hs
  rw [advanced] at hs
  exact hs

end NearCubicWires.RepairOrdinary.CloseoutRowsPacketFlag
