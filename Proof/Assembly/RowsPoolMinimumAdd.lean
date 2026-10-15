import Proof.Assembly.RowsPoolMagnitude

/-! The actual live-mask bit selects addition of the already produced
negative part. No signed field is reparsed and no magnitude is unary. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolMinimum
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def addSlots : Fin 5→Fin 20:=![11,14,15,16,17]
theorem add_injective : Function.Injective addSlots:=by decide
noncomputable def addProgram:=RecoveryFocus.machine addSlots MatrixScoreAccumulate.machine
def probe : Machine 20 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def sizes : Fin 2→ℕ:=![1,13]
noncomputable def programs : (j : Fin 2)→Machine 20 (sizes j)
  | ⟨0,_⟩=>probe
  | ⟨1,_⟩=>addProgram
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (bits : Fin 20→Bool) : Option (Fin 2):=
  if j=0 ∧ bits 13=true then some 1 else none
noncomputable def choice:=RecoveryCalls.machine sizes programs 0 next
def budget (w : ℕ):=12*w+15
def addInput (C w x a : ℕ) : Fin 5→List Bool:=
  ![MatrixScoreWeight.scalar C w x,MatrixScoreWeight.scalar C w a,
    MatrixScoreWeight.zeros C,MatrixScoreWeight.zeros C,MatrixScoreWeight.zeros C]
def addOutput (C w x a : ℕ) : Fin 5→List Bool:=
  ![MatrixScoreWeight.scalar C w x,MatrixScoreWeight.scalar C w (x+a),
    MatrixScoreWeight.scalar C w (x+a),MatrixScoreWeight.zeros C,MatrixScoreWeight.zeros C]
noncomputable def added (C w x a : ℕ) (live : Bool) (A : Fin 20→List Bool):=
  if live then install addSlots A (addOutput C w x a) else A

theorem add_run (C w x a : ℕ) (H : Fin 20→ℕ) (A : Fin 20→List Bool)
    (hc : 4*w+3≤C) (hfit : x+a<2^w)
    (hh : ∀ j,H (addSlots j)=0) (ht : ∀ j,A (addSlots j)=addInput C w x a j) :
    Step addProgram (12*w+13) H A H (install addSlots A (addOutput C w x a)) := by
  have actual:Step MatrixScoreAccumulate.machine (12*w+13) (fun _=>0)
      (addInput C w x a) (fun _=>0) (addOutput C w x a):=
    Step.of_ready (MatrixScoreWeight.padded_accumulate C w x a hc hfit)
  have h:=actual.focus addSlots add_injective H A
  have headsEq:dockH addSlots H (fun _=>0)=H:=by
    funext i
    cases hp:RecoveryFocus.pick addSlots i with
    | none=>simp [dockH,hp]
    | some j=>
      have he:=RecoveryFocus.slot_of_pick addSlots hp
      simp only [dockH,hp]
      exact (hh j).symm.trans (congrArg H he)
  exact h.congr_in headsEq (install_existing _ _ _ ht) |>.congr headsEq rfl

theorem probe_run (H : Fin 20→ℕ) (A : Fin 20→List Bool) : Step probe 0 H A H A:=by
  obtain ⟨r,hr,hf,_⟩:=(Timed.refl probe (⟨0,H,A⟩ : Configuration 20 1)).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem choice_run (C w x a : ℕ) (H : Fin 20→ℕ) (A : Fin 20→List Bool) (live : Bool)
    (hc : 4*w+3≤C) (hfit : x+a<2^w)
    (hh : ∀ j,H (addSlots j)=0) (ht : ∀ j,A (addSlots j)=addInput C w x a j)
    (hl : readTapeBit (A 13) (H 13)=live) :
    Step choice (budget w) H A H (added C w x a live A):=by
  obtain ⟨p,hp,ph,pt,_⟩:=probe_run H A
  have hp':runFrom (programs 0) 0 ⟨(programs 0).start,H,A⟩=some p:=hp
  cases live with
  | false=>
    obtain ⟨n,hn,timed⟩:=stop_receipt sizes programs 0 next 0 0 _ p hp' (by
      change (if (0 : Fin 2)=0 ∧ readTapeBit (p.final.tapes 13) (p.final.heads 13)=true
        then some 1 else none)=none
      rw [pt,ph,hl]
      rfl)
    obtain ⟨r,hr,rf,rs⟩:=timed.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hb:n≤budget w:=by unfold budget;omega
    have more:=runFrom_moreFuel choice n (budget w-n) _ r hr
    rw [Nat.add_sub_of_le hb] at more
    refine ⟨r,more,?_,?_,rs.le.trans hb⟩
    · rw [rf];exact ph
    · rw [rf];exact pt
  | true=>
    obtain ⟨n,hn,first⟩:=call_receipt sizes programs 0 next 0 1 0 _ p hp' (by
      change (if (0 : Fin 2)=0 ∧ readTapeBit (p.final.tapes 13) (p.final.heads 13)=true
        then some 1 else none)=some 1
      rw [pt,ph,hl]
      rfl)
    rw [ph,pt] at first
    obtain ⟨r,hr,rh,rt,_⟩:=add_run C w x a H A hc hfit hh ht
    obtain ⟨m,hm,last⟩:=stop_receipt sizes programs 0 next 1 (12*w+13) _ r hr (by
      simp [next])
    obtain ⟨all,ha,hf,hs⟩:=(first.trans last).run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hb:n+m≤budget w:=by unfold budget;omega
    have more:=runFrom_moreFuel choice (n+m) (budget w-(n+m)) _ all ha
    rw [Nat.add_sub_of_le hb] at more
    refine ⟨all,more,?_,?_,hs.le.trans hb⟩
    · rw [hf];exact rh
    · rw [hf];exact rt

theorem added_accumulator (C w x a : ℕ) (live : Bool) (A : Fin 20→List Bool)
    (ha : A 14=MatrixScoreWeight.scalar C w a) :
    added C w x a live A 14=MatrixScoreWeight.scalar C w (a+if live then x else 0):=by
  cases live with
  | false=>simpa [added] using ha
  | true=>
    change install addSlots A (addOutput C w x a) (addSlots 1)=_
    rw [install_slot addSlots add_injective]
    simp [addOutput,Nat.add_comm]

theorem added_other (C w x a : ℕ) (live : Bool) (A : Fin 20→List Bool) (i : Fin 20)
    (hi : ∀ j,addSlots j≠i) : added C w x a live A i=A i:=by
  cases live
  · rfl
  · exact install_other addSlots A _ i hi

end NearCubicWires.RepairOrdinary.CloseoutRowsPoolMinimum
