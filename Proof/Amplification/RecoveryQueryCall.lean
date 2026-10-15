import Proof.Amplification.RecoveryQueryAnswer

/-! The query producer and actual oracle answer form one fixed two-node
call graph. The final answer is physically stored, and every graph return
and the literal framed query length are charged. -/
namespace NearCubicWires.RepairSource.RecoveryQueryCall
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pieces {t s : Nat} (p : Machine t s) (answerSlot : Fin t) : Fin 2→Piece t
  | ⟨0,_⟩ => ordinary p
  | ⟨1,_⟩ => RecoveryQueryAnswer.piece answerSlot
  | ⟨n+2,h⟩ => False.elim (by omega)
def next {t s : Nat} (p : Machine t s) (answerSlot : Fin t)
    (j : Fin 2) (_ : Fin (pieces p answerSlot j).states) (_ : Fin t→Bool) : Option (Fin 2) :=
  if j.val=0 then some 1 else none
noncomputable abbrev piece {t s : Nat} (p : Machine t s) (answerSlot : Fin t) :=
  graph (pieces p answerSlot) 0 (next p answerSlot)

noncomputable def start {t s : Nat} (p : Machine t s) (answerSlot : Fin t)
    (tapes : Fin t→List Bool) :=
  controlConfig (RecoveryCalls.code (fun j => (pieces p answerSlot j).states) 0)
    (initialConfiguration p tapes)
noncomputable def stopped {t s : Nat} (p : Machine t s) (answerSlot : Fin t)
    (tapes : Fin t→List Bool) :=
  RecoveryCalls.stopped (fun j => (pieces p answerSlot j).states) (fun _ => 0) tapes

theorem call_trace {t s : Nat} (ports : Ports t) (p : Machine t s)
    (answerSlot : Fin t) (o : Nat→Bool) (budget : Nat)
    (input middle : Fin t→List Bool) (bits padding : List Bool)
    (hr : ClockJoin.ReadyRun p budget input middle)
    (hq : middle ports.queryTape=frame bits++padding) :
    ∃ cost ≤ budget+(frame bits).length+4,
      OrdinaryOracleTrace o (ports.program (piece p answerSlot)) cost
        (start p answerSlot input)
        (stopped p answerSlot
          (RecoveryQueryAnswer.output answerSlot middle (o (CanonicalBinary.bitsValue bits)))) := by
  obtain ⟨r,hrun,ht,hh,hs⟩ := hr
  have body := graph_trace (o:=o) ports (pieces p answerSlot) 0 (next p answerSlot) 0
    (ordinary_trace ports p budget (initialConfiguration p input) r hrun)
  have hhalt := (prefix_of_run p budget (initialConfiguration p input) r hrun).2
  have ret := graph_return o ports (pieces p answerSlot) 0 (next p answerSlot) 0 1
    r.final hhalt (by rfl)
  have he : RecoveryCalls.restarted (pieces p answerSlot 1).machine r.final.heads r.final.tapes=
      (⟨0,fun _ => 0,middle⟩ : Configuration t 4) := by
    apply configuration_ext
    · rfl
    · funext i; exact hh i
    · exact ht
  rw [he] at ret
  have ask := graph_trace ports (pieces p answerSlot) 0 (next p answerSlot) 1
    (RecoveryQueryAnswer.answer_trace ports answerSlot o (fun _ => 0) middle bits padding rfl rfl hq)
  have stop := graph_stop o ports (pieces p answerSlot) 0 (next p answerSlot) 1
    (⟨3,fun _ => 0,RecoveryQueryAnswer.output answerSlot middle
      (o (CanonicalBinary.bitsValue bits))⟩ : Configuration t 4) rfl rfl
  have whole := OrdinaryOracleCompose.trans (OrdinaryOracleCompose.trans
    (OrdinaryOracleCompose.trans body ret) ask) stop
  exact ⟨r.steps+1+((frame bits).length+2)+1,by omega,whole⟩

end NearCubicWires.RepairSource.RecoveryQueryCall
