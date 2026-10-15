import Proof.PCP.PCPTripleGlobalLayout

/-! State-independent data contract of the checked whole cold triple loop.
The enclosing physical dock need not reduce either large finite controller. -/
namespace NearCubicWires.RepairOrdinary.PCPTripleGlobal
open LocalBitMultitape PCPSerializerReuse
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def finalHeads (pos appendPos : ℕ) : Fin 133 → ℕ :=
  Fin.addCases (m:=132) (n:=1) (bodyHeads pos appendPos) (fun _ => 1)
def finalTapes (E M : ℕ) (source out : List Bool) : Fin 133 → List Bool :=
  Fin.addCases (m:=132) (n:=1) (bodyTapes E (E+1) source 3 out) (fun _ => CompareMachine.word M)

theorem cfg_heads (E M pos : ℕ) (source out : List Bool) :
    (PCPTripleLoop.cfg 3 E source pos out M 1).heads=finalHeads pos out.length := by
  simp only [PCPTripleLoop.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config]
  rw [bodyEntry_heads]
  rfl
theorem cfg_tapes (E M pos : ℕ) (source out : List Bool) :
    (PCPTripleLoop.cfg 3 E source pos out M 1).tapes=finalTapes E M source out := by
  simp only [PCPTripleLoop.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config]
  rw [bodyEntry_tapes]
  rfl

theorem cold_data_run (pre : List Bool) (groups : List (List (List Bool))) (suffix : List Bool)
    (hthree : ∀ fields∈groups,fields.length=3) :
    ∃ r,runFrom PCPTripleCold.machine
      (PCPTripleCold.budget (envelope (PCPTripleLoop.stream groups).length) groups.length)
      (PCPTripleCold.entry (envelope (PCPTripleLoop.stream groups).length) groups.length
        (pre++PCPTripleLoop.stream groups++suffix) pre.length [])=some r ∧
      r.final.heads=finalHeads (pre.length+(PCPTripleLoop.stream groups).length) (PCPTripleLoop.encoded groups).length ∧
      r.final.tapes=finalTapes (envelope (PCPTripleLoop.stream groups).length) groups.length
        (pre++PCPTripleLoop.stream groups++suffix) (PCPTripleLoop.encoded groups) ∧
      r.steps ≤ PCPTripleCold.budget (envelope (PCPTripleLoop.stream groups).length) groups.length := by
  have hE : 4 ≤ envelope (PCPTripleLoop.stream groups).length := by
    have hpos : 1 ≤ ((PCPTripleLoop.stream groups).length+1)^12 := Nat.one_le_pow 12 _ (by omega)
    unfold envelope
    omega
  obtain ⟨r,hr,rh,rt,rs⟩ := PCPTripleCold.cold_run pre groups suffix []
    (envelope (PCPTripleLoop.stream groups).length) hE hthree (PCPTripleLoop.global_covers groups)
  rw [cfg_heads,List.nil_append] at rh
  rw [cfg_tapes,List.nil_append] at rt
  exact ⟨r,hr,rh,rt,rs⟩

end NearCubicWires.RepairOrdinary.PCPTripleGlobal
