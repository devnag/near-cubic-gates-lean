import Proof.CaseAnalysis.RowsCircuitBottomCopy

/-! Exact retained-bank identities after the three paid append consumers
and the syntax fold. Scratch and the actual domain never change here. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open LocalBitMultitape RadixSemantics RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem Stored.update_extra {cap core : ℕ} {out source membership : List Bool}
    {description wireCount : ℕ} {flag : Bool} {tapes : Fin 1059→List Bool}
    (hs : Stored cap core out source membership description wireCount flag tapes)
    (j : Fin 10) (value next : List Bool) (newDescription newWires : ℕ) (newFlag : Bool)
    (he : CloseoutRowsCircuitBottom.extra cap next source membership newDescription newWires newFlag=
      Function.update (CloseoutRowsCircuitBottom.extra cap out source membership description wireCount flag) j value) :
    Stored cap core next source membership newDescription newWires newFlag
      (Function.update tapes (j.natAdd 1049) value) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [Function.update_of_ne (by
      intro h;have hv:=congrArg Fin.val h
      have hb:=scratch_small i
      change (scratchSlots i).val=1049+j.val at hv;omega)]
    exact hs.scratch i
  · rw [Function.update_of_ne (by
      intro h;have hv:=congrArg Fin.val h
      change 1035=1049+j.val at hv;omega)]
    exact hs.domain
  · intro i
    rw [he]
    by_cases hi:i=j
    · subst i;rw [Function.update_self,Function.update_self]
    · rw [Function.update_of_ne (by
        intro h;apply hi;apply Fin.ext
        have hv:=congrArg Fin.val h
        change 1049+i.val=1049+j.val at hv;omega),Function.update_of_ne hi]
      exact hs.extra i

theorem Stored.described {cap core : ℕ} {out source membership : List Bool}
    {description wireCount : ℕ} {flag : Bool} {tapes : Fin 1059→List Bool}
    (hs : Stored cap core out source membership description wireCount flag tapes) (d : ℕ) :
    Stored cap core out source membership d wireCount flag
      (Function.update tapes 1050 (List.replicate d true)) := by
  exact hs.update_extra 1 _ out d wireCount flag (by funext i;fin_cases i <;> rfl)

theorem Stored.selected {cap core : ℕ} {out source membership : List Bool}
    {description wireCount : ℕ} {flag : Bool} {tapes : Fin 1059→List Bool}
    (hs : Stored cap core out source membership description wireCount flag tapes) (next : List Bool) (w : ℕ) :
    Stored cap core next source membership description w flag
      (Function.update (Function.update tapes 1049 next) 1051 (List.replicate w true)) := by
  have first:=hs.update_extra 0 next next description wireCount flag (by funext i;fin_cases i <;> rfl)
  exact first.update_extra 2 _ next description w flag (by funext i;fin_cases i <;> rfl)

theorem Stored.flagged {cap core : ℕ} {out source membership : List Bool}
    {description wireCount : ℕ} {flag : Bool} {tapes : Fin 1059→List Bool}
    (hs : Stored cap core out source membership description wireCount flag tapes) (newFlag : Bool) :
    Stored cap core out source membership description wireCount newFlag
      (Function.update tapes 1054 [newFlag]) := by
  exact hs.update_extra 5 _ out description wireCount newFlag (by funext i;fin_cases i <;> rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
