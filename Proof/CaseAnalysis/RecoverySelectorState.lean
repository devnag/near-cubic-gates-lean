import Proof.CaseAnalysis.RecoverySelectorEntryPorts

/-! The reusable boundary of the original field-selector loop. Only the
graph, source cursor, saved-reference stack, and value change between calls. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound RepairSource.VerifierDecoding Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stateHeads (out stack : List Bool) (pos : ℕ) : Fin 42→ℕ :=
  Fin.addCases (m:=29) (n:=13) (motive:=fun _=>ℕ) (PCPPNativeClauseBank.heads out)
    ![0,0,0,0,0,0,1,0,pos,0,0,stack.length,0]
def stateData (index base C D value limit : ℕ) (out source stack : List Bool) : Fin 42→List Bool :=
  Fin.addCases (m:=29) (n:=13) (motive:=fun _=>List Bool) (RecoveryBoundedNativeFold.oldData index base C out)
    ![List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false,
      List.replicate C false,List.replicate value true,CompareMachine.word limit,List.replicate C false,
      source,List.replicate C false,List.replicate D false,stack,List.replicate index true]

theorem pad_false (C : ℕ) (hC : 1≤C) : ZeroPadding.pad C [false]=List.replicate C false := by
  have h:=pad_erased C 1 hC
  simpa only [List.replicate_one] using h

theorem entry_heads {n bound : ℕ} (row : Fin (bound+1))
    (start base C D value limit ref : ℕ) (out skipped tail stack : List Bool) :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).heads=
      stateHeads out stack skipped.length := by
  funext i
  fin_cases i <;> rfl

variable {n bound : ℕ} (row : Fin (bound+1))
    (start base C D value limit ref : ℕ) (out skipped tail stack : List Bool)

private theorem entry_tape_0 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 0=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 0 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 ([]))))=([])
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_1 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 1=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 1 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad C (ZeroPadding.pad 0 (List.replicate (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) true))))=(ZeroPadding.pad C (List.replicate (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) true))
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_2 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 2=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 2 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_3 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 3=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 3 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_4 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 4=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 4 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_5 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 5=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 5 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_6 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 6=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 6 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_7 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 7=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 7 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_8 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 8=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 8 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_9 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 9=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 9 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_10 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 10=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 10 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_11 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 11=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 11 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_12 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 12=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 12 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_13 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 13=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 13 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_14 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 14=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 14 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_15 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 15=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 15 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_16 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 16=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 16 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_17 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 17=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 17 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_18 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 18=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 18 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_19 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 19=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 19 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_20 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 20=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 20 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (out))))=(out)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_21 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 21=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 21 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_22 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 22=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 22 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C true))))=(List.replicate C true)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_23 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 23=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 23 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (C+1) false))))=(List.replicate (C+1) false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_24 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 24=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 24 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 ([]))))=([])
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_25 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 25=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 25 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate base true))))=(List.replicate base true)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_26 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 26=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 26 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 ([]))))=([])
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_27 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 27=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 27 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 ([]))))=([])
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_28 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 28=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 28 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 ([]))))=([])
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_29 (hC : 1≤C) :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 29=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 29 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad C (ZeroPadding.pad 0 (ZeroPadding.pad 0 ([false]))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]
  exact pad_false C hC

private theorem entry_tape_30 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 30=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 30 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad C ([])))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]
  rfl

private theorem entry_tape_31 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 31=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 31 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad C (ZeroPadding.pad 0 ([]))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]
  rfl

private theorem entry_tape_32 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 32=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 32 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_33 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 33=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 33 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_34 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 34=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 34 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate value true))))=(List.replicate value true)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_35 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 35=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 35 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (CompareMachine.word limit))))=(CompareMachine.word limit)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_36 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 36=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 36 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad C ([]))))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]
  rfl

private theorem entry_tape_37 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 37=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 37 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (skipped++frame (List.replicate ref true)++tail)))=(skipped++frame (List.replicate ref true)++tail)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_38 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 38=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 38 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false)))=(List.replicate C false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_39 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 39=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 39 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (List.replicate D false))=(List.replicate D false)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_40 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 40=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 40 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (ZeroPadding.pad 0 (stack))=(stack)
  simp only [ZeroPadding.pad_zero]

private theorem entry_tape_41 :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes 41=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack 41 := by
  rw [entry_data_outer,entry_data_join,entry_data_reset,entry_data_reference,entry_data_guard,entry_data_unary]
  change (List.replicate (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) true)=(List.replicate (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) true)
  rfl

theorem entry_tapes (hC : 1≤C) :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes=
      stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit
        out (skipped++frame (List.replicate ref true)++tail) stack := by
  funext i
  fin_cases i
  · exact entry_tape_0 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_1 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_2 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_3 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_4 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_5 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_6 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_7 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_8 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_9 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_10 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_11 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_12 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_13 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_14 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_15 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_16 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_17 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_18 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_19 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_20 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_21 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_22 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_23 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_24 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_25 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_26 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_27 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_28 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_29 row start base C D value limit ref out skipped tail stack hC
  · exact entry_tape_30 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_31 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_32 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_33 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_34 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_35 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_36 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_37 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_38 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_39 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_40 row start base C D value limit ref out skipped tail stack
  · exact entry_tape_41 row start base C D value limit ref out skipped tail stack

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
