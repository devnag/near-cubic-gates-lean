import Proof.Assembly.BankFamilyBankInitializer
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RecoveryExecution RepairSource.VerifierDecoding
open RepairRepresentation SourceInterfaces
open NativeRecipes
namespace PaidDriverBank
attribute [local irreducible] P1TopDownPaidPayload.tapes

noncomputable def machine (a : WilliamsAlgorithm) : Machine (FamilyInitGenerator.initTapes a) 39 := by
 unfold FamilyInitGenerator.initTapes
 exact Bank.machine (P1TopDownPaidPayload.tapes a)

theorem entry_heads (a : WilliamsAlgorithm) :
 FamilyInitGenerator.entryH a=
  (by unfold FamilyInitGenerator.initTapes; exact Bank.inputH (P1TopDownPaidPayload.tapes a)) := by
 unfold FamilyInitGenerator.entryH FamilyInitGenerator.initTapes
 apply funext; apply Bank.all (P1TopDownPaidPayload.tapes a)
 · intro i; simp [Bank.inputH,Bank.layout,Bank.pay]
 all_goals intro i; fin_cases i <;>
  simp [Bank.inputH,Bank.layout,Bank.cap,Bank.row,Bank.body,Bank.count,Bank.extra,Bank.source]

theorem entry_tapes (a : WilliamsAlgorithm) (m : FamilyInitGenerator.Scalars) (D : List Bool) :
 FamilyInitGenerator.entry a m D=
  (by unfold FamilyInitGenerator.initTapes; exact Bank.input (P1TopDownPaidPayload.tapes a) m D) := by
 unfold FamilyInitGenerator.entry FamilyInitGenerator.initTapes
 apply funext; apply Bank.all (P1TopDownPaidPayload.tapes a)
 · intro i
   have hn : i.val≠P1TopDownPaidPayload.tapes a+3 := by have hi:=i.isLt;omega
   simp [Bank.input,Bank.layout,Bank.pay,FamilyInitGenerator.sourcePort,Fin.ext_iff,hn]
 all_goals intro i; fin_cases i <;>
  simp [Bank.input,Bank.layout,Bank.cap,Bank.row,Bank.body,Bank.count,Bank.extra,Bank.source,
    FamilyInitGenerator.sourcePort,FamilyInitGenerator.drivers,Bank.values,Fin.ext_iff,Nat.add_assoc]

theorem exit_heads (a : WilliamsAlgorithm) :
 FamilyInitGenerator.exitH a=
  (by unfold FamilyInitGenerator.initTapes; exact Bank.finalH (P1TopDownPaidPayload.tapes a)) := by
 unfold FamilyInitGenerator.exitH FamilyInitGenerator.initTapes
 apply funext; apply Bank.all (P1TopDownPaidPayload.tapes a)
 · intro i
   simp [r_inputH,f_entry,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    P1TopDownPaidReusable.source,P1TopDownPaidReusable.heads,P1TopDownPaidReusableBody.heads,
    P1Closure.RawRowJoin.heads,Bank.finalH,Bank.layout,Bank.pay]
 all_goals intro i; fin_cases i <;>
  simp [r_inputH,f_entry,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    P1TopDownPaidReusable.source,P1TopDownPaidReusable.heads,P1TopDownPaidReusableBody.heads,
    P1Closure.RawRowJoin.heads,Bank.finalH,Bank.layout,
    Bank.cap,Bank.row,Bank.body,Bank.count,Bank.extra,Bank.source]

theorem exit_tapes (a : WilliamsAlgorithm) (m : FamilyInitGenerator.Scalars) (D : List Bool) :
 FamilyInitGenerator.exitT a m D=
  (by unfold FamilyInitGenerator.initTapes; exact Bank.bank (P1TopDownPaidPayload.tapes a) m D 7) := by
 unfold FamilyInitGenerator.exitT FamilyInitGenerator.initTapes
 apply funext; apply Bank.all (P1TopDownPaidPayload.tapes a)
 · intro i
   simp [FamilyInitGenerator.familyBank,P1TopDownPaidReusable.bank,P1TopDownPaidReusableBody.bank,
     P1Closure.RawRowJoin.bank,Bank.bank,Bank.layout,Bank.pay]
 all_goals intro i; fin_cases i <;>
  simp [FamilyInitGenerator.familyBank,P1TopDownPaidReusable.bank,P1TopDownPaidReusableBody.bank,
    P1Closure.RawRowJoin.bank,P1TopDownPaidFamilySum.extra,FamilyInitGenerator.drivers,Bank.values,
    Bank.bank,Bank.layout,Bank.cap,Bank.row,Bank.body,Bank.count,Bank.extra,Bank.source]

attribute [local irreducible] Step Bank.machine

theorem run (a : WilliamsAlgorithm) (m : FamilyInitGenerator.Scalars) (D : List Bool) :
 Step (machine a) (FamilyInitGenerator.initFuel a m) (FamilyInitGenerator.entryH a) (FamilyInitGenerator.entry a m D) (FamilyInitGenerator.exitH a) (FamilyInitGenerator.exitT a m D) := by
 unfold machine FamilyInitGenerator.initTapes
 rw [entry_heads,entry_tapes,exit_heads,exit_tapes]
 dsimp only [id,FamilyInitGenerator.initTapes]
 have h:=Bank.run (P1TopDownPaidPayload.tapes a) m D
 apply h.enlarge
 unfold FamilyInitGenerator.initFuel
 have hsmall : 4*(m.S+m.R+m.B+m.b+m.v+m.N+m.N*m.b)+24≤
   1000*(m.S+m.R+m.B+m.b+m.v+m.N+m.N*m.b+1) := by omega
 exact hsmall.trans (Nat.mul_le_mul_right _ (by omega : 1000≤1000*(r_tapes a+1)))

end PaidDriverBank
