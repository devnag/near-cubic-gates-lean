import Proof.CaseAnalysis.RecoveryRowPacketStages

/-! The complete fixed fifteen-field original row prototype printer.
Every field is generated from its actual retained scalar; the next append
cursor and all source/reset fields are returned exactly. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
open LocalBitMultitape Composition RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def stage0:=paddedHeader 6 0 false
noncomputable def stage1:=scalarField (scalarPort 0) false
noncomputable def stage2:=scalarField (scalarPort 1) true
noncomputable def stage3:=paddedHeader 6 0 false
noncomputable def stage4:=paddedHeader 8 0 false
noncomputable def stage5:=paddedHeader 7 0 false
noncomputable def stage6:=paddedHeader 6 0 false
noncomputable def stage7:=paddedHeader 2 9 true
noncomputable def stage8:=write (frame (CompareMachine.word 6))
noncomputable def stage9:=write (frame (CompareMachine.word 5))
noncomputable def stage10:=scalarField (scalarPort 3) true
noncomputable def stage11:=write (frame (List.replicate 6 true))
noncomputable def stage12:=scalarField (scalarPort 7) false
noncomputable def stage13:=scalarField (scalarPort 4) true
noncomputable def stage14:=scalarField (scalarPort 5) true
noncomputable def joined0:=stage0
noncomputable def joined1:=Composition.machine joined0 stage1
noncomputable def joined2:=Composition.machine joined1 stage2
noncomputable def joined3:=Composition.machine joined2 stage3
noncomputable def joined4:=Composition.machine joined3 stage4
noncomputable def joined5:=Composition.machine joined4 stage5
noncomputable def joined6:=Composition.machine joined5 stage6
noncomputable def joined7:=Composition.machine joined6 stage7
noncomputable def joined8:=Composition.machine joined7 stage8
noncomputable def joined9:=Composition.machine joined8 stage9
noncomputable def joined10:=Composition.machine joined9 stage10
noncomputable def joined11:=Composition.machine joined10 stage11
noncomputable def joined12:=Composition.machine joined11 stage12
noncomputable def joined13:=Composition.machine joined12 stage13
noncomputable def joined14:=Composition.machine joined13 stage14
noncomputable def machine:=joined14
def budget (C F R count Q clauses : ℕ):=
  (paddedBudget false C)+1+(fieldBudget false C)+1+(fieldBudget true F)+1+(paddedBudget false C)+1+(paddedBudget false C)+1+(paddedBudget false C)+1+(paddedBudget false C)+1+(paddedBudget true (R+1))+1+((frame (CompareMachine.word 6)).length)+1+((frame (CompareMachine.word 5)).length)+1+(fieldBudget true count)+1+((frame (List.replicate 6 true)).length)+1+(fieldBudget false (6+F))+1+(fieldBudget true Q)+1+(fieldBudget true clauses)

theorem packet_run (C D F L R count Q clauses B : ℕ) (out : List Bool)
    (H : Fin 88→ℕ) (A : Fin 88→List Bool)
    (h : Loaded (values C F R count Q clauses) B H A) (hfit : 6+F≤C) :
    Appends machine (budget C F R count Q clauses) H A out
      (out++RecoveryBoundedRowReload.word (RecoveryBoundedRowPrototype.fields C D F L R count Q clauses)) := by
  let e:=emitted C F R count Q clauses
  let w0:=out
  let w1:=w0++e 0
  let w2:=w1++e 1
  let w3:=w2++e 2
  let w4:=w3++e 3
  let w5:=w4++e 4
  let w6:=w5++e 5
  let w7:=w6++e 6
  let w8:=w7++e 7
  let w9:=w8++e 8
  let w10:=w9++e 9
  let w11:=w10++e 10
  let w12:=w11++e 11
  let w13:=w12++e 12
  let w14:=w13++e 13
  let w15:=w14++e 14
  have a0:=h.padded_run 6 0 false w0 (by decide) (by change 6≤C;omega)
  have a1:=h.field_run 0 false w1
  have a2:=h.field_run 1 true w2
  have a3:=h.padded_run 6 0 false w3 (by decide) (by change 6≤C;omega)
  have a4:=h.padded_run 8 0 false w4 (by decide) (by change 0≤C;omega)
  have a5:=h.padded_run 7 0 false w5 (by decide) hfit
  have a6:=h.padded_run 6 0 false w6 (by decide) (by change 6≤C;omega)
  have a7:=h.padded_run 2 9 true w7 (by decide) (by change R≤R+1;omega)
  have a8:=write_run (frame (CompareMachine.word 6)) w8 H A
  have a9:=write_run (frame (CompareMachine.word 5)) w9 H A
  have a10:=h.field_run 3 true w10
  have a11:=write_run (frame (List.replicate 6 true)) w11 H A
  have a12:=h.field_run 7 false w12
  have a13:=h.field_run 4 true w13
  have a14:=h.field_run 5 true w14
  have whole:=((((((((((((((a0.join a1).join a2).join a3).join a4).join a5).join a6).join a7).join a8).join a9).join a10).join a11).join a12).join a13).join a14)
  change Appends machine (budget C F R count Q clauses) H A out w15 at whole
  have hw : w15=out++packet C F R count Q clauses := by
    simp only [w15,w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0,e,packet_order,List.append_assoc]
  rw [hw,packet_original C D F L R count Q clauses (by omega)] at whole
  exact whole

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
