import Proof.CaseAnalysis.RowsSupportAppend
import Proof.CaseAnalysis.RowsCircuitBottomRound

/-! One original bottom round with its declared bitmap copied before the
existing erase. The old native record, guards and all old output fields agree
literally with the original round. The added copy has its own paid budget. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
open LocalBitMultitape RadixSemantics ExtDecompositionBatch
open CanonicalWitnessCodec SupplierPipeline CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def supportEmitted (core : ℕ) (keep : Bool) (bits : List Bool) : List Bool:=
  match decodeSupportedNormalizedGate core (value bits) with
  | none=>[]
  | some g=>if keep then frame (CloseoutRowsGateSupport.gateMembers g.support) else []

theorem append_checked (threshold : Bool) (cap core pos memberPos : ℕ)
    (bits native support source membership : List Bool) (D W : ℕ) (flag : Bool)
    (A : Fin 1059 → List Bool)
    (stored : Stored cap core native source membership D W flag A)
    (hflag : readTapeBit (A 1037) 0=passed core bits)
    (hbitmap : ∀ g,decodeSupportedNormalizedGate core (value bits)=some g →
      A 994=ZeroPadding.pad cap (frame (CloseoutRowsGateSupport.gateMembers g.support))) :
    Step (choice threshold) (4*core+5)
      (extend (heads pos memberPos native D W) support.length) (extend A support)
      (extend (heads pos memberPos native D W)
        (support++supportEmitted core (kept threshold membership memberPos) bits).length)
      (extend A (support++supportEmitted core (kept threshold membership memberPos) bits)) := by
  let H:=heads pos memberPos native D W
  have htest:selected threshold (fun i=>readTapeBit (extend A support i)
      (extend H support.length i))=(passed core bits && kept threshold membership memberPos):=by
    change (readTapeBit (A 1037) 0 && (if threshold then readTapeBit (A 1053) memberPos else true))=_
    rw [hflag]
    have members:A 1053=membership:=stored.extra 4
    rw [members]
    rfl
  cases hd:decodeSupportedNormalizedGate core (value bits) with
  | none=>
    have test:selected threshold (fun i=>readTapeBit (extend A support i)
        (extend H support.length i))=false:=by
      rw [htest];simp only [passed,hd,Option.isSome_none,Bool.false_and]
    simpa only [supportEmitted,hd,List.append_nil] using
      (rejected_run threshold (extend H support.length) (extend A support) test).enlarge
        (show 1≤4*core+5 by omega)
  | some g=>
    cases hk:kept threshold membership memberPos with
    | false=>
      have test:selected threshold (fun i=>readTapeBit (extend A support i)
          (extend H support.length i))=false:=by
        rw [htest,hk];simp only [Bool.and_false]
      simpa only [supportEmitted,hd,hk,Bool.false_eq_true,if_false,List.append_nil] using
        (rejected_run threshold (extend H support.length) (extend A support) test).enlarge
          (show 1≤4*core+5 by omega)
    | true=>
      have test:selected threshold (fun i=>readTapeBit (extend A support i)
          (extend H support.length i))=true:=by
        rw [htest,hk];simp only [passed,hd,Option.isSome_some,Bool.and_self]
      have fit:(A 994).length≤cap:=stored.scratch 994
      rw [hbitmap g hd,ZeroPadding.pad_length,frame_length] at fit
      have hlen:(CloseoutRowsGateSupport.gateMembers g.support).length=core:=List.length_ofFn
      rw [hlen] at fit
      have log:A 1057=List.replicate cap false:=stored.extra 8
      simpa only [supportEmitted,hd,hk,if_true] using
        selected_run threshold g.support cap support H A ⟨rfl,rfl⟩ (hbitmap g hd) log
          (by omega) test

noncomputable def prefixMachine (threshold : Bool):=Composition.machine
  (TapeEmbedding.machine 1 (loaded threshold)) (choice threshold)
noncomputable def round (threshold : Bool):=Composition.machine
  (prefixMachine threshold) (TapeEmbedding.machine 1 finish)

theorem round_run (threshold : Bool) (cap core memberPos : ℕ)
    (bits out supports pre tail membership : List Bool) (description wireCount : ℕ) (flag : Bool)
    (hin : 2*bits.length+1≤cap) (hcap : 2*CloseoutRowsGateMeasured.budget bits+4≤cap) :
    Step (round threshold) (12*cap+4*core+40)
      (extend (heads pre.length memberPos out description wireCount) supports.length)
      (extend (data cap core [] out (pre++frame bits++tail) membership description wireCount flag) supports)
      (extend (heads (pre.length+2*bits.length+1) (memberPos+2)
        (out++emitted core (kept threshold membership memberPos) bits)
        (description+descriptionCost core bits)
        (wireCount+wireCost core (kept threshold membership memberPos) bits))
        (supports++supportEmitted core (kept threshold membership memberPos) bits).length)
      (extend (data cap core [] (out++emitted core (kept threshold membership memberPos) bits)
        (pre++frame bits++tail) membership (description+descriptionCost core bits)
        (wireCount+wireCost core (kept threshold membership memberPos) bits) (flag && passed core bits))
        (supports++supportEmitted core (kept threshold membership memberPos) bits)) := by
  let source:=pre++frame bits++tail
  let position:=pre.length+2*bits.length+1
  let output:=out++emitted core (kept threshold membership memberPos) bits
  let desc:=description+descriptionCost core bits
  let wires:=wireCount+wireCost core (kept threshold membership memberPos) bits
  obtain ⟨l,hl,_ls,lh,lt⟩:=load_run cap core memberPos bits out pre tail membership description wireCount flag hin
  obtain ⟨p,hp,_ps,ph,pflag,pstore,pbitmap⟩:=checked_run_retained threshold cap core position memberPos
    bits out source membership description wireCount flag hin hcap
  have base:Step (loaded threshold) (4*bits.length+3+1+(7*cap+12))
      (heads pre.length memberPos out description wireCount)
      (data cap core [] out source membership description wireCount flag)
      (heads position memberPos output desc wires) p.final.tapes:=
    (Step.of_run hl lh lt).seq (Step.of_run hp ph rfl)
  have copy:=append_checked threshold cap core position memberPos bits output supports source membership
    desc wires flag p.final.tapes pstore pflag pbitmap
  obtain ⟨f,hf,fh,ft,_fs⟩:=finish_run cap core position memberPos output source membership desc wires
    flag p.final.tapes (by omega) pstore
  rw [pflag] at ft
  have first:=base.embed (fun _ : Fin 1=>supports.length) (fun _ : Fin 1=>supports)
  have last:Step (TapeEmbedding.machine 1 finish) (2*cap+10)
      (extend (heads position memberPos output desc wires)
        (supports++supportEmitted core (kept threshold membership memberPos) bits).length)
      (extend p.final.tapes (supports++supportEmitted core (kept threshold membership memberPos) bits))
      (extend (heads position (memberPos+2) output desc wires)
        (supports++supportEmitted core (kept threshold membership memberPos) bits).length)
      (extend (data cap core [] output source membership desc wires (flag && passed core bits))
        (supports++supportEmitted core (kept threshold membership memberPos) bits)):=
    (Step.of_run hf fh ft).embed (fun _ : Fin 1=>
      (supports++supportEmitted core (kept threshold membership memberPos) bits).length)
      (fun _ : Fin 1=>supports++supportEmitted core (kept threshold membership memberPos) bits)
  exact ((first.seq copy).seq last).enlarge (by omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
