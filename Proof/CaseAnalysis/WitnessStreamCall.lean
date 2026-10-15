import Proof.CaseAnalysis.WitnessSelectedOracle
import Proof.Hierarchy.HierarchyStreamLayout
import Proof.Amplification.RecoveryFocusDock

/-! One use of the existing complete selected-PCP stream producer. Its
three inputs alias retained source fields and its workspace alone is fresh. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.StreamCall
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old {t : ℕ} (i : Fin t) : Fin (t+48):=i.castAdd 48
def slots {t : ℕ} (fields : Fin 3→Fin t) (i : Fin 48) : Fin (t+48):=
  if i.val=0 then old (fields 0) else if i.val=13 then old (fields 1)
  else if i.val=14 then old (fields 2) else i.natAdd t

theorem old_injective (t : ℕ) : Function.Injective (@old t):=by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin (t+48)=>i.val) h)

theorem slots_injective {t : ℕ} (fields : Fin 3→Fin t) (hf : Function.Injective fields) :
    Function.Injective (slots fields):=by
  have h01:(fields 0).val≠(fields 1).val:=fun h=>(by decide : (0 : Fin 3)≠1) (hf (Fin.ext h))
  have h02:(fields 0).val≠(fields 2).val:=fun h=>(by decide : (0 : Fin 3)≠2) (hf (Fin.ext h))
  have h12:(fields 1).val≠(fields 2).val:=fun h=>(by decide : (1 : Fin 3)≠2) (hf (Fin.ext h))
  have h0:=(fields 0).isLt
  have h1:=(fields 1).isLt
  have h2:=(fields 2).isLt
  intro a b he
  have hv:=congrArg Fin.val he
  dsimp only [slots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> apply Fin.ext <;> omega

def input {t : ℕ} (base : Fin t→List Bool) : Fin (t+48)→List Bool:=
  Fin.addCases base (fun _=>[])
def machine {t : ℕ} (fields : Fin 3→Fin t):=RecoveryFocus.machine (slots fields) Streams.machine

theorem input_old {t : ℕ} (base : Fin t→List Bool) (i : Fin t) : input base (old i)=base i:=by
  simp only [input,old,Fin.addCases_left]

theorem input_local {t : ℕ} (fields : Fin 3→Fin t) (base : Fin t→List Bool)
    (p : RawProjectionPCP) (R Q : ℕ) (hs : base (fields 0)=p.word)
    (hr : base (fields 1)=List.replicate R true) (hq : base (fields 2)=List.replicate Q true)
    (i : Fin 48) : input base (slots fields i)=Streams.input p R Q i:=by
  rw [Streams.input_literal]
  by_cases h0:i.val=0
  · have he:i=0:=Fin.ext h0
    subst i
    simpa [slots,input_old] using hs
  by_cases h13:i.val=13
  · have he:i=13:=Fin.ext h13
    subst i
    simpa [slots,input_old] using hr
  by_cases h14:i.val=14
  · have he:i=14:=Fin.ext h14
    subst i
    simpa [slots,input_old] using hq
  simp only [slots,h0,h13,h14,if_false,input,Fin.addCases_right,Fin.ext_iff]
  change []=(if i.val=0 then _ else if i.val=13 then _ else if i.val=14 then _ else [])
  rw [if_neg h0,if_neg h13,if_neg h14]

theorem outside {t : ℕ} (fields : Fin 3→Fin t) (i : Fin t)
    (h0:i≠fields 0) (h1:i≠fields 1) (h2:i≠fields 2) : ∀ j,slots fields j≠old i:=by
  have h0':i.val≠(fields 0).val:=fun h=>h0 (Fin.ext h)
  have h1':i.val≠(fields 1).val:=fun h=>h1 (Fin.ext h)
  have h2':i.val≠(fields 2).val:=fun h=>h2 (Fin.ext h)
  intro j hj
  have hv:=congrArg Fin.val hj
  dsimp only [slots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

structure Fields {t s : ℕ} (fields : Fin 3→Fin t) (p : RawProjectionPCP) (R Q : ℕ)
    (cfg : Configuration (t+48) s) : Prop where
  query : cfg.tapes (slots fields 29)=QueryBytes.framedCodes (normalizedRows p R Q).flatten
  queryHead : cfg.heads (slots fields 29)=0
  queryCount : cfg.tapes (slots fields 25)=CompareMachine.word (R*Q)
  queryCountHead : cfg.heads (slots fields 25)=1
  clause : cfg.tapes (slots fields 38)=DedupBytes.fields p
  clauseHead : cfg.heads (slots fields 38)=0
  clauseCount : cfg.tapes (slots fields 46)=CompareMachine.word (Codec.clauses p).length
  clauseCountHead : cfg.heads (slots fields 46)=1

theorem call_run {t : ℕ} (fields : Fin 3→Fin t) (hf : Function.Injective fields)
    (base : Fin t→List Bool) (p : RawProjectionPCP) (R Q : ℕ)
    (hs : base (fields 0)=p.word) (hr : base (fields 1)=List.replicate R true)
    (hq : base (fields 2)=List.replicate Q true) (hR : p.width  ≤  R) (hQ : p.queries  ≤  Q) :
    ∃ actual,run (machine fields) (Streams.budget p R Q) (input base)=some actual ∧
      actual.steps  ≤  Streams.budget p R Q ∧ Fields fields p R Q actual.final ∧
      (∀ i,i≠fields 0 → i≠fields 1 → i≠fields 2 →
        actual.final.heads (old i)=0 ∧ actual.final.tapes (old i)=base i):=by
  obtain ⟨r,hrun,rs,rq,rqc,rc,rcc,rqh,rqch,rch,rcch⟩:=Streams.streams_run p R Q hR hQ
  obtain ⟨a,ha,_,asteps,ah,atape,away⟩:=RecoveryFocus.dock (slots fields) (slots_injective fields hf)
    Streams.machine (Streams.budget p R Q) (fun _=>0) (input base)
    (initialConfiguration Streams.machine (Streams.input p R Q)) (by intro i;rfl)
    (input_local fields base p R Q hs hr hq) r hrun
  refine ⟨a,ha,asteps.trans_le rs,⟨(atape 29).trans rq,(ah 29).trans rqh,
    (atape 25).trans rqc,(ah 25).trans rqch,(atape 38).trans rc,(ah 38).trans rch,
    (atape 46).trans rcc,(ah 46).trans rcch⟩,?_⟩
  intro i h0 h1 h2
  obtain ⟨hh,ht⟩:=away (old i) (outside fields i h0 h1 h2)
  exact ⟨hh,ht.trans (input_old base i)⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.StreamCall
