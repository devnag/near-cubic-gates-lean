import Proof.CaseAnalysis.WitnessSelectedCounters
import Proof.CaseAnalysis.PairClockExact
import Proof.CaseAnalysis.ScheduleCompare

/-! Exact oracle-size acceptance on the produced raw arity and size.
The checked pairing-clock identity reuses the existing power producer and
size+1 template, with no decrement, serialization or enlarged cap. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.OracleCap
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

namespace Core
abbrev P (D : ℕ):=DimensionPolynomial.tapes D
abbrev tapes (D : ℕ):=P D+6
def qSlot (D : ℕ) : Fin (tapes D):=⟨0,by dsimp [tapes,P,DimensionPolynomial.tapes];omega⟩
def sizeSlot (D : ℕ) : Fin (tapes D):=⟨1,by dsimp [tapes,P,DimensionPolynomial.tapes];omega⟩
def powerSlots (D : ℕ) (i : Fin (P D)) : Fin (tapes D):=
  if i.val=0 then qSlot D else ⟨2+i.val,by dsimp only [tapes]; omega⟩
def templateSlots (D : ℕ) : Fin 3→Fin (tapes D):=
  ![sizeSlot D,⟨P D+2,by dsimp only [tapes]; omega⟩,⟨P D+3,by dsimp only [tapes]; omega⟩]
def compareSlots (D : ℕ) : Fin 4→Fin (tapes D):=
  ![⟨P D+2,by dsimp only [tapes]; omega⟩,powerSlots D (DimensionPolynomial.rawSlot D),
    ⟨P D+4,by dsimp only [tapes]; omega⟩,⟨P D+5,by dsimp only [tapes]; omega⟩]
def flagSlot (D : ℕ):=compareSlots D 2

theorem power_injective (D : ℕ) : Function.Injective (powerSlots D):=by
  intro a b h
  have hv:=congrArg Fin.val h
  dsimp only [powerSlots,qSlot] at hv
  split_ifs at hv <;> dsimp at hv <;> apply Fin.ext <;> omega

theorem power_raw_val (D : ℕ) : (powerSlots D (DimensionPolynomial.rawSlot D)).val=7+2*D:=by
  simp [powerSlots,DimensionPolynomial.rawSlot,DimensionPolynomial.binarySlots]
  omega

theorem template_val (D : ℕ) (i : Fin 3) :
    (templateSlots D i).val=(![1,P D+2,P D+3] : Fin 3→ℕ) i:=by fin_cases i <;> rfl
theorem compare_val (D : ℕ) (i : Fin 4) :
    (compareSlots D i).val=(![P D+2,7+2*D,P D+4,P D+5] : Fin 4→ℕ) i:=by
  fin_cases i
  · rfl
  · exact power_raw_val D
  · rfl
  · rfl

theorem template_injective (D : ℕ) : Function.Injective (templateSlots D):=by
  intro a b h
  have hv:=congrArg Fin.val h
  rw [template_val,template_val] at hv
  fin_cases a <;> fin_cases b <;> simp [P,DimensionPolynomial.tapes] at hv ⊢

theorem compare_injective (D : ℕ) : Function.Injective (compareSlots D):=by
  intro a b h
  have hv:=congrArg Fin.val h
  rw [compare_val,compare_val] at hv
  fin_cases a <;> fin_cases b <;> simp [P,DimensionPolynomial.tapes,Fin.ext_iff] at hv ⊢ <;> omega

def input (D q size : ℕ) (i : Fin (tapes D)) : List Bool:=
  if i.val=0 then List.replicate q true else if i.val=1 then List.replicate size true else []
def power (D : ℕ):=RecoveryFocus.machine (powerSlots D) (DimensionPolynomial.machine D 1)
def template (D : ℕ):=RecoveryFocus.machine (templateSlots D) (DimensionTemplate.machine true)
def compare (D : ℕ):=RecoveryFocus.machine (compareSlots D) MatrixBucketDimensions.Compare.machine
def machine (D : ℕ):=Composition.machine (Composition.machine (power D) (template D)) (compare D)
def budget (D q size : ℕ):=DimensionPolynomial.budget D 1 q+1+(2*size+8)+1+
  (2*min (size+1) (DimensionPolynomial.value D 1 q)+6)

theorem run (D q size : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine D) (budget D q size) (input D q size) out ∧
      out (qSlot D)=List.replicate q true ∧ out (sizeSlot D)=List.replicate size true ∧
      out (flagSlot D)=[decide (size+1  ≤  DimensionPolynomial.value D 1 q)]:=by
  obtain ⟨po,hp,pq,pvalue,_,_⟩:=DimensionPolynomial.polynomial_run D 1 q (by decide)
  have hpower:=hp.focus (powerSlots D) (power_injective D) (input D q size) (by
    intro i
    by_cases h0:i.val=0
    · simp [powerSlots,h0,qSlot,input,DimensionPolynomial.input]
    · have h21:2+i.val≠1:=by omega
      simp [powerSlots,h0,input,DimensionPolynomial.input,h21])
  let a:=install (powerSlots D) (input D q size) po
  have afresh (i : Fin (tapes D)) (hi:P D+2  ≤  i.val) : a i=[]:=by
    dsimp only [a]
    rw [install_other _ _ _ _ (by
      intro j hj
      have hv:=congrArg Fin.val hj
      dsimp only [powerSlots,qSlot] at hv
      split_ifs at hv <;> dsimp at hv <;> omega)]
    have h0:i.val≠0:=by omega
    have h1:i.val≠1:=by omega
    simp only [input,h0,h1,if_false]
  have aq:a (qSlot D)=List.replicate q true:=by
    change install (powerSlots D) _ _ (powerSlots D ⟨0,by simp [P,DimensionPolynomial.tapes]⟩)=_
    rw [install_slot _ (power_injective D)]
    exact pq
  have asize:a (sizeSlot D)=List.replicate size true:=by
    dsimp only [a]
    rw [install_other _ _ _ _ (by
      intro j hj
      have hv:=congrArg Fin.val hj
      dsimp only [powerSlots,qSlot,sizeSlot] at hv
      split_ifs at hv
      dsimp at hv
      omega)]
    rfl
  have araw:a (powerSlots D (DimensionPolynomial.rawSlot D))=
      List.replicate (DimensionPolynomial.value D 1 q) true:=
    (install_slot _ (power_injective D) _ _ _).trans pvalue
  have htemplate:=(DimensionTemplate.ready true size).focus (templateSlots D) (template_injective D) a (by
    intro i
    fin_cases i
    · exact asize
    · exact afresh _ (by simp [templateSlots])
    · exact afresh _ (by simp [templateSlots]))
  let b:=install (templateSlots D) a (DimensionTemplate.output true size)
  have bq:b (qSlot D)=List.replicate q true:=by
    dsimp only [b]
    rw [install_other _ _ _ _ (by
      intro j hj
      have hv:=congrArg Fin.val hj
      rw [template_val] at hv
      change (![1,P D+2,P D+3] : Fin 3→ℕ) j=0 at hv
      fin_cases j <;> simp at hv)]
    exact aq
  have bsize:b (sizeSlot D)=List.replicate size true:=by
    change install (templateSlots D) _ _ (templateSlots D 0)=_
    rw [install_slot _ (template_injective D)]
    rfl
  have braw:b (powerSlots D (DimensionPolynomial.rawSlot D))=
      List.replicate (DimensionPolynomial.value D 1 q) true:=by
    dsimp only [b]
    rw [install_other _ _ _ _ (by
      intro j hj
      have hv:=congrArg Fin.val hj
      rw [template_val,power_raw_val] at hv
      fin_cases j <;> simp [P,DimensionPolynomial.tapes] at hv <;> omega)]
    exact araw
  have bfresh (i : Fin (tapes D)) (hi:P D+4  ≤  i.val) : b i=[]:=by
    dsimp only [b]
    rw [install_other _ _ _ _ (by
      intro j hj
      have hv:=congrArg Fin.val hj
      rw [template_val] at hv
      fin_cases j <;> simp at hv <;> omega)]
    exact afresh i (by omega)
  have hcompare:=(CloseoutSchedule.RawCompare.compare_cold (size+1) (DimensionPolynomial.value D 1 q)).focus
    (compareSlots D) (compare_injective D) b (by
      intro i
      fin_cases i
      · change install (templateSlots D) _ _ (templateSlots D 1)=_
        rw [install_slot _ (template_injective D)]
        rfl
      · exact braw
      · exact bfresh _ (by simp [compareSlots])
      · exact bfresh _ (by simp [compareSlots]))
  have hall:=ClockJoin.join (Composition.machine (power D) (template D)) (compare D) _ _ _ _ _
    (ClockJoin.join (power D) (template D) _ _ _ _ _ hpower htemplate) hcompare
  have caway (i : Fin (tapes D)) (hi:i.val  ≤  1) : ∀ j,compareSlots D j≠i:=by
    intro j hj
    have hv:=congrArg Fin.val hj
    rw [compare_val] at hv
    fin_cases j <;> simp [P,DimensionPolynomial.tapes] at hv <;> omega
  refine ⟨_,hall,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (caway (qSlot D) (by simp [qSlot]))]
    exact bq
  · rw [install_other _ _ _ _ (caway (sizeSlot D) (by simp [sizeSlot]))]
    exact bsize
  · exact install_slot _ (compare_injective D) _ _ 2
end Core

def degree (G : ℕ):=2^(RecoveryScheduleEnvelope.oracleDepth G)
def machine (G : ℕ):=Core.machine (degree G)
def budget (G q size : ℕ):=Core.budget (degree G) q size

theorem cap_run (G q size : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine G) (budget G q size) (Core.input (degree G) q size) out ∧
      out (Core.qSlot (degree G))=List.replicate q true ∧
      out (Core.sizeSlot (degree G))=List.replicate size true ∧
      out (Core.flagSlot (degree G))=[decide (size  ≤  RecoveryScheduleEnvelope.oracleSizeBound G q)]:=by
  obtain ⟨out,hr,hq,hs,hflag⟩:=Core.run (degree G) q size
  refine ⟨out,hr,hq,hs,?_⟩
  have he : (size+1 ≤ DimensionPolynomial.value (degree G) 1 q) ↔
      size ≤ RecoveryScheduleEnvelope.oracleSizeBound G q :=
    (CloseoutPairClock.size_guard_produced G q size).symm
  simpa only [he] using hflag

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.OracleCap
