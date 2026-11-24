import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.GenericRejection

-- The search checks incident pairs and the maximal false tests of the plane.
-- If two births were comparable, the earlier one would reach both operands.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_4217_57
  (comparable : ∀ C : Circuit,
    let v (w : ℕ) (p q : Fin 14) := wireVal 14 C w (pairInput p q)
    let quiet (w : ℕ) := v w 0 0 = false ∧ v w 7 7 = false
    let ic := InCone 14 C
    let andGate (j : ℕ) := (gateAt C j).op = .and
    let reaches (a w : ℕ) := 14 + a = w ∨ ic a (w - 14)
    let born (w a : ℕ) := reaches a w ∧ andGate a ∧ quiet (14 + a) ∧ ∃ b : Fin 2, v (opnd C a b) 0 0 = true ∧ v (opnd C a (1 - b)) 7 7 = true
    C.size ≤ 27 → IsAO2 14 C → (∀ w ∈ C.gates, w.inputs.Nodup) →
    RightOnIncidentPairs fanoLines C →
    (∀ X Y, IsMaximalFalse fanoLines X Y → C.eval (incidenceInput X Y) = false) →
    ∀ g a b : ℕ, andGate g → reaches g C.output → v (14 + g) 0 7 = true →
      (∀ i : Fin 2, quiet (opnd C g i)) →
      born (opnd C g 0) a → born (opnd C g 1) b →
      (¬ ∃ k, born (opnd C g 0) k ∧ born (opnd C g 1) k) →
      a = b ∨ ic a b ∨ ic b a)
  (trans : ∀ (n : ℕ) (C : Circuit) (a b c : ℕ),
    InCone n C a b → InCone n C b c → InCone n C a c) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);   have x3 : ℕ → ℕ → Prop := fun (x3 x4 : ℕ) => ((14 : ℕ) + x4 = x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 (x3 - (14 : ℕ))) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x2 ((14 : ℕ) + x4) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 ((14 : ℕ) + x4) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ ∃ (x5 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x4 x5) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (PEqualNP.TopForm.opnd x1 x4 ((1 : Fin (2 : ℕ)) - x5)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;   x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).inputs.Nodup) → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x7 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x8 : Fin (7 : ℕ)) (x9 : Fin (7 : ℕ)), x8 ∈ PEqualNP.CircuitLowerBounds.fanoLines x9 ∧ x7 (Fin.castAdd (7 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (7 : ℕ) x9) = Bool.true)) → ∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → (14 : ℕ) + x8 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x8 (x1.output - (14 : ℕ)) → x2 ((14 : ℕ) + x8) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → (∀ (x12 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x8 x12) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 (PEqualNP.TopForm.opnd x1 x8 x12) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false) → (¬∃ (x13 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x8 (0 : Fin (2 : ℕ))) x13 ∧ x3 (PEqualNP.TopForm.opnd x1 x8 (1 : Fin (2 : ℕ))) x13) → ¬∃ (x14 : ℕ) (x15 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x8 (0 : Fin (2 : ℕ))) x14 ∧ x3 (PEqualNP.TopForm.opnd x1 x8 (1 : Fin (2 : ℕ))) x15 := by
  intro C V born budget shape distinct correct g andG reaches truePair quiet noShared both
  obtain ⟨a, b, left, right⟩ := both
  let input (X Y : Finset (Fin 7)) : Fin 14 → Bool :=
    Fin.append (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
  have eval (X Y : Finset (Fin 7)) :
      C.eval (incidenceInput X Y) = circuitFun 14 C (input X Y) := by
    change C.eval (List.ofFn (fun p : Fin 7 => decide (p ∈ X)) ++
      List.ofFn (fun l : Fin 7 => decide (l ∈ Y))) = C.eval (List.ofFn (input X Y))
    rw [show List.ofFn (input X Y) = _ from List.ofFn_fin_append _ _]
  have points (X Y : Finset (Fin 7)) (p : Fin 7) :
      input X Y (Fin.castAdd 7 p) = decide (p ∈ X) := Fin.append_left _ _ _
  have lines (X Y : Finset (Fin 7)) (l : Fin 7) :
      input X Y (Fin.natAdd 7 l) = decide (l ∈ Y) := Fin.append_right _ _ _
  have yes : RightOnIncidentPairs fanoLines C := by
    intro l p pl
    rw [eval, correct]
    apply decide_eq_true
    refine ⟨p, l, pl, ?_, ?_⟩
    · simp only [points, Finset.mem_singleton, decide_true]
    · simp only [lines, Finset.mem_singleton, decide_true]
  have no (X Y : Finset (Fin 7)) (hn : IsMaximalFalse fanoLines X Y) :
      C.eval (incidenceInput X Y) = false := by
    rw [eval, correct, decide_eq_false_iff_not]
    rintro ⟨p, l, hit, hp, hl⟩
    simp only [points, lines, decide_eq_true_eq] at hp hl
    exact (Finset.disjoint_left.mp (hn.1 l hl)) hit hp
  have cross (u v wl wr : ℕ) (uv : InCone 14 C u v)
      (origin : born wl u) (later : born wr v) : born wr u := by
    have go : InCone 14 C u (wr - 14) := by
      rcases later.1 with h | h
      · have hv : wr - 14 = v := by omega
        exact hv.symm ▸ uv
      · exact trans 14 C u v (wr - 14) uv h
    exact ⟨Or.inr go, origin.2⟩
  have pins (w : Gate) (hw : w ∈ C.gates) : w.inputs.Nodup := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have e : gateAt C i = C.gates[i] := List.getD_eq_getElem _ _ hi
    rw [← e]
    exact distinct i hi
  have cases := comparable C budget shape pins yes no g a b andG reaches truePair quiet
    (by simpa only [born, and_assoc] using left)
    (by simpa only [born, and_assoc] using right)
    (by simpa only [born, and_assoc] using noShared)
  rcases cases with e | ab | ba
  · exact noShared ⟨a, left, e.symm ▸ right⟩
  · exact noShared ⟨a, left, cross a b _ _ ab left right⟩
  · exact noShared ⟨b, cross b a _ _ ba right left, right⟩
