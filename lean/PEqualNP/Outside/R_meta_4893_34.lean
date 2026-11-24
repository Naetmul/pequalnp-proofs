import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Use the affine restriction of R-meta-2625-317, with the output fixed to the
-- last wire. Completing the four missing stars adds twenty gates.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_4893_34
  (affine :
    let D : Finset (Fin 13) := {0,1,3,9}
    let R : List (ℕ × ℕ) := [(7, 904), (13, 2848), (19, 708), (21, 2720), (25, 2656), (37, 2440), (41, 2370), (133, 808)]
    let row := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
      let b := fun (a c : ℕ) (i : Fin 13) =>
        if dual then c.testBit (-(m * i + t)).val else a.testBit (m * i + t).val
      Fin.append (b z.1 z.2) (b z.2 z.1)
    let idx := fun i : Fin 21 => Fin.ofNat 26
      (i.val + if i.val < 1 then 2 else if i.val < 6 then 3 else if i.val < 9 then 4 else 5)
    ∃ B : Circuit, IsAO2 21 B ∧ B.size = 43 ∧ B.output = 63 ∧
      (∀ p l : Fin 13, p ∉ D → (∃ d ∈ D, p = l + d) →
        circuitFun 21 B ((fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l)) ∘ idx) = true) ∧
      ∀ z ∈ R, ∀ m ∈ ([1,3,9] : List (Fin 13)), ∀ t dual,
        circuitFun 21 B (row z m t dual ∘ idx) = false)
  (complete :
    let idx := fun i : Fin 21 => Fin.ofNat 26
      (i.val + if i.val < 1 then 2 else if i.val < 6 then 3 else if i.val < 9 then 4 else 5)
    let hit := fun x : Fin 26 → Bool => ([0,1,3,9] : List (Fin 13)).any fun p =>
      x (Fin.castAdd 13 p) && ([0,1,3,9] : List (Fin 13)).any fun d => x (Fin.natAdd 13 (p-d))
    ∀ B : Circuit, IsAO2 21 B → B.size = 43 → B.output = 63 →
      ∃ C : Circuit, IsAO2 26 C ∧ C.size = 63 ∧ C.output = 88 ∧
        ∀ x, circuitFun 26 C x = (circuitFun 21 B (x ∘ idx) || hit x))
  (encode :
    let run := fun (d : Fin 63 → Bool) (a b : Fin 63 → Fin 89) (x : Fin 26 → Bool) =>
      ((List.ofFn (fun j : Fin 63 => (d j, a j, b j))).foldl
        (fun (w : List Bool) g => w ++ [bif g.1 then w.getD g.2.1.val false && w.getD g.2.2.val false
          else w.getD g.2.1.val false || w.getD g.2.2.val false]) (List.ofFn x)).getD 88 false
    ∀ C : Circuit, IsAO2 26 C → C.size = 63 → C.output = 88 →
      ∃ (d : Fin 63 → Bool) (a b : Fin 63 → Fin 89),
        (∀ j, (a j).val < 26 + j.val ∧ (b j).val < 26 + j.val ∧ a j ≤ b j) ∧
        ∀ x, run d a b x = circuitFun 26 C x) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : Fin (63 : ℕ) → Bool) (x5 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x6 : Fin (63 : ℕ) → Fin (89 : ℕ)),   (∀ (x7 : Fin (63 : ℕ)), ↑(x5 x7) < (26 : ℕ) + ↑x7 ∧ ↑(x6 x7) < (26 : ℕ) + ↑x7 ∧ x5 x7 ≤ x6 x7) ∧     have x7 : (Fin (26 : ℕ) → Bool) → Bool := fun (x7 : Fin (26 : ℕ) → Bool) => (List.foldl (fun (x8 : List Bool) (x9 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) => x8 ++ [bif x9.1 then x8.getD (↑x9.2.1) Bool.false && x8.getD (↑x9.2.2) Bool.false else x8.getD (↑x9.2.1) Bool.false || x8.getD (↑x9.2.2) Bool.false]) (List.ofFn x7) (List.ofFn fun (x8 : Fin (63 : ℕ)) => (x4 x8, x5 x8, x6 x8))).getD (88 : ℕ) Bool.false;     (∀ (x8 x9 : Fin (13 : ℕ)), (∃ x10 ∈ x1, x8 = x9 + x10) → (x7 fun (x11 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x8 ∨ x11 = Fin.natAdd (13 : ℕ) x9)) = Bool.true) ∧ ∀ x8 ∈ x2, ∀ x10 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x12 : Fin (13 : ℕ)) (x13 : Bool), x7 (x3 x8 x10 x12 x13) = Bool.false := by
  intro D R row
  let hit := fun x : Fin 26 → Bool => ([0,1,3,9] : List (Fin 13)).any fun p =>
      x (Fin.castAdd 13 p) && ([0,1,3,9] : List (Fin 13)).any fun d => x (Fin.natAdd 13 (p-d))
  have hPos : ∀ p l : Fin 13, p ∈ D → (∃ d ∈ D, p = l + d) →
      hit (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l)) = true := by
    decide +kernel
  have hNeg : ∀ z ∈ R, ∀ m ∈ ([1,3,9] : List (Fin 13)), ∀ t dual,
      hit (row z m t dual) = false := by
    decide +kernel
  obtain ⟨B,hB,sB,oB,pos,neg⟩ := affine
  obtain ⟨C,hC,sC,oC,simulation⟩ := complete B hB sB oB
  obtain ⟨op,a,b,legal,eval⟩ := encode C hC sC oC
  refine ⟨op,a,b,legal,?_,?_⟩
  · intro p l hp
    let sample : Fin 26 → Bool := fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l)
    refine (eval sample).trans ((simulation sample).trans ?_)
    by_cases inside : p ∈ D
    · rw [Bool.or_eq_true]
      exact Or.inr (hPos p l inside hp)
    · rw [Bool.or_eq_true]
      exact Or.inl (pos p l inside hp)
  · intro z hz m hm t dual
    let sample := row z m t dual
    exact (eval sample).trans ((simulation sample).trans
      (congrArg₂ (· || ·) (neg z hz m hm t dual) (hNeg z hz m hm t dual)))
