import HTPILib.Chap6
namespace HTPI.Exercises

/- Section 6.1 -/
-- 1.
theorem Like_Exercise_6_1_1 :
    ∀ (n : Nat), 2 * Sum i from 0 to n, i = n * (n + 1) := by
    by_induc
    · --Base case
      decide
      done
    · --Induction case
      fix n: Nat
      assume ih: 2 * Sum i from 0 to n, i = n * (n + 1)
      show 2 * Sum i from 0 to n + 1, i = (n + 1) * (n + 1 + 1) from
        calc (2 * Sum i from 0 to n + 1, i)
          _ = 2 * ((Sum i from 0 to n, i) + (n + 1)) := by
            rw[sum_from_zero_step]
          _ = 2 * (Sum i from 0 to n, i) + 2 * (n + 1) := by ring
          _ = n * (n + 1) + 2 * (n + 1) := by
            rw [ih]
          _ = (n + 1) * (n + 1 + 1) := by ring
      done

-- 2.
theorem Like_Exercise_6_1_4 :
    ∀ (n : Nat), Sum i from 0 to n, 2 * i + 1 = (n + 1) ^ 2 := by
    by_induc
    · --Base case
      decide
    · --Induction case
      fix n: Nat
      assume ih: Sum i from 0 to n, 2 * i + 1 = (n + 1) ^ 2
      show Sum i from 0 to n + 1, 2 * i + 1 = (n + 1 + 1) ^ 2 from
        calc (Sum i from 0 to n + 1, 2 * i + 1)
          _ = (Sum i from 0 to n, 2 * i + 1) + (2 * (n + 1) + 1) := by
            rw [sum_from_zero_step]
          _ = (n + 1) ^ 2 + (2 * (n + 1) + 1) := by
            rw [ih]
          _ = (n + 1 + 1) ^ 2 := by ring
      done

-- 3.
theorem Exercise_6_1_9a : ∀ (n : Nat), 2 ∣ n ^ 2 + n := by
  by_induc
  · --Base case
    decide
  · --Induction case
    fix n: Nat
    assume ih : 2 ∣ n ^ 2 + n
    define at ih; obtain k ihk from ih; clear ih
    define; exists k + n + 1; ring
    show 2 + n * 3 + n ^ 2 = 2 + n * 2 + k * 2 from
      calc (2 + n * 3 + n ^ 2)
        _ = (2 + n * 2 + (n ^ 2 + n)) := by ring
        _ = (2 + n * 2 + 2 * k) := by rw [ihk]
        _ = (2 + n * 2 + k * 2) := by ring
    done

-- 4.
theorem Exercise_6_1_13 :
    ∀ (a b : Int) (n : Nat), (a - b) ∣ (a ^ n - b ^ n) := by
    fix a; fix b
    by_induc
    · --Base case
      define; exists 0; ring
    · --Induction case
      fix n: Nat
      assume ih; define at ih
      obtain k ihk from ih; clear ih
      define;
      -- a^(n+1) - b^(n+1) = a*(a^n - b^n) + b^n(a - b)
      exists a * k + b ^ n
      show a ^ (n + 1) - b ^ (n + 1) = (a - b) * (a * k + b ^ n) from
        calc (a ^ (n + 1) - b ^ (n + 1))
          _ = a * (a ^ n - b ^ n) + b ^ n * (a - b) := by ring
          _ = a * ((a - b) * k) + b ^ n * (a - b) := by rw [ihk]
          _ = (a - b) * (a * k + b ^ n) := by ring
      done

-- 5.
theorem Exercise_6_1_15 : ∀ n ≥ 10, 2 ^ n > n ^ 3 := by
  by_induc
  · --Base case
    decide
  · --Induction case
    fix n: Nat
    assume ih1 : n ≥ 10
    assume ih2 : 2 ^ n > n ^ 3
    have h1 : n * n ^ 2 >= 10 * n ^ 2 := Nat.mul_le_mul_right (n ^ 2) ih1
    have h2 : n * n >=  10 * n := Nat.mul_le_mul_right n ih1
    show 2 ^ (n + 1) > (n + 1) ^ 3 from
      calc 2 ^ (n + 1)
      _ = 2 * 2 ^ n := by ring
      _ > 2 * n ^ 3 := by linarith
      _ >= n ^ 3 + 10 * n ^ 2 := by linarith
      _ >= n ^ 3 + 3 * n ^ 2 + 70 * n := by linarith
      _ >= n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by linarith
      _ = (n + 1) ^ 3 := by ring
    done

-- 6.
lemma nonzero_is_successor :
    ∀ (n : Nat), n ≠ 0 → ∃ (m : Nat), n = m + 1 := by
    by_induc
    · -- base case
      assume h; contradict h; rfl
    · -- induction case
      fix n: Nat
      assume ih1; assume ih2
      exists n
      done

-- 7.
theorem Exercise_6_1_16a1 :
    ∀ (n : Nat), nat_even n ∨ nat_odd n := by
    by_induc
    · -- base case
      apply Or.inl
      define; exists 0
    · -- induction case
      fix n: Nat
      assume h; by_cases on h
      · -- nat_odd n
        define at h; obtain k hk from h; clear h
        apply Or.inr; define
        exists k; rw [hk]
      · -- nat_even n
        define at h; obtain k hk from h; clear h
        apply Or.inl; define
        exists k + 1; rw [hk]
        ring
      done

-- 8.
--Hint:  You may find the lemma nonzero_is_successor
--from a previous exercise useful, as well as Nat.add_right_cancel.
theorem Exercise_6_1_16a2 :
    ∀ (n : Nat), ¬(nat_even n ∧ nat_odd n) := by
    by_induc
    · --base case
      demorgan
      apply Or.inr
      by_contra h; define at h
      obtain k hk from h; clear h
      simp at hk
    · --induction case
      fix n: Nat
      assume h; demorgan at h
      demorgan
      by_cases on h
      · -- not even n
        apply Or.inr
        by_contra h1; define at h1
        obtain k hk from h1; clear h1
        contradict h; clear h
        define; exists k
        apply Nat.add_right_cancel at hk
        apply hk
      · -- not odd n
        apply Or.inl
        by_contra h1; define at h1
        obtain k hk from h1; clear h1
        contradict h; clear h
        have h : ∃ (m : Nat), k = m + 1 := by
          apply nonzero_is_successor
          intro h
          rw [h] at hk
          simp at hk
          done
        obtain m hm from h; clear h
        define; exists m
        rw [hm] at hk
        apply add_right_cancel at hk
        apply hk
      done

/- Section 6.2 -/
-- 1.
lemma Lemma_6_2_1_2 {A : Type} {R : BinRel A} {B : Set A} {b c : A}
    (h1 : partial_order R) (h2 : b ∈ B) (h3 : minimalElt R c (B \ {b}))
    (h4 : ¬R b c) : minimalElt R c B := by
    define at h3; define
    have h3l := h3.left; define at h3l
    apply And.intro h3l.left
    have h3r := h3.right; clear h3; quant_neg at h3r
    by_contra h; obtain x hx from h; clear h
    apply h3r x
    apply And.intro _ hx.right
    define; apply And.intro hx.left
    contradict h4 with h5; define at h5
    rw[← h5]; apply hx.right.left
    done

-- 2.
lemma extendPO_is_ref {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : reflexive (extendPO R b) := by
    define; fix a
    define; apply Or.inl (h.left a)
    done

-- 3.
lemma extendPO_is_trans {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : transitive (extendPO R b) := by
    define; fix x; fix y; fix z
    intros h1 h2
    define at h1; define at h2; define
    by_cases on h1
    · by_cases on h2
      · apply Or.inl
        apply h.right.left x y z h1 h2
      · apply Or.inr
        apply And.intro _ h2.right
        apply h.right.left x y b h1 h2.left
    · by_cases on h2
      · or_right with h3
        apply And.intro h1.left
        contradict h1.right with h4
        apply h.right.left y z b h2 h4
      · apply Or.inr
        apply And.intro h1.left h2.right
    done

-- 4.
lemma extendPO_is_antisymm {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : antisymmetric (extendPO R b) := by
    define; fix x; fix y
    intros h1 h2
    define at h1; define at h2
    by_cases on h1
    · by_cases on h2
      · apply h.right.right
        apply h1; apply h2
      · contradict h2.right with h3
        apply h.right.left x y b h1 h2.left
    · by_cases on h2
      · contradict h1.right with h3
        apply h.right.left y x b h2 h1.left
      · contradict h1.right with h3
        apply h2.left
    done

-- 5.
theorem Exercise_6_2_3 {A : Type} (R : BinRel A)
    (h : total_order R) : ∀ n ≥ 1, ∀ (B : Set A),
    numElts B n → ∃ (b : A), smallestElt R b B := by
    by_induc
    · --base case, n = 1
      fix X: Set A
      assume h1; rw [one_elt_iff_singleton] at h1
      obtain x hx from h1; clear h1
      exists x; define
      apply And.intro
      ·   rw[hx]; rfl
      ·   fix y; assume h1
          rw [hx] at h1; define at h1
          rw [h1]
          define at h; apply h.left.left
    · --induction case
      define at h
      fix n : Nat
      intros h1 h2
      fix X; assume h3
      have hn1 : n + 1 > 0 := by linarith
      have h4 := by apply nonempty_of_pos_numElts h3 hn1
      obtain a ha from h4; clear h4
      have h5 := by apply remove_one_numElts h3 ha
      apply h2 at h5
      obtain b hb from h5; clear h5
      have hab := by apply h.right a b
      by_cases on hab
      · --R a b
        exists a
        define at hb; define
        apply And.intro ha
        fix x; assume hx
        by_cases hxa : x = a
        · -- x = a
          rw [hxa]
          apply h.left.left a
        · -- x ≠ a
          have hbx : R b x := by
            apply hb.right
            define
            apply And.intro hx hxa
          apply h.left.right.left a b x hab hbx
      · -- R b a
        exists b; define; define at hb
        apply And.intro
        · have hb1 := hb.left; define at hb1
          apply hb1.left
        · fix x; assume hx
          have hb2 := hb.right
          by_cases hxa: x = a
          · -- x = a
            rw [hxa]; apply hab
          · -- x ≠ a
            apply hb2
            define
            apply And.intro hx hxa
    done

-- 6.
--Hint:  First prove that R is reflexive
theorem Exercise_6_2_4a {A : Type} (R : BinRel A)
    (h : ∀ (x y : A), R x y ∨ R y x) : ∀ n ≥ 1, ∀ (B : Set A),
    numElts B n → ∃ x ∈ B, ∀ y ∈ B, ∃ (z : A), R x z ∧ R z y := by
    have Rreflex : reflexive R := by
      define; fix x
      have hx := by apply h x x
      by_cases on hx
      apply hx; apply hx
      done
    by_induc
    · --base case
      fix X: Set A
      intros h1
      rw [one_elt_iff_singleton] at h1
      obtain x hx from h1; clear h1
      exists x
      apply And.intro
      · -- x ∈ X
        rw [hx]; define; rfl
      · -- ∀ y ∈ X, ∃ (z : A), R x z ∧ R z y
        fix y; assume hy
        exists x
        apply And.intro
        · apply Rreflex x
        · rw [hx] at hy; define at hy
          rw[hy]; apply Rreflex x
      done
    · --induction case
      fix n: Nat
      intros h1 h2
      fix X; intro h3
      have hn1 : n + 1 > 0 := by linarith
      have h4 := by apply nonempty_of_pos_numElts h3 hn1
      clear hn1
      obtain a ha from h4; clear h4
      have h5 := by apply remove_one_numElts h3 ha
      apply h2 at h5
      obtain x hx from h5; clear h5
      clear h3; clear h2
      have h2 := hx.left; define at h2
      have h3 := hx.right; clear hx
      by_cases hxa: ∃ (z: A), R x z ∧ R z a
      · --∃ (z: A), R x z ∧ R z a
        obtain z hz from hxa; clear hxa
        exists x
        apply And.intro h2.left
        fix y; intro hy
        by_cases hya : y = a
        · --y=a
          exists z; rw[hya]; apply hz
        · --y≠a
          apply h3; define
          apply And.intro hy hya
      · --¬∃ (z : A), R x z ∧ R z a
        quant_neg at hxa
        exists a
        apply And.intro ha
        fix y; assume hy
        by_cases hya : y = a
        · --y=a
          exists a
          apply And.intro
          apply Rreflex a
          rw [hya]; apply Rreflex a
        · --y≠a
          have h: y ∈ X \ {a} := by
            define
            apply And.intro hy hya
            done
          apply h3 at h
          obtain z hz from h; clear h
          have h4 : ¬(R x z ∧ R z a) := by
            apply hxa
            done
          demorgan at h4
          by_cases on h4
          · contradict h4; apply hz.left
          · exists z
            apply And.intro _ hz.right
            have haz := by apply h a z
            disj_syll haz h4
            apply haz
      done

-- 7.
theorem Like_Exercise_6_2_16 {A : Type} (f : A → A)
    (h : one_to_one f) : ∀ (n : Nat) (B : Set A), numElts B n →
    closed f B → ∀ y ∈ B, ∃ x ∈ B, f x = y := by
    by_induc
    · --base case
      fix X: Set A
      assume h1; rw [zero_elts_iff_empty] at h1; define at h1
      assume h2
      fix x; assume h3
      contradict h1 with h4
      exists x
      done
    · --induction case
      fix n : Nat
      intros h1 X h2 h3 y h4
      define at h
      define at h3
      have h5 := by apply remove_one_numElts h2 h4
      clear h2
      by_cases h2: closed f (X \ {y})
      · --closed f (X \ {y})
        have g1: ∀ z ∈ (X \ {y}), ∃ x ∈ (X \ {y}), f x = z := by
          apply h1 (X \ {y}) h5 h2
          done
        clear h1 h5 h2
        exists y; apply And.intro h4
        have g2 := by apply h3 y h4
        by_contra g3
        have g4 : f y ∈ X \ {y} := by
          define; apply And.intro g2
          define; apply g3
          done
        apply g1 at g4
        obtain x gx from g4
        clear g1 g2 g3 g4
        have gxy : x = y := by apply h x y gx.right
        contradict gx.left
        define; demorgan; apply Or.inr; define
        apply gxy
      · --not closed f (X \ {y})
        define at h2; quant_neg at h2
        obtain x g1 from h2; clear h2
        conditional at g1
        have g2 := g1.right; define at g2; demorgan at g2
        have g3 := g1.left; clear g1
        define at g3
        exists x; apply And.intro g3.left
        by_cases on g2
        · contradict g2;
          apply h3; apply g3.left
        · define at g2; apply g2
    done

-- 8.
--Hint:  Use Exercise_6_2_2
theorem Example_6_2_2 {A : Type} (R : BinRel A)
    (h1 : ∃ (n : Nat), numElts {x : A | x = x} n)
    (h2 : partial_order R) : ∃ (T : BinRel A),
      total_order T ∧ ∀ (x y : A), R x y → T x y := by
    obtain n h3 from h1; clear h1
    have h1 := by apply Exercise_6_2_2 R h2 n {x: A | x = x} h3
    obtain T h from h1; clear h1; clear h3
    exists T; apply And.intro _ h.right.left
    define; apply And.intro h.left
    intros x y
    apply h.right.right
    define; rfl
    done

/- Section 6.3 -/
-- 1.
theorem Exercise_6_3_4 : ∀ (n : Nat),
    3 * (Sum i from 0 to n, (2 * i + 1) ^ 2) =
    (n + 1) * (2 * n + 1) * (2 * n + 3) := by
    by_induc
    · --base case
      decide
    · --induction case
      fix n : Nat
      intros h
      show 3 * Sum i from 0 to n + 1, (2 * i + 1) ^ 2 = (n + 1 + 1) * (2 * (n + 1) + 1) * (2 * (n + 1) + 3) from
        calc (3 * Sum i from 0 to n + 1, (2 * i + 1) ^ 2)
        _ = 3 * ((Sum i from 0 to n, (2 * i + 1) ^ 2) + (2 * (n + 1) + 1) ^ 2) := by rw [sum_from_zero_step]
        _ = 3 * (Sum i from 0 to n, (2 * i + 1) ^ 2) + 3 * (2 * (n + 1) + 1) ^ 2 := by linarith
        _ = (n + 1) * (2 * n + 1) * (2 * n + 3) + 3 * (2 * (n + 1) + 1) ^ 2 := by linarith
        _ = (n + 1 + 1) * (2 * (n + 1) + 1) * (2 * (n + 1) + 3) := by linarith
    done

-- 2.
theorem Exercise_6_3_7b (f : Nat → Real) (c : Real) : ∀ (n : Nat),
    Sum i from 0 to n, c * f i = c * Sum i from 0 to n, f i := by
    by_induc
    · --base case
      rw[sum_base, sum_base]
    · --induction case
      fix n : Nat
      intros ih
      rw[sum_from_zero_step, sum_from_zero_step, ih]
      linarith
    done


-- 3.
theorem fact_pos : ∀ (n : Nat), fact n ≥ 1 := by
  by_induc
  · --base
    decide
  · --induction
    fix n: Nat
    intros ih
    show fact (n + 1) ≥ 1 from
      calc fact (n + 1)
        _ = (n + 1) * (fact n) := by rfl
        _ ≥ (n + 1) * 1 := by rel [ih]
        _ = n + 1 := by linarith
        _ ≥ 1 := by linarith
    done

-- 4.
--Hint:  Use the theorem fact_pos from the previous exercise
theorem Exercise_6_3_13a (k : Nat) : ∀ (n : Nat),
    fact (k ^ 2 + n) ≥ k ^ (2 * n) := by
    by_induc
    · --base
      simp
      apply fact_pos
    · --induction
      intros n ih
      rw [← Nat.add_assoc]
      have h1 : k ^ 2 ≤ k ^ 2 + n + 1 := by linarith
      show _ from
        calc (fact (k ^ 2 + n + 1))
          _ = (k ^ 2 + n + 1) * fact (k ^ 2 + n) := by rfl
          _ ≥ (k ^ 2 + n + 1) * k ^ (2 * n) := by rel[ih]
          _ ≥ k ^ 2 * k ^ (2 * n) := by rel [Nat.mul_le_mul_right, h1]
          _ = k ^ (2 * (n + 1)) := by ring
    done

-- 5.
--Hint:  Use the theorem in the previous exercise.
--You may find it useful to first prove a lemma:
--∀ (k : Nat), 2 * k ^ 2 + 1 ≥ k
theorem Exercise_6_3_13b (k : Nat) : ∀ n ≥ 2 * k ^ 2,
    fact n ≥ k ^ n := by
    have Lemma: ∀ (k: Nat), 2 * k ^ 2 + 1 ≥ k := by
      by_induc
      · --k=0
        linarith
      · --induction
        intros n ih
        show 2 * (n + 1) ^ 2 + 1 ≥ n + 1 from
          calc 2 * (n + 1) ^ 2 + 1
            _ = 2 * (n ^ 2 + 2 * n + 1) + 1 := by linarith
            _ = 2 * n ^ 2 + 1 + 4 * n + 2 := by linarith
            _ ≥ n + 4 * n + 2 := by linarith
            _ ≥ n + 1 := by linarith
      done

    by_induc
    · --base case
      have h := by apply Exercise_6_3_13a k (k ^ 2)
      have g: k ^ 2 + k ^ 2 = 2 * k ^ 2 := by linarith
      rw [g] at h
      apply h
    · --induction case
      fix n : Nat
      intros h1 h2
      -- n + 1 ≥ 2 * k ^ 2 + 1 ≥ k
      show fact (n + 1) ≥ k ^ (n + 1) from
        calc fact (n + 1)
          _ = (n + 1) * fact n := by rfl
          _ ≥ (n + 1) * k ^ n := by rel[h2]
          _ ≥ (2 * k ^ 2 + 1) * k ^ n := by rel[h1]
          _ ≥ k * k ^ n := by rel[Lemma k]
          _ = k ^ (n + 1) := by ring
      done

-- 6.
def seq_6_3_15 (k : Nat) : Int :=
    match k with
      | 0 => 0
      | n + 1 => 2 * seq_6_3_15 n + n

theorem Exercise_6_3_15 : ∀ (n : Nat),
    seq_6_3_15 n = 2 ^ n - n - 1 := by
    by_induc
    · --n = 0
      rfl
    · --induction
      intros n h1
      have h2 : n ≤ n := by linarith
      have h3 : 2 * ↑n - n = ↑n := by
        calc 2 * ↑n - n
          _ = n + n - n := by ring
          _ = n := by apply Nat.add_sub_cancel
        done

      show seq_6_3_15 (n + 1) = 2 ^ (n + 1) - ↑(n + 1) - 1 from
        calc seq_6_3_15 (n + 1)
          _ = 2 * seq_6_3_15 n + n := by rfl
          _ = 2 * (2 ^ n - ↑n - 1) + n := by rw [h1]
          _ = 2 ^ (n + 1) - 2 * ↑n - 2 + n := by ring
          _ = 2 ^ (n + 1) - (2 * ↑n - n) - 2 := by linarith
          _ = 2 ^ (n + 1) - n - 2 := by linarith
          _ = 2 ^ (n + 1) - (n + 1) - 1 := by linarith
      done

-- 7.
def seq_6_3_16 (k : Nat) : Nat :=
    match k with
      | 0 => 2
      | n + 1 => (seq_6_3_16 n) ^ 2

theorem Exercise_6_3_16 : ∀ (n : Nat),
    seq_6_3_16 n = 2 ^ (2 ^ n) := by
    by_induc
    · --base case
      rfl
    · --induction
      intros n h1
      show seq_6_3_16 (n + 1) = 2 ^ (2 ^ (n + 1)) from
        calc seq_6_3_16 (n + 1)
          _ = (seq_6_3_16 n) ^ 2 := by rfl
          _ = (2 ^ (2 ^ n)) ^ 2 := by rw[h1]
          _ = 2 ^ (2 ^ n) * 2 ^ (2 ^ n) := by ring
          _ = 2 ^ (2 ^ n + 2 ^ n) := by ring
          _ = 2 ^ (2 * 2 ^ n) := by ring
          _ = 2 ^ (2 ^ (n + 1)) := by ring
      done

/- Section 6.4 -/
-- 1.
--Hint: Use Exercise_6_1_16a1 and Exercise_6_1_16a2
lemma sq_even_iff_even (n : Nat) :
    nat_even (n * n) ↔ nat_even n := by
    apply Iff.intro
    · -- (->)
      intros h
      have h1 := by apply Exercise_6_1_16a1 n
      by_cases on h1
      · --even n
        apply h1
      · --odd n
        define at h1
        obtain m hm from h1; clear h1
        have h2 : nat_odd (n * n) := by
          define
          -- 4 * m ^ 2 + 4 * m + 1
          exists  2 * m ^ 2 + 2 * m
          rw[hm]; ring
          done
        contradict Exercise_6_1_16a2; quant_neg
        exists n * n
    · -- (<-)
      intros h; define at h
      obtain k hk from h; clear h
      define; exists 2 * k * k
      rw [hk]
      ring
    done

-- 2.
--This theorem proves that the square root of 6 is irrational
theorem Exercise_6_4_4a :
    ¬∃ (q p : Nat), p * p = 6 * (q * q) ∧ q ≠ 0 := by
    set S : Set Nat :=
      {q : Nat | ∃ (p : Nat), p * p = 6 * (q * q) ∧ q ≠ 0}
    by_contra h1
    have h2 : ∃ (q: Nat), q ∈ S := h1
    have h3 := well_ord_princ S h2; clear h2
    obtain q hq from h3; clear h3
    have h2 := hq.left; define at h2
    have h3 := hq.right; clear hq
    obtain p h4 from h2; clear h2
    have h5 := h4.left; have h2 := h4.right; clear h4
    -- p * p is even, so p is even
    have g1 : nat_even (p * p) := by
      define; exists 3 * q * q
      rw [h5]; ring
      done
    rw [sq_even_iff_even] at g1
    define at g1; obtain p' g2 from g1; clear g1
    rw [g2] at h5
    have g1 : 2 * p' * p' = 3 * q * q := by linarith
    -- 3 * q * q is even
    -- so q * q must be even, q is even
    clear h5
    have g3 : nat_even (3 * (q * q)) := by
      define; exists p' * p'
      rw [← mul_assoc, ← g1]; ring
      done
    have g4 : nat_even (q * q) := by
      -- prove by contradiction, assuming q * q is odd
      -- then prove 3 * q * q is also odd
      have f1 := by apply Exercise_6_1_16a1 (q * q)
      by_cases on f1
      · apply f1
      · define at f1; obtain k f3 from f1; clear f1
        have contra: nat_odd (3 * (q * q)) := by
          define; rw[f3]; exists (3 * k + 1)
          ring
          done
        contradict Exercise_6_1_16a2
        quant_neg
        exists 3 * (q * q)
      done
    -- q = 2 * q', then p' * p' = 6 * q' * q'
    -- q' ∈ S, contracdicted with q is smallest
    rw [sq_even_iff_even] at g4
    define at g4; obtain q' g5 from g4; clear g4
    rw[g5] at g1
    -- prove q' ∈ S
    have hleft: 2 * (p' * p') = 2 * (6 * (q' * q')) := by
      calc 2 * (p' * p')
        _ = 2 * p' * p' := by rw[mul_assoc]
        _ = 3 * (2 * q') * (2 * q') := by rw[g1]
        _ = 2 * (6 * (q' * q')) := by ring
    have g6 : 2 > 0 := by linarith
    rw [mul_left_cancel_iff_of_pos g6] at hleft
    have hright: q' ≠ 0 := by
      contradict h2 with h4
      rw [h4] at g5
      rw [g5]
      done
    have h : q' ∈ S := by
      define
      exists p'
      done
    -- contradict with q is smallest element of S
    have qleq': q ≤ q' := by apply h3 q' h
    rw[g5] at qleq'
    contradict hright
    linarith
    done

-- 3.
theorem Exercise_6_4_5 :
    ∀ n ≥ 12, ∃ (a b : Nat), 3 * a + 7 * b = n := by
    by_strong_induc
    intros n h1 h2
    have g1 : 3 > 0 := by linarith
    have h3 := by apply Example_6_4_1 3 g1 n
    clear g1
    obtain q g1 from h3; clear h3
    obtain r g from g1; clear g1
    have g1 := g.left; have g2 := g.right; clear g
    by_cases g3 : r = 0
    · -- r = 0
      rw[g3] at g1
      exists q; exists 0
      rw [g1]
    · -- not r = 0
      by_cases g4 : r = 1
      · -- r = 1
        rw [g4] at g1
        have g5: q ≥ 2 := by linarith
        have g6 := by apply Nat.exists_eq_add_of_le g5
        obtain q' g7 from g6; clear g5; clear g6
        exists q'; exists 1
        rw[g1, g7]; ring
      · -- r = 2
        have g5 : q ≥ 4 := by linarith
        have g6 : r ≥ 1 := Nat.pos_of_ne_zero g3; clear g3
        have g7 : r ≥ 2 := lt_of_le_of_ne' g6 g4; clear g4; clear g6
        have g3 := by apply Nat.exists_eq_add_of_le g5
        obtain q' gq' from g3; clear g3
        have g3 : r = 2 := by linarith
        clear g2; clear g7; clear g5
        exists q'; exists 2
        rw [g1, gq', g3]
        ring
    done

-- 4.
theorem Exercise_6_4_7a : ∀ (n : Nat),
    (Sum i from 0 to n, Fib i) + 1 = Fib (n + 2) := by
  by_strong_induc
  intros n h1
  by_cases h2: n = 0
  · -- n = 0
    rw[h2, sum_base]
    rfl
  · -- n > 0
    have h3 := by apply exists_eq_add_one_of_ne_zero h2
    clear h2; obtain n' h2 from h3; clear h3
    rw[h2, sum_from_zero_step]
    have g: n > n' := by linarith
    have h3 := by apply h1 n' g
    clear g
    calc (Sum i from 0 to n', Fib i) + Fib (n' + 1) + 1
      _ = (Sum i from 0 to n', Fib i) + 1 + Fib (n' + 1) := by ring
      _ = Fib (n' + 2) + Fib (n' + 1) := by rw [h3]
      _ = Fib (n' + 1) + Fib (n' + 2) := by ring
  done

-- 5.
theorem Exercise_6_4_7c : ∀ (n : Nat),
    Sum i from 0 to n, Fib (2 * i + 1) = Fib (2 * n + 2) := by
    by_strong_induc
    intros n h1
    by_cases h: n = 0
    · -- n = 0
      rw[h, sum_base]
      rfl
    · -- n > 0
      have h2 := by apply exists_eq_add_one_of_ne_zero h
      clear h; obtain n' h3 from h2; clear h2
      rw[h3, sum_from_zero_step]
      have g: n > n' := by linarith
      have h2 := by apply h1 n' g
      clear g; clear h3
      calc (Sum i from 0 to n', Fib (2 * i + 1)) + Fib (2 * (n' + 1) + 1)
        _ = Fib (2 * n' + 2) + Fib (2 * (n' + 1) + 1) := by rw[h2]
    done

-- 6.
theorem Exercise_6_4_8a : ∀ (m n : Nat),
    Fib (m + n + 1) = Fib m * Fib n + Fib (m + 1) * Fib (n + 1) := by
    by_strong_induc
    intros m h1 n
    by_cases h: m = 0
    · --m = 0
      rw [h]
      symm
      calc Fib 0 * Fib n + Fib (0 + 1) * Fib (n + 1)
        _ = 0 * Fib n + Fib 1 * Fib (n + 1) := by rfl
        _ = 0 + Fib 1 * Fib (n + 1) := by ring
        _ = 0 + 1 * Fib (n + 1) := by rfl
        _ = Fib (0 + n + 1) := by ring
      done
    · --m > 0
      by_cases h2: m = 1
      · --m = 1
        rw [h2]; ring
        calc Fib (2 + n)
          _ = Fib (n + 2) := by ring
          _ = Fib n + Fib (n + 1) := by rfl
          _ = 1 * Fib n + 1 * Fib (1 + n) := by ring
          _ = Fib 1 * Fib n + Fib 2 * Fib (1 + n) := by rfl
        done
      · --m >= 2
        have h3 := by apply exists_eq_add_two_of_ne_zero_one h h2
        clear h; clear h2; obtain m' h2 from h3; clear h3
        have g1 : m' + 1 < m := by linarith
        have h3 := by apply h1 (m' + 1) g1 (n + 1)
        rw[h2]; ring
        have g2 : Fib (3 + m' + n) = Fib (m' + 1 + (n + 1) + 1) := by ring
        rw [g2, h3]; ring
        clear g2; clear h3
        have g2 : Fib (2 + n) = Fib n + Fib (n + 1) := by
          calc Fib (2 + n)
          _ = Fib (n + 2) := by ring
          _ = Fib n + Fib (n + 1) := by rfl
        rw [g2]; ring; clear g2
        have g2 : Fib (3 + m') = Fib (m' + 1) + Fib (m' + 2) := by
          calc Fib (3 + m')
          _ = Fib (m' + 1 + 2) := by ring
          _ = Fib (m' + 1) + Fib (m' + 2) := by rfl
        rw [g2]; ring
      done

-- 7.
theorem Exercise_6_4_8d : ∀ (m k : Nat), Fib m ∣ Fib (m * k) := by
  intros m
  by_induc
  · --base k = 0
    define
    exists 0
  · --induction
    intros k h
    define at h; obtain c h1 from h; clear h
    define
    by_cases h: m = 0 ∨ k = 0
    · by_cases on h
      · --m = 0
        rw [h]; ring; exists 1
      · --k = 0
        rw [h]; exists 1; ring
    · -- m > 0 and k > 0
      demorgan at h
      have h2 : m * k ≠ 0 := by
        rw [mul_ne_zero_iff]
        apply h
        done
      have h3 := by apply exists_eq_add_one_of_ne_zero h2
      clear h; clear h2
      obtain j h2 from h3; clear h3
      have h3 : m * (k + 1) = j + m + 1 := by linarith
      rw [h3]; clear h3
      have h4 := by apply Exercise_6_4_8a j m
      rw[← h2, h1] at h4
      exists Fib j + c * Fib (m + 1)
      rw[h4]
      ring
    done

-- 8.
def Fib_like (n : Nat) : Nat :=
  match n with
    | 0 => 1
    | 1 => 2
    | k + 2 => 2 * (Fib_like k) + Fib_like (k + 1)

theorem Fib_like_formula : ∀ (n : Nat), Fib_like n = 2 ^ n := by
  by_strong_induc
  intros n h
  by_cases g1: n = 0
  · --n = 0
    rw [g1]
    rfl
  · --n > 0
    by_cases g2: n = 1
    · --n = 1
      rw [g2]
      rfl
    · --n > 1
      have g3 := by apply exists_eq_add_two_of_ne_zero_one g1 g2
      clear g1; clear g2
      obtain n' g1 from g3; clear g3
      rw[g1]
      have g2: n' < n := by linarith
      have g3: n' + 1 < n := by linarith
      have h1 := by apply h n' g2
      have h2 := by apply h (n' + 1) g3
      calc Fib_like (n' + 2)
        _ = 2 * (Fib_like n') + Fib_like (n' + 1) := by rfl
        _ = 2 * 2 ^ n' + 2 ^ (n' + 1) := by rw[h1, h2]
        _ = 2 ^ (n' + 2) := by ring
    done

-- 9.
def triple_rec (n : Nat) : Nat :=
  match n with
    | 0 => 0
    | 1 => 2
    | 2 => 4
    | k + 3 => 4 * triple_rec k +
                6 * triple_rec (k + 1) + triple_rec (k + 2)

theorem triple_rec_formula :
    ∀ (n : Nat), triple_rec n = 2 ^ n * Fib n := by
    by_strong_induc
    intros n h1
    by_cases g1: n = 0
    · --n = 0
      rw [g1]; rfl
    · by_cases g2: n = 1
      · --n = 1
        rw [g2]; rfl
      · by_cases g3: n = 2
        · --n = 2
          rw [g3]; rfl
        · --n >= 3
          have h2: 1 ≤ n := Nat.pos_of_ne_zero g1
          have h3: 2 ≤ n := lt_of_le_of_ne' h2 g2
          have h4: 3 ≤ n := lt_of_le_of_ne' h3 g3
          have g := by apply Nat.exists_eq_add_of_le' h4
          clear h2; clear h3; clear h4
          clear g1; clear g2; clear g3
          obtain n' g1 from g; clear g
          rw[g1]
          have g2: n' < n := by linarith
          have g3: n' + 1 < n := by linarith
          have g4: n' + 2 < n := by linarith
          have h2 := by apply h1 n' g2
          have h3 := by apply h1 (n' + 1) g3
          have h4 := by apply h1 (n' + 2) g4
          calc triple_rec (n' + 3)
            _ = 4 * triple_rec n' + 6 * triple_rec (n' + 1) + triple_rec (n' + 2) := by rfl
            _ = 4 * (2 ^ n' * Fib n') + 6 * (2 ^ (n' + 1) * Fib (n' + 1)) + (2 ^ (n' + 2) * Fib (n' + 2)) := by rw[h2, h3, h4]
            _ = 2 ^ (n' + 2) * (Fib n' + Fib (n' + 1)) + 2 * 2 ^ (n' + 2) * Fib (n' + 1) + 2 ^ (n' + 2) * Fib (n' + 2) := by ring
            _ = 2 ^ (n' + 2) * Fib (n' + 2) + 2 * 2 ^ (n' + 2) * Fib (n' + 1) + 2 ^ (n' + 2) * Fib (n' + 2) := by rfl
            _ = 2 * 2 ^ (n' + 2) * Fib (n' + 1) + 2 * 2 ^ (n' + 2) * Fib (n' + 2) := by ring
            _ = 2 ^ (n' + 3) * (Fib (n' + 1) + Fib (n' + 2)) := by ring
            _ = 2 ^ (n' + 3) * Fib (n' + 3) := by rfl
        done

-- 10.
lemma quot_rem_unique_lemma {m q r q' r' : Nat}
    (h1 : m * q + r = m * q' + r') (h2 : r' < m) : q ≤ q' := by
    #check Nat.add_sub_cancel
    have h3 : r' = r + m * q - m * q' := by
      calc r'
        _ = r' + m * q' - m * q' := by rw [Nat.add_sub_cancel]
        _ = m * q' + r' - m * q' := by ring
        _ = m * q + r - m * q' := by rw[h1]
        _ = r + m * q - m * q' := by ring
    rw [h3] at h2
    by_contra h4
    have g : q > q' := by linarith
    have g1 : 0 < q - q' := by apply Nat.zero_lt_sub_of_lt g
    clear h4
    have h4 := by
      calc m * q - m * q'
        _ = m * (q - q') := by rw[Nat.mul_sub_left_distrib]
        _ ≥ m := by apply Nat.le_mul_of_pos_right m g1
    have g2 : q' ≤ q := by linarith
    have g3 : m * q' ≤ m * q := by apply Nat.mul_le_mul_left m g2
    have h5 : r + m * q - m * q' ≥ m := by
      calc r + m * q - m * q'
        _ = r + (m * q - m * q') := by apply Nat.add_sub_assoc g3
        _ ≥ r + m := by linarith
        _ ≥ m := by linarith
    contradict h2
    apply Nat.not_lt_of_ge at h5
    apply h5
    done

theorem quot_rem_unique (m q r q' r' : Nat)
    (h1 : m * q + r = m * q' + r') (h2 : r < m) (h3 : r' < m) :
    q = q' ∧ r = r' := by
    have h4 := by apply quot_rem_unique_lemma h1 h3
    symm at h1
    have h5 := by apply quot_rem_unique_lemma h1 h2
    have h : q = q' := by apply eq_of_le_of_ge h4 h5
    apply And.intro h
    rw[h] at h1
    calc r
      _ = r + m * q' - m * q' := by rw [Nat.add_sub_cancel r (m * q')]
      _ = m * q' + r - m * q' := by ring
      _ = m * q' + r' - m * q' := by rw[h1]
      _ = r' + m * q' - m * q' := by ring
      _ = r' := by rw [Nat.add_sub_cancel]
    done

-- 11.
theorem div_mod_char (m n q r : Nat)
    (h1 : n = m * q + r) (h2 : r < m) : q = n / m ∧ r = n % m := by
    apply And.intro
    · -- q = n / m
      have g1 : 0 < m := by linarith
      symm; rw [Nat.div_eq_iff g1]
      apply And.intro
      · --q * m ≤ n
        linarith
      · --n ≤ q * m + m - 1
        have g2 : m ≠ 0 := by linarith
        have g3 := by apply exists_eq_add_one_of_ne_zero g2
        clear g2; obtain m' g2 from g3; clear g3
        rw [g2] at h2
        have g3 : r ≤ m' := by apply Nat.le_of_lt_add_one h2
        have g4 : m' = m - 1 := by
          calc m'
            _ = m' + 1 - 1 := by apply Nat.add_sub_cancel m' 1
            _ = m - 1 := by rw[g2]
          done
        have g5 : 1 ≤ m := by linarith
        calc n
          _ = m * q + r := by rw [h1]
          _ = q * m + r := by ring
          _ ≤ q * m + m' := by rel[g3]
          _ = q * m + (m - 1) := by rw[g4]
          _ = q * m + m - 1 := by rw[Nat.add_sub_assoc g5]
        done
    · -- r = n % m
      symm
      rw [Nat.mod_eq_iff]
      apply Or.inr
      apply And.intro h2
      exists q
    done

/- Section 6.5 -/
-- Definitions for next three exercises
def rep_image_family {A : Type}
    (F : Set (A → A)) (n : Nat) (B : Set A) : Set A :=
  match n with
    | 0 => B
    | k + 1 => {x : A | ∃ f ∈ F, x ∈ image f (rep_image_family F k B)}

def cumul_image_family {A : Type}
    (F : Set (A → A)) (B : Set A) : Set A :=
  {x : A | ∃ (n : Nat), x ∈ rep_image_family F n B}

def image2 {A : Type} (f : A → A → A) (B : Set A) : Set A :=
  {z : A | ∃ (x y : A), x ∈ B ∧ y ∈ B ∧ z = f x y}

def rep_image2 {A : Type}
    (f : A → A → A) (n : Nat) (B : Set A) : Set A :=
  match n with
    | 0 => B
    | k + 1 => image2 f (rep_image2 f k B)

def cumul_image2 {A : Type} (f : A → A → A) (B : Set A) : Set A :=
  {x : A | ∃ (n : Nat), x ∈ rep_image2 f n B}

def un_image2 {A : Type} (f : A → A → A) (B : Set A) : Set A :=
  B ∪ (image2 f B)

def rep_un_image2 {A : Type}
    (f : A → A → A) (n : Nat) (B : Set A) : Set A :=
  match n with
    | 0 => B
    | k + 1 => un_image2 f (rep_un_image2 f k B)

def cumul_un_image2 {A : Type}
    (f : A → A → A) (B : Set A) : Set A :=
  {x : A | ∃ (n : Nat), x ∈ rep_un_image2 f n B}

-- 1.
theorem rep_image_family_base {A : Type}
    (F : Set (A → A)) (B : Set A) : rep_image_family F 0 B = B := by rfl

theorem rep_image_family_step {A : Type}
    (F : Set (A → A)) (n : Nat) (B : Set A) :
    rep_image_family F (n + 1) B =
    {x : A | ∃ f ∈ F, x ∈ image f (rep_image_family F n B)} := by rfl

lemma rep_image_family_sub_closed {A : Type}
    (F : Set (A → A)) (B D : Set A)
    (h1 : B ⊆ D) (h2 : closed_family F D) :
    ∀ (n : Nat), rep_image_family F n B ⊆ D := sorry

theorem Exercise_6_5_3 {A : Type} (F : Set (A → A)) (B : Set A) :
    closure_family F B (cumul_image_family F B) := sorry

-- 2.
theorem rep_image2_base {A : Type} (f : A → A → A) (B : Set A) :
    rep_image2 f 0 B = B := by rfl

theorem rep_image2_step {A : Type}
    (f : A → A → A) (n : Nat) (B : Set A) :
    rep_image2 f (n + 1) B = image2 f (rep_image2 f n B) := by rfl

--You won't be able to complete this proof
theorem Exercise_6_5_6 {A : Type} (f : A → A → A) (B : Set A) :
    closed2 f (cumul_image2 f B) := sorry

-- 3.
theorem rep_un_image2_base {A : Type} (f : A → A → A) (B : Set A) :
    rep_un_image2 f 0 B = B := by rfl

theorem rep_un_image2_step {A : Type}
    (f : A → A → A) (n : Nat) (B : Set A) :
    rep_un_image2 f (n + 1) B =
    un_image2 f (rep_un_image2 f n B) := by rfl

theorem Exercise_6_5_8a {A : Type} (f : A → A → A) (B : Set A) :
    ∀ (m n : Nat), m ≤ n →
    rep_un_image2 f m B ⊆ rep_un_image2 f n B := sorry

lemma rep_un_image2_sub_closed {A : Type} {f : A → A → A} {B D : Set A}
    (h1 : B ⊆ D) (h2 : closed2 f D) :
    ∀ (n : Nat), rep_un_image2 f n B ⊆ D := sorry

lemma closed_lemma
    {A : Type} {f : A → A → A} {B : Set A} {x y : A} {nx ny n : Nat}
    (h1 : x ∈ rep_un_image2 f nx B) (h2 : y ∈ rep_un_image2 f ny B)
    (h3 : nx ≤ n) (h4 : ny ≤ n) :
    f x y ∈ cumul_un_image2 f B := sorry

theorem Exercise_6_5_8b {A : Type} (f : A → A → A) (B : Set A) :
    closure2 f B (cumul_un_image2 f B) := sorry

-- Definitions for next four exercises
def idExt (A : Type) : Set (A × A) := {(x, y) : A × A | x = y}

def rep_comp {A : Type} (R : Set (A × A)) (n : Nat) : Set (A × A) :=
  match n with
    | 0 => idExt A
    | k + 1 => comp (rep_comp R k) R

def cumul_comp {A : Type} (R : Set (A × A)) : Set (A × A) :=
  {(x, y) : A × A | ∃ n ≥ 1, (x, y) ∈ rep_comp R n}
-- 4.
theorem rep_comp_one {A : Type} (R : Set (A × A)) :
    rep_comp R 1 = R := sorry

-- 5.
theorem Exercise_6_5_11 {A : Type} (R : Set (A × A)) :
    ∀ (m n : Nat), rep_comp R (m + n) =
    comp (rep_comp R m) (rep_comp R n) := sorry

-- 6.
lemma rep_comp_sub_trans {A : Type} {R S : Set (A × A)}
    (h1 : R ⊆ S) (h2 : transitive (RelFromExt S)) :
    ∀ n ≥ 1, rep_comp R n ⊆ S := sorry

-- 7.
theorem Exercise_6_5_14 {A : Type} (R : Set (A × A)) :
    smallestElt (sub (A × A)) (cumul_comp R)
    {S : Set (A × A) | R ⊆ S ∧ transitive (RelFromExt S)} := sorry
