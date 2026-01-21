import HTPILib.Chap7
namespace HTPI.Exercises

/- Section 7.1 -/
-- 1.
theorem dvd_a_of_dvd_b_mod {a b d : Nat}
    (h1 : d ∣ b) (h2 : d ∣ (a % b)) : d ∣ a := by
    define at h1; obtain k1 h3 from h1; clear h1
    define at h2; obtain k2 h4 from h2; clear h2
    set q := a / b
    have h1: b * q + a % b = a := Nat.div_add_mod a b
    define; exists k1 * q + k2
    calc a
        _ = b * q + a % b := by rw[h1]
        _ = d * k1 * q + d * k2 := by rw[h4, h3]
        _ = d * (k1 * q) + d * k2 := by rw[Nat.mul_assoc]
        _ = d * (k1 * q + k2) := by rw [Nat.left_distrib]
    done

-- 2.
lemma gcd_comm_lt {a b : Nat} (h : a < b) : gcd a b = gcd b a := by
  have g1: b ≠ 0 := by linarith
  have h1 := by apply gcd_nonzero a g1
  have g2: 0 < b := by linarith
  have h2 : a / b = 0 := by
    rw [Nat.div_eq_zero_iff_lt g2]
    apply h
    done
  have h3 : b * (a / b) + a % b = a := Nat.div_add_mod a b
  rw[h2, mul_zero, zero_add] at h3
  rw [h3] at h1
  apply h1
  done

theorem gcd_comm (a b : Nat) : gcd a b = gcd b a := by
  by_cases h1: a < b
  · -- a < b
    apply gcd_comm_lt h1
  · by_cases h2: a = b
    · -- a = b
      rw [h2]
    · -- a > b
      have h3 := by apply Nat.lt_or_gt_of_ne h2
      disj_syll h3 h1
      have h4 : b < a := by linarith
      have h := by apply gcd_comm_lt h4
      symm
      apply h
    done

-- 3.
theorem Exercise_7_1_5 (a b : Nat) (n : Int) :
    (∃ (s t : Int), s * a + t * b = n) ↔ (↑(gcd a b) : Int) ∣ n := by
    apply Iff.intro
    · -- (->)
      intros h1
      obtain s tmp from h1; clear h1
      obtain t h1 from tmp; clear tmp
      have h2 := by apply gcd_dvd_left a b
      define at h2; obtain k1 hk1 from h2; clear h2
      have h3 := by apply gcd_dvd_right a b
      define at h3; obtain k2 hk2 from h3; clear h3
      rw [hk1] at h1
      nth_rewrite 2 [hk2] at h1
      define
      exists s * k1 + t * k2
      rw [← h1]; ring
      rw [mul_assoc, mul_assoc, Nat.cast_mul, Nat.cast_mul]
      done
    · -- (<-)
      intros h1; define at h1
      obtain k hk from h1; clear h1
      have h2 := by apply gcd_lin_comb b a
      rw [← h2] at hk
      exists (gcd_c1 a b) * k
      exists (gcd_c2 a b) * k
      rw [hk]
      ring
    done

-- 4.
theorem Exercise_7_1_6 (a b c : Nat) :
    gcd a b = gcd (a + b * c) b := by
    by_cases h: b = 0
    · --b = 0
      rw [h]; ring
    · --b ≠ 0
      have h1: (a + b * c) % b = a % b := by
        set r := a % b
        have g1 : b * (a / b) + r = a := Nat.div_add_mod a b
        rw [Nat.mod_eq_iff]; apply Or.inr
        apply And.intro
        · apply mod_nonzero_lt; apply h
        · exists (a / b + c)
          nth_rewrite 1 [← g1]
          ring
        done
      have h2 := by apply gcd_nonzero (a + b * c) h
      rw[h1] at h2
      have h3 := by apply gcd_nonzero a h
      rw [h2, h3]
      done

-- 5.
theorem gcd_is_nonzero {a b : Nat} (h : a ≠ 0 ∨ b ≠ 0) :
    gcd a b ≠ 0 := by
    by_cases on h
    · -- a ≠ 0
      have h1 := by apply gcd_dvd_left a b
      define at h1; obtain k h2 from h1; clear h1
      contradict h with h1
      rw [h2, h1]
      ring
    · --b ≠ 0
      have h1 := by apply gcd_dvd_right a b
      define at h1; obtain k h2 from h1; clear h1
      contradict h with h1
      rw [h2, h1]
      ring
    done

-- 6.
theorem gcd_greatest {a b d : Nat} (h1 : gcd a b ≠ 0)
    (h2 : d ∣ a) (h3 : d ∣ b) : d ≤ gcd a b := by
    have h := by apply Theorem_7_1_6 h2 h3
    define at h; obtain k hk from h; clear h
    rw[hk] at h1
    rw [Nat.mul_ne_zero_iff] at h1
    have h4 := h1.right
    rw [Nat.ne_zero_iff_zero_lt] at h4
    have h5 : 1 ≤ k := by linarith
    rw[hk]
    have g1 : d = d * 1 := by ring
    nth_rw 1 [g1]
    apply Nat.mul_le_mul_left d h5
    done

-- 7.
lemma Lemma_7_1_10a {a b : Nat}
    (n : Nat) (h : a ∣ b) : (n * a) ∣ (n * b) := by
    define at h; obtain k hk from h; clear h
    define; exists k
    rw [hk]; ring
    done

lemma Lemma_7_1_10b {a b n : Nat}
    (h1 : n ≠ 0) (h2 : (n * a) ∣ (n * b)) : a ∣ b := by
    define at h2; obtain k h3 from h2; clear h2
    define; exists k
    #check Nat.mul_left_cancel
    #check Nat.pos_of_ne_zero
    have g: 0 < n := by apply Nat.pos_of_ne_zero h1
    rw [mul_assoc] at h3
    apply Nat.mul_left_cancel g h3
    done

lemma Lemma_7_1_10c {a b : Nat}
    (h1 : a ∣ b) (h2 : b ∣ a) : a = b := by
    by_cases h: b = 0
    · --b = 0
      define at h1
      obtain k h3 from h2; clear h2
      rw [h3, h]
      ring
    · --b ≠ 0
      define at h1; obtain x g1 from h1; clear h1
      define at h2; obtain y g2 from h2; clear h2
      have h1 := g1
      rw [g2] at h1
      have h2 : b = b * 1 := by ring
      nth_rw 1 [h2] at h1; clear h2
      rw [mul_assoc] at h1
      have g3 : 0 < b := by apply Nat.pos_of_ne_zero h
      apply Nat.mul_left_cancel g3 at h1
      symm at h1
      apply Nat.eq_one_of_mul_eq_one_right at h1
      rw [h1] at g2
      rw [g2]; ring
    done

theorem Exercise_7_1_10 (a b n : Nat) :
    gcd (n * a) (n * b) = n * gcd a b := by
    apply Lemma_7_1_10c
    · --gcd (n * a) (n * b) ∣ n * gcd a b
      have h1 := by apply gcd_dvd_left (n * a) (n * b)
      have h2 := by apply gcd_dvd_right (n * a) (n * b)
      obtain k1 hna from h1; clear h1
      obtain k2 hnb from h2; clear h2
      have h:= by apply gcd_lin_comb b a
      rw [← Int.natCast_dvd_natCast]
      define
      exists (gcd_c1 a b) * k1 + (gcd_c2 a b) * k2
      show ↑(n * gcd a b) = ↑(gcd (n * a) (n * b)) * (gcd_c1 a b * ↑k1 + gcd_c2 a b * ↑k2) from
        calc ↑(n * gcd a b)
          _ = ↑n * ↑(gcd a b) := by rw[Nat.cast_mul]
          _ = ↑n * (gcd_c1 a b * ↑a + gcd_c2 a b * ↑b) := by rw [h]
          _ = ↑n * gcd_c1 a b * ↑a + ↑n * gcd_c2 a b * ↑b := by rw[left_distrib, mul_assoc, mul_assoc]
          _ = ↑(n * a) * gcd_c1 a b + ↑(n * b) * gcd_c2 a b := by
            rw[mul_right_comm]; nth_rewrite 2 [mul_right_comm]; rw [← Nat.cast_mul, ← Nat.cast_mul]
          _ = ↑(gcd (n * a) (n * b) * k1) * gcd_c1 a b + ↑(gcd (n * a) (n * b) * k2) * gcd_c2 a b := by nth_rewrite 1 [hna]; nth_rewrite 2 [hnb]; rfl
          _ = ↑(gcd (n * a) (n * b)) * (gcd_c1 a b * ↑k1 + gcd_c2 a b * ↑k2) := by rw [Nat.cast_mul, mul_assoc, Nat.cast_mul, mul_assoc, left_distrib]; rw [mul_comm ↑k1 (gcd_c1 a b), mul_comm ↑k2 (gcd_c2 a b)]
      done
      --na = k1 * gcd(na, nb)
      --nb = k2 * gcd(na, nb)
      --gcd_c1(a, b)*na + gcd_c2(a, b) * nb = n * gcd (a, b)
      --(gcd_c1(a, b) * k1 + gcd_c2(a, b) * k2) * gcd(na, nb) = n * gcd(a, b)

    · --n * gcd a b | gcd (n * a) (n * b)
      have h1 := by apply gcd_dvd_left a b
      have h2 := by apply gcd_dvd_right a b
      obtain k1 ha from h1
      obtain k2 hb from h2
      have h:= by apply gcd_lin_comb (n * b) (n * a)
      rw [← Int.natCast_dvd_natCast]
      define
      exists (gcd_c1 (n * a) (n * b) * k1 + gcd_c2 (n * a) ( n * b) * k2)
      show ↑(gcd (n * a) (n * b)) = ↑(n * gcd a b) * (gcd_c1 (n * a) (n * b) * ↑k1 + gcd_c2 (n * a) (n * b) * ↑k2) from
        calc ↑(gcd (n * a) (n * b))
          _ = gcd_c1 (n * a) (n * b) * ↑(n * a) + gcd_c2 (n * a) (n * b) * ↑(n * b) := by rw [h]
          _ = gcd_c1 (n * a) (n * b) * ↑(n * (gcd a b * k1)) + gcd_c2 (n * a) (n * b) * ↑(n * (gcd a b * k2)) := by nth_rewrite 2 [ha]; nth_rewrite 4 [hb]; rfl
          _ = gcd_c1 (n * a) (n * b) * ↑(n * gcd a b) * ↑k1 + gcd_c2 (n * a) (n * b) * ↑(n * gcd a b) * ↑k2 := by ring; rw [Nat.cast_mul]; nth_rewrite 2 [Nat.cast_mul]; rw[←mul_assoc, ←mul_assoc]
          _ = ↑(n * gcd a b) * gcd_c1 (n * a) (n * b) * ↑k1 + ↑(n * gcd a b) * gcd_c2 (n * a) (n * b) * ↑k2 := by nth_rw 2 [mul_comm]; rw [mul_comm (gcd_c2 (n * a) (n * b)) ↑(n * gcd a b)]
          _ = ↑(n * gcd a b) * (gcd_c1 (n * a) (n * b) * ↑k1 + gcd_c2 (n * a) (n * b) * ↑k2) := by rw[left_distrib, mul_assoc, mul_assoc]
      done
      -- a = k1 * gcd(a, b)
      -- b = k2 * gcd(a, b)
      -- gcd(na, nb) = gcd_c1(na, nb) * n * a + gcd_c2(na, nb) * n * b
      --             = (gcd_c1(na, nb)* k1 + gcd_c2(na,nb) * k2) * n * gcd(a, b)

/- Section 7.2 -/
-- 1.
lemma dvd_prime {a p : Nat}
    (h1 : prime p) (h2 : a ∣ p) : a = 1 ∨ a = p := by
    define at h1
    define at h2; obtain b h3 from h2
    contradict h1.right with h
    -- a * b = p ∧ a < p ∧ b < p
    exists a; exists b
    symm at h3
    apply And.intro h3
    -- a < p
    demorgan at h
    have g1: 0 < p := by linarith
    have g2: a ≤ p := by apply Nat.le_of_dvd g1 h2
    have g3: a < p := by apply Nat.lt_of_le_of_ne g2 h.right
    apply And.intro g3
    clear g2
    -- b < p
    have f1: b ∣ p := by
      define; exists a; rw [← h3]; ring
    have f2: 0 < b := by apply Nat.pos_of_dvd_of_pos f1 g1
    have f3: b ≤ p := by apply Nat.le_of_dvd g1 f1
    apply Nat.lt_of_le_of_ne f3
    contradict h.left with f4
    rw [f4] at h3
    have f: a * p = 1 * p := by rw[h3]; ring
    apply Nat.mul_right_cancel at f
    apply f; apply g1
    done

-- 2.
-- Hints:  Start with apply List.rec.  You may find mul_ne_zero useful
theorem prod_nonzero_nonzero : ∀ (l : List Nat),
    (∀ a ∈ l, a ≠ 0) → prod l ≠ 0 := by
    apply List.rec
    · --nil case
      intros h; decide
    · --cons case
      intros a L h1 h2
      rw[prod]; rw [Nat.mul_ne_zero_iff]
      apply And.intro
      · -- a ≠ 0
        apply h2
        apply List.mem_cons_self
      · -- prod L ≠ 0
        apply h1
        intros x h3
        apply h2; apply List.mem_cons_of_mem
        apply h3
    done

-- 3.
lemma prime_two: prime 2 := by
    define
    apply And.intro
    linarith
    by_contra g3
    obtain x tmp from g3; clear g3
    obtain y g3 from tmp; clear tmp
    have g4: x ≠ 0 ∧ y ≠ 0 := by
      have g5 : x * y ≠ 0 := by linarith
      rw [mul_ne_zero_iff] at g5
      apply g5
    have gx : x > 0 := by
      have g5 := g4.left
      rw [Nat.ne_zero_iff_zero_lt] at g5
      apply g5
    have gy : y > 0 := by
      have g5 := g4.right
      rw [Nat.ne_zero_iff_zero_lt] at g5
      apply g5
    have gx1 : x = 1 := by linarith
    have gy1 : y = 1 := by linarith
    contradict g3.left
    rw [gx1, gy1]
    decide

theorem rel_prime_iff_no_common_factor (a b : Nat) :
    rel_prime a b ↔ ¬∃ (p : Nat), prime p ∧ p ∣ a ∧ p ∣ b := by
    apply Iff.intro
    · -- rel_prime a b → ¬∃ (p : ℕ), prime p ∧ p ∣ a ∧ p ∣ b
      intros h1; define at h1
      contradict h1 with h2
      obtain p h3 from h2; clear h2
      have h2: gcd a b ≠ 0 := by linarith
      have h4 := by apply gcd_greatest h2 h3.right.left h3.right.right
      have h5 : 2 ≤ p := by
        have g1 := h3.left
        define at g1
        apply g1.left
        done
      linarith
    · --(¬∃ (p : ℕ), prime p ∧ p ∣ a ∧ p ∣ b) → rel_prime a b
      intros h1; define
      contradict h1 with h2; clear h1
      by_cases g1: a = 0 ∧ b = 0
      · --a = 0 ∧ b = 0
        exists 2
        apply And.intro prime_two
        rw [g1.left, g1.right]
        decide
      . --¬(a = 0 ∧ b = 0)
        demorgan at g1
        have g2: gcd a b ≠ 0:= by
          apply gcd_is_nonzero
          apply g1
          done
        have g3: 1 ≤ gcd a b := by apply pos_of_ne_zero g2
        have g4: 2 ≤ gcd a b := by apply lt_of_le_of_ne' g3 h2
        have g5 := by apply exists_least_prime_factor g4
        obtain p g6 from g5; clear g5
        have pa := g6.left; define at pa
        exists p
        apply And.intro pa.left
        apply And.intro
        · -- p | a
          apply dvd_trans pa.right (gcd_dvd_left a b)
        · -- p | b
          apply dvd_trans pa.right (gcd_dvd_right a b)
        done

-- 4.
theorem rel_prime_symm {a b : Nat} (h : rel_prime a b) :
    rel_prime b a := by
    define at h; define
    rw [gcd_comm] at h
    apply h

-- 5.
lemma in_prime_factorization_iff_prime_factor {a : Nat} {l : List Nat}
    (h1 : prime_factorization a l) (p : Nat) :
    p ∈ l ↔ prime_factor p a := by
    apply Iff.intro
    · --p ∈ l → prime_factor p a
      intros h2
      define at h1; define
      have g1:= h1.left.left; define at g1
      apply And.intro
      · --prime p
        apply g1; apply h2
      · --p | a
        have g2 := h1.right
        rw [← g2]
        apply list_elt_dvd_prod
        apply h2
    · --prime_factor p a → p ∈ l
      intros h2; define at h2
      define at h1
      have g1:= h1.left.left
      rw [← h1.right] at h2
      apply prime_in_list
      apply h2.left; apply g1; apply h2.right
      done

-- 6.
theorem Exercise_7_2_5 {a b : Nat} {l m : List Nat}
    (h1 : prime_factorization a l) (h2 : prime_factorization b m) :
    rel_prime a b ↔ (¬∃ (p : Nat), p ∈ l ∧ p ∈ m) := by
    apply Iff.intro
    · --rel_prime a b → ¬∃ p ∈ l, p ∈ m
      intros h3; define at h3
      by_contra h4; obtain p h5 from h4; clear h4
      define at h1; define at h2
      have g1:= h5.left
      apply list_elt_dvd_prod at g1; rw [h1.right] at g1
      have g2:= h5.right
      apply list_elt_dvd_prod at g2; rw [h2.right] at g2
      have g3:= h1.left.left
      have g4: prime p := by
        apply g3; apply h5.left
      have h4: gcd a b ≠ 0 := by linarith
      have g5:= by apply gcd_greatest h4 g1 g2
      rw [h3] at g5
      contradict g5
      define at g4
      have g6:= g4.left
      linarith
    · --(¬∃ p ∈ l, p ∈ m) → rel_prime a b
      intros h3
      rw [rel_prime_iff_no_common_factor]
      contradict h3 with h4; clear h3
      obtain p h3 from h4; clear h4
      exists p
      define at h1; define at h2
      apply And.intro
      · -- p ∈ l
        apply prime_in_list
        apply h3.left; apply h1.left.left
        rw [h1.right]; apply h3.right.left
      · --p ∈ m
        apply prime_in_list
        apply h3.left; apply h2.left.left
        rw [h2.right]; apply h3.right.right
      done

-- 7.
theorem Exercise_7_2_6 (a b : Nat) :
    rel_prime a b ↔ ∃ (s t : Int), s * a + t * b = 1 := by
    apply Iff.intro
    · --rel_prime a b → ∃ (s : ℤ) (t : ℤ), s * ↑a + t * ↑b = 1
      intros h1; define at h1
      have h2:= by apply gcd_lin_comb b a
      exists gcd_c1 a b
      exists gcd_c2 a b
      rw [h2]
      rw [h1]
      rfl
    · --(∃ (s : ℤ) (t : ℤ), s * ↑a + t * ↑b = 1) → rel_prime a b
      intros h1
      define
      rw [Exercise_7_1_5 a b ↑1] at h1
      define at h1
      obtain x hx from h1; clear h1
      symm at hx
      rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at hx
      by_cases on hx
      · linarith
      · have h1 := by apply Int.natCast_nonneg (gcd a b)
        linarith -- ↑(gcd a b) can't be negative
    done

-- 8.
theorem Exercise_7_2_7 {a b a' b' : Nat}
    (h1 : rel_prime a b) (h2 : a' ∣ a) (h3 : b' ∣ b) :
    rel_prime a' b' := by
    rw [Exercise_7_2_6] at h1
    obtain s tmp from h1; clear h1
    obtain t h1 from tmp; clear tmp
    define at h2; obtain k1 hk1 from h2; clear h2
    define at h3; obtain k2 hk2 from h3; clear h3
    rw [Exercise_7_2_6]
    exists s * k1
    exists t * k2
    calc s * ↑k1 * ↑a' + t * ↑k2 * ↑b'
      _ = s * ↑(a' * k1) + t * ↑(b' * k2) := by
        rw [Nat.cast_mul, Nat.cast_mul, Int.mul_comm ↑a',
        Int.mul_comm ↑b', Int.mul_assoc, Int.mul_assoc]
      _ = s * ↑a + t * ↑b := by rw [hk1, hk2]
      _ = 1 := by rw[h1]
    done

-- 9.
theorem Exercise_7_2_9 {a b j k : Nat}
    (h1 : gcd a b ≠ 0) (h2 : a = j * gcd a b) (h3 : b = k * gcd a b) :
    rel_prime j k := by
    have g1:= by apply gcd_dvd_left j k
    define at g1
    obtain k1 h4 from g1; clear g1
    have g2:= by apply gcd_dvd_right j k
    define at g2
    obtain k2 h5 from g2; clear g2
    rw [h4] at h2
    rw [h5] at h3
    have g1: (gcd j k * gcd a b) ∣ a := by
      define; exists k1
      nth_rw 1 [h2];
      ring
    have g2: (gcd j k * gcd a b) ∣ b := by
      define; exists k2
      nth_rw 1 [h3]; ring
    have g3 := by apply gcd_greatest h1 g1 g2
    have g4 : 0 < gcd a b := by apply pos_of_ne_zero h1
    have g5: gcd a b = 1 * gcd a b := by linarith
    nth_rw 2 [g5] at g3
    rw [Nat.mul_le_mul_right_iff g4] at g3
    define
    -- proof by contradiction: suppose gcd j k = 0, then gcd a b = 0
    contradict h1 with contra
    have g6: gcd j k < 1 := by apply Nat.lt_of_le_of_ne g3 contra
    have g7: gcd j k = 0 := by linarith
    rw [g7] at h3
    rw [g7] at h2
    have bzero : b = 0 := by linarith
    have azero : a = 0 := by linarith
    rw [bzero, azero, gcd]
    done

-- 10.
theorem Exercise_7_2_17a (a b c : Nat) :
    gcd a (b * c) ∣ gcd a b * gcd a c := by
    have h1 := by apply gcd_lin_comb b a
    have h2 := by apply gcd_lin_comb c a
    have h3 := by apply gcd_dvd_left a (b * c)
    obtain x (hx: a = gcd a (b * c) * x) from h3
    have h4 := by apply gcd_dvd_right a (b * c)
    obtain y (hy: b * c = gcd a (b * c) * y) from h4
    clear h4
    set k1 := gcd_c1 a b
    set k2 := gcd_c2 a b
    set k3 := gcd_c1 a c
    set k4 := gcd_c2 a c
    set k := gcd a (b * c)
    rw [←Int.natCast_dvd_natCast]
    rw[mul_comm] at hx
    rw[mul_comm _ y] at hy
    define
    exists (k1*↑a*k3*↑x + k1*k4*↑c*↑x + k2*↑b*k3*↑x + k2*k4*↑y)
    calc ↑(gcd a b * gcd a c)
      _ = (k1 * ↑a + k2 * ↑b) * (k3 * ↑a + k4 * ↑c) := by rw[h1, h2, Nat.cast_mul]
      _ = k1 * ↑a * k3 * ↑a + k1 * ↑a * k4 * ↑c + k2 * ↑b * k3 * ↑a + k2 * ↑b * k4 * ↑c := by
        rw[right_distrib, left_distrib, left_distrib]
        repeat rw[← mul_assoc]
        rw [← add_assoc]
      _ = k1 * ↑a * k3 * ↑x * ↑k + k1 * k4 * ↑c * ↑x * ↑k + ↑k2 * ↑b * k3 * ↑x * ↑k + k2 * k4 * ↑y * ↑k := by
        nth_rw 2 [hx]; rw [Nat.cast_mul, ← mul_assoc]
        have g1: k1 * ↑a * k4 * ↑c = k1 * k4 * ↑c * ↑x * ↑k := by
          rw [hx]; nth_rw 2 [mul_right_comm]
          nth_rw 1 [mul_right_comm]; rw [Nat.cast_mul, ← mul_assoc]
          done
        rw [g1]
        nth_rw 2 [hx]; rw [Nat.cast_mul, ← mul_assoc]
        have g2: k2 * ↑b * k4 * ↑c = k2 * k4 * ↑y * ↑k := by
          rw [mul_right_comm]
          nth_rw 2 [mul_assoc]; rw [← Nat.cast_mul]
          rw [mul_right_comm]; rw[hy, Nat.cast_mul, ← mul_assoc]
          done
        rw [g2]
      _ = (k1 * ↑a * k3 * ↑x + k1 * k4 * ↑c * ↑x + ↑k2 * ↑b * k3 * ↑x + k2 * k4 * ↑y) * ↑k := by
        repeat rw [right_distrib]
      _ = ↑k * (k1 * ↑a * k3 * ↑x + k1 * k4 * ↑c * ↑x + k2 * ↑b * k3 * ↑x + k2 * k4 * ↑y) := by rw [mul_comm]
    done
    -- a = kx
    -- bc = ky
    -- gcd a (b * c) = s * a + t * b * c
    -- gcd a b = k1a + k2b
    -- gcd a c = k3a + k4c
    -- gcd a b * gcd a c = (k1a + k2b)(k3a + k4c)
    -- = k1k3 a^2 + k2k3 ab + k1k4 ac + k2k4 bc
    -- = k1k3ax * k + k2k3bx * k + k1k4cx * k + k2k4y * k


/- Section 7.3 -/
-- 1.
theorem congr_trans {m : Nat} : ∀ {a b c : Int},
    a ≡ b (MOD m) → b ≡ c (MOD m) → a ≡ c (MOD m) := by
    intros a b c hab hbc
    define at hab; obtain c1 hc1 from hab; clear hab
    define at hbc; obtain c2 hc2 from hbc; clear hbc
    define; exists c1 + c2
    calc a - c
      _ = a - b + b - c := by rw[Int.sub_add_cancel a b]
      _ = ↑m * c1 + (b - c) := by rw[hc1, Int.add_sub_assoc]
      _ = ↑m * c1 + ↑m * c2 := by rw[hc2]
      _ = ↑m * (c1 + c2) := by rw[left_distrib]
    done

-- 2.
theorem Theorem_7_3_6_3 {m : Nat} (X : ZMod m) : X + [0]_m = X := by
    obtain a h from cc_rep X
    rw [h]
    rw [add_class]; ring
    done

-- 3.
theorem Theorem_7_3_6_4 {m : Nat} (X : ZMod m) :
    ∃ (Y : ZMod m), X + Y = [0]_m := by
    obtain a h1 from cc_rep X
    rw [h1]
    exists (cc m (-a))
    rw [add_class]; ring
    done

-- 4.
theorem Exercise_7_3_4a {m : Nat} (Z1 Z2 : ZMod m)
    (h1 : ∀ (X : ZMod m), X + Z1 = X)
    (h2 : ∀ (X : ZMod m), X + Z2 = X) : Z1 = Z2 := by
    have h3 := by apply h1 Z2
    have h4 := by apply h2 Z1
    rw[← h3]
    nth_rw 1 [← h4]
    rw [Theorem_7_3_6_1]
    done

-- 5.
theorem Exercise_7_3_4b {m : Nat} (X Y1 Y2 : ZMod m)
    (h1 : X + Y1 = [0]_m) (h2 : X + Y2 = [0]_m) : Y1 = Y2 := by
    obtain a g1 from cc_rep X
    obtain b1 g2 from cc_rep Y1
    obtain b2 g3 from cc_rep Y2
    rw [g1, g2, add_class] at h1
    rw [g1, g3, add_class] at h2
    rw [← h2] at h1
    rw [cc_eq_iff_congr] at h1
    rw [g2, g3]
    obtain k g4 from h1
    rw [cc_eq_iff_congr]; exists k
    rw [← g4]
    ring
    done

-- 6.
theorem Theorem_7_3_10 (m a : Nat) (b : Int) :
    ¬(↑(gcd m a) : Int) ∣ b → ¬∃ (x : Int), a * x ≡ b (MOD m) := by
    contrapos
    intros h1; obtain x h2 from h1; clear h1
    obtain k h1 from h2; clear h2
    have h2 := by apply gcd_dvd_left m a
    obtain k1 hk1 from h2; clear h2
    have h3 := by apply gcd_dvd_right m a
    obtain k2 hk2 from h3; clear h3
    rw [hk1] at h1
    nth_rw 1 [hk2] at h1
    -- k2 * x - k1 * k
    exists ↑k2 * x - ↑k1 * k
    ring
    simp at h1
    linarith
    done

-- 7.
theorem Theorem_7_3_11 (m n : Nat) (a b : Int) (h1 : n ≠ 0) :
    n * a ≡ n * b (MOD n * m) ↔ a ≡ b (MOD m) := by
    apply Iff.intro
    · --↑n * a ≡ ↑n * b (MOD n * m) → a ≡ b (MOD m)
      intros h2
      define at h2; obtain x h3 from h2; clear h2
      define; exists x
      simp at h3
      rw [← mul_sub_left_distrib, mul_assoc] at h3
      #check Int.mul_ediv_cancel_left
      rw [← Int.natCast_ne_zero] at h1
      calc a - b
        _ = ↑n * (a - b) / ↑n := by rw [Int.mul_ediv_cancel_left (a - b) h1]
        _ = ↑n * (↑m * x) / ↑n := by rw[h3]
        _ = ↑m * x := by rw[Int.mul_ediv_cancel_left (↑m * x) h1]
      done
    · --a ≡ b (MOD m) → ↑n * a ≡ ↑n * b (MOD n * m)
      intros h2; define at h2
      obtain x h3 from h2; clear h2
      exists x
      rw [← mul_sub_left_distrib, h3, ← mul_assoc, Nat.cast_mul]
      done

-- 8.
theorem Exercise_7_3_16 {m : Nat} {a b : Int} (h : a ≡ b (MOD m)) :
    ∀ (n : Nat), a ^ n ≡ b ^ n (MOD m) := by
    define at h; obtain k h1 from h; clear h
    by_strong_induc
    intros n ih
    · by_cases g1: n = 0
      · -- n = 0
        rw[g1]; exists 0; ring
      · by_cases g2: n = 1
        · -- n = 1
          rw[g2]; exists k; ring; apply h1
        · -- n > 1
          have g3 : n - 1 < n := by apply Nat.sub_one_lt g1
          have ih1 := by apply ih (n - 1) g3
          have g4: 0 < n := by linarith
          have g5: 1 ≤ n := by linarith
          have h2: n - 2 < n := by
            calc n - 2
              _ = n - (1 + 1) := by ring
              _ = n - 1 - 1 := by apply Nat.sub_add_eq
              _ < n - 1 := by
                apply Nat.sub_one_lt
                contradict g2 with tmp
                calc n = n - 1 + 1 := by rw[Nat.sub_add_cancel g5]
                    _ = 0 + 1 := by rw[tmp]
                    _ = 1 := by ring
              _ < n := by linarith
          have ih2 := by apply ih (n - 2) h2
          obtain x h3 from ih1; clear ih1
          obtain y h4 from ih2; clear ih2
          -- mx(a+b) - myab
          exists x * (a + b) - y * a * b
          symm
          rw [mul_sub_left_distrib, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← h3, ← h4]; ring
          nth_rw 1 [← Int.pow_one a]
          nth_rw 3 [← Int.pow_one a]
          nth_rw 2 [← Int.pow_one b]
          nth_rw 6 [← Int.pow_one b]
          nth_rw 2 [mul_assoc]
          rw [← Int.pow_add, ← Int.pow_add, ← Int.pow_add, ← Int.pow_add]
          have h5: 1 + (n - 1) = n := by
            rw [← Nat.add_sub_assoc g5 1]
            rw [add_comm, Nat.add_sub_cancel]
          have t1: 1 < n := by
            apply Nat.lt_of_le_of_ne g5
            contradict g2 with t2
            rw [t2]
          have tmp : 2 ≤ n := by apply Nat.add_one_le_of_lt t1
          have h6: 1 + (n - 2) = n - 1 := by
            rw [← Nat.add_sub_assoc tmp 1]
            rw [add_comm]
            calc n + 1 - 2
              _ = n + 1 - (1 + 1) := by ring
              _ = n + 1 - 1 - 1 := by rw[← Nat.sub_add_eq]
              _ = n - 1 := by rw[Nat.add_sub_cancel]
          rw [h5, h6]; ring
    done

-- 9.
example {m : Nat} [NeZero m] (X : ZMod m) :
    ∃! (a : Int), 0 ≤ a ∧ a < m ∧ X = [a]_m := by
    exists_unique
    · --existence
      obtain a h1 from cc_rep X
      exists a % m
      have h2 := by apply mod_cmpl_res m a
      apply And.intro h2.left
      apply And.intro h2.right.left
      rw [h1]; apply cc_eq_mod m a
    · --uniqueness
      intros a1 a2 h1 h2
      have g1 := h1.right.right
      have g2 := h2.right.right
      rw [g1] at g2
      have g3 := by apply cc_eq_iff_congr m a1 a2
      rw [g3] at g2
      obtain k g4 from g2; clear g2
      have g5: a1 - a2 < m * 1 := by linarith
      have g6 : m * (-1) < a1 - a2 := by linarith
      rw [g4] at g5
      rw [g4] at g6
      have g7: (↑m: Int) ≥ 0 := Nat.cast_nonneg m
      have g8 : k < 1 := lt_of_mul_lt_mul_of_nonneg_left g5 g7
      have g9 : -1 < k := lt_of_mul_lt_mul_of_nonneg_left g6 g7
      have g10 : k = 0 := by linarith
      rw [g10] at g4
      calc a1
        _ = a1 - a2 + a2 := by ring
        _ = ↑m * 0 + a2 := by rw[g4]
        _ = a2 := by ring
      done

-- 10.
theorem congr_rel_prime {m a b : Nat} (h1 : a ≡ b (MOD m)) :
    rel_prime m a ↔ rel_prime m b := by
    apply Iff.intro
    · --rel_prime m a → rel_prime m b
      intros h2
      rw [Exercise_7_2_6] at h2
      obtain s tmp from h2; clear h2
      obtain t h2 from tmp; clear tmp
      obtain k h3 from h1; clear h1
      rw [Exercise_7_2_6]
      exists s + t * k
      exists t
      rw [← h2]
      have h4: a = m * k + b := by
        calc ↑a
          _ = (↑a: Int) - b + b := by rw [sub_add_cancel]
          _ = ↑m * k + b := by rw[h3]
        done
      rw [h4]; ring
    · --rel_prime m b → rel_prime m a
      intros h2
      rw [Exercise_7_2_6] at h2
      obtain s tmp from h2; clear h2
      obtain t h2 from tmp; clear tmp
      obtain k h3 from h1; clear h1
      rw [Exercise_7_2_6]
      -- sm + tb = sm + t(a - mk) = 1
      -- (s-tk)m + ta = 1
      exists s - t * k
      exists t
      rw [← h2]
      have h4: a = m * k + b := by
        calc ↑a
          _ = (↑a: Int) - b + b := by rw [sub_add_cancel]
          _ = ↑m * k + b := by rw[h3]
        done
      rw [h4]; ring
    done

-- 11.
--Hint: You may find the theorem Int.ofNat_mod_ofNat useful.
theorem rel_prime_mod (m a : Nat) :
    rel_prime m (a % m) ↔ rel_prime m a := by
    apply Iff.intro
    #check Int.ofNat_mod_ofNat
    -- ∀ (m n : ℕ), ↑m % ↑n = ↑(m % n)
    · --rel_prime m (a % m) → rel_prime m a
      intros h1
      rw [Exercise_7_2_6] at h1
      obtain s t1 from h1; clear h1
      obtain t h1 from t1; clear t1
      rw [Exercise_7_2_6]
      -- s * m + t * (a%m) = 1
      -- s * m + t * (a - a/m * m) = 1
      -- (s - t * a/m) * m + t * a = 1
      set q := a / m
      exists s - t * q
      exists t
      have h2:  m * q + a % m = a := Nat.div_add_mod a m
      #check Nat.cast_div
      have h3: (↑a: Int) - m * q = ↑(a % m) := by
        calc (↑a: Int) - m * q
          _ = ↑(m * q + a % m) - m * q := by nth_rw 1 [← h2]
          _ = ↑(a % m) + m * q - m * q := by rw[add_comm, Nat.cast_add, Nat.cast_mul]
          _ = a % m := by rw[Int.add_sub_cancel ↑(a % m) (↑m * ↑q), Int.ofNat_mod_ofNat]
      rw [← h1, ← h3]
      ring
    · --rel_prime m a → rel_prime m (a % m)
      intros h1
      rw [Exercise_7_2_6] at h1
      obtain s t1 from h1; clear h1
      obtain t h1 from t1; clear t1
      rw [Exercise_7_2_6]
      -- sm + ta = sm + t(qm + a%m) = (s+tq)m + t*a%m = 1
      set q := a / m
      exists s + t * q
      exists t
      have h2:  m * q + a % m = a := Nat.div_add_mod a m
      rw [← h1]; nth_rw 2 [← h2]
      ring
      rw [Nat.cast_add, left_distrib, ←add_assoc, Nat.cast_mul]
      nth_rw 7 [mul_comm]
      rw [mul_assoc]
    done

-- 12.
lemma congr_iff_mod_eq_Int (m : Nat) (a b : Int) [NeZero m] :
    a ≡ b (MOD m) ↔ a % ↑m = b % ↑m := by
    apply Iff.intro
    · --a ≡ b (MOD m) → a % ↑m = b % ↑m
      intros h1
      have h2 := by apply congr_mod_mod m a
      have h3 := by apply congr_mod_mod m b
      have h4: a ≡ b % m (MOD m) := by
        apply congr_trans h1 h3
      -- Theorem_7_3_1 shows the uniqueness of r
      have h := by apply Theorem_7_3_1 m a
      define at h
      obtain r hr from h; clear h
      have h5 := hr.right; clear hr
      have g1 := by apply mod_cmpl_res m a
      have g2 := by apply mod_cmpl_res m b
      have g3 := by
        apply h5 (a % m)
        apply And.intro g1.left
        apply And.intro g1.right.left h2
      have g4 := by
        apply h5 (b % m)
        apply And.intro g2.left
        apply And.intro g2.right.left h4
      rw [g3, g4]
    · --a % ↑m = b % ↑m → a ≡ b (MOD m)
      intros h1
      have h2 := by apply Int.mul_ediv_add_emod a m
      have h3 := by apply Int.mul_ediv_add_emod b m
      set q1 := a / m
      set q2 := b / m
      exists q1 - q2
      rw[← h2, ← h3, h1]
      ring
    done
--Hint for next theorem: Use the lemma above,
--together with the theorems Int.ofNat_mod_ofNat and Nat.cast_inj.
theorem congr_iff_mod_eq_Nat (m a b : Nat) [NeZero m] :
    ↑a ≡ ↑b (MOD m) ↔ a % m = b % m := by
    apply Iff.intro
    · --↑a ≡ ↑b (MOD m) → a % m = b % m
      intros h1
      rw [congr_iff_mod_eq_Int] at h1
      rw [Int.ofNat_mod_ofNat, Int.ofNat_mod_ofNat, Nat.cast_inj] at h1
      apply h1
    · --a % m = b % m → ↑a ≡ ↑b (MOD m)
      intros h1
      rw [congr_iff_mod_eq_Int]
      rw[Int.ofNat_mod_ofNat, Int.ofNat_mod_ofNat, Nat.cast_inj]
      apply h1
      done

/- Section 7.4 -/
-- 1.
--Hint:  Use induction.
--For the base case, compute [a]_m ^ 0 * [1]_m in two ways:
--by Theorem_7_3_6_7, [a] ^ 0 * [1]_m = [a]_m ^ 0
--by ring, [a]_m ^ 0 * [1]_m = [1]_m.
lemma Exercise_7_4_5_Int (m : Nat) (a : Int) :
    ∀ (n : Nat), [a]_m ^ n = [a ^ n]_m := by
    by_induc
    · -- base case, n = 0
      have h1: [a]_m ^ 0 * [1]_m = [a]_m ^ 0 := by
        apply Theorem_7_3_6_7
      have h2: [a]_m ^ 0 * [1]_m = [a ^ 0]_m := by
        ring
      rw[← h1, ← h2]
    · -- induction case
      intros n h1
      calc [a]_m ^ (n + 1)
        _ = [a]_m ^ n * [a]_m := by ring
        _ = [a ^ n]_m * [a]_m := by rw[h1]
        _ = [a ^ n * a]_m := by apply mul_class
        _ = [a ^ (n + 1)]_m := by ring
      done

-- 2.
lemma left_inv_one_one_below {n : Nat} {g g' : Nat → Nat}
    (h1 : ∀ i < n, g' (g i) = i) : one_one_below n g := by
  define
  intros i hi j hj heq
  have h2 := by apply h1 i hi
  have h3 := by apply h1 j hj
  rw [← h2, ← h3, heq]
  done

-- 3.
lemma comp_perm_below {n : Nat} {f g : Nat → Nat}
    (h1 : perm_below n f) (h2 : perm_below n g) :
    perm_below n (f ∘ g) := by
    define; define at h1; define at h2
    apply And.intro
    · --maps_below n (f ∘ g)
      define; intros i h3
      apply h1.left
      apply h2.left
      apply h3
    · apply And.intro
      · --one_one_below n (f ∘ g)
        define; intros i hi j hj heq
        apply h1.right.left at heq
        apply h2.right.left at heq
        apply heq
        apply hi; apply hj
        apply h2.left
        apply hi
        apply h2.left; apply hj
      · --onto_below n (f ∘ g)
        define; intros k hk
        apply h1.right.right at hk
        obtain x hx from hk; clear hk
        have hxn := hx.left
        apply h2.right.right at hxn
        obtain y hy from hxn; clear hxn
        exists y
        apply And.intro hy.left
        rw [comp_def, hy.right]
        apply hx.right
      done

-- 4.
lemma perm_below_fixed {n : Nat} {g : Nat → Nat}
    (h1 : perm_below (n + 1) g) (h2 : g n = n) : perm_below n g := by
    define at h1; define
    have g1 := h1.left; define at g1
    have g2 := h1.right.left; define at g2
    have g3 := h1.right.right; define at g3
    clear h1
    apply And.intro
    · --maps_below n g
      define; intros i hi
      have gi: i < n + 1 := by linarith
      apply g1 at gi
      have gne: g i ≠ n := by
        by_contra g4
        rw [← h2] at g4
        apply g2 at g4
        linarith -- i < n contradict with i = n
        linarith; linarith
      have g4: g i ≤ n := by linarith
      apply Nat.lt_of_le_of_ne g4 gne
    · apply And.intro
      · --one_one_below n g
        define; intros i hi j hj heq
        apply g2
        linarith; linarith
        apply heq
      · --onto_below n g
        define; intros j hj
        have gj : j < n + 1 := by linarith
        apply g3 at gj
        obtain i gi from gj
        have hne: i ≠ n := by
          by_contra g4
          rw[g4] at gi
          rw[gi.right] at h2
          linarith
        have g4: i ≤ n := by linarith
        have g5: i < n := by
          apply Nat.lt_of_le_of_ne g4 hne
        exists i
        apply And.intro g5 gi.right
      done

-- 5.
lemma Lemma_7_4_6 {a b c : Nat} :
    rel_prime (a * b) c ↔ rel_prime a c ∧ rel_prime b c := by
    apply Iff.intro
    · --rel_prime (a * b) c → rel_prime a c ∧ rel_prime b c
      intros h1
      rw [Exercise_7_2_6] at h1
      obtain s t1 from h1
      obtain t h2 from t1
      clear h1; clear t1
      apply And.intro
      · --rel_prime a c
        rw [Exercise_7_2_6]
        exists s * b
        exists t
        rw [← h2, mul_comm a b, Nat.cast_mul, ← mul_assoc]
      · --rel_prime b c
        rw [Exercise_7_2_6]
        exists s * a
        exists t
        rw [← h2, Nat.cast_mul, ← mul_assoc]
      done
    · --rel_prime a c ∧ rel_prime b c → rel_prime (a * b) c
      intros h1
      have h2 := h1.left; rw [Exercise_7_2_6] at h2
      have h3 := h1.right; rw [Exercise_7_2_6] at h3
      clear h1
      obtain s1 tmp from h2;
      obtain t1 h1 from tmp;
      clear tmp; clear h2
      obtain s2 tmp from h3;
      obtain t2 h2 from tmp;
      clear tmp; clear h3
      rw [Exercise_7_2_6]
      -- (s1 a + t1 c)(s2 b + t2 c) = 1
      -- s1s2 a b + (s1 a t2 + t1 s2 b + t1 t2) c = 1
      exists s1 * s2
      exists s1 * a * t2 + t1 * s2 * b + t1 * t2 * c
      have h3 : (s1 * ↑a + t1 * ↑c) * (s2 * ↑b + t2 * ↑c) = 1 := by
        rw [h1, h2]; ring
      rw [← h3]; ring
      rw [Nat.cast_mul, ← mul_assoc]
    done

-- 6.
example {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    a ^ (phi m + 1) ≡ a (MOD m) := by
    have h2 := by apply Euler's_theorem h1
    obtain k h3 from h2; clear h2
    define; exists a * k
    have h2: a ^ phi m = m * k + 1 := by linarith
    ring; rw [h2]; ring
    done

-- 7.
theorem Like_Exercise_7_4_11 {m a p : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : p + 1 = phi m) :
    [a]_m * [a ^ p]_m = [1]_m := by
    rw [mul_class]
    have h3: (↑a: Int) * ↑a ^ p = a ^ phi m := by
      nth_rw 1 [← pow_one a, Nat.cast_pow]
      rw [← pow_add, add_comm, h2]
    rw [h3]
    rw [← Exercise_7_4_5_Int m a (phi m)]
    apply Theorem_7_4_2 h1
    done

-- 8.
theorem Like_Exercise_7_4_12 {m a p q k : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : p = q + (phi m) * k) :
    a ^ p ≡ a ^ q (MOD m) := by
    have h3 := by apply Euler's_theorem h1
    rw [← cc_eq_iff_congr]
    rw [← cc_eq_iff_congr] at h3
    rw [h2, pow_add, ← mul_class, pow_mul, ← Exercise_7_4_5_Int m _ k]
    rw [h3, Exercise_7_4_5_Int]; ring
    rw [mul_class]; ring
    done

/- Section 7.5 -/
-- 1.
--Hint:  Use induction.
lemma num_rp_prime {p : Nat} (h1 : prime p) :
    ∀ k < p, num_rp_below p (k + 1) = k := by
    by_induc
    · --k = 0
      intros h2
      have h3: ¬rel_prime p 0 := by
        define; rw [gcd]
        have g1 := h1.left
        linarith
      rw [num_rp_below_step_not_rp h3]
      apply num_rp_below_base
    · --induction case
      intros k h2 h3
      have h4: rel_prime p (k + 1) := by
        apply rel_prime_symm
        apply rel_prime_of_prime_not_dvd h1
        by_contra contra
        obtain x gx from contra
        rw[gx] at h3
        nth_rw 2 [← mul_one p] at h3
        have g1: 0 ≤ p := by linarith
        #check lt_of_mul_lt_mul_left
        have hx: x < 1 := by apply lt_of_mul_lt_mul_left h3 g1
        have hxzero : x = 0 := by linarith
        rw [hxzero, mul_zero] at gx
        linarith
      rw [num_rp_below_step_rp h4, h2]
      linarith
    done

-- 2.
lemma three_prime : prime 3 := by
    apply And.intro
    · -- 2 ≤ 3
      linarith
    · -- ¬∃ (a : ℕ) (b : ℕ), a * b = 3 ∧ a < 3 ∧ b < 3
      by_contra h1
      obtain a tmp from h1
      obtain b h2 from tmp
      clear h1; clear tmp
      by_cases azero: a = 0
      · -- a = 0
        have h1 := h2.left
        rw [azero] at h1
        linarith
      · by_cases aone: a = 1
        -- a = 1
        have h1 := h2.left
        rw [aone] at h1
        have h3: b = 3 := by linarith
        linarith
        · by_cases atwo: a = 2
          -- a = 2
          have h1 := h2.left
          rw [atwo] at h1
          by_cases bzero: b = 0
          · -- b = 0
            rw [bzero] at h1; linarith
          · by_cases bone: b = 1
            · --b = 1
              rw [bone] at h1
              linarith
            · --b > 1
              have h3: b >= 2 := by linarith
              linarith
          · -- a > 2
            have h1 := h2.left
            have h3: a ≥ 1 := by apply pos_of_ne_zero azero
            have h4 : a > 1 := by
              apply lt_of_le_of_ne h3
              rw [ne_comm]
              apply aone
            have h5: 2 ≤ a := by apply Nat.add_one_le_of_lt h4
            have h6: a > 2 := by
              apply lt_of_le_of_ne h5
              rw [ne_comm]
              apply atwo
            linarith
      done

-- 3.
--Hint:  Use the previous exercise, Exercise_7_2_7, and Theorem_7_4_2.
theorem Exercise_7_5_13a (a : Nat) (h1 : rel_prime 561 a) :
    a ^ 560 ≡ 1 (MOD 3) := by
    rw [← cc_eq_iff_congr]
    have g1 : 3 ∣ 561 := by decide
    have g2 : a ∣ a := by
      exists 1; ring
    have h2: rel_prime 3 a := by
      apply Exercise_7_2_7 h1 g1 g2
    have h3 : phi 3 = 2 := by apply phi_prime three_prime
    calc [a ^ 560]_3
      _ = [a]_3 ^ 560 := by rw[Exercise_7_4_5_Int 3 a 560]
      _ = [a]_3 ^ (2 * 280) := by ring
      _ = ([a]_3 ^ 2) ^ 280 := by rw[pow_mul]
      _ = ([a]_3 ^ (phi 3)) ^ 280 := by rw [h3]
      _ = [1]_3 ^ 280 := by rw [Theorem_7_4_2 h2]
      _ = [1 ^ 280]_3 := by rw[Exercise_7_4_5_Int]
      _ = [1]_3 := by ring
    done

-- 4.
--Hint:  Imitate the way Theorem_7_2_2_Int was proven from Theorem_7_2_2.
lemma Theorem_7_2_3_Int {p : Nat} {a b : Int}
    (h1 : prime p) (h2 : ↑p ∣ a * b) : ↑p ∣ a ∨ ↑p ∣ b := by
    #check Theorem_7_2_3
    rw [Int.natCast_dvd, Int.natAbs_mul] at h2
    rw[Int.natCast_dvd, Int.natCast_dvd]
    apply Theorem_7_2_3 h1 at h2
    apply h2
    done

-- 5.
--Hint:  Use the previous exercise.
theorem Exercise_7_5_14b (n : Nat) (b : Int)
    (h1 : prime n) (h2 : b ^ 2 ≡ 1 (MOD n)) :
    b ≡ 1 (MOD n) ∨ b ≡ -1 (MOD n) := by
    apply Theorem_7_2_3_Int h1
    ring; rw [add_comm]
    define at h2
    obtain x h3 from h2; clear h2
    exists x
    done
